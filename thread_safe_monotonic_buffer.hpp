#pragma once

#include <atomic>
#include <cstddef>
#include <memory_resource>
#include <new>

namespace tsmbr {

// Thread-safe monotonic buffer resource using lock-free atomic operations
// Based on formal verification in ThreadSafeMonotonicBuffer.dfy
class thread_safe_monotonic_buffer_resource : public std::pmr::memory_resource {
private:
    // Internal chunk footer structure (corresponds to ChunkFooter in ThreadSafeMonotonicBuffer.dfy:79-92)
    struct ChunkFooter {
        void* allocation_ptr = nullptr;           // Start of usable memory
        size_t allocation_size = 0;               // Total chunk size
        std::atomic<size_t> next{0};              // Next allocation offset (atomic!)
        ChunkFooter* prev = nullptr;              // Previous chunk in chain

        // Invariant from ThreadSafeMonotonicBuffer.dfy:87 - next <= allocation_size
        bool valid() const noexcept {
            return next.load(std::memory_order_relaxed) <= allocation_size;
        }

        void* base() const noexcept {
            return allocation_ptr;
        }

        size_t hwm() const noexcept {
            return next.load(std::memory_order_relaxed);
        }
    };

    std::atomic<ChunkFooter*> current;       // Current active chunk
    ChunkFooter initial;                     // Initial buffer descriptor
    std::pmr::memory_resource* upstream;     // Upstream allocator
    size_t next_buffer_size;                 // Size for next allocation

    static constexpr size_t default_buffer_size = 1024;
    static constexpr size_t growth_factor = 2;

    // Corresponds to alignUp function in Dafny (ThreadSafeMonotonicBuffer.dfy:65-69)
    static size_t align_up(size_t offset, size_t alignment) noexcept {
        return ((offset + alignment - 1) / alignment) * alignment;
    }

    // Verify alignment is power of 2 (corresponds to isValidAlignment in Dafny ThreadSafeMonotonicBuffer.dfy:25-28)
    static bool is_valid_alignment(size_t alignment) noexcept {
        return alignment > 0 && (alignment & (alignment - 1)) == 0;
    }

    // Construct a new chunk footer at the end of allocated memory
    static ChunkFooter* construct_chunk_footer(
        void* ptr,
        size_t size,
        ChunkFooter* prev
    ) noexcept {
        // Place footer at end of allocation
        auto footer = static_cast<ChunkFooter*>(
            static_cast<void*>(
                static_cast<char*>(ptr) + size - sizeof(ChunkFooter)
            )
        );

        footer->allocation_ptr = ptr;
        footer->allocation_size = size - sizeof(ChunkFooter);
        footer->next.store(0, std::memory_order_relaxed);
        footer->prev = prev;

        return footer;
    }

    // Try to allocate from existing chunk using CAS loop
    // Corresponds to tryAllocateWithCAS in ThreadSafeMonotonicBuffer.dfy:202-262
    void* try_allocate_from_chunk(
        ChunkFooter* chunk,
        size_t bytes,
        size_t alignment
    ) noexcept {
        // CAS loop - corresponds to while true loop in ThreadSafeMonotonicBuffer.dfy:222
        while (true) {
            // Load current offset (ThreadSafeMonotonicBuffer.dfy:229)
            size_t old_offset = chunk->next.load(std::memory_order_relaxed);

            // Compute aligned offset (ThreadSafeMonotonicBuffer.dfy:230-231)
            size_t aligned_offset = align_up(old_offset, alignment);
            size_t new_offset = aligned_offset + bytes;

            // Check bounds - Invariant: new_offset <= allocation_size (ThreadSafeMonotonicBuffer.dfy:233)
            if (new_offset > chunk->allocation_size) {
                return nullptr;  // No space in this chunk
            }

            // Try CAS to claim this offset range (ThreadSafeMonotonicBuffer.dfy:235)
            // Corresponds to atomicCAS in ThreadSafeMonotonicBuffer.dfy:98-123
            if (chunk->next.compare_exchange_weak(
                old_offset,
                new_offset,
                std::memory_order_release,
                std::memory_order_relaxed
            )) {
                // CASSuccess case (ThreadSafeMonotonicBuffer.dfy:238-250)
                // We atomically claimed [aligned_offset, new_offset)
                // Proven non-overlapping by casDisjointnessTheorem (ThreadSafeMonotonicBuffer.dfy:269-300)
                return static_cast<char*>(chunk->base()) + aligned_offset;
            }

            // CASFailure case (ThreadSafeMonotonicBuffer.dfy:252-255) - another thread won, retry
        }
    }

    // Allocate a new chunk from upstream
    ChunkFooter* allocate_new_chunk(
        size_t bytes,
        size_t alignment,
        ChunkFooter* prev_chunk
    ) {
        // Calculate new chunk size
        size_t needed = bytes + alignment + sizeof(ChunkFooter);
        size_t new_size = (needed > next_buffer_size) ? needed : next_buffer_size;

        // Update next buffer size for geometric growth
        next_buffer_size = new_size * growth_factor;

        // Allocate from upstream
        void* ptr = upstream->allocate(new_size, alignof(ChunkFooter));

        // Initialize new chunk
        return construct_chunk_footer(ptr, new_size, prev_chunk);
    }

protected:
    // Core allocation routine
    // Thread-safe via CAS operations - proven by linearizabilityTheorem (ThreadSafeMonotonicBuffer.dfy:303-309)
    void* do_allocate(size_t bytes, size_t alignment) override {
        if (bytes == 0) {
            return nullptr;
        }

        if (!is_valid_alignment(alignment)) {
            throw std::bad_alloc();
        }

        while (true) {
            // Load current chunk (atomic acquire)
            ChunkFooter* chunk = current.load(std::memory_order_acquire);

            // Attempt bump allocation with CAS loop
            // Non-overlapping allocations guaranteed by raceFreedomTheorem (ThreadSafeMonotonicBuffer.dfy:351-365)
            void* result = try_allocate_from_chunk(chunk, bytes, alignment);
            if (result != nullptr) {
                return result;
            }

            // No space in current chunk: allocate once, then keep reattaching to
            // the moving head until we become the new head.
            ChunkFooter* new_chunk = allocate_new_chunk(bytes, alignment, chunk);

            ChunkFooter* expected = chunk;
            while (!current.compare_exchange_weak(
                expected,
                new_chunk,
                std::memory_order_acq_rel,
                std::memory_order_acquire
            )) {
                // Another thread published a chunk first. Point at the new head
                // and retry without discarding our standby chunk.
                chunk = expected;
                new_chunk->prev = chunk;
                new_chunk->next.store(0, std::memory_order_relaxed);
                expected = chunk;
            }

            continue;
        }
    }

    // No-op: monotonic semantics
    void do_deallocate(void* p, size_t bytes, size_t alignment) noexcept override {
        (void)p;
        (void)bytes;
        (void)alignment;
        // Monotonic allocator: deallocate is a no-op
    }

    bool do_is_equal(const std::pmr::memory_resource& other) const noexcept override {
        return this == &other;
    }

public:
    // Default constructor
    thread_safe_monotonic_buffer_resource()
        : upstream(std::pmr::get_default_resource())
        , next_buffer_size(default_buffer_size)
    {
        current.store(&initial, std::memory_order_relaxed);
    }

    // Constructor with upstream resource
    explicit thread_safe_monotonic_buffer_resource(std::pmr::memory_resource* upstream_arg)
        : upstream(upstream_arg ? upstream_arg : std::pmr::get_default_resource())
        , next_buffer_size(default_buffer_size)
    {
        current.store(&initial, std::memory_order_relaxed);
    }

    // Constructor with initial size
    thread_safe_monotonic_buffer_resource(
        size_t initial_size,
        std::pmr::memory_resource* upstream_arg
    )
        : upstream(upstream_arg ? upstream_arg : std::pmr::get_default_resource())
        , next_buffer_size(initial_size * growth_factor)
    {
        current.store(&initial, std::memory_order_relaxed);
    }

    // Constructor with initial buffer
    thread_safe_monotonic_buffer_resource(
        void* buffer,
        size_t buffer_size,
        std::pmr::memory_resource* upstream_arg
    )
        : upstream(upstream_arg ? upstream_arg : std::pmr::get_default_resource())
        , next_buffer_size(buffer_size * growth_factor)
    {
        initial.allocation_ptr = buffer;
        initial.allocation_size = buffer_size;
        current.store(&initial, std::memory_order_relaxed);
    }

    // Destructor - calls release()
    ~thread_safe_monotonic_buffer_resource() override {
        release();
    }

    // Non-copyable, non-movable
    thread_safe_monotonic_buffer_resource(const thread_safe_monotonic_buffer_resource&) = delete;
    thread_safe_monotonic_buffer_resource& operator=(const thread_safe_monotonic_buffer_resource&) = delete;

    // Release all allocated memory
    // WARNING: Requires external synchronization (no concurrent allocations)
    void release() noexcept {
        // Walk chunk chain and deallocate
        ChunkFooter* curr = current.load(std::memory_order_relaxed);

        while (curr != &initial) {
            ChunkFooter* prev = curr->prev;
            void* ptr = curr->allocation_ptr;
            size_t size = curr->allocation_size + sizeof(ChunkFooter);
            upstream->deallocate(ptr, size, alignof(ChunkFooter));
            curr = prev;
        }

        // Reset initial chunk
        current.store(&initial, std::memory_order_relaxed);
        initial.next.store(0, std::memory_order_relaxed);
    }

    // Get upstream resource
    std::pmr::memory_resource* upstream_resource() const noexcept {
        return upstream;
    }
};

} // namespace tsmbr
