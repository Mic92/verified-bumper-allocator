# Thread-Safe Monotonic Buffer Resource

A lock-free, thread-safe bump allocator using atomic operations with chained buffer allocation strategy.
This implementation is based on formal verification in Dafny.

## Features

- **Thread-safe**: Multiple threads can allocate concurrently without locks
- **Lock-free**: System-wide progress guaranteed (individual threads may retry on contention)
- **Formally verified**: Implementation corresponds to verified Dafny specification
- **Drop-in replacement**: Compatible with `std::pmr::memory_resource` interface

## Formal Guarantees

The implementation is based on the formal proof in `ThreadSafeMonotonicBuffer.dfy`, which proves:

1. **Linearizability** (`linearizabilityTheorem` - line 303): All concurrent operations are linearizable to a sequential execution
2. **Memory Safety** (`casDisjointnessTheorem` - line 269): No allocation overlaps another
3. **Race Freedom** (`raceFreedomTheorem` - line 351): Pairwise disjointness from monotonic ordering
4. **Lock-Freedom**: System-wide progress guaranteed (some thread always makes progress)

## Usage

```cpp
#include "thread_safe_monotonic_buffer.hpp"

// Basic usage
tsmbr::thread_safe_monotonic_buffer_resource pool;
void* p = pool.allocate(1024, 8);

// Multi-threaded usage
tsmbr::thread_safe_monotonic_buffer_resource shared_pool;
std::vector<std::thread> threads;

for (int i = 0; i < 10; ++i) {
    threads.emplace_back([&shared_pool] {
        void* p = shared_pool.allocate(sizeof(int) * 100, alignof(int));
        // Use allocation...
    });
}

for (auto& t : threads) t.join();
shared_pool.release(); // Safe: no concurrent allocations
```

## Constructors

```cpp
// Default: uses std::pmr::get_default_resource()
thread_safe_monotonic_buffer_resource();

// With custom upstream allocator
explicit thread_safe_monotonic_buffer_resource(std::pmr::memory_resource* upstream);

// With initial size hint
thread_safe_monotonic_buffer_resource(size_t initial_size,
                                      std::pmr::memory_resource* upstream);

// With initial buffer (user-provided storage)
thread_safe_monotonic_buffer_resource(void* buffer,
                                      size_t buffer_size,
                                      std::pmr::memory_resource* upstream);
```

## API

### `void* allocate(size_t bytes, size_t alignment)`
Allocate `bytes` with specified `alignment`. Thread-safe and lock-free.

### `void deallocate(void* p, size_t bytes, size_t alignment) noexcept`
No-op (monotonic semantics). Thread-safe.

### `void release() noexcept`
Release all allocated memory. **Requires external synchronization** - undefined if concurrent allocations occur.

### `std::pmr::memory_resource* upstream_resource() const noexcept`
Get the upstream allocator. Thread-safe.

## Implementation Details

### Algorithm

The allocator uses a lock-free CAS (compare-and-swap) loop for bump allocation:

1. Load current chunk atomically
2. Attempt bump allocation with CAS
3. On success: return allocated pointer
4. On failure: retry or allocate new chunk

See `ThreadSafeMonotonicBuffer.dfy:202-262` for the verified algorithm.

### Data Structures

```cpp
struct ChunkFooter {
    void* allocation_ptr;           // Start of usable memory
    size_t allocation_size;         // Total chunk size
    std::atomic<size_t> next;       // Next allocation offset (atomic!)
    ChunkFooter* prev;              // Previous chunk in chain
};
```

**Invariant** (from `ThreadSafeMonotonicBuffer.dfy:87`): `next <= allocation_size`

### Thread-Safety

- **allocate()**: Lock-free, thread-safe
- **deallocate()**: Thread-safe (no-op)
- **release()**: Requires external synchronization
- **upstream_resource()**: Thread-safe (immutable after construction)

## Building and Testing

```bash
# Run tests
make check

# Run benchmark
make bench

# Verify formal proof
make verify
```

## Files

- `thread_safe_monotonic_buffer.hpp` - C++ implementation
- `ThreadSafeMonotonicBuffer.dfy` - Formal verification in Dafny
- `test_thread_safe_monotonic_buffer.cpp` - Test suite
- `spec.md` - Detailed specification

## Verification

The Dafny proof can be verified with `make verify`.

## Performance Characteristics

- **Common case**: Lock-free bump allocation (single CAS on success)
- **Chunk overflow**: One upstream allocation + CAS to install new chunk
- **Contention**: CAS retry loop (unbounded retries possible, but system makes progress)
- **Overhead**: One or more atomic operations per allocation

## Limitations

- No concurrent `release()` - requires external synchronization
- Monotonic only - `deallocate()` is a no-op
- Memory is only reclaimed on `release()` or destruction

## License

See project license.
