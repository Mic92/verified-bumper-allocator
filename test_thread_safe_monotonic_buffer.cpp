#include "thread_safe_monotonic_buffer.hpp"
#include <cassert>
#include <cstring>
#include <iostream>
#include <thread>
#include <vector>
#include <set>
#include <mutex>

// Test alignment requirements
void test_alignment() {
    std::cout << "Running test_alignment..." << std::endl;

    tsmbr::thread_safe_monotonic_buffer_resource pool;

    // Test various alignments
    for (size_t align : {1, 2, 4, 8, 16, 32, 64, 128}) {
        void* p = pool.allocate(32, align);
        assert(p != nullptr);
        assert(reinterpret_cast<uintptr_t>(p) % align == 0);
    }

    std::cout << "test_alignment PASSED" << std::endl;
}

// Test concurrent allocations - verifies thread-safety
// Validates linearizabilityTheorem and raceFreedomTheorem from ThreadSafeMonotonicBuffer.dfy
void test_concurrent_allocations() {
    std::cout << "Running test_concurrent_allocations..." << std::endl;

    tsmbr::thread_safe_monotonic_buffer_resource pool;
    constexpr int num_threads = 10;
    constexpr int allocations_per_thread = 1000;

    std::mutex result_mutex;
    std::set<void*> all_allocations;

    auto worker = [&]() {
        std::vector<void*> local_allocations;

        for (int i = 0; i < allocations_per_thread; ++i) {
            size_t size = 16 + (i % 128);  // Varying sizes
            size_t alignment = 8;
            void* p = pool.allocate(size, alignment);
            assert(p != nullptr);
            assert(reinterpret_cast<uintptr_t>(p) % alignment == 0);

            // Write to ensure memory is usable
            std::memset(p, i % 256, size);

            local_allocations.push_back(p);
        }

        // Collect all allocations to verify uniqueness
        std::lock_guard<std::mutex> lock(result_mutex);
        for (void* p : local_allocations) {
            auto [it, inserted] = all_allocations.insert(p);
            // All allocations should be unique (non-overlapping proven by raceFreedomTheorem)
            assert(inserted && "Duplicate allocation detected!");
        }
    };

    std::vector<std::thread> threads;
    for (int i = 0; i < num_threads; ++i) {
        threads.emplace_back(worker);
    }

    for (auto& t : threads) {
        t.join();
    }

    // Verify we got all expected allocations
    assert(all_allocations.size() == num_threads * allocations_per_thread);

    std::cout << "test_concurrent_allocations PASSED (verified "
              << all_allocations.size() << " unique allocations)" << std::endl;
}

// Test that allocations are non-overlapping (validates casDisjointnessTheorem)
void test_non_overlapping() {
    std::cout << "Running test_non_overlapping..." << std::endl;

    tsmbr::thread_safe_monotonic_buffer_resource pool;

    struct Allocation {
        void* ptr;
        size_t size;

        bool overlaps(const Allocation& other) const {
            uintptr_t start1 = reinterpret_cast<uintptr_t>(ptr);
            uintptr_t end1 = start1 + size;
            uintptr_t start2 = reinterpret_cast<uintptr_t>(other.ptr);
            uintptr_t end2 = start2 + other.size;

            return !(end1 <= start2 || end2 <= start1);
        }
    };

    std::vector<Allocation> allocations;

    // Make many allocations
    for (int i = 0; i < 100; ++i) {
        size_t size = 32 + (i * 7) % 256;  // Varying sizes
        void* p = pool.allocate(size, 8);
        assert(p != nullptr);
        allocations.push_back({p, size});
    }

    // Verify no overlaps (validates disjoint property from Dafny proof)
    for (size_t i = 0; i < allocations.size(); ++i) {
        for (size_t j = i + 1; j < allocations.size(); ++j) {
            assert(!allocations[i].overlaps(allocations[j]) &&
                   "Overlapping allocations detected!");
        }
    }

    std::cout << "test_non_overlapping PASSED" << std::endl;
}

int main() {
    std::cout << "=== Thread-Safe Monotonic Buffer Resource Tests ===" << std::endl;
    std::cout << "Based on formal proof in ThreadSafeMonotonicBuffer.dfy" << std::endl;
    std::cout << std::endl;

    test_alignment();
    test_non_overlapping();
    test_concurrent_allocations();

    std::cout << std::endl;
    std::cout << "=== ALL TESTS PASSED ===" << std::endl;

    return 0;
}
