#include <atomic>
#include <barrier>
#include <chrono>
#include <cstddef>
#include <cstdio>
#include <memory_resource>
#include <thread>
#include <vector>

#include "thread_safe_monotonic_buffer.hpp"

using namespace std::chrono;

namespace {

struct benchmark_case {
    std::size_t threads;
    std::size_t iterations;
    std::size_t alloc_size;
    const char* label;
};

template <typename Fn>
void run_case(const char* name, const benchmark_case& c, Fn&& body) {
    using tsmbr::thread_safe_monotonic_buffer_resource;

    std::barrier sync_point(static_cast<std::ptrdiff_t>(c.threads));
    std::vector<std::thread> workers;
    workers.reserve(c.threads);

    auto start = steady_clock::now();

    for (std::size_t t = 0; t < c.threads; ++t) {
        workers.emplace_back([&, t] {
            sync_point.arrive_and_wait();
            for (std::size_t i = 0; i < c.iterations; ++i) {
                body(c.alloc_size);
            }
        });
    }

    for (auto& th : workers) {
        th.join();
    }

    auto stop = steady_clock::now();
    double elapsed_ms = duration<double, std::milli>(stop - start).count();

    double total_allocs = static_cast<double>(c.threads) * static_cast<double>(c.iterations);
    double allocs_per_sec = total_allocs / duration<double>(stop - start).count();

    std::printf(
        "%s: threads=%zu, iterations=%zu, size=%zu -> %.2f ms (%.2f Mallocs/s)\n",
        name,
        c.threads,
        c.iterations,
        c.alloc_size,
        elapsed_ms,
        allocs_per_sec / 1'000'000.0
    );
}

} // namespace

int main() {
    std::puts("=== Monotonic Buffer Microbenchmark ===");

    const benchmark_case cases[] = {
        {1, 1'000'000, 32, "tiny"},
        {1, 1'000'000, 256, "small"},
        {2, 500'000, 64, "2 threads"},
        {4, 500'000, 64, "4 threads"},
        {8, 250'000, 64, "8 threads"},
    };

    for (const auto& c : cases) {
        tsmbr::thread_safe_monotonic_buffer_resource resource(1 << 20, std::pmr::get_default_resource());
        run_case("tsmbr", c, [&](std::size_t sz) {
            return resource.allocate(sz, alignof(std::max_align_t));
        });
        resource.release();
    }

    for (const auto& c : cases) {
        run_case("pmr", c, [&](std::size_t sz) {
            thread_local std::pmr::monotonic_buffer_resource resource(1 << 20, std::pmr::get_default_resource());
            return resource.allocate(sz, alignof(std::max_align_t));
        });
    }

    for (const auto& c : cases) {
        run_case("malloc", c, [&](std::size_t sz) {
            void* block = std::malloc(sz);
            // Write to memory to prevent optimization
            *static_cast<volatile char*>(block) = 0;
            std::free(block);
        });
    }

    return 0;
}
