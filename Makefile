CXXFLAGS = -std=c++20 -pthread -Wall -Wextra -O2 -g
PREFIX ?= /usr/local
INCLUDEDIR = $(PREFIX)/include

TARGET = bench
TEST = test
SRC = bench_thread_safe_monotonic_buffer.cpp
TEST_SRC = test_thread_safe_monotonic_buffer.cpp
HEADER = thread_safe_monotonic_buffer.hpp

.PHONY: all bench check install clean

all:
	@echo "Use 'make bench' to build and run"

$(TARGET): $(SRC) $(HEADER)
	$(CXX) $(CXXFLAGS) $(SRC) -o $(TARGET)

$(TEST): $(TEST_SRC) $(HEADER)
	$(CXX) $(CXXFLAGS) $(TEST_SRC) -o $(TEST)

bench: $(TARGET)
	./$(TARGET)

check: $(TEST)
	./$(TEST)

install: $(HEADER)
	install -d $(INCLUDEDIR)
	install -m 644 $(HEADER) $(INCLUDEDIR)/

clean:
	rm -f $(TARGET) $(TEST)
