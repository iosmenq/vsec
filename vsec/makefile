# Makefile Header
# Makefile for building vsec

# Compiler
CC = clang

# SDK path
SDK = /usr/share/SDKs/iPhoneOS.sdk

# Compiler flags
CFLAGS = -O2 -Wall -Wextra -isysroot $(SDK)

# Frameworks
FRAMEWORKS = -framework Security -framework CoreFoundation

# Source and output
SRC = vsec.c
OUT = vsec

# Default target
all: $(OUT)

# Build target
$(OUT): $(SRC)
	$(CC) $(CFLAGS) -o $(OUT) $(SRC) $(FRAMEWORKS)

# Clean target
clean:
	rm -f $(OUT)

.PHONY: all clean
