# Settings
CC=@clang
LIB=./include
SRC=.

# Optimizations
OPT?=-O1

# Incldues
INCLUDES+=-I$(LIB)

# Warnings
WARN+=-Wno-parentheses-equality
WARN+=-Wno-attributes
WARN+=-Wno-return-type
WARN+=-Wno-int-conversion
WARN+=-Wno-incompatible-pointer-types
WARN+=-Wno-incompatible-function-pointer-types
WARN+=-Wno-pointer-sign
WARN+=-Wno-bitfield-constant-conversion
WARN+=-Wno-implicit-function-declaration

# Compilation flags
CFLAGS+=-emit-llvm -g $(OPT)
CFLAGS+=-ffreestanding --target=wasm32 -c -m32
CFLAGS+=$(INCLUDES)
CFLAGS+=$(WARN)
CFLAGS+=-fbracket-depth=512

# Files
SOURCES:=$(wildcard $(SRC)/*.c)
OBJECTS:=$(SOURCES:.c=.o)

.SECONDARY: $(OBJECTS)

default: libc.wasm

%.bc: %.c
	$(CC) $(CFLAGS) -o $@ $<

%.o: %.bc
	@opt $(OPT) $< -o $<
	@llc $(OPT) -march=wasm32 -filetype=obj $< -o $@

libc.wasm: $(OBJECTS)
	@wasm-ld $^ -o $@ --no-entry --export-all --relocatable
