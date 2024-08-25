# Settings
CC=clang
LD=wasm-ld
LIB=.
SRC=.
BIN=../../bin
BUILD=../../_build

# Optimizations
OPT ?= -O0

# Incldues
INCLUDES += -I$(LIB)

# Warnings
WARN += -Wno-parentheses-equality
WARN += -Wno-attributes
WARN += -Wno-return-type
WARN += -Wno-int-conversion
WARN += -Wno-incompatible-pointer-types
WARN += -Wno-incompatible-function-pointer-types
WARN += -Wno-pointer-sign
WARN += -Wno-bitfield-constant-conversion
WARN += -Wno-implicit-function-declaration

# Compilation flags
CFLAGS += -emit-llvm -g $(OPT)
CFLAGS += -ffreestanding --target=wasm32 -c -m32
CFLAGS += $(INCLUDES)
CFLAGS += $(WARN)
CFLAGS += -fbracket-depth=512

# Files
SOURCES := $(wildcard $(SRC)/*.c)
OBJECTS := $(addprefix $(BUILD)/,$(notdir $(SOURCES:.c=.o)))

.PHONY: clean

.SECONDARY: $(OBJECTS)

default: all

all: $(BIN)/libc.wasm

$(BUILD)/%.bc: %.c
	@mkdir -p $(dir $@)
	@echo "$(CC) $(CFLAGS) -o $@ $<"; $(CC) $(CFLAGS) -o $@ $<

$(BUILD)/%.o: $(BUILD)/%.bc
	@echo "opt $(OPT) $< -o $<"; opt $(OPT) $< -o $<
	@echo "llc $(OPT) -march=wasm32 -filetype=obj $< -o $@"; llc $(OPT) -march=wasm32 -filetype=obj $< -o $@

$(BIN)/libc.wasm: $(OBJECTS)
	@mkdir -p $(dir $@)
	@$(LD) $^ -o $@ --no-entry --export-all --relocatable

clean:
	@echo "rm -rf $(BUILD) $(BIN)/libc.wasm"; rm -rf $(BUILD) $(BIN)/libc.wasm
