CC=clang
LD=wasm-ld

LIBC_DIR ?= bin/
LIBC_INC ?= lib

OPT_LVL ?= -O0
OTHER_CODE ?=

BUILD_DIR ?= _build
ENTRY_FUN ?= __original_main

# Will overwrite TODO
-include Makefile.config

WARN += -Wno-parentheses-equality
WARN += -Wno-attributes
WARN += -Wno-return-type
WARN += -Wno-int-conversion
WARN += -Wno-incompatible-pointer-types
WARN += -Wno-incompatible-function-pointer-types
WARN += -Wno-pointer-sign
WARN += -Wno-bitfield-constant-conversion
WARN += -Wno-implicit-function-declaration

INCLUDES += -I$(LIBC_INC)

CFLAGS += -g -emit-llvm --target=wasm32 -m32
CFLAGS += -ffreestanding -fbracket-depth=512 -fno-jump-tables
CFLAGS += $(INCLUDES)
CFLAGS += $(WARN) -c

LDFLAGS += -L$(LIBC_DIR)
LDFLAGS += --no-entry --export=$(ENTRY_FUN)
LDFLAGS += -lc

SOURCES := $(wildcard *.c)
OBJECTS := $(addprefix $(BUILD_DIR)/,$(SOURCES:.c=.o))

.PHONY: clean

default: all clean

all: $(OBJECTS:.o=.wat)
	@mv -v $< .

$(BUILD_DIR)/%.bc: %.c
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(OPT_LVL) $(CFLAGS) -o $@ $<

$(BUILD_DIR)/%.o: $(BUILD_DIR)/%.bc
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

$(BUILD_DIR)/%.wasm: $(BUILD_DIR)/%.o
	@echo "Building $@"
	@$(LD) $^ $(OTHER_CODE) -o $@ $(LDFLAGS)

$(BUILD_DIR)/%.wat: $(BUILD_DIR)/%.wasm
	@echo "Building $@"
	@wasm2wat $^ -o $@

clean:
	@echo "rm -rf $(BUILD_DIR)"; rm -rf $(BUILD_DIR)
