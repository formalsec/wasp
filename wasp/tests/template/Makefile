CC=clang
LIB=lib
SRC=src
BUILD=build

# Optimizations
OPT ?= -O0

# Includes
INCLUDES += -I$(LIB)/include

# Warnings
WARN += -Wno-int-conversion
WARN += -Wno-implicit-function-declaration

CFLAGS += -emit-llvm -g $(OPT)
CFLAGS += --target=wasm32 -c -m32
CFLAGS += $(INCLUDES)
CFLAGS += $(WARN)

SOURCES := $(wildcard $(SRC)/*.c)
LIB_SRC := $(wildcard $(LIB)/*.c)
OBJECTS := $(addprefix $(BUILD)/,$(notdir $(SOURCES:.c=.o)))
LIB_OBJ := $(addprefix $(BUILD)/lib/,$(notdir $(LIB_SRC:.c=.o)))

default: all

all: $(OBJECTS:.o=.wat)

$(BUILD)/%.bc: $(SRC)/%.c
	@mkdir -p $(dir $@)
	@echo "$(CC) $(CFLAGS) -o $@ $<"; $(CC) $(CFLAGS) -o $@ $<

$(BUILD)/%.o: $(BUILD)/%.bc
	@echo "opt $(OPT) $< -o $<"; opt $(OPT) $< -o $<
	@echo "llc $(OPT) -march=wasm32 -filetype=obj $< -o $@"; llc $(OPT) -march=wasm32 -filetype=obj $< -o $@

$(BUILD)/%.wasm: $(BUILD)/%.o $(LIB_OBJ)
	@echo "wasm-ld --no-entry --export-all $^ -o $@"; wasm-ld --no-entry --export-all $^ -o $@

$(BUILD)/%.wat: $(BUILD)/%.wasm
	@echo "wasm2wat $^ -o $@"; wasm2wat $^ -o $@

$(BUILD)/lib/%.bc: $(LIB)/%.c
	@mkdir -p $(dir $@)
	@echo "$(CC) $(CFLAGS) -o $@ $<"; $(CC) $(CFLAGS) -o $@ $<

$(BUILD)/lib/%.o: $(BUILD)/lib/%.bc
	@echo "opt $(OPT) $< -o $<"; opt $(OPT) $< -o $<
	@echo "llc $(OPT) -march=wasm32 -filetype=obj $< -o $@"; llc $(OPT) -march=wasm32 -filetype=obj $< -o $@

clean:
	$(RM) -rf $(BUILD)
