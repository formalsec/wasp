CC=clang
CC_OPT=-emit-llvm -g -O0 -ffreestanding --target=wasm32 -c -m32 -I$(LIB) -fbracket-depth=512 
LINKER=wasm-ld
LIB=../../lib
BUILD_DIR=_build

lib=$(wildcard $(LIB)/*.c)
libo=$(addprefix $(BUILD_DIR)/lib/,$(notdir $(lib:.c=.o)))
libbc=$(addprefix $(BUILD_DIR)/lib/,$(notdir $(lib:.c=.bc)))

tests=$(wildcard *.c)
testso=$(addprefix $(BUILD_DIR)/,$(tests:.c=.o))
testsbc=$(addprefix $(BUILD_DIR)/,$(tests:.c=.bc))
testswasm=$(addprefix $(BUILD_DIR)/,$(tests:.c=.wasm))

default: all

all: normal wat yml clean_up patch

normal: $(testswasm)

wat: $(addprefix $(BUILD_DIR)/,$(tests:.c=.wat))

yml: 
	cp -v $(tests:.c=.yml) $(BUILD_DIR)

patch:
	@./patch.sh

$(BUILD_DIR)/%.bc: %.c $(libbc)
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -o $@ $< 

$(BUILD_DIR)/%.o: $(BUILD_DIR)/%.bc $(libo)
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

$(BUILD_DIR)/%.wasm: $(BUILD_DIR)/%.o $(libo)
	@echo "Building $@"
	@$(LINKER) --no-entry --export-all $^ -o $@

$(BUILD_DIR)/%.wat: $(BUILD_DIR)/%.wasm
	@echo "Building $@"
	@wasm2wat $^ -o $@

$(BUILD_DIR)/lib/%.bc: $(LIB)/%.c
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -o $@ $^

$(BUILD_DIR)/lib/%.o: $(BUILD_DIR)/lib/%.bc
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

clean_up:
	@rm -rf $(testswasm) $(BUILD_DIR)/*.bc $(BUILD_DIR)/*.o

clean:
	@echo "rm -rf $(BUILD_DIR)"; rm -rf $(BUILD_DIR)
