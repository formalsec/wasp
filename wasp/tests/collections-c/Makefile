CC=clang
CC_OPT=-emit-llvm -g -O1 --target=wasm32 -c -m32
LINKER=wasm-ld
LIB_DIR=lib
BUG_LIB_DIR=lib-with-bugs
UTILS_DIR=for-wasp/utils
MOCKS_DIR=for-wasp/mockups
NORMAL_TESTS=for-wasp/normal
BUG_TESTS=for-wasp/bugs
BUILD_DIR=_build

lib=$(wildcard $(LIB_DIR)/*.c)
libo=$(addprefix $(BUILD_DIR)/,$(lib:.c=.o))
libbc=$(addprefix $(BUILD_DIR)/,$(lib:.c=.bc))

libbug=$(wildcard $(BUG_LIB_DIR)/*.c)
libbugo=$(addprefix $(BUILD_DIR)/,$(libbug:.c=.o))
libbugbc=$(addprefix $(BUILD_DIR)/,$(libbug:.c=.bc))

tests=$(wildcard $(NORMAL_TESTS)/**/*.c)
testso=$(addprefix $(BUILD_DIR)/,$(tests:.c=.o))
testsbc=$(addprefix $(BUILD_DIR)/,$(tests:.c=.bc))
testswasm=$(addprefix $(BUILD_DIR)/,$(tests:.c=.wasm))

testbugs=$(wildcard $(BUG_TESTS)/*.c)
testbugso=$(addprefix $(BUILD_DIR)/,$(testbugs:.c=.o))
testbugsbc=$(addprefix $(BUILD_DIR)/,$(testbugs:.c=.bc))
testbugswasm=$(addprefix $(BUILD_DIR)/,$(testbugs:.c=.wasm))

.PHONY: clean

.SECONDARY: $(libo) $(libbugo)

default: all

all: pre normal bug wat post clean-up

pre:
	@python for_wasp.py

bug: $(testbugswasm)

normal: $(testswasm)

wat: $(addprefix $(BUILD_DIR)/,$(tests:.c=.wat)) $(addprefix $(BUILD_DIR)/,$(testbugs:.c=.wat))

post:
	@./add_mocks.sh

# TESTS WITH BUGS

$(BUILD_DIR)/for-wasp/bugs/%.bc: for-wasp/bugs/%.c $(libbugbc) $(BUILD_DIR)/for-wasp/utils/utils.bc $(BUILD_DIR)/for-wasp/mockups/mockups.bc
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -I $(MOCKS_DIR) -I $(UTILS_DIR) -I $(BUG_LIB_DIR)/include -o $@ $< > /dev/null 2>&1

$(BUILD_DIR)/for-wasp/bugs/%.o: $(BUILD_DIR)/for-wasp/bugs/%.bc $(libbugo) $(BUILD_DIR)/for-wasp/utils/utils.o $(BUILD_DIR)/for-wasp/mockups/mockups.o
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

$(BUILD_DIR)/for-wasp/bugs/%.wasm: $(BUILD_DIR)/for-wasp/bugs/%.o $(libbugo) $(BUILD_DIR)/for-wasp/utils/utils.o $(BUILD_DIR)/for-wasp/mockups/mockups.o
	@echo "Building $@"
	@$(LINKER) --no-entry --export-all $^ -o $@

$(BUILD_DIR)/for-wasp/bugs/%.wat: $(BUILD_DIR)/for-wasp/bugs/%.wasm
	@echo "Building $@"
	@wasm2wat $^ -o $@

# NORMAL TESTS

$(BUILD_DIR)/for-wasp/normal/%.bc: for-wasp/normal/%.c $(libbc) $(BUILD_DIR)/for-wasp/utils/utils.bc $(BUILD_DIR)/for-wasp/mockups/mockups.bc
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -I $(MOCKS_DIR) -I $(UTILS_DIR) -I $(LIB_DIR)/include -o $@ $< > /dev/null 2>&1

$(BUILD_DIR)/for-wasp/normal/%.o: $(BUILD_DIR)/for-wasp/normal/%.bc $(libo) $(BUILD_DIR)/for-wasp/utils/utils.o $(BUILD_DIR)/for-wasp/mockups/mockups.o
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

$(BUILD_DIR)/for-wasp/normal/%.wasm: $(BUILD_DIR)/for-wasp/normal/%.o $(libo) $(BUILD_DIR)/for-wasp/utils/utils.o $(BUILD_DIR)/for-wasp/mockups/mockups.o
	@echo "Building $@"
	@$(LINKER) --no-entry --export-all $^ -o $@

$(BUILD_DIR)/for-wasp/normal/%.wat: $(BUILD_DIR)/for-wasp/normal/%.wasm
	@echo "Building $@"
	@wasm2wat $^ -o $@

# OTHER

$(BUILD_DIR)/for-wasp/utils/utils.bc: $(UTILS_DIR)/utils.c
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -I $(MOCKS_DIR) -o $@ $^ > /dev/null 2>&1

$(BUILD_DIR)/for-wasp/utils/utils.o: $(BUILD_DIR)/for-wasp/utils/utils.bc
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

$(BUILD_DIR)/for-wasp/mockups/mockups.bc: $(MOCKS_DIR)/mockups.c
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -o $@ $^ > /dev/null 2>&1

$(BUILD_DIR)/for-wasp/mockups/mockups.o: $(BUILD_DIR)/for-wasp/mockups/mockups.bc
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

# LIBS

$(BUILD_DIR)/lib/%.bc: lib/%.c $(BUILD_DIR)/for-wasp/mockups/mockups.bc
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -I $(MOCKS_DIR) -I $(LIB_DIR)/include $< -o $@ > /dev/null 2>&1

$(BUILD_DIR)/lib/%.o: $(BUILD_DIR)/lib/%.bc
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

$(BUILD_DIR)/lib-with-bugs/%.bc: lib-with-bugs/%.c $(BUILD_DIR)/for-wasp/mockups/mockups.bc
	@mkdir -p $(dir $@)
	@echo "Building $@"
	@$(CC) $(CC_OPT) -I $(MOCKS_DIR) -I $(BUG_LIB_DIR)/include $< -o $@ 

$(BUILD_DIR)/lib-with-bugs/%.o: $(BUILD_DIR)/lib-with-bugs/%.bc
	@echo "Building $@"
	@opt -O1 $< -o $<
	@llc -O1 -march=wasm32 -filetype=obj $< -o $@

clean-up:
	@rm -rf $(wildcard $(BUILD_DIR)/*.o) $(wildcard $(BUILD_DIR)/*.bc) $(wildcard $(BUILD_DIR)/*.wasm)

clean:
	@echo "rm -rf $(BUILD_DIR)"; rm -rf $(BUILD_DIR)
