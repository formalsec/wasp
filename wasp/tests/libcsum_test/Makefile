tgt=./strlen_test1.wasm

default: all

all: $(tgt) wat clean patch

$(tgt): $(tgt:.wasm=.o) ./api.o ./libc_summaries.o ./utils.o ./mockups.o
	wasm-ld --no-entry --export-all $^ -o $@

./%.bc: ./%.c
	clang --target=wasm32 -O0 -emit-llvm -c $<

./%.o: ./%.bc
	opt -O0 $< -o $<
	llc -O0 -march=wasm32 -filetype=obj $< -o $@

clean:
	rm -rf *.o *.bc *.wasm

wat:
	wasm2wat $(tgt) -o $(tgt:.wasm=.wat)

patch:
	@echo "patching mocks..."
	@./patch_mocks.sh
