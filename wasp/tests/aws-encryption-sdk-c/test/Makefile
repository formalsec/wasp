TARGET=aws_cryptosdk_cmm_base_init_harness.wasm

$(TARGET): $(TARGET:.wasm=.o) mockups.o assert.o stdlib.o
	wasm-ld --no-entry --export-all $^ -o $@

%.o: %.bc
	opt -O1 $< -o $<
	llc -O1 -march=wasm32 -filetype=obj $< -o $@

%.bc: %.c
	clang --target=wasm32 -O1 -emit-llvm -c $<

clean:
	rm -rf *.o *.bc *.wasm

wat:
	wasm2wat $(TARGET) -o $(TARGET:.wasm=.wat)
