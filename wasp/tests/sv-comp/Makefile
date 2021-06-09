ARRAY=array-cav19 array-crafted array-examples array-fpi array-industry-pattern array-lopstr16 array-multidimensional array-patterns array-programs array-tiling
BITVECTOR=bitvector bitvector-loops bitvector-regression
CONTROL_FLOW=ntdrivers-simplified openssl openssl-simplified locks
ECA=psyco
FLOATS=float-benchs float-newlib floats-cdfpl floats-cbmc-regression floats-esbmc-regression loop-floats-scientific-comp
HEAP=forester-heap heap-data list-simple list-properties list-ext-properties list-ext2-properties list-ext3-properties
LOOPS=loop-crafted loop-industry-pattern loop-invariants loop-invgen loop-lit loop-new loop-simple loop-zilu verifythis nla-digbench nla-digbench-scaling
RECURSIVE=recursive recursive-simple recursive-with-pointer
SEQUENTIALIZED=systemc
XCSP=xcsp
COMBINATIONS=combinations
ARRAY_MEMSAFETY=array-memsafety array-memsafety-realloc
HEAP_MEMSAFETY=memsafety memsafety-bftpd memsafety-ext memsafety-ext2
TERMINATION_CONTROLFLOW=termination-crafted termination-crafted-lit termination-numeric reducercommutativity

TARGET=$(ARRAY) $(BITVECTOR) $(CONTROL_FLOW) $(ECA) $(FLOATS) $(HEAP) $(LOOPS) $(RECURSIVE) $(SEQUENTIALIZED) $(XCSP) $(COMBINATIONS) $(ARRAY_MEMSAFETY) $(HEAP_MEMSAFETY) $(TERMINATION_CONTROLFLOW)

.PHONY: clean

default: all

all: $(TARGET)

$(TARGET):
	mkdir -p _build/
	$(MAKE) -C for-wasp/$@
	mv -vf for-wasp/$@/_build _build/$@

clean:
	$(RM) -rf _build
