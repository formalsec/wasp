ARRAY=array-cav19 array-crafted array-examples array-fpi array-industry-pattern array-lopstr16 array-multidimensional array-patterns array-programs array-tiling
BITVECTOR=bitvector bitvector-loops bitvector-regression
MISC=reducercommutativity locks combinations verifythis xcsp psyco systemc
FLOAT=float-benchs float-newlib floats-cdfpl floats-cbmc-regression floats-esbmc-regression
LOOPS=loop-crafted loop-industry-pattern loop-floats-scientific-comp loop-invariants loop-invgen loop-lit loop-new loop-simple loop-zilu
LIST=list-simple list-properties list-ext-properties list-ext2-properties list-ext3-properties
HEAP=forester-heap heap-data
NTDRIVERS=ntdrivers-simplified
OPENSSL=openssl openssl-simplified
RECURSIVE=recursive recursive-simple recursive-with-pointer
DIGBENCH=nla-digbench nla-digbench-scaling
TERMINATION=termination-crafted termination-crafted-lit termination-numeric

TARGET=$(ARRAY) $(BITVECTOR) $(MISC) $(FLOAT) $(LOOPS) $(LIST) $(HEAP) $(NTDRIVERS) $(OPENSSL) $(RECURSIVE) $(DIGBENCH) $(TERMINATION)

.PHONY: clean

default: all

all: $(TARGET)

$(TARGET):
	mkdir -p _build/
	$(MAKE) -C for-wasp/$@
	#mv -vf for-wasp/$@/_build _build/$@

clean:
	$(RM) -rf _build
