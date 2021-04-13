TARGETS=array-cav19 array-crafted

.PHONY: clean

default: all

all: $(TARGETS)

$(TARGETS):
	mkdir -p _build/
	$(MAKE) -C for-wasp/$@
	mv -v for-wasp/$@/_build _build/$@

clean:
	$(RM) -rf _build
