# Helpers
rwildcard=$(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d))

BUILD=_build
PROOFS := $(call rwildcard,proofs,*.c)

TESTS := $(patsubst proofs/%.c,$(BUILD)/tests/%.wat,$(PROOFS))

.PHONY: clean

default: all

all: $(TESTS) post

post:
	@./patch.sh .

$(BUILD)/tests/%.wat: proofs/%.c
	@echo "Building $@..."
	@$(MAKE) -C $(dir $<)

clean:
	$(RM) -rf $(BUILD)
