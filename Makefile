default_target: all

.PHONY: clean force all clean_all tries clean_tries coqutil clean_coqutil clone_all update_all clean_deps deps

# absolute paths so that emacs compile mode knows where to find error
# use cygpath -m because Coq on Windows cannot handle cygwin paths
ABS_ROOT_DIR := $(shell cygpath -m "$$(pwd)" 2>/dev/null || pwd)
SRC_DIR := $(ABS_ROOT_DIR)/src

COQC ?= "$(COQBIN)coqc"
COQ_VERSION:=$(shell $(COQC) --print-version | cut -d " " -f 1)

SRC_VS ?= $(shell find $(SRC_DIR) -type f -name '*.v')

define COQPROJECT
-R $(ABS_ROOT_DIR)/coqutil/src/coqutil coqutil
-R $(ABS_ROOT_DIR)/canonical-binary-tries/ Tries
-R $(SRC_DIR)/Utils Utils
-R $(SRC_DIR)/Pyrosome Pyrosome

endef
export COQPROJECT

#TODO: build this automatically
_CoqProject:
	printenv COQPROJECT > _CoqProject

#TODO: build dependencies


clone_all:
	git submodule update --init --recursive

update_all:
	git submodule update --recursive

all: Makefile.coq $(SRC_VS)
	$(MAKE) -f Makefile.coq

COQ_MAKEFILE := $(COQBIN)coq_makefile -f _CoqProject -docroot coqutil $(COQMF_ARGS)

deps: tries coqutil

Makefile.coq: deps force _CoqProject
	@echo "Generating Makefile.coq"
	@$(COQ_MAKEFILE) $(SRC_VS) -o Makefile.coq

force:


tries:
	$(MAKE) -C $(ABS_ROOT_DIR)/canonical-binary-tries

clean_tries:
	$(MAKE) -C $(ABS_ROOT_DIR)/canonical-binary-tries clean

coqutil:
	$(MAKE) -C $(ABS_ROOT_DIR)/coqutil

clean_coqutil:
	$(MAKE) -C $(ABS_ROOT_DIR)/coqutil clean

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	find . -type f \( -name '*~' -o -name '*.glob' -o -name '*.aux' -o -name '.lia.cache' -o -name '.nia.cache' \) -delete
	rm -f Makefile.coq Makefile.coq.conf _CoqProject

clean_deps: clean_coqutil clean_tries

clean_all: clean_deps clean
