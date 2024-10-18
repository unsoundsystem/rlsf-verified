STDLIB = ptr mem

RUST_TARGET ?= $(shell rustc -vV | sed -n 's|host: ||p')
RUST_PATH ?=	target/$(RUST_TARGET)/release




generate_stdlib: $(STDLIB:=.crate)

clean_stdlib: $(STDLIB:=.clean)

stdlib.proof: generate_stdlib
	dune build --display short

%.proof:	%.crate
	cd $* && dune build --display short

#%.crate:	export PATH := $(CURDIR)/../rr_frontend/$(RUST_PATH):$(PATH)
%.crate: %
	cd $* && /home/shinaikakishita/projects/tlsf-verif/refinedrust-dev/result/bin/cargo-refinedrust

%.clean: phony
	cd $* && cargo clean
.PHONY: phony
