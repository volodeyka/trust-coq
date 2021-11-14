COQMODULE    := relive
COQTHEORIES  := src/trust/*.v src/lib/*.v src/basic/*.v src/models/*.v

.PHONY: all theories clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq quick

quick-check: Makefile.coq
	$(MAKE) -f Makefile.coq vio2vo J=6

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq

tounicode:
	sed -i .bak 's/<</⟪/g' $(COQTHEORIES) 
	sed -i .bak 's/>>/⟫/g' $(COQTHEORIES)
	sed -i .bak 's/;;/⨾/g' $(COQTHEORIES)
	sed -i .bak 's/<|/⦗/g' $(COQTHEORIES)
	sed -i .bak 's/|>/⦘/g' $(COQTHEORIES)
	sed -i .bak 's/\^+/⁺/g' $(COQTHEORIES)
	sed -i .bak 's/\^\*/＊/g' $(COQTHEORIES)

# Install build-dependencies
build-dep/opam: opam Makefile
	@echo "# Creating build-dep package."
	@mkdir -p build-dep
	@sed <opam -E 's/^(build|install|remove):.*/\1: []/; s/^name: *"(.*)" */name: "\1-builddep"/' >build-dep/opam
	@fgrep builddep build-dep/opam >/dev/null || (echo "sed failed to fix the package name" && exit 1) # sanity check

build-dep: build-dep/opam phony
	@# We want opam to not just instal the build-deps now, but to also keep satisfying these
	@# constraints.  Otherwise, `opam upgrade` may well update some packages to versions
	@# that are incompatible with our build requirements.
	@# To achieve this, we create a fake opam package that has our build-dependencies as
	@# dependencies, but does not actually install anything itself.
	@echo "# Installing build-dep package."
	@opam install $(OPAMFLAGS) build-dep/
