OUTDIR := build
DOCS_DIR := docs
ASCIIDOCTOR_OPS := -a linkcss -a copycss -D build -r asciidoctor-diagram 
SRCS := $(DOCS_DIR)/prop2verif.adoc \
								$(DOCS_DIR)/rlsf.adoc \
								$(DOCS_DIR)/zhangetal.adoc \
								$(DOCS_DIR)/refinedrust.adoc \
								$(DOCS_DIR)/verus.adoc \
								$(DOCS_DIR)/verus-rlsf.adoc \
								$(DOCS_DIR)/rlsf-index-calc.adoc \
								$(DOCS_DIR)/literature.adoc \
								status.adoc
HTMLS := $(addprefix $(OUTDIR)/, index.html $(subst .adoc,.html,$(SRCS)))

all: $(HTMLS)
	#cd verus-
	#-dune build --root=rr-ex coq/extras.html
	#cp -rf ./rr-ex/_build/default/coq/extras.html $(OUTDIR)/coqdoc

$(OUTDIR)/index.html: README.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $< -o $(@F)

$(OUTDIR)/%.html: %.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $<
