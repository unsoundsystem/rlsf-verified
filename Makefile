OUTDIR := build_docs
DOCS_DIR := docs
ASCIIDOCTOR_OPS := -a linkcss -a copycss -D build -r asciidoctor-diagram 
								$(DOCS_DIR)/verus.adoc \
								$(DOCS_DIR)/rlsf-index-calc.adoc
HTMLS := $(addprefix $(OUTDIR)/, index.html $(subst .adoc,.html,$(SRCS)))

all: $(HTMLS)
	#cd verus-
	#-dune build --root=rr-ex coq/extras.html
	#cp -rf ./rr-ex/_build/default/coq/extras.html $(OUTDIR)/coqdoc

$(OUTDIR)/index.html: README.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $< -o $(@F)

$(OUTDIR)/%.html: %.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $<
