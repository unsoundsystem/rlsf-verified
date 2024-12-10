OUTDIR := build
ASCIIDOCTOR_OPS := -a linkcss -a copycss -D build
SRCS := prop2verif.adoc \
								rlsf.adoc \
								zhangetal.adoc \
								refinedrust.adoc \
								status.adoc \
								verus.adoc \
								verus-rlsf.adoc
HTMLS := $(addprefix $(OUTDIR)/, index.html $(subst .adoc,.html,$(SRCS)))

all: $(HTMLS)
	#cd verus-
	#-dune build --root=rr-ex coq/extras.html
	#cp -rf ./rr-ex/_build/default/coq/extras.html $(OUTDIR)/coqdoc

$(OUTDIR)/index.html: README.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $< -o $(@F)

$(OUTDIR)/%.html: %.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $<
