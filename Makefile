OUTDIR := build
ASCIIDOCTOR_OPS := -a linkcss -a copycss -D build
SRCS := prop2verif.adoc \
								rlsf.adoc \
								zhangetal.adoc \
								refinedrust.adoc
HTMLS := $(addprefix $(OUTDIR)/, index.html $(subst .adoc,.html,$(SRCS)))

all: $(HTMLS)

$(OUTDIR)/index.html: README.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $< -o $(@F)

$(OUTDIR)/%.html: %.adoc
	asciidoctor $(ASCIIDOCTOR_OPS) $<
