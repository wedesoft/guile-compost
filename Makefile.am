include guile.am

moddir=$(prefix)/share/guile/site/$(GUILE_EFFECTIVE_VERSION)
godir=$(libdir)/guile/$(GUILE_EFFECTIVE_VERSION)/ccache

SOURCES = \
	compost.scm \
	compost/config.scm \
	compost/compiler.scm \
	compost/runtime.scm \
	compost/packed-struct.scm \
	compost/syntax.scm \
	compost/type-inference.scm

EXTRA_DIST += env.in COPYING examples

TESTS = \
	tests/basic.test
TESTS_ENVIRONMENT = $(top_builddir)/env $(GUILE) --no-auto-compile
EXTRA_DIST += $(TESTS)
