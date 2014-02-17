include guile.am

moddir=$(prefix)/share/guile/site/$(GUILE_EFFECTIVE_VERSION)
godir=$(libdir)/guile/$(GUILE_EFFECTIVE_VERSION)/ccache

SOURCES = \
	compost.scm \
	compost/arities.scm \
	compost/assembler.scm \
	compost/backend.scm \
	compost/bitfield.scm \
	compost/config.scm \
	compost/compiler.scm \
	compost/error.scm \
	compost/register-allocation.scm \
	compost/representations.scm \
	compost/packed-struct.scm \
	compost/signs.scm \
	compost/syntax.scm \
	compost/type-check.scm \
	compost/type-inference.scm \
	compost/types.scm

EXTRA_DIST += env.in COPYING examples

TESTS = \
	tests/basic.test
TESTS_ENVIRONMENT = $(top_builddir)/env $(GUILE) --no-auto-compile
EXTRA_DIST += $(TESTS)
