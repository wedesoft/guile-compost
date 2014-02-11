dnl -*- Autoconf -*-

AC_INIT(guile-nagle, 0.1.0)
AC_CONFIG_SRCDIR(nagle.scm)
AC_CONFIG_AUX_DIR([build-aux])
AM_INIT_AUTOMAKE([color-tests -Wall -Wno-portability foreign serial-tests])
AM_SILENT_RULES([yes])

GUILE_PROGS([2.2])

AC_CONFIG_FILES([Makefile nagle/config.scm])
AC_CONFIG_FILES([env], [chmod +x env])

AC_OUTPUT
