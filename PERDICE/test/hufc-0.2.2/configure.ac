#                                               -*- Autoconf -*-
# Process this file with autoconf to produce a configure script.

AC_PREREQ(2.69)
AC_INIT([hufc], [0.2.2])
AC_CONFIG_SRCDIR([src/hufc.c])
AM_INIT_AUTOMAKE
AC_CONFIG_HEADERS([config.h])

# Checks for programs.
AC_PROG_CC

# Checks for libraries.

# Checks for header files.
AC_CHECK_HEADERS([inttypes.h netinet/in.h stdlib.h string.h sys/time.h])

# Checks for typedefs, structures, and compiler characteristics.
AC_C_INLINE
AC_TYPE_MODE_T
AC_TYPE_SIZE_T
AC_TYPE_UINT16_T
AC_TYPE_UINT32_T
AC_TYPE_UINT8_T

# Checks for library functions.
AC_FUNC_MALLOC
AC_CHECK_FUNCS([gettimeofday memset strrchr strstr])

# Checks for x86 assembly code usage.
use_x86asm=""

AC_ARG_ENABLE([x86asm],
		[AS_HELP_STRING([--enable-x86asm],
				[use x86 assembly versions of CRC and checksum])],
		[AC_DEFINE([__HUFC_USE_X86_ASM__], [1],
				[Define if x86 asm code is used])
		use_x86asm=$enableval],
		[use_x86asm=no])

AC_MSG_CHECKING([whether x86 assembly code is used])
AC_MSG_RESULT([$use_x86asm])

# Checks for big endian checksum.
use_big_endian=""

AC_ARG_ENABLE([big-endian],
		[AS_HELP_STRING([--enable-big-endian],
				[use big endian checksum])],
		[AC_DEFINE([__HUFC_BIG_ENDIAN__], [1],
				[Define if big endian checksum is used])
		use_big_endian=$enableval],
		[use_big_endian=no])

AC_MSG_CHECKING([whether big endian checksum is used])
AC_MSG_RESULT([$use_big_endian])


AC_CONFIG_FILES([Makefile
                 src/Makefile])
AC_OUTPUT
