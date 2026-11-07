AC_PREREQ(2.59)
AC_INIT([Rocq-Waterproof], [2.0.0-git])

AC_DEFUN([AX_VERSION_GE], [AS_VERSION_COMPARE([$1],[$2],[$4],[$3],[$3])])

AC_CHECK_TOOL([OCAMLC], [ocamlc], [no]
)
AS_IF(
    [test "x$OCAMLC" = xno],
    [AC_MSG_ERROR([Cannot find ocamlc.])]
)

AC_CHECK_TOOL([COQC], [coqc], [no])
AS_IF(
    [test "x$COQC" = xno],
    [AC_MSG_ERROR([Cannot find coqc.])]
)

AC_MSG_CHECKING(Coq version)
coq_version=$($COQC -v | grep version | sed -e 's/^.*version \([[0-9.+a-z]]*\).*$/\1/')
AC_MSG_RESULT($coq_version)
AX_VERSION_GE(
    [$coq_version],
    8.21,
    [],
    [AC_MSG_ERROR([must be at least 8.21.])]
)
AC_CHECK_TOOL([OCAMLFIND], [ocamlfind], [no])
AS_IF(
    [test "x$OCAMLFIND" = xno],
    [AC_MSG_ERROR([Cannot find ocamlfind.])]
)

COQTOP_WHERE=$(coqtop -where)
LTAC2_DIR="${COQTOP_WHERE}-core/plugins/ltac2"
AS_IF(
    [test -d ${LTAC2_DIR}],
    [
        LTAC2_CAML_FILES="${LTAC2_CAML_FILES} ${LTAC2_DIR}"
        AC_MSG_RESULT([yes])
    ],
    [
        AC_MSG_RESULT([no])
        AC_MSG_ERROR([ *** Unable to find Ltac2 which should be installed with Coq >= 8.21])
    ]
)
AC_SUBST(LTAC2_CAML_FILES)

COQ_THEORY_FILES="$(find theories/ -type f -name "*.v" | tr '\n' ' ')"
AC_SUBST(COQ_THEORY_FILES)

AC_CONFIG_FILES([Makefile _CoqProject])
AC_OUTPUT