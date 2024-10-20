This directory contains a modernised version of `src/float`. The data
representation has been updated to make use of HOL4 bit-vectors. There is also
additional tool support, e.g. for relatively efficient evaluation of basic
floating-point arithmetic operations.

 * binary_ieeeTheory

   Generic IEEE-754 floating-point theory. Introduces the type
   ``:('t, 'w) float``, where ``:'t`` and ``:'w`` represent the sizes of the
   significand and exponent respectively.

 * lift_ieeeTheory and lift_machine_ieeeTheory

   Error bound theorems for some roundTiesToEven floating-point operations.

 * binary_ieeeSyntax

   Syntax support for binary_ieeeTheory.

 * binary_ieeeLib

   Contains conversions for evaluating floating-point operations.

 * native/native_ieeeLib (Poly/ML only)

   Contains conversions for evaluating floating-point operations using the
   native SML type "float". These generate oracle theorems.

 * machine_ieeeLib

   Supports building floating-point theories for particular bit-vector
   encodings.

 * machine_ieeeTheory

   Uses machine_ieeeLib to build a theory covering 16-bit, 32-bit and 64-bit
   floating-point encodings. For example, floating-point operations are defined
   over the type ``:word16`` by using maps to and from the type
   ``:(10, 5) float``, which is abbreviated to ``:half``. We also have
   ``:single`` for ``:(23, 8) float`` and ``:double`` for ``:(52, 11) float``.

 * fp16Syntax, fp32Syntax, fp64Syntax

   These provide syntax support for the theory machine_ieeeTheory. They are
   built using the functor in fp-functor.sml and signature in fp-sig.sml.

 * machine_ieeeSyntax

   Syntax support for floating-point operations that convert between single and
   double precision values.
