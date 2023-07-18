name: hol-extreal-unint
version: 1.0
description: HOL4 extended reals (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: extreal-arith
  import: extreal
}
extreal-arith {
  article: "../real/extreal_arith.ot.art"
}
extreal {
  import: extreal-arith
  article: "extreal.ot.art"
}
