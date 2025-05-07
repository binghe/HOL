name: hol-rational-unint
version: 1.0
description: HOL rational theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: int-extension
  import: frac
  import: rat
}
int-extension {
  article: "intExtension.ot.art"
}
frac {
  import: int-extension
  article: "frac.ot.art"
}
rat {
  import: int-extension
  import: frac
  article: "rat.ot.art"
}
