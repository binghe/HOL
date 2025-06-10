name: hol-set-unint
version: 1.0
description: HOL set theories (before re-interpretation)
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
main {
  import: wellorder
  import: cardinal
  import: topology
  import: ordinal
}
wellorder {
  article: "wellorder.ot.art"
}
cardinal {
  import: wellorder
  article: "cardinal.ot.art"
}
topology {
  import: cardinal
  article: "topology.ot.art"
}
ordinal {
  import: wellorder
  import: cardinal
  import: topology
  article: "ordinal.ot.art"
}
