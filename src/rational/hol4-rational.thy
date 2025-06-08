name: hol-rational
version: 1.0
description: HOL integer theories
author: HOL OpenTheory Packager <opentheory-packager@hol-theorem-prover.org>
license: MIT
requires: base
requires: hol-base
requires: hol-words
requires: hol-string
requires: hol-quotient
requires: hol-integer
show: "HOL4"
show: "Data.Bool"
show: "Data.Pair"
show: "Data.List"
show: "Function"
show: "Relation"
show: "Number.Natural"
main {
  article: "hol4-rational-unint.art"
  interpretation: "../opentheory/hol4.int"
}
