name: hol-large-numbers-unint
version: 1.0
description: HOL theories up to the Law of Large Numbers (before re-interpretation)
author: Chun Tian <binghe.lisp@gmail.com>
license: MIT
main {
  import: stochastic-process
  import: large-number
}
stochastoc-process {
  article: "stochastic_process.ot.art"
}
large-number {
  import: convergence
  article: "large_number.ot.art"
}
