(* ------------------------------------------------------------------------- *)
(* The monoids of addition and multiplication of real numbers.               *)
(* ------------------------------------------------------------------------- *)
(* The groups of addition and multiplication of real numbers.                *)
(* ------------------------------------------------------------------------- *)

open HolKernel boolLib bossLib Parse;

open pred_setTheory realTheory monoidTheory groupTheory ringTheory;

val _ = new_theory "real_algebra";

Definition real_add_monoid_def:
  real_add_monoid : real monoid =
  <| carrier := UNIV; id := 0; op := (real_add) |>
End

Theorem real_add_monoid_simps[simp]:
  real_add_monoid.carrier = UNIV /\
  real_add_monoid.op = (real_add) /\
  real_add_monoid.id = 0
Proof
  rw[real_add_monoid_def]
QED

Theorem real_add_monoid[simp]:
  AbelianMonoid real_add_monoid
Proof
  rw[AbelianMonoid_def]
  >- (
    rewrite_tac[Monoid_def]
    \\ simp[REAL_ADD_ASSOC] )
  \\ simp[REAL_ADD_COMM]
QED

Definition real_mul_monoid_def:
  real_mul_monoid : real monoid =
  <| carrier := UNIV; id := 1; op := (real_mul) |>
End

Theorem real_mul_monoid_simps[simp]:
  real_mul_monoid.carrier = UNIV /\
  real_mul_monoid.op = (real_mul) /\
  real_mul_monoid.id = 1
Proof
  rw[real_mul_monoid_def]
QED

Theorem real_mul_monoid[simp]:
  AbelianMonoid real_mul_monoid
Proof
  rw[AbelianMonoid_def]
  >- (
    rewrite_tac[Monoid_def]
    \\ simp[REAL_MUL_ASSOC] )
  \\ simp[REAL_MUL_COMM]
QED

Theorem real_add_group[simp]:
  AbelianGroup real_add_monoid
Proof
  mp_tac real_add_monoid
  \\ rewrite_tac[AbelianMonoid_def]
  \\ rw[AbelianGroup_def, Group_def]
  \\ rw[monoid_invertibles_def]
  \\ simp[Once EXTENSION]
  \\ gen_tac \\ qexists_tac`-x`
  \\ simp[]
QED

Theorem real_mul_group:
  AbelianGroup (real_mul_monoid excluding 0)
Proof
  mp_tac real_mul_monoid
  \\ rewrite_tac[AbelianMonoid_def]
  \\ rw[AbelianGroup_def, Group_def]
  >- (
    full_simp_tac std_ss [Monoid_def]
    \\ fs[excluding_def] )
  \\ rw[monoid_invertibles_def]
  \\ simp[excluding_def, Once EXTENSION]
  \\ gen_tac \\ Cases_on`x = 0` \\ rw[]
  \\ qexists_tac`realinv x`
  \\ simp[realTheory.REAL_MUL_RINV]
QED

val _ = export_theory();
