open HolKernel boolLib bossLib BasicProvers;

open optionTheory pairTheory stringTheory hurdUtils;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open comparisonTheory;
open pred_setTheory;

val _ = new_theory "AVL_trees";

(* by default, literal integers are interpreted as natural numbers (:num) *)
val _ = intLib.deprecate_int ();

Datatype:
  avl_tree = Tip | Bin int num 'a avl_tree avl_tree
End

Definition height_def[simp]:
  height Tip = 0 ∧
  height (Bin h k v l r) = MAX (height l) (height r) + 1
End

Theorem height_eq_0[simp]:
  (height t = 0 ⇔ t = Tip) ∧
  (0 = height t ⇔ t = Tip)
Proof
  Cases_on ‘t’ >> simp[]
QED

Definition singleton_avl_def:
  singleton_avl k v = Bin 0 k v Tip Tip
End

Definition avl_def[simp]:
  avl Tip = T ∧
  avl (Bin bf k v l r) =
    ((height l = height r ∨ height l = height r + 1 ∨ height r = height l + 1) ∧
     bf = &height r - &height l ∧
     avl l ∧ avl r)
End

Definition node_count_def[simp] :
  node_count Tip = 0n ∧
  node_count (Bin bf k v l r) = node_count l + node_count r + 1
End

Definition N_def:
 N k = MIN_SET(IMAGE node_count {x:num avl_tree | height x = k ∧ avl x})
End

Theorem N_0:
  N 0 = 0
Proof
  csimp[N_def, MIN_SET_THM]
QED

Theorem N_1:
   N 1 = 1
Proof
     REWRITE_TAC [N_def, height_def, avl_def, node_count_def]
  >> sg ‘IMAGE node_count {x :num avl_tree| height x = 1 ∧ avl x} = {1}’
  >- (REWRITE_TAC [EXTENSION, IN_IMAGE]
      >> GEN_TAC
      >> EQ_TAC
      >> STRIP_TAC
      >> ASM_REWRITE_TAC []
      >-(Cases_on ‘x'’
         >> ASM_REWRITE_TAC [height_def,avl_def,node_count_def]
         >> fs[])
      >> fs[]
      >> Q.EXISTS_TAC ‘Bin 0 k v Tip Tip’
      >> fs[])
  >> ASM_REWRITE_TAC[MIN_SET_SING]
QED

Definition complete_avl_def[simp]:
  complete_avl 0 = Tip ∧
  complete_avl (SUC n) = Bin 0 0 ARB (complete_avl n) (complete_avl n)
End

Theorem height_complete_avl[simp]:
  height (complete_avl n) = n
Proof
  Induct_on ‘n’ >> simp[]
QED

Theorem avl_complete_avl[simp]:
  avl (complete_avl k) = T
Proof
  Induct_on ‘k’ >> simp[]
QED

Theorem trees_of_height_exist:
  ∀k. ∃t. avl t ∧ height t = k
Proof
  GEN_TAC
  >> Q.EXISTS_TAC‘complete_avl k’
  >> simp[]
QED

Definition minimal_avl_def:
  minimal_avl (t: 'a avl_tree) ⇔
    avl t ∧
    ∀t': 'a avl_tree.
      avl t' ∧ height t' = height t ⇒
      node_count t ≤ node_count t'
End

Theorem minimal_avl_exists:
  ∀k. ∃t. minimal_avl t ∧ height t = k
Proof
  GEN_TAC
  >> qabbrev_tac ‘P = λt. avl t ∧ height t = k’
  >> MP_TAC (Q.SPECL [‘P’, ‘node_count’]
              (INST_TYPE [“:'a” |-> “:'a avl_tree”] WOP_measure))
  >> impl_tac
  >- (rw [Abbr ‘P’] \\
     Q.EXISTS_TAC ‘complete_avl k’
      >> simp[])
  >> rw [Abbr ‘P’]
  >> Q.EXISTS_TAC ‘b’ >> rw[]
  >> rw[minimal_avl_def]
QED

(* NOTE: This theorem is provided by Chun TIAN *)
Theorem minimal_avl_node_count :
  ∀k (t :num avl_tree). minimal_avl t ∧ height t = k
                                    ⇒ node_count t = N k
Proof
    rw [N_def]
 >> irule MIN_SET_TEST >> rw []
 >- (fs [minimal_avl_def])
 >- (rw [Once EXTENSION] \\
     Q.EXISTS_TAC ‘complete_avl (height t)’ >> rw [])
 >> Q.EXISTS_TAC ‘t’
 >> fs [minimal_avl_def]
QED


Theorem minimal_avl_l_is_avl:
  ∀t. minimal_avl t ⇒ avl t
Proof
  GEN_TAC >>
          rw[avl_def , minimal_avl_def]
  >> fs[minimal_avl_def]
QED

Theorem height_of_minimal_avl_diff_1:
  ∀ bf k v l r. minimal_avl (Bin bf k v l r) ⇒
                (l = Tip ∧ r = Tip) ∨
                height l = height r + 1 ∨
                height r = height l + 1
Proof
  rw[minimal_avl_def,avl_def]
  >> fs[]
  >> CCONTR_TAC
  >> Cases_on ‘l’ >> gvs[] >> gvs[] >> gvs[]
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 1 k v a r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 1 k v a r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 1 k v a0 r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
QED


Theorem children_of_minimal_avl:
  ∀bf k v l r. minimal_avl (Bin bf k v l r) ⇒
                           minimal_avl l ∧ minimal_avl r
Proof
  rw[minimal_avl_def,avl_def]
     >> CCONTR_TAC
  >> gvs[NOT_LE]
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 0 k v t' r’ mp_tac)
    >> simp[]
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin 0 k v l t'’ mp_tac)
    >> simp[]
    )
  >-(first_x_assum(Q.SPEC_THEN ‘Bin (-1) k v t' r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
    >-(first_x_assum(Q.SPEC_THEN ‘Bin (-1) k v l t'’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
      )
    >-(first_x_assum(Q.SPEC_THEN ‘Bin (1) k v t' r’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
      )
    >-(first_x_assum(Q.SPEC_THEN ‘Bin (1) k v l t'’ mp_tac)
     >> simp[]
     >>intLib.ARITH_TAC
    )
QED


Theorem N_k:
  ∀k. N (k+2) = N (k+1) + N(k) + 1
Proof
  GEN_TAC
  >> Q.SPEC_THEN ‘k+2’ mp_tac
                 (INST_TYPE [“:'a” |-> “:num”]minimal_avl_exists)
  >> STRIP_TAC
  >> ‘N (k+2) = node_count t’
    by metis_tac[minimal_avl_node_count]
  >> simp[]
  >> Cases_on ‘t’
  >- gvs[]
  >> rename1 ‘minimal_avl (Bin bf s v l r)’
  >> ‘minimal_avl l ∧ minimal_avl r’
     by metis_tac[children_of_minimal_avl]
  >> gvs[]
  >> Q.PAT_X_ASSUM ‘minimal_avl (Bin bf s v l r)’
     (MP_TAC o (MATCH_MP height_of_minimal_avl_diff_1))
  >> STRIP_TAC
  >- gvs[]
  >- ( fs[MAX_DEF] >>
      Q_TAC SUFF_TAC ‘node_count r = N k ∧ node_count l = N (k+1)’
       >- rw[]
       >> STRIP_TAC
       >- metis_tac[minimal_avl_node_count]
       >> metis_tac[minimal_avl_node_count]
     )
  >> fs[MAX_DEF] >>
      Q_TAC SUFF_TAC ‘node_count r = N (k+1) ∧ node_count l = N k’
       >- rw[]
       >> STRIP_TAC
       >- metis_tac[minimal_avl_node_count]
       >> metis_tac[minimal_avl_node_count]
QED

Definition Fibonacci_def :
    Fibonacci (n :num) =
       if n = 0 then (0:num) else
         if n = 1 then (1:num) else
          Fibonacci (n - 1) + Fibonacci (n - 2)
End

Theorem Fibonacci_thm:
  ∀k. Fibonacci (k + 2) = Fibonacci (k + 1) + Fibonacci k
Proof
  rw[Once Fibonacci_def]
QED
Theorem Fibonacci_mono:
  ∀n. Fibonacci n ≤ Fibonacci (n+1)
Proof
  STRIP_TAC
  >> Cases_on ‘n’
  >- ( ONCE_REWRITE_TAC[Fibonacci_def]
  >> gvs[]
     )
  >> gvs[SUC_ONE_ADD]
  >> rw[Fibonacci_thm]
QED

Theorem Fibonacci_mono_transitive:
  ∀ m n. m≤n ⇒ Fibonacci m ≤ Fibonacci n
Proof
  rpt STRIP_TAC
  >> ‘m = n ∨ m<n’ by rw[]
  >- rw[]
  >> MP_TAC (Q.SPECL [‘$<=’,‘Fibonacci’]
             (INST_TYPE [“:α” |-> “:num”] transitive_monotone))
  >> rw[transitive_LE]
  >> POP_ASSUM irule
  >> rw[ADD1,Fibonacci_mono]
QED

Theorem N_fibonacci_relation:
  ∀k. N k = Fibonacci (k+2)-1
Proof
  completeInduct_on ‘k’
  >> Cases_on ‘k’
  >- (simp[N_0]
  >> ONCE_REWRITE_TAC[Fibonacci_def]
  >> gvs[]
  >> ONCE_REWRITE_TAC[Fibonacci_def]
  >> gvs[])
  >> gvs[SUC_ONE_ADD]
  >> ONCE_REWRITE_TAC[Fibonacci_def]
  >> gvs[]
  >> Cases_on ‘n’
  >-( simp[N_1]
      >>ONCE_REWRITE_TAC[Fibonacci_def]
      >> gvs[]
      >> ONCE_REWRITE_TAC[Fibonacci_def]
      >> gvs[]
    )
  >>gvs[SUC_ONE_ADD]
  >> qabbrev_tac ‘k = n'+2’
  >> sg ‘N k = N(k-1) + N(k-2)+1’
  >- gvs[N_k,Abbr‘k’]
  >> rw[]
  >> ‘k-1<k ∧ k-2<k’ by rw[Abbr‘k’]
  >> rw[Abbr‘k’]
  >> gvs[]
  >> sg ‘Fibonacci 1 ≤ Fibonacci (n'+2) ’
  >- rw[Fibonacci_mono_transitive]
  >> sg ‘Fibonacci 1 ≤ Fibonacci (n'+3)’
  >- rw[Fibonacci_mono_transitive]
  >> sg ‘Fibonacci 1 = 1’
  >-(ONCE_REWRITE_TAC[Fibonacci_def]
      >> gvs[]
    )
  >> rw[]
QED

Definition tree_def:
  tree k v l r =
    Bin (&height r - &height l) k v l r
End

Definition balanceL_def:
  balanceL k v l r =
    if height l = height r + 2 then
      (case l of
         Bin _ lk lv ll lr =>
           if height ll < height lr then
             (case lr of
                Bin _ lrn lrv lrl lrr => tree lrn lrv (tree lk lv ll lrl) (tree k v lrr r)
              | _ => tree lk lv ll (tree k v lr r))
           else
             tree lk lv ll (tree k v lr r)
       | Tip => tree k v l r)
    else
      tree k v l r
End

Definition balanceR_def:
  balanceR k v l r =
    if height r = height l + 2 then
      (case r of
        Bin _ rk rv rl rr =>
          if height rl > height rr then
            (case rl of
               Bin _ rln rlv rll rlr => tree rln rlv (tree k v l rll) (tree rk rv rlr rr)
             | _ => tree rk rv (tree k v l rl) rr)
          else
            tree rk rv (tree k v l rl) rr
       | Tip => tree k v l r)
    else
      tree k v l r
End

Definition insert_avl_def:
  insert_avl x v Tip = singleton_avl x v ∧
  insert_avl x v (Bin bf k kv l r) =
    if x = k then
      Bin bf k kv l r
    else if x < k then
      balanceL k kv (insert_avl x v l) r
    else
      balanceR k kv l (insert_avl x v r)
End

val t1_t = ``insert_avl 3 3 Tip``
Theorem t1 = EVAL ``^t1_t``

val t2_t = ``insert_avl 5 5 ^t1_t``
Theorem t2 = EVAL ``^t2_t``

val t3_t = ``insert_avl 2 2 ^t2_t``
Theorem t3 = EVAL ``^t3_t``

val t4_t = ``insert_avl 4 4 ^t3_t``
Theorem t4 = EVAL ``^t4_t``

val t5_t = ``insert_avl 13 13 ^t4_t``
Theorem t5 = EVAL ``^t5_t``

val t6_t = ``insert_avl 14 14 ^t5_t``
Theorem t6 = EVAL ``^t6_t``

val t7_t = ``insert_avl 1 1 ^t6_t``
Theorem t7 = EVAL ``^t7_t``

val t8_t = ``insert_avl 6 6 ^t7_t``
Theorem t8 = EVAL ``^t8_t``

val t9_t = ``insert_avl 7 7 ^t8_t``
Theorem t9 = EVAL ``^t9_t``

(* This function takes one of the above t* theorems and return another one
   saying the corresponding tree is indeed an AVL tree. -- Chun TIAN
 *)
fun is_avl (th) =
    EVAL (mk_comb (“avl :num avl_tree -> bool”, rhs (concl th)));

(* |- avl (Bin 0 3 3 Tip Tip) *)
Theorem avl_t1 = is_avl t1 |> EQT_ELIM

Theorem avl_t2 = is_avl t2 |> EQT_ELIM
Theorem avl_t3 = is_avl t3 |> EQT_ELIM
Theorem avl_t4 = is_avl t4 |> EQT_ELIM
Theorem avl_t5 = is_avl t5 |> EQT_ELIM
Theorem avl_t6 = is_avl t6 |> EQT_ELIM
Theorem avl_t7 = is_avl t7 |> EQT_ELIM

Definition remove_max_def:
  remove_max (Bin _ k v l Tip) = (k, v, l) ∧
  remove_max (Bin _ k v l r) =
    let (max_k, max_v, r') = remove_max r in
    (max_k, max_v, balanceL k v l r')
End

Definition delete_avl_def:
  delete_avl x Tip = Tip ∧
  delete_avl x (Bin bf k kv l r) =
    if x = k then
      (case (l, r) of
         (Tip, Tip) => Tip
       | (Tip, _)   => r
       | (_, Tip)   => l
       | (_, _)     =>
           let (pred_k, pred_v, l') = remove_max l in
           balanceR pred_k pred_v l' r
      )
    else if x < k then
      balanceR k kv (delete_avl x l) r
    else
      balanceL k kv l (delete_avl x r)
End


(* (rhs o concl) (|- a = b) returns b *)
val t10_t = ``delete_avl 14 ^((rhs o concl) t9)``;
Theorem t10 = EVAL ``^t10_t``

val t11_t = ``delete_avl 5 ^((rhs o concl) t10)``;
Theorem t11 = EVAL ``^t11_t``

val t12_t = ``delete_avl 4 ^((rhs o concl) t11)``;
Theorem t12 = EVAL ``^t12_t``

Definition lookup_avl_def:
  lookup_avl x Tip = NONE ∧
  lookup_avl x (Bin _ k kv l r) =
    if x = k then
      SOME kv
    else if x < k then
      lookup_avl x l
    else
      lookup_avl x r
End

(* Test lookup on the tree after insertion *)
val lookup1_t = ``lookup_avl 3 ^((rhs o concl) t9)``  (* Should return SOME 3 *)
Theorem lookup1 = EVAL ``^lookup1_t``

val lookup2_t = ``lookup_avl 14 ^((rhs o concl) t9)``
Theorem lookup2 = EVAL ``^lookup2_t``

val lookup3_t = ``lookup_avl 4 ^((rhs o concl) t12)``  (* Should return NONE if 4 is deleted *)
Theorem lookup3 = EVAL ``^lookup3_t``

val lookup4_t = ``lookup_avl 6 ^((rhs o concl) t9)``  (* Should return SOME 6 *)
Theorem lookup4 = EVAL ``^lookup4_t``

val lookup5_t = ``lookup_avl 10 ^((rhs o concl) t9)``  (* Should return NONE if 10 is not present *)
Theorem lookup5 = EVAL ``^lookup5_t``


Definition keys_def[simp]:
  keys Tip = {} ∧
  keys (Bin _ k v l r) = {k} ∪ keys l ∪ keys r
End

Theorem keys_balanceL[simp]:
  ∀ k v t1 t2. keys(balanceL k v t1 t2) = {k} ∪ keys t1 ∪ keys t2
Proof
  rw[balanceL_def,tree_def]
  >> reverse(Cases_on ‘t1’ >> rw[])
  >-(SET_TAC[])
  >> rename [‘height t1 < height t2’]
  >> Cases_on ‘t2’ >> rw[] >> SET_TAC[]
QED

Theorem keys_balanceR[simp]:
  ∀ k v t1 t2. keys(balanceR k v t1 t2) = {k} ∪ keys t1 ∪ keys t2
Proof
  rw[balanceR_def,tree_def]
  >> reverse(Cases_on ‘t2’ >> rw[])
  >-(SET_TAC[])
  >> rename [‘height t1 > height t2’]
  >> Cases_on ‘t1’ >> rw[] >> SET_TAC[]
QED

Theorem keys_insert:
  ∀ x v t. keys(insert_avl x v t) = (keys t ∪ {x})
Proof
   Induct_on ‘t’
  >> rw[insert_avl_def,singleton_avl_def]
   >>SET_TAC[]
QED


Theorem height_balL:
  ∀ k v l r. height l = height r+2 ∧ avl l ∧ avl r ⇒
             height (balanceL k v l r) = height r+2 ∨
             height (balanceL k v l r) = height r+3
Proof
  rpt STRIP_TAC
  >> Cases_on ‘l’
  >- gvs[]
  >> gvs[tree_def]
  >> gvs[balanceL_def]
  >> gvs[MAX_DEF]
  >> gvs[balanceL_def]
  >> gvs[tree_def]
  >> gvs[MAX_DEF]
  >> gvs[height_def,MAX_DEF]
  >> Cases_on ‘a0’
  >- gvs[]
  >> gvs[height_def]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def]
QED

Theorem height_balR:
  ∀ k v l r. height r = height l+2 ∧ avl l ∧ avl r ⇒
             height (balanceR k v l r) = height l+2 ∨
             height (balanceR k v l r) = height l+3
Proof
  rpt STRIP_TAC
  >> Cases_on ‘r’
  >- gvs[]
  >> gvs[tree_def]
  >> gvs[balanceR_def]
  >> gvs[MAX_DEF]
  >> Cases_on ‘a’
  >- gvs[]
  >> gvs[height_def]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def,height_def,MAX_DEF]
  >> gvs[tree_def]
  >> gvs[balanceR_def]
  >> gvs[tree_def]
  >> gvs[MAX_DEF]
QED

Theorem height_balL2:
  ∀ k v l r. avl l ∧ avl r ∧ height l ≠ height r + 2 ⇒
  height (balanceL k v l r) = (1 + MAX (height l) (height r))
Proof
  rpt STRIP_TAC
  >> Cases_on ‘l’
  >> gvs[balanceL_def,tree_def,height_def,MAX_DEF]
  >> gvs[balanceL_def,tree_def,height_def,MAX_DEF]
QED

Theorem height_balR2:
  ∀ k v l r. avl l ∧ avl r ∧ height r ≠ height l + 2 ⇒
  height (balanceR k v l r) = (1 + MAX (height l) (height r))
Proof
  rpt STRIP_TAC
  >> Cases_on ‘r’
  >> gvs[balanceR_def,tree_def,height_def,MAX_DEF]
  >> gvs[balanceR_def,tree_def,height_def,MAX_DEF]
QED


Theorem avl_balL:
  ∀ k v l r. avl l ∧ avl r ∧ (height l = height r ∨ height l = height r+1 ∨ height r = height l+1 ∨ height l = height r+2)                     ⇒ avl(balanceL k v l r)
Proof
  rpt STRIP_TAC
  >> gvs[balanceL_def,tree_def,height_def]
  >> gvs[balanceL_def,tree_def,height_def]
  >> gvs[balanceL_def,tree_def,height_def]
  >> Cases_on ‘l’
  >- gvs[]
  >> gvs[balanceL_def,tree_def,height_def,MAX_DEF]
  >> Cases_on ‘a0’
  >- gvs[]
  >> gvs[height_def,MAX_DEF]
QED

Theorem avl_balR:
  ∀ k v l r. avl l ∧ avl r ∧ (height r = height l ∨ height r = height l+1 ∨ height l = height r+1 ∨ height r = height l+2)                     ⇒ avl(balanceR k v l r)
Proof
  rpt STRIP_TAC
  >> gvs[balanceR_def,tree_def,height_def]
  >> gvs[balanceR_def,tree_def,height_def]
  >> gvs[balanceR_def,tree_def,height_def]
  >> Cases_on ‘r’
  >- gvs[]
  >> gvs[balanceR_def,tree_def,height_def,MAX_DEF]
  >> Cases_on ‘a’
  >- gvs[]
  >> gvs[height_def,MAX_DEF]
QED


Theorem avl_tree_preserves_avl:
  ∀ l r k v. avl l ∧ avl r ∧ (height l = height r ∨ height l = height r+1 ∨ height  r = height l+1) ⇒ avl (tree k v l r)
Proof
  rpt STRIP_TAC
  >- (rw[tree_def])
  >- (rw[tree_def])
  >> rw[tree_def]
QED


Theorem avl_insert_aux:
  ∀ k v t. avl t ⇒
         avl (insert_avl k v t) ∧
         (height (insert_avl k v t) = height t ∨ height (insert_avl k v t) = height t + 1)
Proof
    rpt GEN_TAC
 >> Induct_on ‘t’
 >- rw[insert_avl_def,singleton_avl_def]
 >> rw[insert_avl_def] (* 12 subgoals *)
 (* goal 1 (of 12) *)
 >- (MATCH_MP_TAC avl_balL >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [])
 (* goal 2 (of 12) *)
 >- (simp [] (* eliminate MAX *) \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC \\
     rw [height_balL,height_balL2] >> rw [] \\
     DISJ2_TAC \\
     simp [MAX_DEF] (* eliminate MAX *))
 (* goal 3 (of 12) *)
 >- (MATCH_MP_TAC avl_balL >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [])
 (* goal 4 (of 12) *)
 >- (simp [MAX_DEF] (* eliminate MAX *) \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [] (* 2 subgoals *)
     >- (Know ‘height (balanceL n a1 (insert_avl k v t) t') =
               1 + MAX (height (insert_avl k v t)) (height t')’
         >- (MATCH_MP_TAC height_balL2 >> simp []) \\
         rw [] \\
         DISJ1_TAC >> simp [MAX_DEF]) \\
      rw [height_balL])
 (* goal 5 (of 12) *)
 >- (MATCH_MP_TAC avl_balL >> rw [] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [])
 (* goal 6 (of 12) *)
 >- (simp [MAX_DEF] \\
     Q.PAT_X_ASSUM ‘avl t ==> _’ MP_TAC >> rw [] (* 2 subgoals *)
     >- (Know ‘height (balanceL n a1 (insert_avl k v t) t') =
               1 + MAX (height (insert_avl k v t)) (height t')’
         >- (MATCH_MP_TAC height_balL2 >> simp []) \\
         rw [] \\
         DISJ1_TAC >> simp [MAX_DEF]) \\
     Know ‘height (balanceL n a1 (insert_avl k v t) t') =
           1 + MAX (height (insert_avl k v t)) (height t')’
     >- (MATCH_MP_TAC height_balL2 >> simp []) \\
     rw [])
 (* goal 7 (of 12) *)
 >- (cheat)
 (* goal 8 (of 12) *)
 >- (cheat)
 (* goal 9 (of 12) *)
 >- (cheat)
 (* goal 10 (of 12) *)
 >- (cheat)
 (* goal 11 (of 12) *)
 >- (cheat)
 (* goal 12 (of 12) *)
 >> (cheat)
QED

(*
Theorem height_insert_avl:
  ∀ k v t. height(insert_avl k v t) = height t ∨
           height (insert_avl k v t) = height t+1
Proof
  rpt GEN_TAC
  >>Induct_on ‘t’ >> rw[insert_avl_def,singleton_avl_def]


QED
Theorem avl_balanceL_0:
  ∀ k v t1 t2. height t1 = height t2 ∧ avl t1 ∧avl t2 ⇒
                      avl(balanceL k v t1 t2)
Proof
  rw[balanceL_def,tree_def]
QED

Theorem avl_balanceL_1:
  ∀ k v t1 t2. height t1 = height t2 + 1 ∧ avl t1 ∧avl t2 ⇒
                      avl(balanceL k v t1 t2)
Proof
  rw[balanceL_def,tree_def]
QED

Theorem insertion_preserves_avl:
  ∀ k v t. avl t ⇒ avl(insert_avl k v t )
Proof
  Induct_on ‘t’ >> rw[avl_def,insert_avl_def,singleton_avl_def]
  >-(rw[])
QED
*)

val _ = export_theory ();
