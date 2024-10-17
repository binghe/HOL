open HolKernel boolLib bossLib BasicProvers;
open optionTheory pairTheory stringTheory hurdUtils;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open comparisonTheory;
open pred_setTheory;

val _ = new_theory "AVL_trees";

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

Definition keys_def:
  keys Tip = {} ∧  
  keys (Bin _ k v l r) = {k} ∪ keys l ∪ keys r
End

Theorem keys_insert:
  ∀ x v t. keys(insert_avl x v t) = (keys t ∪ {x})
Proof
  fs[]
  >> rpt GEN_TAC
  >> Induct_on ‘t’
  >> fs[]
  >> rw[insert_avl_def,keys_def,singleton_avl_def]
  >> gvs[insert_avl_def]    


        
QED
val _ = export_theory ();


