open HolKernel boolLib bossLib BasicProvers;
open optionTheory pairTheory stringTheory hurdUtils;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open comparisonTheory;
open integerTheory;
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
  singleton_avl k v = Bin 1 k v Tip Tip
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

Definition Fibonacci_def :
    Fibonacci (n :num) =
       if n = 0 then (0:num) else
         if n = 1 then (1:num) else
          Fibonacci (n - 1) + Fibonacci (n - 2)
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
        
Theorem N_fibonacci_relation:
  ∀k. N k = Fibonacci (k+2)-1
Proof
  rpt STRIP_TAC
  >> Induct_on ‘k’
  >> simp[N_0]               
  >> fs[Fibonacci_def]       
QED        
val _ = export_theory ();
