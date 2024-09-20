open HolKernel boolLib bossLib BasicProvers;
open optionTheory pairTheory stringTheory;
open arithmeticTheory pred_setTheory listTheory finite_mapTheory alistTheory sortingTheory;
open comparisonTheory;
open integerTheory;

val _ = new_theory "avl_tree";

Datatype:
  avl_tree = Tip | Bin int num 'a avl_tree avl_tree 
End
           
Definition height_def[simp]:
  height Tip = 0∧
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
       if n = 0 then 0 else
         if n = 1 then 1 else
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

(*
Theorem xxx :
  ∀k t. minimal_avl t ∧ height t = k ⇒ node_count t = N k
Proof
  rpt STRIP_TAC
  >> MP_TAC (Q.ISPEC ‘IMAGE node_count {x | height x = k ∧ avl x}’
              MIN_SET_PROPERTY)
  >> impl_tac
  >- (rw [EXTENSION] \\
      Q.EXISTS_TAC ‘t’ >> rw [] \\
      fs [minimal_avl_def])
      
  >> simp [N_def]
  >> fs [minimal_avl_def]
  >> sg ‘(∃x. height (x :'a avl_tree) = height t ∧ avl x)’
  >- ()
  cheat
QED
*)
        
Theorem N_k:
  ∀k. 2 <= k ⇒ N(k) = N(k-1) + N(k-2) + 1
Proof
  rpt STRIP_TAC
  >> Induct_on ‘k’
  >> fs[]
  >> fs[]
  >>      
QED  
