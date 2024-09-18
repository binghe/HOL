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

Theorem height_eq_1[simp]:
  (height t = 1 ⇔ (∃k v. t = Bin 1 k v Tip Tip)) ∧
  (1 = height t ⇔ (∃k v. t = Bin 1 k v Tip Tip))
Proof
  >> STRIP_TAC
  >> Cases_on ‘t’
  >> csimp[]
  >> ASM_REWRITE_TAC[height_def,height_eq_0]
  >>

QED



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
   N 1 = 0
Proof
  >> REWRITE_TAC [N_def, height_def, avl_def, node_count_def]
  >> sg ‘IMAGE node_count {x | height x = 1 ∧ avl x} = {0}’
  >> REWRITE_TAC [EXTENSION, IN_IMAGE, IN_SING, MIN_SET_ELIM]       
  >> GEN_TAC  
  >> EQ_TAC 
  >- [STRIP_TAC
     ASM_REWRITE_TAC [] THEN
      Cases_on ‘x'’ THEN
      ASM_REWRITE_TAC [height_def,avl_def,node_count_def] 
    >> sg ‘height a = 0 ∧ height a0 = 0’ 
    >> ASM_REWRITE_TAC[height_def,height_eq_0]
    >> STRIP_TAC
    >>     
                
QED      



