import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/- 
# Sorting a list

-/

namespace Notes

variable {α : Type} (r : α → α → Prop) [DecidableRel r]

/- 
We sort lists of type `α` using the comparison function 
`f` (or `r`). 

If `f a₁ a₂ = true`, then this is the "correct" order. 
Otherwise, it is "incorrect"

If `r a₁ a₂` has a proof, then this is the "correct" order. 
Otherwise, it is "incorrect"

What are some examples of sorted lists?

- [] is should be sorted
- for any `a:α`, then `[a]` is sorted 
- for any `a₁ a₂ : α` and any `as : List α` such that 
  `f a₁ a₂  = true` and `a₂ :: as` is sorted, then 
  `a₁ :: a₂ :: as` is sorted 
-/

inductive Sorted (r : α → α → Prop) : List α → Prop where 
  | nil : Sorted r []
  | single {a : α} : Sorted r [a]
  | longer {a₁ a₂ : α} {as : List α} (h : r a₁ a₂) 
    (h' : Sorted r (a₂ :: as)) : Sorted r (a₁::a₂::as)

open Sorted

/- We can check that particular lists are `Sorted` -/
example : Sorted (·≤·) [1,2,3] := by 
  apply longer
  · simp 
  · apply longer 
    · simp 
    · apply single

/- We can also prove basic facts about our implementation 
of sorted lists -/
theorem sorted_tail_of_sorted (a : α) (as : List α) 
    (h : Sorted r (a::as)) : Sorted r as := by
  match h with 
  | single => apply nil  
  | longer _ h'' => exact h''

/- We now we want to implement an algortihm to sort 
lists and then _prove_ that it always produces a `Sorted` 
list. 

We will use insert sort. We will recursively sort the 
tail of a list and then insert the head in the 
appropriate place. We first give the insertion function.-/

/-- 
`insert` places `a` before the first element `a'` 
of `l` which satisfies `f a a'`. 
-/
def insert (a : α) (l : List α) : List α :=
  match l with 
  | [] => [a] 
  | a'::as => 
    if r a a' then a::a'::as else a'::insert a as

#check insert 

/- We prove a basic result about the length of inserted 
list and tag it with `@[simp]` for use with `simp` -/
@[simp]
theorem len_insert_eq_succ_len {a : α} {l : List α} : 
    (insert r a l).length = l.length + 1 := 
  match l with 
  | [] => by simp [insert]
  | a'::as =>
    if h : r a a' then by simp [insert, h] else
    by simp [insert, h]; apply len_insert_eq_succ_len 

/--
We sort `l` recursively sorting the tail first and then 
inserting the head at the appropriate location.
-/
def insertSort (l : List α) : List α :=
  match l with 
  | [] => [] 
  | a::as => insert r a <| insertSort as

#check insertSort

/- Some examples our polymorphic sorting algorithm applies to -/
#eval insertSort (·≤·) [4,5,2,4,5,6]
#eval insertSort (fun (b b' : Bool) => b && b') [true,false,false]
#eval insertSort (fun _ _ => true) [4,5,2,4,5,6]


/- For a general `f`, we will not be able to show that the 
output of `insert f l` satsisfies `Sorted f l`. For example, 
for `fun _ _ => false`, if we have `Sorted f l` then 
`l.length` is 0 or 1. This is a reasonable class of `f` to 
make sorting work as expected -/
class Asymmetric (r : α → α → Prop) where
  asym {a a'} : ¬ r a a' → r a' a

open Asymmetric

/- A helpful constructor for `Sorted` that unifies the 
nonempty cases -/
def Sorted.cons {a : α} {l : List α} (h₁ : Sorted r l) 
    (h₂ : l.length > 0) (h₃ : r a l[0]) : Sorted r (a::l) :=
  match h₁ with 
  | nil => single
  | single => longer h₃ single
  | longer h h' => longer h₃ <| longer h h'

/- If we have a `Sorted` list with at least two elements, 
then the first elements are ordered appropriately with 
respect to `f` -/
theorem ordered_of_sorted {a a' : α} {as : List α} 
    (h : Sorted r (a::a'::as)) : r a a' :=
  match h with 
  | longer h' _ => h'

/- If we have a `Sorted` list `a'::as` where `a` and `a'` are 
ordered wrong, then the first two elements of `a'::insert f a as` 
are ordered correctly -/
theorem ordered_cons_insert_of_unordered {a a' : α} {as : List α}
    (h : Sorted r (a'::as)) (h' : r a' a) : r a' (insert r a as)[0] :=
  match as with 
  | [] => by simp [insert]; assumption
  | a''::as' => 
    if h'' : r a a'' then
    by simpa [insert, h'']
    else
    by simp [insert, h'']; apply ordered_of_sorted r h

/- We prove that if we insert an element into a `Sorted` list 
it will remain `Sorted` assuming `f` is `Asymmetric` -/
theorem insert_sorted_of_sorted {a : α} {l : List α} [Asymmetric r] 
    (h : Sorted r l) : Sorted r <| insert r a l :=
  match l with 
  | [] => single
  | a'::as =>
    if h' : r a a' then 
    by simp [insert, h']; apply longer h' h 
    else
    by
      simp [insert, h']
      apply cons r
      · apply insert_sorted_of_sorted <| sorted_tail_of_sorted r a' as h   
      · apply ordered_cons_insert_of_unordered r h 
        · apply asym; simp; assumption

/- Finally, we prove that if `f` is `Asymmetric` then `insertSort` 
always produces a `Sorted` list no matter `α` or `f` -/
theorem sorted_of_insertSort (l : List α) [Asymmetric r] : 
    Sorted r <| insertSort r l :=
  match l with 
  | [] => nil
  | a::as => by
    dsimp [insertSort]
    apply insert_sorted_of_sorted r <| sorted_of_insertSort as

variable [Trans r r r]

class Transitive (r : α → α → Prop) where
  trans' {a₁ a₂ a₃} : r a₁ a₂ → r a₂ a₃ → r a₁ a₃ 

theorem Nat.succ_of_lt {i j : ℕ} (h : i < j) : ∃ l, l+1 = j := sorry

open Transitive

theorem totally_ordered_of_sorted [Transitive r] {l : List α} (h : Sorted r l) :
    ∀ {i j : ℕ}, (i < j) → (_ : i < l.length) → (_ : j < l.length) → r l[i] l[j] :=
  match h with
  | nil => fun _ h' _ => False.elim <| by
    rw [List.length_nil] at h'
    exact Nat.not_lt_zero _ h'
  | single => fun h hi hj => by 
    dsimp at hi hj
    apply False.elim
    linarith
  | longer h₁ h₂ => by 
    intro h' hi hj
    rename_i i j a₁ a₂ as
    have ⟨l,hl⟩ := Nat.succ_of_lt h'
    rw [←hl] at hj h'
    simp only [←hl]
    have : l < (a₂ :: as).length := 
      Nat.pred_lt_pred (by simp) hj
    have hl' : (a₁::a₂::as)[l+1] = (a₂::as)[l] := rfl
    by_cases i = 0 
    · simp [h,hl'] at *
      by_cases l = 0
      · simp [h,h₁] 
      · apply trans'
        . exact h₁ 
        · change r (a₂::as)[0] (a₂::as)[l]
          apply totally_ordered_of_sorted h₂
          apply Nat.one_le_iff_ne_zero.mpr h
    · have ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero h
      rw [hk] at hi h'
      simp only [hk]
      have : k < (a₂::as).length :=
        Nat.pred_lt_pred (by simp) hi
      have hk' : (a₁::a₂::as)[k+1] = (a₂::as)[k] := rfl
      rw [hk',hl']
      apply totally_ordered_of_sorted h₂ 
      apply Nat.pred_lt_pred (by simp) h'
