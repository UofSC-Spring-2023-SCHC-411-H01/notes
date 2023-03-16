import Mathlib.Data.Nat.Basic

/- 
# Sorting a list

-/

namespace Notes

variable {α : Type} (f : α → α → Bool) (r : α → α → Prop) 

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

inductive Sorted (f : α → α → Bool) : List α → Prop where 
  | nil : Sorted f []
  | single {a : α} : Sorted f [a]
  | longer {a₁ a₂ : α} {as : List α} (h : f a₁ a₂) 
    (h' : Sorted f (a₂ :: as)) : Sorted f (a₁::a₂::as)

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
    (h : Sorted f (a::as)) : Sorted f as := by
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
    match f a a' with 
    | true => a::a'::as 
    | false => a'::insert a as 

#check insert 

/- We prove a basic result about the length of inserted 
list and tag it with `@[simp]` for use with `simp` -/
@[simp]
theorem len_insert_eq_succ_len {a : α} {l : List α} : 
    (insert f a l).length = l.length + 1 := by 
  match l with 
  | [] => simp [insert]
  | a'::as =>
    match h : f a a' with 
    | true => simp [insert, h]
    | false => simp [insert, h]; apply len_insert_eq_succ_len 

/--
We sort `l` recursively sorting the tail first and then 
inserting the head at the appropriate location.
-/
def insertSort (l : List α) : List α :=
  match l with 
  | [] => [] 
  | a::as => insert f a <| insertSort as

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
class Asymmetric (f : α → α → Bool) where
  asym {a a'} : !f a a' → f a' a

open Asymmetric

/- A helpful constructor for `Sorted` that unifies the 
nonempty cases -/
def Sorted.cons {a : α} {l : List α} (h₁ : Sorted f l) 
    (h₂ : l.length > 0) (h₃ : f a l[0]) : Sorted f (a::l) :=
  match h₁ with 
  | nil => single
  | single => longer h₃ single
  | longer h h' => longer h₃ <| longer h h'

/- If we have a `Sorted` list with at least two elements, 
then the first elements are ordered appropriately with 
respect to `f` -/
theorem ordered_of_sorted {a a' : α} {as : List α} 
    (h : Sorted f (a::a'::as)) : f a a' :=
  match h with 
  | longer h' _ => h'

/- If we have a `Sorted` list `a'::as` where `a` and `a'` are 
ordered wrong, then the first two elements of `a'::insert f a as` 
are ordered correctly -/
theorem ordered_cons_insert_of_unordered {a a' : α} {as : List α}
    (h : Sorted f (a'::as)) (h' : f a' a) : f a' (insert f a as)[0] :=
  match as with 
  | [] => by simpa [insert]
  | a''::as' => 
  match h'' : f a a'' with 
    | true => by simpa [insert, h'']
    | false => by simp [insert, h'']; apply ordered_of_sorted f h

/- We prove that if we insert an element into a `Sorted` list 
it will remain `Sorted` assuming `f` is `Asymmetric` -/
theorem insert_sorted_of_sorted {a : α} {l : List α} [Asymmetric f] 
    (h : Sorted f l) : Sorted f <| insert f a l :=
  match l with 
  | [] => single
  | a'::as =>
    match h' : f a a' with 
    | true => by simp [insert, h']; apply longer h' h 
    | false => by
      simp [insert, h']
      apply cons f
      · apply insert_sorted_of_sorted <| sorted_tail_of_sorted f a' as h   
      · apply ordered_cons_insert_of_unordered f h 
        · apply asym; simp; assumption

/- Finally, we prove that if `f` is `Asymmetric` then `insertSort` 
always produces a `Sorted` list no matter `α` or `f` -/
theorem sorted_of_insertSort (l : List α) [Asymmetric f] : 
    Sorted f <| insertSort f l :=
  match l with 
  | [] => nil
  | a::as => by
    dsimp [insertSort]
    apply insert_sorted_of_sorted f <| sorted_of_insertSort as

