/- 
# Sorting a list

-/

variable {α : Type} {f : α → α → Bool} (r : α → α → Prop) 

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

example : Sorted (·≤·) [1,2,3] := by 
  apply longer
  · simp 
  · apply longer 
    · simp 
    · apply single

theorem sorted_tail_of_sorted (a : α) (as : List α) 
    (h : Sorted f (a::as)) : Sorted f as := by
  match h with 
  | single => apply nil  
  | longer _ h'' => exact h''

def insert (a : α) (l : List α) : List α :=
  match l with 
  | [] => [a] 
  | a'::as => 
    match f a a' with 
    | true => a::a'::as 
    | false => a'::insert a as 

#check insert 

def insertSort (l : List α) : List α := sorry 
