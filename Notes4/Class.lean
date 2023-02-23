import Mathlib.Data.Rat.Basic 
import Mathlib.CategoryTheory.Bicategory.Basic

/- 
We have see how structures as a way to carry around addition data. 
But there can be _a lot_ of additional in general. 
-/ 

#print Rat 

/- For the rational numbers `ℚ` or `Rat` are lots of natural 
things to do, add, multiply, divide (if nonzero), take floors,... 
Building a single structure with all of these as fields is 
not a good idea. 

(Type)Classes provide an answer to this. The syntax looks very 
similar to a structure. 
-/

example (q r : ℚ) : ℚ := q+r 

example : Add ℚ := inferInstance 

example : ℚ := default 

class LawlessGroup (α : Type) where 
  unit : α 
  mul : α → α → α 
  inv : α → α 

#print LawlessGroup

/- While can declare instances of a class like with structure 
using `def` or `example`, we can also declare instances 
using the `instance` keyword -/

instance : LawlessGroup ℕ where 
  unit := 0 
  mul n m := n + m 
  inv _ := 0 

/- The advantage of classes is that Lean keeps track of 
typeclass instancs and will try to provide one in the 
correct context -/

-- `inferInstance` is basically telling Lean to find one
example : LawlessGroup ℕ := inferInstance  

-- Now Lean can find `mul` from the instance of `LawlessGroup` on `ℕ` 
example : ℕ → ℕ → ℕ := LawlessGroup.mul

-- Even better, we can open the `LawlessGroup` namespace 

open LawlessGroup 

example : ℕ → ℕ := inv

#print Inhabited 
#print Nonempty 

instance myInstance { α β : Type } [ Inhabited α ] (f : α → β) : Inhabited β := 
  { default := f default }
#check myInstance 
example (β : Type) (f : ℕ → β) : Inhabited β := myInstance f 

instance {α β : Type} [Add β] : Add (α → β) where 
  add := fun f g a => f a + g a   

#check Add

def myAdd {α : Type} [Add α] (l l' : List α) : (List α) := 
  match l, l' with 
  | [],_ => [] 
  | _,[] => [] 
  | a::as, a'::as' => (Add.add a a') :: myAdd as as'

#eval myAdd [1,2] [3]

instance [Add α] : Add (List α) where 
  add := myAdd

def myHead { α : Type} [Inhabited α] (l : List α) : α := 
  match l with 
  | [] => default 
  | a::_ => a 

