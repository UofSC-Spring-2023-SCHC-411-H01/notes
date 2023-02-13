import Std.Tactic.ShowTerm
import Mathlib.Init.Function 

/- 
Tactics are human helpers for constructing proof terms, ie terms `c : p` where 
`p` is the proposition to be proven. 

Let's look at the following two proofs 
-/

section 

variable (α β γ : Type) (f : α → β) (g : β → γ) 

open Function 

example : Injective (g ∘ f) → Injective f := by sorry 

example : Surjective (g ∘ f) → Surjective g := by sorry 

/-
What do the proof terms look like? 
-/ 

example : Injective (g ∘ f) → Injective f := by 
  show_term {sorry} 

-- We can then do this
example : Injective (g ∘ f) → Injective f := sorry 

example : Surjective (g ∘ f) → Surjective g := by 
  show_term {sorry}

-- And this 
example : Surjective (g ∘ f) → Surjective g := sorry 

end 
/- 
Concision is the main advantage of constructing a proof term directly. Another 
possible advantage is a lower level of complexity. Tactics can be implemented 
with strange behavior in edge cases, in theory. 

A distinct disadvantage is lower level of readability. 
-/

/- 
Lean is based on dependent type theory. Above we can have seen one incarnation 
of "dependence". 

`Injective f` depends on the input `f : α → β`. Thus, we have a type which 
depends on a term. 

While the name "dependent type theory" originates from this form of dependence 
there are others built into Lean. 

Terms can depend on a type. 
-/ 

def proj₁ (α₁ α₂ : Type) : α₁ × α₂ → α₁ := fun ⟨a,_⟩ => a 

/-
This is a term of a basic function type but it depends on `α` and `β`. 
Instantiating either gives a concrete term. 
-/

-- This is now a concrete term 
#check proj₁ UInt8 Bool 

/- 
We can also have a type depend on another type, like `List`. 

And of course we have terms that depend on other terms, ie functions.

Lean accomodates all these versions of dependence. It is based on the 
Calculus of Inductive Constructions introduced by Thierry Coquand. 

More details on the type theory of Lean can be found in Mario Carneiro's
[Masters thesis](https://github.com/digama0/lean-type-theory). 
-/

