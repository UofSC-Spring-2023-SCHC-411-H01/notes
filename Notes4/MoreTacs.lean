import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

/-
Already our proofs are getting fairly complicated. A common technique 
in a proof is to construct helper results which then are employed to 
assist with the main goal. 
-/

open Function 

variable {α β γ δ : Type} (f : α → β) (g : β → γ) (h : γ → δ)

example : (h ∘ g) ∘ f = h ∘ (g ∘ f) := by 
  apply funext
  intro x
  simp

#print Injective 

/-
We can use `have` to declare intermediate goals
-/

example (h₁ : Injective f) (h₂ : Injective g) : Injective (g ∘ f) := by 
  intro a₁ a₂ h' 
  have h'' : f a₁ = f a₂ := h₂ h' 
  apply h₁ h''

#print Surjective 

/-
We can also use `have` to destructure types
-/

example (h₁ : Surjective f) (h₂ : Surjective g) : Surjective (g ∘ f) := by 
  intro c
  have ⟨b,h'⟩ := h₂ c
  have ⟨a,h''⟩ := h₁ b
  apply Exists.intro a
  dsimp 
  rw [h'',h']

#print Bijective 

example (h' : Bijective f) : Injective f := by 
  have ⟨inj,_⟩ := h' 
  assumption 

example : Injective (g ∘ f) → Injective f := sorry 

example : Surjective (g ∘ f) → Surjective f := sorry 
/- 
`let` is similar to `have` but is meant for data-carring types while `have` is 
for `Prop`
-/

def translate (f : ℤ → ℤ) (shift input : ℤ) : ℤ := 
  let g : ℤ → ℤ := fun n => f n + shift
  g input

/-
When working with `=` or another transitive relation, we can use a `calc`. 
-/

example (a : ℤ) (f : ℤ → ℤ) : translate (translate f a) (-a) = f := by 
  apply funext 
  intro m 
  calc 
    translate (translate f a) (-a) m = translate f a m + (-a) := by simp [translate] 
    _ = (f m + a) + (-a) := by simp [translate] 
    _ = f m + (a + (-a)) := by rw [Int.add_assoc] 
    _ = f m + 0 := by rw [Int.add_right_neg]  
    _ = f m := by rw [Int.add_zero] 

/-
More generally `calc` blocks can be used for transitive relations. 
-/

example (p q r : Prop) (h : p ↔ q) (h' : q ↔ r) : p ↔ r := by 
  calc
    p ↔ q := by exact h
    _ ↔ r := by exact h'

#print Equiv

