import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Basic

/-
Already our proofs are getting fairly complicated. A common technique 
in a proof is to construct helper results which then are employed to 
assist with the main goal. 
-/

open Function 

variable {α β γ δ : Type} (f : α → β) (g : β → γ) (h : γ → δ)

#check Function.comp

-- \circ ∘ 
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

/-
Here is `Nat.add`'s definition but with a new name
-/
def plus (m n : ℕ) : ℕ := 
  match n with 
  | 0 => m 
  | n'+1 => .succ (plus m n')

/- 
Let's check that if `m₁ ≤ m₂` then `m₁ ≤ m₂ +1` 
-/

theorem leq_succ_of_leq (m n : Nat) (h : m ≤ n) : m ≤ plus n 1 := by 
  match n with 
  | 0 => 
    have meq0 : m = 0 := Nat.eq_zero_of_le_zero h
    rw [meq0]
    simp
  | n'+1 => 
    simp [plus]
    calc 
      m ≤ n'+1 := by exact h 
      _ ≤ (n'+1)+1 := by exact Nat.le_succ _  

theorem succ_leq_succ_of_leq (m n a : Nat) (h : m ≤ n) : plus m a ≤ plus n a := by 
  match a with 
  | 0 => simp [plus]; assumption 
  | b+1 => 
    simp [plus] 
    apply Nat.succ_le_succ
    exact succ_leq_succ_of_leq m n b h
