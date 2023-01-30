import Mathlib.Data.Nat.Basic -- for ℕ notation

/-
We have covered the basics of propositional logic. The main limitation 
of propositional logic is that all statements have to be propositions. 

For example, we are not allowed to talk about a statement like: `n` is odd. 
This is not a proposition because `n` does not actually have a value. It 
is a placeholder which will be instantiated at some point by an actual 
value. 

Propositions that depend on variables are called _predicates_. They are 
implemented in Lean quite easily. 
-/

variable {α β : Type} 
variable (P P': α → Prop) (Q : α → β → Prop) 

/- 
Here `P` is a predicate on one variable by type `α` while `Q` is a 
predicate on two variables. 
-/

def leSquare : ℕ → ℕ → Prop := fun n m ↦ n ≤ m^2 

/-
We can convert predicates into propositions by _quantifying_ over them. 
In our previous example, we can go from `n` is odd to for all `n`, `n` is 
odd. This is now a proposition. 

Instead of asking that the predicate is true for all values, we can ask 
that it is true for at least one value: there exists `n` such that `n` is 
odd. 
-/

def allLESquare : Prop := ∀ n m, leSquare n m

def someLESquare : Prop := ∃ n m, leSquare n m 

/- 
Since we have multiple variables, we use different quantifiers. 
-/

def allLESomeSquare : Prop := ∀ n, ∃ m, leSquare n m 

def someLEAllSquares : Prop := ∃ n, ∀ m, leSquare n m 

/-
Notice that the order of quantifiers is important in general. 
-/

def someSquareGEAll : Prop := ∃ m, ∀ n, leSquare n m 

/-
Like the connectives, quantified statements have introduction and elimination 
rules.

The universal quantifier is essentially a function that take as input 
any value of the variables and gives as output a proof the proposition 
with that value. In Lean it acts as such. 
-/

example : ∀ (n : ℕ), n = n  := by
  intro n
  rfl 

example : ∀ (n : ℕ), n = n  := by
  exact fun n => rfl 

example (h : allLESquare) : 5 ≤ 4 := by 
  exact h 5 2

/-
The existentional quantifier in contrast is implemented as its own inductive 
type. 
/--
Existential quantification. If `p : α → Prop` is a predicate, then `∃ x : α, p x`
asserts that there is some `x` of type `α` such that `p x` holds.
To create an existential proof, use the `exists` tactic,
or the anonymous constructor notation `⟨x, h⟩`.
To unpack an existential, use `cases h` where `h` is a proof of `∃ x : α, p x`,
or `let ⟨x, hx⟩ := h` where `.
-/
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  /-- Existential introduction. If `a : α` and `h : p a`,
  then `⟨a, h⟩` is a proof that `∃ x : α, p x`. -/
  | intro (w : α) (h : p w) : Exists p
-/

example : ∃ n, ∀ m, leSquare n m := by
  apply Exists.intro 0
  intro m
  sorry 

example : ∃ n, ∀ m, leSquare n m := by
  exact ⟨0, sorry⟩ 

example (h : ∃ m, ∀ n, leSquare n m) : False := by 
  cases h with 
  | intro w h => sorry 

/- 
We can commute quantifiers of the same type. 
-/

example : ∀ a, ∀ b, Q a b ↔ ∀ b, ∀ a, Q a b := sorry 

example : ∃ a, ∃ b, Q a b ↔ ∃ b, ∃ a, Q a b := sorry 

/- 
Some other examples 
-/

example : ∃ a, ¬ P a → ¬ ∀ a, P a := sorry 

example (a : α) (h : ¬ ∀ a, P a) : ∃ a, ¬ P a := sorry 

example (h : ∀ a, P a) (h' : ∀ a, P' a) : ∀ a, P a ∧ P' a := sorry 

example (h : ∃ a, P a) : ∃ a, P a ∨ P' a := sorry 
