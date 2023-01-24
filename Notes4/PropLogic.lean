import Mathlib.Data.Nat.Prime

namespace Intro 
/- 
We can declare variables of type Prop as 
-/
variable (p q : Prop) 

/-
Terms of type (p : Prop) are _proofs_ of the proposition p. 

We state a theorem to declare we want to produce a proof 
-/
theorem foo : p := sorry 

/-
Of course we cannot fill in this sorry. Not every proposition in 
that can be stated in Lean will have a proof. For example, 
-/ 
theorem crazy : ∀ (n : ℕ), Nat.Prime n := sorry 

end Intro 
/- 
Under the rules of propositional and higher logics, there are 
a handful of ways to make new propositions, called _connectives_, 
and a handful to rules to produce new proofs from old ones, _rules 
of inference_. 

The connectives in propositional logic are 
- implication : p → q 
- conjunction : p ∧ q 
- disjunction : p ∨ q 
- negation : ¬ p 
- bi-implication : p ↔ q 

Each takes an existing set of propositions and constructs a new one. 
They can be iterated, eg (p ↔ q) ∨ ¬ p → q. Note that parentheses 
are important for the order of application of the connectives. 

Each connective comes with rules for providing a proof, introduction 
rules, and using as a hypothesis, elimination rules. 
-/

/- 
Implication

Suppose we have (p q : Prop). What do we need to produce a proof of 
p → q? Well, whenever we have a proof of p, we need to construct 
a proof of q. In Lean, we can see the difference syntactically. 
-/

variable {p q r : Prop}

theorem imp (h : p) : q := sorry 

theorem imp' : p → q := sorry 

/-
The introduction rule says that give `imp` we can conclude `imp'`. 
In Lean, we can give a proof of `imp'` using `imp` and the 
tactics `intro` and `exact`. 
-/

example : p → q := by 
  intro h -- the goal is now q and we have (h : p) in the context
  exact imp h  -- tells Lean that `imp h` is _exactly_ the term we want

/-
The elimination rule says that give `f : p → q` and `h : p` we can 
conclude `q`. 
-/ 

example (h : p) (f : p → q) : q := by 
  apply f
  exact h

/- 
In Lean, propositional implication is a function type. Application is 
elimination. The tactic `apply` allows us to replace a goal `β` with 
`α` if we have a term of type `α → β` in the context.
-/

/- 
Unlike implication, conjunction is defined separately in Lean. In Lean 
core, it is defined as. 

structure And (a b : Prop) : Prop where
  /-- `And.intro : a → b → a ∧ b` is the constructor for the And operation. -/
  intro ::
  /-- Extract the left conjunct from a conjunction. `h : a ∧ b` then
  `h.left`, also notated as `h.1`, is a proof of `a`. -/
  left : a
  /-- Extract the right conjunct from a conjunction. `h : a ∧ b` then
  `h.right`, also notated as `h.2`, is a proof of `b`. -/
  right : b

Built into its definition are its introduction `intro` and its two 
elimination rules `left` and `right`.

-/

example : (p ∧ q → r) → p → q → r := sorry 

example (h : r → p) (h' : r → q) : r → p ∧ q := sorry 

/- 
Disjunction is also its own type. 

`Or a b`, or `a ∨ b`, is the disjunction of propositions. There are two
constructors for `Or`, called `Or.inl : a → a ∨ b` and `Or.inr : b → a ∨ b`,
and you can use `match` or `cases` to destruct an `Or` assumption into the
two cases.

inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b

Disjunction has two introduction rules, intro left or `inl` and intro right or `inr`. 
It's elimination rule is derived from the fact it is an inductive type. 
-/

example : (p → q) → (q → q ∨ r) := sorry 

example : (p ∨ q → r) → (p → r) → q → r := sorry 

/- 
Negatation relies on `False : Prop`. 

`False` is the empty proposition. Thus, it has no introduction rules.
It represents a contradiction. `False` elimination rule 
expresses the fact that anything follows from a contradiction.
This rule is sometimes called ex falso (short for ex falso sequitur quodlibet),
or the principle of explosion.

inductive False : Prop

-/

example (f : False) : crazy := by
  cases f 
  -- exact f.elim 

/- 
There is a corresponding type `True : Prop` with a single constructor. 
`True.intro`. 

By definition in Lean, `¬ p` is _defined as_ `p → False`. 
-/

example : (p → q) → ¬ q → ¬ p := sorry 

example : ¬ p ∨ ¬ q → ¬ (p ∧ q) := sorry 

/-
Finally bi-implication or if-and-only-if looks a bit similar to `And` 
under the hood. 

If and only if, or logical bi-implication. `a ↔ b` means that `a` implies `b`
and vice versa.

structure Iff (a b : Prop) : Prop where
  /-- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  intro ::
  /-- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  mp : a → b
  /-- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  mpr : b → a
-/

example (h : p ↔ q) : (q → r) → p → r := sorry 

example : ¬ (p ↔ ¬ p) := sorry 
