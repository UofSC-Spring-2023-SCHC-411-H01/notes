/-
The final ingredient in predicate logic is equality, usually written 
`=`. It is characterised by four propreties 
- Reflexivity : `∀ a, a = a`  
- Symmetry : `∀ a a', a = a' → a' = a`
- Transitivity : `∀ a₁ a₁ a₂, a₁ = a₂ → a₂ = a₃ → a₁ = a₃` 
- Substitution : `∀ (f : α → β), a = a' → f a = f a'` 

Equality is implemented in Lean using the type `Eq`. 

/--
The equality relation. It has one introduction rule, `Eq.refl`.
We use `a = b` as notation for `Eq a b`.
A fundamental property of equality is that it is an equivalence relation.
```
variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)

example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd
```
Equality is much more than an equivalence relation, however. It has the important property that every assertion
respects the equivalence, in the sense that we can substitute equal expressions without changing the truth value.
That is, given `h1 : a = b` and `h2 : p a`, we can construct a proof for `p b` using substitution: `Eq.subst h1 h2`.
Example:
```
example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2
```
The triangle in the second presentation is a macro built on top of `Eq.subst` and `Eq.symm`, and you can enter it by typing `\t`.
For more information: [Equality](https://leanprover.github.io/theorem_proving_in_lean4/quantifiers_and_equality.html#equality)
-/
inductive Eq : α → α → Prop where
  /-- `Eq.refl a : a = a` is reflexivity, the unique constructor of the
  equality type. See also `rfl`, which is usually used instead. -/
  | refl (a : α) : Eq a a

So in Lean these four properties can be called via 
- Reflexivity : `Eq.refl`
- Symmetry : `Eq.symm` 
- Transitivity : `Eq.trans` 
- Substitution : `Eq.subst` 

-/

#check @Eq.refl 
#check @Eq.symm
#check @Eq.trans 
#check @Eq.subst

-- More generally we have 
#check @congrArg 

variable {α β : Type} (f : α → β) (a a' : α) 

-- A proof of the last one would look like 
example (h : a = a') : f a = f a' := by 
  cases h 
  exact Eq.refl <| f a  

/-

Equality goals appear very frequently in proofs so we have the `rfl` tactic 
to close such goals. 

At the heart of equality is rewriting terms. Lean provides a robust set of tools 
for ease of rewriting. Foremost is the rewriting tactic `rw`. 

-/

example : a = a' → a' = a := by 
  intro h
  rw [h] 

/-

`rw [h]` rewrite the goal using h by looking for occurences of the term on 
left hand side and replacing with the term on the right hand side. You can 
rewrite right to left via `rw [←h]`. 

You can also rewrite hypotheses using `at`. 

-/

structure Point {α β : Type} where 
  x : α 
  y : β 

variable (b b' : β) 

example (h : a = a') (h' : b = b') : Point.mk a b = Point.mk a' b' := by 
  rw [h,h']

/-

Lean's simplifier `simp` is another tool for rewriting. It is not restricted to 
equality 

-/
