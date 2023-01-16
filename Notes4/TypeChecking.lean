/- 
We saw a bit of Lean's type theory last time. One of the core 
functions of Lean is a type-checker. 

To get a sense of how tha works, we will discuss type checking in 
in the context of simple type theory. 

We have typing conclusions called _judgements_ or _inferences_ and 
rules for building those judgements. 

A typing judgement always takes place in the presence of a 
_local context_ C. You can think of this as the current scope in 
the program. The local context keeps track of the current 
constants, variables and their corresponding types. 

Definitions and variables add new terms to the local context. 
-/ 

variable (x : Nat) -- now we have a variable of type Nat in context 
variable (f' : Nat → Float) -- now a function in the context 

/- 
We write C ⊢ x : τ to mean that in the (local) context, the term x has 
type τ. 

The rules for deriving typing judgement are 

Typing rules:

  —————————— Cst   if c is declared with type σ
  C ⊢ c : σ

  —————————— Var   if x : σ is the last occurrence of x in C
  C ⊢ x : σ

  C ⊢ t : σ → τ    C ⊢ u : σ
  ——————————————————————————— App
  C ⊢ t u : τ

  C, x : σ ⊢ t : τ
  ———————————————————————— Lam
  C ⊢ (λx : σ, t) : σ → τ

The Cst rule allows us to type check constants and the Var rule does 
the same for variables. 

The final two rules describe how function application and 
abstraction interact with typing. 
-/

def sadFace : String := sorry 

#check sadFace -- type checks correctly 

variable (s : String) 

#check s -- type checks correctly  

-- use a "general" type α 
variable { α : Type } 

def sumin : α := sorry 

#check sumin 

variable (a₀ : α) 

#check a₀  

variable { β : Type } (f : α → β) 

#check f a₀  -- good 

def myTerm (a : α) : β := sorry  

def myFun : α → β := fun a => myTerm a  

#check @myFun α β 

/- 
Types have terms themselves in Lean 
-/
variable (α β γ δ ε : Type) 

/- 

## Type inhabitation 

Not every type has a term in general. You are even more 
constrained if you case try to construct a term of a type 
given a fixed local context. 

We say a type in _inhabited_ if it there is a term of that type. 

For iterated function types, there is a search process to 
try to build a term. Constructing a term of τ → σ using function 
abstraction is equivalent to positing a variable x : τ in the 
context and then attempting to build a term of σ using x and 
other terms in C. 

Let's do an example. We mark it with sorry to tone down 
the error to a warning as we proceed. 
-/

-- Common types are inhabited 
example : String := "" 
example : Nat := 0 
example : Int := 0 
example : Float := 0.0 
example : Bool := true 
example : Char := ⟨0,(by simp)⟩  

/-
A generic type build from base types by making function may 
not have a term. 
-/
-- Can you fill this in? 
example : α → β := sorry 

-- How about 
example : α → α := sorry 

-- Or 
example : α → β → α := sorry 

/-
Let's look a more general algorithm in a more complex 
examples. 
-/

-- We want a term of this type 
example : (α → β → γ) → (α → β) → (α → γ) := sorry 

/- 
We can introduce a bound variable of type f : α → β → γ and 
sorry what is left. 
-/ 
example : (α → β → γ) → (α → β) → (α → γ) := fun f => sorry 
/- 
We see we need to fill in sorry with a term of type (α → β) → 
α → γ. We give a bound variable g : α → β to simplify the goal. 
-/
example : (α → β → γ) → (α → β) → (α → γ) := fun f g => sorry 
/- 
We continue again introducing a : α 
-/ 
example : (α → β → γ) → (α → β) → (α → γ) := fun f g a => sorry 
/- 
Our goal now is to make a term of type γ. This is not a function 
type so we cannot continue. But we now have f g a and can use 
function application to make new types. In particular, f a : β → γ 
and g a : β. With these results, we can use application once 
more to get f a (g a) : γ - the desired term. 
-/ 
def done : (α → β → γ) → (α → β) → α → γ := 
  fun (f : α → β → γ) (g : α → β) (a : α) => f a (g a) 

-- Some more examples 

example : (α → γ) → (δ → β) → (γ → T) → (β → γ) → δ → ε := sorry 

example : (((α → β) → β) → β) → (α → β) := sorry 

example : ((β → α) → α) → (β → γ) → (γ → α) → α := sorry 
