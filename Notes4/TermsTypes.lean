import Mathlib.Algebra.Group.Basic

/- 

# Simple type theory and its embedding into Lean 

## Types

We have some collection of base types τ, σ,... and the ability to 
form function types τ → σ. 

While the base types are symbolic, we often use familiar types 
like Int, Float, or String. Mathematical objects can also fit 
here like ℝ or Set. 

Using function types, we can build new types from old like 
τ → (σ → τ). 

Note here that parenthesis are important. ℕ → (ℚ → ℝ) differs from 
(ℕ → ℚ) → ℝ. The first takes natural numbers as inputs and returns 
functions whose inputs are rational numbers and whose outputs are 
real numbers. The latter inputs _functions_ ℕ → ℚ and outputs ℝ. 

-/

-- We have familiar types in Lean core
#check UInt64 
#check Float 
#check String 
#check List

-- Other types are defined in libraries 
#check Group 
#check Monoid 
#check ℕ 

-- From these we can iteratively make function types 
#check Float → String 
#check (ℕ → ℕ) → ℕ  
#check ℕ → (ℕ → ℕ) 
-- #check ℕ × ℕ → ℕ 
-- By convention we right associate iterated function types 
#check String → (ℤ → Bool) → Prop 
-- Note the lack of parenthesis 

/- 

## Terms 

Terms are organized by their type. For example, 50.12 is a Float 
and 10 (most naturally) has type ℕ 

To build terms of simple type theory, we have two basic 
building blocks: constants and variables. The two examples above are 
constants and their meaning is fixed. 

Variables behave as familiar. 

One way to declare new constants in Lean is to use the axiom 
keyword opaque  
-/ 

-- This tells Lean that we have a string that 
opaque s : String 
#check s 
-- #eval s 
axiom zeus : Bool 
/-
What do we know about it? Nothing. Opaque and its cousin axiom should 
be avoided

We can build strings use the def keyword. 
-/
def better : String := "Better" 
#check better 
#eval better 
-- or integers 
def myfav : UInt8 := 10 
def legit : Bool := true 
example : Float := 12395959594848494949

-- Variables can be declared using the variable keyword 
variable (x : ℤ) 
#check x 
variable (u v w : String) 
#check v  

/- 
These are usually called free variables. Bound variables appear 
in one of the two ways to make new terms from old. 

In function application, we can combine a term (f : τ → σ) and a 
term (t : τ) to get a term of type σ. This is denoted by f t, eg f(t) in math.  

In function abstraction, we given a variable (x: τ) and a term 
(s : σ) that may involve x we can form the function that we would 
usually in math denote x ↦ s(x). In a function abstraction, 
the variable x is called _bound_. 
-/ 

-- We build functions in Lean using the fun keyword 
def funFun : String → ℕ := fun s => s.length 
-- We can construct the variable term directly 
def fancy (n : ℕ) : ℕ := 3*n+4
#check fancy 
-- We can also use λ notation 
def lamAbst : ℕ → String := λ s => toString s 

-- We write application of function as concatentation. 
#check funFun better
#eval funFun better 
#reduce funFun better 

-- Note that types need to match 
#check funFun myfav 

/- As a consequence of our associativity convention for 
iterated function types, we left associate function application 
by default. 
-/
#check fancy fancy 5 
#check fancy (fancy 5) 

/- 
Multivariable functions come from iterating →. Below we make a 
function of two variables of type the natural numbers. 
-/
def biggest : ℕ → ℕ → ℕ := 
  fun n => fun m => max n m 
def biggest' : ℕ → ℕ → ℕ := 
  fun n m => max n m 
def biggest'' (n m : ℕ) : ℕ := max n m 

/- 
Partial application of curried functions is natural from 
these conventions. 

Given f : σ₀ → σ₁ → σ₂ → ⋯ → σₘ and a term s : σ₀, we have 
f s : σ₁ → ⋯ → σₘ 
-/
#check biggest' 10 

/- 
We've used some existing functions in Lean to simply our 
constructions above, eg length, toString, and max. 

Lean possesses standard programming language constructs 
which we can use to build terms directly, like if-then-else if-then-else.
-/

def goodChoice (n : Nat) : Nat := 
  if n = 37 then 37 
  else if n = 73 then 73 
  else 0 

/- 
Note that the #check command is just to check the type of a term. 
It does not betray any computation on the term. 

If you want to actually evaluate a function, you can use one of 
two options: #eval and #reduce 
-/

#eval goodChoice 10 
#reduce goodChoice 37

/- 
While both perform computation, there are important differences. 

#reduce attempts to reduce terms to a normal form. It works within 
the type checking kernel of Lean. It is generally more expensive. 

#eval uses an external VM to perform quick (unverified) computation. 
-/

