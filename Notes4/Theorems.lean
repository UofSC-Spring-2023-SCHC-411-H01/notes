import Mathlib.Data.Nat.Basic
import Notes4.IndTypes

/-
One of the features that sets Lean apart from other programming languages, and 
motivates this course, is the ability to reason your written code in a 
computational way. 

We can state theorems expressing invariants of code and then write more 
code to produce a proof verifying that theorem. 

For example, we expect, implemented correctly, taking lenghts of 
lists is additive under appending an element, ie length a::l = 1 + length l.
-/

theorem list_length_add_of_cons {α : Type} (a : α) (l: List α) : 
    (a::l).length = 1 + l.length := sorry 

/- 
Theorems are terms of type Prop. Prop is a special type in Lean whose terms 
are propositions in the sense of mathematical logic. For example, 

- There are infinitely many prime numbers. 
- If f and g are differentiable, then so is f + g. 
- There is at most one path between any two vertices in a tree. 
- All natural numbers are odd.

Propositions can have proofs or not. These proofs are built by stringing 
together existing proofs to make new ones using basic rules of inference. 
Thanks to this computational nature, one can model propositional (and 
higher) logic in Lean and other languages like Coq, Agda, HOL, Isabelle, 
F-star, Idris,... 

This provides the ability to use the _same tools_ to create proofs as 
to program. Assuming the underlying implementation sound, then proving a 
theorem universally assures that correctness of the code, with regards 
to that particular statement. For list_length_add_of_append, giving a proof 
assures that our implementation of append is _always_ additive with 
respect to lengths of lists. There are no edge cases and no bugs. 

What does a proof look like?
-/

example {α : Type} (a : α) (l: List α) : (a::l).length = 1 + l.length := by 
  match l with 
  | [] => simp  
  | a'::as => 
    simp only [List.length]
    ac_rfl

/-
_You do not have to have any understanding of the actual tactics in 
use in these examples right now._ 
Most of the course will devoted to obtaining facility 
in constructing proofs using these tactics. 

Right now, you should familiarize yourself with the structure of a proof.

Let's step through this proof to get a sense of the pieces involved. Every 
proof starts with either an `example` or `theorem` keyword. If we use the 
theorem keyword, we need to provide a unique name. Otherwise, we do not. 

Then comes the hypotheses of the statement 
`{α : Type} (a : α) (l: List α)` which say we have 
- some type α which Lean should try to fill in from the context, 
- a term `a` of type `α`, and 
- a list `l` with elements of type `α`. 

At the end of the hypotheses, we find a `:` to indicate the type of 
proposition will follow. Here the type is `(a::l).length = 1 + l.length`. 
This is the proposition we are trying to prove. 

Next, we have `:=` which tells Lean that the statement of the type is done 
and next we will provide the term of that term, here a proof. 

Immediately after `:=` we have a `by` which enters _tactic mode_. We 
will start out using proving tactic mode to construct proofs. 

Tactics are a method of automation to construct terms of desired types. 
As such, they fall in the realm of _meta_-programming. A well-written 
tactic can be incredibly useful and great time-saver. 

The remainder of the proof consists of calls to appropriate tactics: 
- `match` allows to reduce to providing proofs for each constructor 
of List, nil and cons. 
- In the nil, [], branch, we call on Lean's simplifier _simp_ which is 
a extensiable rewriting system. 
- In the cons branch, we again called simp but using the definition of 
List.length to simplify the goal. Then we called the `ac_rfl` tactic 
which closes goals using associativity, commutativity, and reflexivity. 

In general, there is a zoo of tactics of which we will see only a corner. 
If time allows, we will discuss how to write tactics. 

Let's see another example of the structure of a theorem and its proof. 
-/ 

theorem exp_eq_exp' (b e : Nat) : exp b e = exp' b e := by 
  match e with 
  | 0 => simp [exp,exp'] 
  | n+1 => 
    simp only [exp,exp']
    simp only [Nat.add]
    rw [exp_eq_exp' b n]
     
/-
Now we know from `exp_eq_exp'` that our two definition of natural 
number exponentiation always produce the same outputs. 

Here we saw another tactic `rw` which is also a rewriting tactic. 

Now that we know that both version of exp are equal let's prove a 
basic property of exponention. 
-/

example : ∀ a b c : Nat, exp a (b + c) = (exp a b)*(exp a c) := by 
  intro a b c
  induction' b with n ih  
  · simp [exp]
  · rw [Nat.succ_eq_add_one]
    rw [Nat.add_assoc,Nat.add_comm 1 c,←Nat.add_assoc]
    simp [exp]
    rw [Nat.mul_assoc,Nat.mul_comm a _,←Nat.mul_assoc]
    rw [ih]

