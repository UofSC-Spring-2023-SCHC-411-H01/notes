/- 
Lean has a robust type theory. The foremost example of this are 
its _inductive types_. To get a sense of these, let's look at 
some examples 
-/

-- We open a namespace to avoid conflict with existing ones. 
namespace Notes

-- This is what the natural numbers in Lean look like. 
inductive Nat : Type where 
  | zero 
  | succ (n : Nat) 

/- 
The keyword _inductive_ tells Lean we are going to define an 
inductive type. Then we provide the name for the type, here Nat, 
and can provide its type. 

The _where_ clause starts the list of constructors used to define 
the type. 

In this example, Nat has two constructors 
- Nat.zero 
- Nat.succ n with n : Nat 

-/

#check Nat.zero 

#check Nat.succ

/- 
Every term of type Nat is built using these constructors. We can 
enumerate the terms: 
Nat.zero, Nat.succ Nat.zero, Nat.succ (Nat.succ Nat.zero),...

These would correspond to 0,1,2,... in our familiar notation. 

In general, the terms of an inductive type are all terms you 
can build from iterated application of the constructors. All 
sequences constructor applications yield distinct terms. 

-/

inductive Example where 
 | base 
 | X (eg : Example) 
 | Y (eg : Example) 

example : Example.X (Example.Y base) = Example.Y (Example.X base) := by 
  rfl 

-- Here is List
inductive List (α : Type) where 
  | nil
  | cons (a:α) (l:List α) 

variable (α : Type) 

#check List α 

#check List.nil 

#check List.cons 

/-
We can also define the integers using an inductive type. 
-/

inductive Int : Type where 
  | ofNat (n : Nat) 
  | negSucc (n : Nat) 

/-
Here OfNat n is the natural number n viewed as non-negative integer 
while NegSucc n is -n-1. 
-/

/- 
Option α represents possible value of α or failure. 
-/

inductive Option (α : Type) where 
  | some (a : α) 
  | none 

/- 
We can represent products also 
-/

inductive Prod (α β : Type) where 
  | mk (a : α) (b : β) 

/-
Or what are often call sum types 
-/

inductive Sum (α β : Type) where 
  | left (a : α) 
  | right (b : β) 

end Notes 

-- We step out of the name space and compare with the existing defs.

variable (α : Type) 

#print Nat 

#print List 

#check List.nil 

#check List.cons 

#print Int

/- 
Core inductive types have special syntax to make use more ergonomic.
In particular, Nat and List have familiar syntax. 
-/

#check 1 + 2 

#check [0,1,2]

#check 0::[1,2,3]

#check [0,1]++[2,3]

/- 
To specify a function from an inductive type, we need to specify a 
value for each constructor. 
-/

inductive CoinFlip where 
  | heads 
  | tails 
deriving Repr -- allows #eval to display the following

#eval CoinFlip.heads

-- This is the _equation compiler_ syntax for defining functions 
def CoinFlip.odds : CoinFlip → Float 
  | .heads => 0.5
  | .tails => 0.5

#eval CoinFlip.heads.odds 

-- Here is another example. What does it do? 

def Nat.minus : Nat → Nat → Nat 
  | 0, _ => 0 
  | n, 0 => n 
  | n+1, m+1 => Nat.minus n m 

#eval Nat.minus 10 5 
#eval Nat.minus 5 10 

/- 
Note that inductive types are heavily recursive. This is evident in the 
previous example where we have two base cases: n = 0 and m = 0. Then we 
treat the case of n+1 and m+1 using the definition at n and m. 
-/

def List.shuffle {α : Type} : List α → List α → List α 
  | [], l => l
  | l, [] => l
  | x::xs, y::ys => x::y::List.shuffle xs ys 

#eval [1,2,3].shuffle [4,5,6] 

/- 
We can also include parameters in the function definitions
-/ 

def exp (base : Nat) : Nat → Nat 
  | 0 => 1 
  | n+1 => (exp base n)*base 

def exp' : Nat → Nat → Nat 
  | _, 0 => 1 
  | base, n+1 => (exp' base n)*base 

#eval exp 2 10 
#eval exp' 2 10 

-- These are the same so we should prove it
theorem exp_eq (n m : Nat) : exp n m = exp' n m := sorry 
-- More on this next time. 
