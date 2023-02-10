import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Cases
import Notes4.IndTypes
/- 
Induction with Inductive Types

Let's see a bit how how induction is called inductive types. 
For each inductive type, recursors are automatically instantiated. 
-/

#check Nat.rec
#check List.rec

example (a b c: ℕ) : exp (a*b) c = (exp a c) * exp b c := by 
  apply @Nat.rec (fun c => exp (a*b) c = ((exp a c) * exp b c))
  · simp [exp]
  · intro n ih 
    simp [exp]
    rw [ih]
    ac_rfl

/-

Using the recusors directly is not as ergnomic as some built in tactics 
of which there are few.

First, we have already seen that `match` can be used to argue via 
induction. 

Let's prove that our exponentiation function on ℕ is multiplicative in 
the base. 
-/

theorem mul_of_mul_base_exp (a b c : ℕ) : exp (a*b) c = (exp a c) * exp b c := by 
  match c with 
  | 0 => simp only [exp] 
  | z+1 => 
    simp only [exp,Nat.add]
    rw [mul_of_mul_base_exp a b z]
    ac_rfl

/-

In `mul_of_mul_base_exp`, we used induction at the step `rw [mul_of_mul_base_exp a b c]` 
since this presumes a proof of `mul_of_mul_base_exp a b c`.

Consider the following version using an anonymous `example`. 

example (a b c: ℕ) : exp (a*b) c = (exp a c) * exp b c := by 
  match c with 
  | 0 => simp only [exp] 
  | c+1 => 
    simp only [exp,Nat.add] 
    -- how do we call the inductive step without a name?
    sorry 

In this case, we can use `induction` or `induction'`. 

-/

variable {α : Type} 

open List

def iterateAppend : ℕ → List α → List α
  | 0, _ => [] 
  | n+1, l => l ++ iterateAppend n l

-- Using `induction` 
example (n : ℕ) (l : List α) : n*(l.length) = (iterateAppend n l).length := by 
  induction n with 
  | zero => 
    simp only [iterateAppend,length]
    rw [Nat.zero_mul]
  | succ n' inductionHyp => 
    simp [iterateAppend,length]
    rw [Nat.succ_mul]
    rw [inductionHyp]
    ac_rfl 

-- Using `induction'`
example (n : ℕ) (l : List α) : n*(l.length) = (iterateAppend n l).length := by 
  induction' n with m indhyp 
  · simp only [iterateAppend,length]
    rw [Nat.zero_mul] 
  · simp [iterateAppend,length]
    rw [Nat.succ_mul]
    rw [indhyp]
    ac_rfl 

#check Nat.mul

open Nat

def times : ℕ → ℕ → ℕ  
  | _, 0 => 0 
  | a , b+1 => times a b + a 

example (n m : ℕ) : times n m = times m n := by 
  induction m with 
  | zero => 
    induction n with 
      | zero => rfl 
      | succ n' ih => 
        simp [times] at *
        exact ih
  | succ m' ih => 
    induction n with 
      | zero => 
        simp [times] at *
        exact ih 
      | succ n' ih' => 
        simp [times] at *
        rw [ih]
        sorry 
@[simp]
theorem zero_times { n: ℕ } : times 0 n = 0 := by
  match n with 
  | 0 => simp 
  | n'+1 => 
    simp [times]
    exact zero_times 

@[simp]
theorem succ_times { n m : ℕ } : times (n+1) m = times n m + m := by 
  match m with 
  | 0 =>
    simp [times]
  | m'+1 => 
    simp [times]
    rw [@succ_times n m']
    ac_rfl

theorem times_comm (n m : ℕ) : times n m = times m n := by 
  match n,m with 
  | n, 0 => 
    simp [times]
    -- rw [zero_times]  
  | n, m'+1 => 
    simp [times]
    -- rw [succ_times]
    rw [times_comm n m']

example (a n m : ℕ) : times a (m + n) = times a m + times a n := by 
  induction a with
  | zero => simp
  | succ b ih => 
    simp only [succ_times]
    rw [ih]
    ac_rfl

