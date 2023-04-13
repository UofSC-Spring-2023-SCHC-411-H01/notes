-- import Mathlib

namespace Notes

def myNat : ℕ :=
  let n := 37
  let n := n+1
  n

#print Option

noncomputable def Real.dvd? (x y : ℝ) : Option ℝ :=
  if y = 0 then none else some (x/y)

def Rat.dvd? (p q : ℚ) : Option ℚ :=
  if q = 0 then none else some (p/q)

infix:90 " /? " => Rat.dvd?

#check 10 /? 11

/-
p*(q /? r) = (p*q) /? r
-/

def hMul (p : ℚ) (q : Option ℚ) : Option ℚ := do
  let q₀ ← q
  p*q₀
  -- match q with
  -- | none => none
  -- | some q' => some (p*q')

instance : HMul ℚ (Option ℚ) (Option ℚ) := ⟨hMul⟩

theorem mul_some (p q : ℚ) : p*some q = some (p*q) := rfl

example (p q r : ℚ) : p * (q /? r) = (p*q) /? r := by
  dsimp [Rat.dvd?]
  by_cases r = 0
  · simp only [if_pos h]; rfl
  · simp only [if_neg h]; rw [mul_some, mul_div]

def mul (p q : Option ℚ) : Option ℚ := do
  let p' ← p
  let q' ← q
  p'*q'

#print Monad

#print Option.some
#print Option.bind

/-
So hMul p q = Option.bind (fun q' => some (p*q'))

mul p q = Option.bind (hMul · q)
-/

def mul' (p q : Option ℚ) : Option ℚ := do
  let p' ← p
  do
    let q' ← q
  p'*q'
#check Option.bind
/- Generally, we expect some rules
- pure x >>= f = f
- ((x:m α) >>= pure : m α → m α) = id (m α → m α)
- (x >>= f) >>= g = x >>= ((· >>= g) ∘ f)
(· >>= g) ∘ (· >>= f) = (· >>= ((· >>=) ∘ f))
(f : α → m β) (g : β → m γ)
(· >>= f) : m α → m β
(· >>= g) : m β → m γ

(· >>= g) ∘ f : α → m γ
-/

#check LawfulMonad

#synth LawfulMonad Option

/-
Show that (a : Type) → ℝᵃ is a lawful monad
-/
#synth Monad List
instance : Monad List where
  pure := fun a => [a]
  bind := fun l f => (l.map f).join

/-
α = ℕ, f n = [0,1,2,3,...,n-1]

l = [4,5,6] ↦ [[0,1,2,3],[0,1,2,3,4],[0,1,2,3,4,5]] ↦ [0,1,2,3,0,1,2,3,4,0,1,2,3,4,5]
-/

#check IO.FS.readFile
#check IO.FS.writeFile

open IO
#check IO
def greeting : IO Unit := do
  let stdin ← getStdin
  let stdout ← getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"Hello, {name}!"

def sum (n : Nat) : IO Unit := do
  let rec f (n : Nat) :=
    match n with
    | 0 => 0
    | n+1 => n+1 + f n
  println s!"{f n}"

#eval sum 5

def sum_imp (n : Nat) : IO Unit := do
  let mut i := 0
  for j in [0:n+1] do
    i := i+j
  println s!"{i}"

#eval sum_imp 3

def sum_imp' (n : Nat) : Nat := Id.run do
  let mut i := 0
  let mut j := 0
  while j ≤ n do
    i := i + j
    j := j + 1
  return i

#eval sum_imp' 3

/- Compute the sum of 1^2+2^2+...+162^2 -/
