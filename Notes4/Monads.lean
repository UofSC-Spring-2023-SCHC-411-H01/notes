import Mathlib

namespace Notes

def myNat : ℕ :=
  let n := 37
  let n := n+1
  n

#print Option

noncomputable def Real.dvd? (x y : ℝ) : Option ℝ :=
  if y = 0 then none else some (x/y)
