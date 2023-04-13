import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Ring
-- import Mathlib.Data.Real.Basic

/- Universes -/

#check Prop
#check Nat
#check Float
#check String
#check Bool

#check Type 0
#check Type
#check Type 6

/- Declare universe variables -/
-- universe u₁ u₂ u₃
--
-- variable (α : Type u₁) (β : Type u₂) (f : α → β)
--
-- #check α → β

#check List Type

#check Sort 0
#check Sort 1
#check Sort 2

variable (γ : Type u → Type u)

#check ∀ (ty : Type u), γ ty

variable (p : Type u → Prop)

#check ∀ (ty : Type u), p ty

/- Proof irrelevance -/

example {q : Prop} (h₁ h₂ : q) : h₁ = h₂ := rfl

-- def root (n : Nat) (h : ∃ m, m*m = n) : Nat :=
--   match h with
--   | Exists.intro m _ => m

/- The axiom of choice -/

#check Nonempty
#check Classical.choice

inductive Weekday where
  | Sunday
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday

instance : Nonempty (Weekday) := ⟨ .Thursday ⟩

noncomputable example : Weekday := by
  apply Classical.choice
  infer_instance

#check Classical.choose
#check Classical.choose_spec
#check Classical.axiomOfChoice

/- Subtypes -/

#check Set

variable (s : Set Weekday)

#check s

#check Coe
example : Type := s

example : Type := { day : Weekday // day = .Monday }

example : Type := Subtype (fun (day : Weekday) => day = .Monday)

variable (α : Type) (n : ℕ)

#check Fin n

def Vector : Type := { xs : List α // xs.length = n}

variable {α} {n}

instance [Add α] : Add (Vector α n) where
  add v₁ v₂ := ⟨List.zipWith (·+·) v₁.val v₂.val,
    by simp [v₁.property,v₂.property]⟩

-- instance [Add α] : HAdd (Vector α n) (Vector α n) (Vector α n) where
--   hAdd v₁ v₂ := ⟨List.zipWith (·+·) v₁.val v₂.val,
--     by simp [v₁.property,v₂.property]⟩
--
-- #check HAdd

-- example (v₁ v₂ : Vector α n) : Vector α n := v₁ + v₂

def scalarMul [Mul α] (a : α) (v : Vector α n) :
    Vector α n := ⟨v.val.map (a * ·), by simp [v.property]⟩

instance [Mul α] : SMul α (Vector α n) where
  smul := scalarMul

-- variable (a : α) (v : Vector α n)

-- #check a • v

-- #check SMul

/- Quotient types -/

#check Setoid

instance mod2 : Setoid ℤ where
  r := fun n m => 2 ∣ (m - n)
  iseqv :=
    { refl := by
        intro n
        -- apply Exists.intro 0
        use 0
        ring
        -- simp [Int.sub_self]
      symm := by
        intro n m ⟨c,hc⟩
        use (-c)
        have : m - n + n= 2*c + n := congrArg (·+n) hc
        rw [Int.sub_add_cancel] at this
        rw [this]
        ring
      trans := by
        intro a b c ⟨u,hu⟩ ⟨v,hv⟩
        use (u+v)
        rw [Int.mul_add,←hu,←hv]
        ring }

/- 2 | 4 - (-2) -/
#check -2 ≈ 4

def Mod2 : Type := Quotient mod2

#check Mod2
#check Quotient
#check Quotient.mk

example : Mod2 := ⟦5⟧  --Quotient.mk mod2 5

#check Quotient.sound

#check Equiv

def cl : Fin 2 → Mod2 := fun n => ⟦n⟧ -- Quotient.mk mod2 (n.val:ℤ)

def rem : Mod2 → Fin 2 := by
  refine Quotient.lift (s := mod2) ?_ ?_
