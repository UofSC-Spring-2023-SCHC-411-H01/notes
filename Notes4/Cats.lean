import Mathlib.Data.Nat.Basic

namespace Notes

class Quiver (α : Type _) where 
  Hom : α → α → Type _

instance : Quiver ℕ where 
  Hom := fun n m => if n ≤ m then Unit else Empty

instance (α : Type) : Quiver α where 
  Hom := fun _ _ => α → α  
--
instance : Quiver Type where 
  Hom := fun Ty₁ Ty₂ => Ty₁ → Ty₂ 

/- Given f : Hom a₁ a₂ and g : Hom a₂ a₃ we want 
express that we can construct g ≫ f : Hom a₁ a₃ -/

class LawlessCategory (α : Type _) extends Quiver α where 
  comp : ∀ {a₁ a₂ a₃ : α}, 
    Hom a₁ a₂ → Hom a₂ a₃ → Hom a₁ a₃ 
  id : ∀ (a : α), Hom a a 

instance : LawlessCategory Type where 
  comp := fun f g => g ∘ f 
  id := fun _ b  => b 

class Category (α : Type _) extends LawlessCategory α where 
  assoc : ∀ {a₁ a₂ a₃ a₄ : α} (f₁ : Hom a₁ a₂) (f₂ : Hom a₂ a₃) (f₃ : Hom a₃ a₄), comp f₁ (comp f₂ f₃) = comp (comp f₁ f₂) f₃ 
  comp_id : ∀ {a₁ a₂ : α} (f : Hom a₁ a₂), comp f (id a₂) = f 
  id_comp : ∀ {a₁ a₂ : α} (f : Hom a₁ a₂), comp (id a₁) f = f 

instance : Category Type where 
  comp := fun f g => g ∘ f 
  id := fun _ b  => b 
  assoc f g h := by simp; funext; simp 
  comp_id f := by simp; funext; simp 
  id_comp f := by simp; funext; simp 
  
