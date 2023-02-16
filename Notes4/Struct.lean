import Mathlib.Data.Real.Basic

/-
We have structures already. For example, 
-/ 

namespace Notes 

structure PartialOrder {α : Type} (R : α → α → Prop) where 
  refl : ∀ {a b}, R a b → R b a → a = b
  antisym : ∀ {a b}, R a b → R b a → a = b
  trans : ∀ {a b c}, R a b → R b c → R a c

/-
Structures, also often called records, are useful for 
combining different types into a single type. Another example
-/

structure Point3D (α : Type) where 
  xCoord : α 
  yCoord : α 
  zCoord : α 

/-
You tell Lean you are making a new type which is a structure by 
using the `structure` keyword. 

Next comes the identifier `PartialOrder` and `Point3D` in the examples. 

After the identifier comes the _parameters_. These are things on which 
the structure depends. So `PartialOrder` needs a relation `R` which 
in turn needs the type `α` of values it is relating. `Point3D` 
depends on a type `α` which is the type of the coordinates. 

After the parameters, you can the `where` keyword (or a `:=`) to 
tell Lean that the _fields_ of the structure are coming. 

In `PartialOrder`, we have three fields and their types. Same 
with `Point3d`. 
-/

/- Suppose we want to tell Lean about the point (1,1,1) in `ℝ³`. 
One way looks as follows
-/

def myPoint : Point3D ℝ where 
  xCoord := 1 
  yCoord := 1 
  zCoord := 1

/- Printing `myPoint` shows the alternate syntax for declaring 
instances of structures -/
#print myPoint

/- One more way to get an instance is to use the built-in 
constructor. The default name `mk`. -/

#check Point3D.mk 

example : Point3D ℝ := Point3D.mk 1 1 1 

/- We can change the name of the default constructor if 
we wish. This is why we can write `And.intro` and `Exists.intro` 
in place of `And.mk` and `Exists.mk` -/

structure Point3D' (α : Type) where 
build:: 
  xCoord : α 
  yCoord : α 
  zCoord : α 

example : Point3D' ℝ := .build 1 1 1

-- example : Point3D' ℝ := .mk 1 1 1

/- One more way to build a structure is using the _anonymous 
constructor_ notation -/

example : Point3D ℝ := ⟨1,1,1⟩ 

-- This doesn't work because `ℕ` is a not a structure
-- example : ℕ := ⟨0⟩

/- Here the brackets are typed \< and \>. Lean knows from the 
context that you need to put a term of type `Point3D ℝ` so 
understands what structure you are building from just the `1`'s. 
-/

/- We can extend structures -/ 

structure Point4D (α : Type) extends Point3D α where 
  time : α 

example {α : Type} (p : Point3D α) (t : α) : Point4D α := ⟨p,t⟩

example {α : Type} (p : Point4D α) : α := p.toPoint3D.xCoord

/- There is syntax for updating fields -/

example {α : Type} (p : Point3D α) (x : α) : Point3D α := {p with xCoord := x}

/- Often is it useful to provide default values -/

structure UserData where 
  name : String  := "Andres Galarraga" 
  uid : ℕ  := 0 
  email : String 

def user : UserData := {email := "ag@email.sc.edu"}

#print user 

/- Lean allows us the flexibility for fields in a structure 
to depend on other fields -/ 

structure LawlessGroup where 
  Carrier : Type
  unit : Carrier 
  mul : Carrier → Carrier → Carrier 
  inv : Carrier → Carrier

#print LawlessGroup.unit 

-- `ℝ` is actually a group under addition 
example : LawlessGroup where 
  Carrier := ℝ 
  unit := 0 
  mul := fun x y => x + y 
  inv := fun x => -x 

-- This is not a real group which is why called it lawless. 
example : LawlessGroup := ⟨ℕ, 37, fun _ _ => 0, (·+1) ⟩

/- Under the hood, a `structure` is essentially a inductive type 
with a single constructor which is why the following works. -/

namespace Inductive 

inductive Inhabited (α : Type) where 
 | default (a : α) : Inhabited α  

example : Inhabited ℝ := ⟨-1⟩ 

/- So `LawlessGroup` similar to -/

inductive LawlessGroup 
  | mk : ∀ (Carrier :Type), Carrier → (Carrier → Carrier → Carrier) → (Carrier → Carrier) → LawlessGroup

def LawlessGroup.Carrier : LawlessGroup → Type 
  | .mk Carrier _ _ _ => Carrier

def LawlessGroup.unit : (self : LawlessGroup) → self.Carrier  
  | .mk _ unit _ _ => unit 

def LawlessGroup.mul : (self : LawlessGroup) → self.Carrier → self.Carrier → self.Carrier 
  | .mk _ _ mul _ => mul 

def LawlessGroup.inv : (self : LawlessGroup) → self.Carrier → self.Carrier
  | .mk _ _ _ inv => inv 

def ok : LawlessGroup := .mk ℝ 0 (·+·) (-·) 

#check ok.Carrier 

#check ok.unit 

#check ok.mul 

#check ok.inv

end Inductive 

/- In general, structures can be more _bundled_ where parameters 
are pushed into the fields or more _unbundled_ where fields are 
pushed into the parameters -/ 

structure LawlessGroup' (Carrier : Type) where 
  unit : Carrier 
  mul : Carrier → Carrier → Carrier 
  inv : Carrier → Carrier
