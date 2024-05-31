/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Monoidal
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!

# Category of measurable spaces and s-finite kernels

-/

open CategoryTheory MeasureTheory

namespace ProbabilityTheory

universe u

def StochCat : Type (u + 1) := Bundled MeasurableSpace

namespace StochCat

instance : CoeSort StochCat (Type*) := Bundled.coeSort

instance (X : StochCat) : MeasurableSpace X := X.str

/-- Construct a bundled `MeasCat` from the underlying type and the typeclass. -/
def of (α : Type u) [ms : MeasurableSpace α] : StochCat := ⟨α, ms⟩

@[simp]
theorem coe_of (X : Type u) [MeasurableSpace X] : (of X : Type u) = X := rfl

noncomputable
instance : Category StochCat where
  Hom α β := {κ : kernel α β // IsSFiniteKernel κ}
  id α := ⟨kernel.id, inferInstance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, by have := κ.2; have := η.2; infer_instance⟩
  assoc κ η ξ := sorry -- kernel.comp_assoc

noncomputable
instance : LargeCategory StochCat := inferInstance

instance : ConcreteCategory StochCat where
  forget := sorry
  forget_faithful := sorry

noncomputable
instance : MonoidalCategoryStruct StochCat where
  tensorObj X Y := Bundled.of (X × Y)
  whiskerLeft X Y₁ Y₂ f := sorry
  whiskerRight f Y := sorry
  --tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) : (tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂) :=
  --  whiskerRight f X₂ ≫ whiskerLeft Y₁ g
  tensorUnit := sorry
  associator := sorry
  leftUnitor := sorry
  rightUnitor := sorry

instance : MonoidalCategory StochCat := sorry

/-
deriving instance LargeCategory for MeasCat

-- Porting note: `deriving instance ConcreteCategory for MeasCat` didn't work. Define it manually.
-- see https://github.com/leanprover-community/mathlib4/issues/5020
instance : ConcreteCategory MeasCat := by
  unfold MeasCat
  infer_instance

instance : Inhabited MeasCat :=
  ⟨MeasCat.of Empty⟩
-/

end StochCat

end ProbabilityTheory
