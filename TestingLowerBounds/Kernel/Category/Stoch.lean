/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Category.GiryStrong
import TestingLowerBounds.Kernel.Category.KleisliMarkov
import TestingLowerBounds.Kernel.Category.MeasCatMarkov

/-!

# Category of measurable spaces and Markov kernels

-/

open scoped ENNReal

open CategoryTheory MeasureTheory MonoidalCategory MeasCat

universe u v

namespace ProbabilityTheory

/-- Category of measurable spaces and Markov kernels. -/
def Stoch := Kleisli ProbGiry

namespace Stoch

variable {X Y : Stoch}

noncomputable
instance : Category Stoch := inferInstanceAs (Category <| Kleisli ProbGiry)

instance : CoeSort Stoch (Type _) where
  coe X := show MeasCat from X

example (X : Stoch) : MeasurableSpace X := inferInstance

example (f : X ⟶ Y) : ProbabilityTheory.Kernel X Y where
  toFun := fun x ↦ (f.val x).toMeasure
  measurable' := measurable_subtype_coe.comp f.property

example (κ : Kernel X Y) [IsMarkovKernel κ] : X ⟶ Y :=
  ⟨fun x ↦ ⟨κ x, inferInstance⟩, κ.measurable.subtype_mk⟩

noncomputable
instance : MonoidalCategory Stoch := inferInstanceAs (MonoidalCategory <| Kleisli ProbGiry)

noncomputable
instance : MarkovCategory Stoch := inferInstanceAs (MarkovCategory <| Kleisli ProbGiry)

end Stoch

end ProbabilityTheory
