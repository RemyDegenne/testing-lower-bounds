/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.MeasurableIntegral
import TestingLowerBounds.Kernel.Category.Giry
import TestingLowerBounds.Kernel.Category.MeasCat
import TestingLowerBounds.Kernel.Category.CommutativeMonad

/-!

# Categories of measurable spaces and Kernels

-/

open CategoryTheory MonoidalCategory MeasureTheory ProbabilityTheory

universe u v

namespace ProbabilityTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma ProbabilityMeasure.measurable_measure_prod_mk_left {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × ProbabilityMeasure β ↦ p.2.toMeasure (Prod.mk p.1 ⁻¹' s) := by
  let κ : Kernel (α × ProbabilityMeasure β) β := ⟨Subtype.val ∘ Prod.snd,
    measurable_subtype_coe.comp measurable_snd⟩
  have : IsMarkovKernel κ := by
    refine ⟨fun p ↦ ?_⟩
    simp only [Kernel.coe_mk, Function.comp_apply, ProbabilityMeasure.val_eq_to_measure, κ]
    exact p.2.2
  let s' := {((a, _), b) : (α × ProbabilityMeasure β) × β | (a, b) ∈ s}
  have hs' : MeasurableSet s' := (measurable_fst.fst.prod_mk measurable_snd) hs
  exact Kernel.measurable_kernel_prod_mk_left (κ := κ) hs'

lemma ProbabilityMeasure.measurable_map_prod_mk :
    Measurable (fun (p : α × ProbabilityMeasure β) ↦ p.2.map (f := Prod.mk p.1)
      measurable_prod_mk_left.aemeasurable) := by
  refine ProbabilityMeasure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [ProbabilityMeasure.toMeasure_map, Measure.map_apply measurable_prod_mk_left hs]
  exact measurable_measure_prod_mk_left hs

end ProbabilityTheory

namespace MeasCat

attribute [local instance] ConcreteCategory.instFunLike

noncomputable
def leftStrength : ((𝟭 MeasCat).prod ProbGiry) ⋙ (tensor MeasCat)
    ⟶ (tensor MeasCat) ⋙ ProbGiry where
  app := fun P ↦ ⟨fun p ↦ p.2.map (f := Prod.mk p.1) measurable_prod_mk_left.aemeasurable,
    ProbabilityMeasure.measurable_map_prod_mk⟩
  naturality := fun (P₁, P₂) (Q₁, Q₂) f ↦ by
    simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, Functor.comp_map,
      Functor.prod_map, Functor.id_map, tensor_map]
    simp [MeasCat.ProbGiry, MeasCat.Prob] -- todo: add API
    ext x
    simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, comp_apply,
      MeasCat.tensor_apply]
    -- up to the weird types: rw [ProbabilityMeasure.map_map] twice should do it
    sorry

@[simp]
lemma leftStrength_apply {P : MeasCat × MeasCat} (p : ↑(P.1 ⊗ ProbGiry.obj P.2)) :
    leftStrength.app P p = p.2.map (f := Prod.mk p.1) measurable_prod_mk_left.aemeasurable := by
  rfl

@[simp]
lemma leftStrength_apply' {X Y : MeasCat} (p : ↑(X ⊗ ProbGiry.obj Y)) :
    leftStrength.app (X, Y) p = p.2.map (f := Prod.mk p.1) measurable_prod_mk_left.aemeasurable := by
  rfl

noncomputable
instance : LeftStrong ProbGiry where
  leftStr := leftStrength
  left_unit_comp X := rfl
  left_assoc X Y Z := by
    simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj]
    ext x
    simp only [comp_apply, whiskerLeft_apply]
    simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, leftStrength]
    sorry
  left_unit_comm X Y := sorry
  left_mul_comm X Y := sorry

instance : RightStrong ProbGiry where
  rightStr := sorry
  right_unit_comp X := sorry
  right_assoc X Y Z := sorry
  right_unit_comm X Y := sorry
  right_mul_comm X Y := sorry

noncomputable
instance : Strong ProbGiry where
  left_right X Y Z := sorry

noncomputable
instance : CommutativeMonad ProbGiry where
  comm X Y := sorry

noncomputable
instance : SymmetricMonad ProbGiry where
  braiding_left_right X Y := sorry
  braiding_right_left X Y := sorry

instance : Affine ProbGiry where
  affine := sorry

end MeasCat
