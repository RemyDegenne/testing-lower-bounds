/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.CategoryTheory.Monad.Kleisli
import TestingLowerBounds.Kernel.Category.CommutativeMonad
import TestingLowerBounds.Kernel.Category.MeasCat
import TestingLowerBounds.Kernel.Category.SFiniteKernel

/-!

# Categories of measurable spaces and Kernels

-/

open MeasureTheory CategoryTheory MonoidalCategory Limits

open scoped ENNReal

universe u v

namespace ProbabilityTheory

/- This is probably false: it probably needs s-finite measures, since
`measurable_measure_prod_mk_left` (the case where p.2 is constant) requires an s-finite measure.
Why though? Can we find a counter-example if we don't have the s-finite assumption? -/
lemma measurable_measure_prod_mk_left' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × Measure β ↦ p.2 (Prod.mk p.1 ⁻¹' s) := by
  sorry

lemma measurable_measure_prod_mk_left'' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × SFiniteMeasure β ↦ p.2 (Prod.mk p.1 ⁻¹' s) := by
  let κ : Kernel (α × SFiniteMeasure β) β := ⟨Subtype.val ∘ Prod.snd,
    measurable_subtype_coe.comp measurable_snd⟩
  have : IsSFiniteKernel κ := by
    sorry
  let s' := {((a, ν), b) : (α × SFiniteMeasure β) × β | (a, b) ∈ s}
  have hs' : MeasurableSet s' := (measurable_fst.fst.prod_mk measurable_snd) hs
  exact Kernel.measurable_kernel_prod_mk_left (κ := κ) hs'

lemma measurable_measure_prod_mk_left''' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × ProbabilityMeasure β ↦ (p.2 : Measure β) (Prod.mk p.1 ⁻¹' s) := by
  let κ : Kernel (α × ProbabilityMeasure β) β := ⟨Subtype.val ∘ Prod.snd,
    measurable_subtype_coe.comp measurable_snd⟩
  have : IsMarkovKernel κ := by
    constructor
    intro p
    change IsProbabilityMeasure p.2
    infer_instance
  let s' := {((a, _), b) : (α × ProbabilityMeasure β) × β | (a, b) ∈ s}
  have hs' : MeasurableSet s' := (measurable_fst.fst.prod_mk measurable_snd) hs
  exact Kernel.measurable_kernel_prod_mk_left (κ := κ) hs'

-- This is probably false, it probably needs s-finite measures.
lemma Measure.measurable_map_prod_mk {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (p : α × Measure β) ↦ p.2.map (Prod.mk p.1)) := by
  refine' Measure.measurable_of_measurable_coe _ fun s hs => _
  simp_rw [Measure.map_apply measurable_prod_mk_left hs]
  exact measurable_measure_prod_mk_left' hs

-- this is probably false, because `Measure.measurable_map_prod_mk` probably needs s-finite measures.
noncomputable
instance : LeftStrong MeasCat.Giry where
  leftStr := {
    app := fun P ↦ ⟨fun p ↦ p.2.map (Prod.mk p.1), Measure.measurable_map_prod_mk⟩
    naturality := fun (P₁, P₂) (Q₁, Q₂) f ↦ by
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, Functor.comp_map,
        Functor.prod_map, Functor.id_map, tensor_map]
      simp [MeasCat.Giry, MeasCat.Measure] -- todo: add API
      ext x
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, comp_apply,
        MeasCat.tensor_apply]
      -- up to the weird types: rw [Measure.map_map] twice should do it
      sorry }

end ProbabilityTheory

-- todo: not really Stoch because it contains all Kernels, not only Markov Kernels
def Stoch := Kleisli MeasCat.Giry

/- TODO: prove that the Kleisli category of a commutative monad on a cartesian symmetric monoidal
category is a symmetric monoidal category (and a copy-discard category).
If furthermore the monad is affine, the Kleisli category is a Markov category. -/

namespace ProbabilityTheory

def SFiniteCat : Type (u + 1) := Bundled MeasurableSpace

namespace SFiniteCat

instance : CoeSort SFiniteCat (Type*) := Bundled.coeSort

instance (X : SFiniteCat) : MeasurableSpace X := X.str

/-- Construct a bundled `SFiniteCat` from the underlying type and the typeclass. -/
def of (α : Type u) [ms : MeasurableSpace α] : SFiniteCat := ⟨α, ms⟩

@[simp]
theorem coe_of (X : Type u) [MeasurableSpace X] : (of X : Type u) = X := rfl

noncomputable
instance : Category SFiniteCat where
  Hom X Y := SFiniteKernel X Y
  id X := SFiniteKernel.id X
  comp := SFiniteKernel.comp
  assoc := SFiniteKernel.comp_assoc

noncomputable
instance : LargeCategory SFiniteCat where

--instance : ConcreteCategory SFiniteCat := by
--  unfold SFiniteCat
--  infer_instance

instance : Inhabited SFiniteCat := ⟨SFiniteCat.of Empty⟩

noncomputable
instance : MonoidalCategoryStruct SFiniteCat where
  tensorObj X Y := SFiniteCat.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := SFiniteKernel.parallelComp (SFiniteKernel.id X) κ
  whiskerRight κ Y := SFiniteKernel.parallelComp κ (SFiniteKernel.id Y)
  tensorHom κ η := SFiniteKernel.parallelComp κ η
  tensorUnit := SFiniteCat.of Unit
  associator X Y Z := sorry
  leftUnitor X := sorry
  rightUnitor X := sorry

noncomputable
instance : MonoidalCategory SFiniteCat where
  tensorHom_def κ η := (SFiniteKernel.parallelComp_left_comp_right κ η).symm
  tensor_id X Y := SFiniteKernel.parallelComp_id
  tensor_comp κ η κ' η' := SFiniteKernel.parallelComp_comp κ η κ' η'
  whiskerLeft_id X Y := SFiniteKernel.parallelComp_id
  id_whiskerRight X Y := SFiniteKernel.parallelComp_id
  associator_naturality κ η ξ := sorry
  leftUnitor_naturality κ := sorry
  rightUnitor_naturality κ := sorry
  pentagon W X Y Z := sorry
  triangle X Y := sorry

noncomputable
def swapIso (X Y : SFiniteCat) :
    (MonoidalCategory.tensorObj X Y) ≅ (MonoidalCategory.tensorObj Y X) where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

noncomputable
instance : BraidedCategory SFiniteCat where
  braiding X Y := sorry
  braiding_naturality_right X Y Z κ := sorry
  braiding_naturality_left κ Z := sorry
  hexagon_forward X Y Z := sorry
  hexagon_reverse X Y Z := sorry

noncomputable
instance : SymmetricCategory SFiniteCat where
  symmetry X Y := sorry

end SFiniteCat

end ProbabilityTheory
