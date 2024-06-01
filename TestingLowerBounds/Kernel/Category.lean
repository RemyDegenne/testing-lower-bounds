/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom

/-!

# Categories of measurable spaces and kernels

-/

open MeasureTheory CategoryTheory

open scoped ENNReal

namespace ProbabilityTheory

section SFiniteKernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

def SFiniteKernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  { κ : kernel α β // IsSFiniteKernel κ }

namespace SFiniteKernel

@[coe]
def toKernel : SFiniteKernel α β → kernel α β := Subtype.val

instance instCoe : Coe (SFiniteKernel α β) (kernel α β) where
  coe := toKernel

instance isSFiniteKernel (κ : SFiniteKernel α β) : IsSFiniteKernel (κ : kernel α β) := κ.prop

@[simp, norm_cast] lemma coe_mk (κ : kernel α β) (hκ) : toKernel ⟨κ, hκ⟩ = κ := rfl

@[simp]
theorem val_eq_toKernel (κ : SFiniteKernel α β) : κ.val = (κ : kernel α β) :=
  rfl

theorem toKernel_injective : Function.Injective ((↑) : SFiniteKernel α β → kernel α β) :=
  Subtype.coe_injective

instance instFunLike : FunLike (SFiniteKernel α β) α (Measure β) where
  coe κ a := (κ : kernel α β) a
  coe_injective' κ η h := toKernel_injective $ by simp only [DFunLike.coe_fn_eq] at h; exact h

lemma coeFn_def (κ : SFiniteKernel α β) : κ = fun a ↦ (κ : kernel α β) a := rfl

lemma coeFn_mk (κ : kernel α β) (hκ) :
    DFunLike.coe (F := SFiniteKernel α β) ⟨κ, hκ⟩ = fun a ↦ κ a := rfl

@[simp]
lemma mk_apply (κ : kernel α β) (hκ) (a : α) :
    DFunLike.coe (F := SFiniteKernel α β) ⟨κ, hκ⟩ a = κ a := rfl

noncomputable
def id (α : Type*) [MeasurableSpace α] : SFiniteKernel α α := ⟨kernel.id, inferInstance⟩

noncomputable
def comp (κ : SFiniteKernel α β) (η : SFiniteKernel β γ) : SFiniteKernel α γ :=
  ⟨η.toKernel ∘ₖ κ.toKernel, by have := κ.2; have := η.2; infer_instance⟩

@[simp]
lemma comp_id (κ : SFiniteKernel α β) : κ.comp (id β) = κ := by
  apply DFunLike.ext
  intro a
  ext s hs
  simp only [comp, id, mk_apply, kernel.comp_apply]
  norm_cast
  rw [Measure.bind_apply hs (kernel.measurable _)]
  simp only [kernel.id_apply, Measure.dirac_apply' _ hs]
  rw [lintegral_indicator_one hs]
  rfl

@[simp]
lemma id_comp (κ : SFiniteKernel α β) : (id α).comp κ = κ := by
  apply DFunLike.ext
  intro a
  ext s hs
  simp only [comp, id, mk_apply, kernel.comp_apply]
  norm_cast
  rw [Measure.bind_apply hs (kernel.measurable _)]
  simp only [kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact kernel.measurable_coe _ hs

lemma comp_assoc (κ : SFiniteKernel α β) (η : SFiniteKernel β γ) (ξ : SFiniteKernel γ δ) :
    (κ.comp η).comp ξ = κ.comp (η.comp ξ) := by
  simp only [comp]
  norm_cast
  apply DFunLike.ext
  intro a
  simp only [mk_apply]
  rw [kernel.comp_assoc]

noncomputable
def parallelComp (κ : SFiniteKernel α β) (η : SFiniteKernel γ δ) : SFiniteKernel (α × γ) (β × δ) :=
  ⟨κ ∥ₖ η, inferInstance⟩

@[simp]
lemma parallelComp_id : parallelComp (id α) (id β) = id (α × β) := by
  sorry

@[simp]
lemma parallelComp_left_comp_right (κ : SFiniteKernel α β) (η : SFiniteKernel γ δ) :
    (parallelComp κ (id γ)).comp (parallelComp (id β) η) = parallelComp κ η := by
  sorry

lemma parallelComp_comp {β' δ' : Type*} {_ : MeasurableSpace β'} {_ : MeasurableSpace δ'}
    (κ : SFiniteKernel α β) (η : SFiniteKernel γ δ)
    (κ' : SFiniteKernel β β') (η' : SFiniteKernel δ δ') :
    parallelComp (κ.comp κ') (η.comp η') = (parallelComp κ η).comp (parallelComp κ' η') := by
  sorry

end SFiniteKernel

end SFiniteKernel

universe u

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
  tensorObj X Y := Bundled.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := SFiniteKernel.parallelComp (SFiniteKernel.id X) κ
  whiskerRight κ Y := SFiniteKernel.parallelComp κ (SFiniteKernel.id Y)
  tensorHom κ η := SFiniteKernel.parallelComp κ η
  tensorUnit := Bundled.of Unit
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
instance : BraidedCategory SFiniteCat where
  braiding X Y := sorry
  braiding_naturality_right := sorry
  braiding_naturality_left := sorry
  hexagon_forward := sorry
  hexagon_reverse := sorry

noncomputable
instance : SymmetricCategory SFiniteCat where
  symmetry := sorry

end SFiniteCat

end ProbabilityTheory
