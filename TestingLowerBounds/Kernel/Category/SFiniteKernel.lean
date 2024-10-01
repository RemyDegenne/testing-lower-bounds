/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TestingLowerBounds.Kernel.ParallelComp

/-!

# Bundled s-finite measures and kernels

-/

open MeasureTheory

open scoped ENNReal

namespace MeasureTheory.SFiniteMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

def _root_.MeasureTheory.SFiniteMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // SFinite μ }

@[coe]
def toMeasure : SFiniteMeasure Ω → Measure Ω := Subtype.val

instance instCoe : Coe (SFiniteMeasure Ω) (MeasureTheory.Measure Ω) where
  coe := toMeasure

instance isFiniteMeasure (μ : SFiniteMeasure Ω) : SFinite (μ : Measure Ω) := μ.prop

@[simp]
theorem val_eq_toMeasure (ν : SFiniteMeasure Ω) : ν.val = (ν : Measure Ω) :=
  rfl

theorem toMeasure_injective : Function.Injective ((↑) : SFiniteMeasure Ω → Measure Ω) :=
  Subtype.coe_injective

instance instFunLike : FunLike (SFiniteMeasure Ω) (Set Ω) ℝ≥0∞ where
  coe μ s := (μ : Measure Ω) s
  coe_injective' _ _ h := toMeasure_injective $ Measure.ext fun s _ ↦  congr_fun h s

lemma coeFn_def (μ : SFiniteMeasure Ω) : μ = fun s ↦ (μ : Measure Ω) s := rfl

lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := SFiniteMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ μ s := rfl

@[simp]
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := SFiniteMeasure Ω) ⟨μ, hμ⟩ s = μ s := rfl

theorem apply_mono (μ : SFiniteMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ :=
  (μ : Measure Ω).mono h

instance instZero : Zero (SFiniteMeasure Ω) where zero := ⟨0, inferInstance⟩

@[simp, norm_cast] lemma coeFn_zero : ⇑(0 : SFiniteMeasure Ω) = 0 := rfl

@[ext]
theorem eq_of_forall_toMeasure_apply_eq (μ ν : SFiniteMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply Subtype.ext
  ext s s_mble
  exact h s s_mble

theorem eq_of_forall_apply_eq (μ ν : SFiniteMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext s s_mble
  exact h s s_mble

instance instInhabited : Inhabited (SFiniteMeasure Ω) := ⟨0⟩

noncomputable
instance instAdd : Add (SFiniteMeasure Ω) where add μ ν := ⟨μ + ν, inferInstance⟩

variable {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

instance instSMul : SMul R (SFiniteMeasure Ω) where
  smul (c : R) μ := ⟨c • (μ : Measure Ω), sorry⟩

@[simp, norm_cast]
theorem toMeasure_zero : ((↑) : SFiniteMeasure Ω → Measure Ω) 0 = 0 := rfl

-- Porting note: with `simp` here the `coeFn` lemmas below fall prey to `simpNF`: the LHS simplifies
@[norm_cast]
theorem toMeasure_add (μ ν : SFiniteMeasure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω) := rfl

@[simp, norm_cast]
theorem toMeasure_smul (c : R) (μ : SFiniteMeasure Ω) : ↑(c • μ) = c • (μ : Measure Ω) := rfl

@[simp, norm_cast]
theorem coeFn_add (μ ν : SFiniteMeasure Ω) : ⇑(μ + ν) = ⇑μ + ⇑ν := by
  funext
  simp only [Pi.add_apply]
  norm_cast

@[simp, norm_cast]
theorem coeFn_smul (c : R) (μ : SFiniteMeasure Ω) : ⇑(c • μ) = c • ⇑μ := rfl

noncomputable
instance instAddCommMonoid : AddCommMonoid (SFiniteMeasure Ω) :=
  toMeasure_injective.addCommMonoid (↑) toMeasure_zero toMeasure_add fun _ _ => toMeasure_smul _ _

/-- Coercion is an `AddMonoidHom`. -/
@[simps]
def toMeasureAddMonoidHom : SFiniteMeasure Ω →+ Measure Ω where
  toFun := (↑)
  map_zero' := toMeasure_zero
  map_add' := toMeasure_add

noncomputable
instance {Ω : Type*} [MeasurableSpace Ω] : Module ℝ≥0∞ (SFiniteMeasure Ω) :=
  Function.Injective.module _ toMeasureAddMonoidHom toMeasure_injective toMeasure_smul

@[simp]
theorem smul_apply (c : R) (μ : SFiniteMeasure Ω) (s : Set Ω) :
    (c • μ) s = c • μ s := by
  rw [coeFn_smul, Pi.smul_apply]

instance : MeasurableSpace (SFiniteMeasure Ω) := Subtype.instMeasurableSpace

end MeasureTheory.SFiniteMeasure

instance {Ω : Type*} [MeasurableSpace Ω] : MeasurableSpace (FiniteMeasure Ω) :=
  Subtype.instMeasurableSpace

instance {Ω : Type*} [MeasurableSpace Ω] : MeasurableSpace (ProbabilityMeasure Ω) :=
  Subtype.instMeasurableSpace

namespace ProbabilityTheory

section SFiniteKernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

def SFiniteKernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  { κ : Kernel α β // IsSFiniteKernel κ }

namespace SFiniteKernel

@[coe]
def toKernel : SFiniteKernel α β → Kernel α β := Subtype.val

instance instCoe : Coe (SFiniteKernel α β) (Kernel α β) where
  coe := toKernel

instance isSFiniteKernel (κ : SFiniteKernel α β) : IsSFiniteKernel (κ : Kernel α β) := κ.prop

@[simp, norm_cast] lemma coe_mk (κ : Kernel α β) (hκ) : toKernel ⟨κ, hκ⟩ = κ := rfl

@[simp]
theorem val_eq_toKernel (κ : SFiniteKernel α β) : κ.val = (κ : Kernel α β) :=
  rfl

theorem toKernel_injective : Function.Injective ((↑) : SFiniteKernel α β → Kernel α β) :=
  Subtype.coe_injective

instance instFunLike : FunLike (SFiniteKernel α β) α (Measure β) where
  coe κ a := (κ : Kernel α β) a
  coe_injective' κ η h := toKernel_injective $ by simp only [DFunLike.coe_fn_eq] at h; exact h

lemma coeFn_def (κ : SFiniteKernel α β) : κ = fun a ↦ (κ : Kernel α β) a := rfl

lemma coeFn_mk (κ : Kernel α β) (hκ) :
    DFunLike.coe (F := SFiniteKernel α β) ⟨κ, hκ⟩ = fun a ↦ κ a := rfl

@[simp]
lemma mk_apply (κ : Kernel α β) (hκ) (a : α) :
    DFunLike.coe (F := SFiniteKernel α β) ⟨κ, hκ⟩ a = κ a := rfl

noncomputable
def id (α : Type*) [MeasurableSpace α] : SFiniteKernel α α := ⟨Kernel.id, inferInstance⟩

noncomputable
def comp (κ : SFiniteKernel α β) (η : SFiniteKernel β γ) : SFiniteKernel α γ :=
  ⟨η.toKernel ∘ₖ κ.toKernel, by have := κ.2; have := η.2; infer_instance⟩

@[simp]
lemma comp_id (κ : SFiniteKernel α β) : κ.comp (id β) = κ := by
  apply DFunLike.ext
  intro a
  ext s hs
  simp only [comp, id, mk_apply, Kernel.comp_apply]
  norm_cast
  rw [Measure.bind_apply hs (Kernel.measurable _)]
  simp only [Kernel.id_apply, Measure.dirac_apply' _ hs]
  rw [lintegral_indicator_one hs]
  rfl

@[simp]
lemma id_comp (κ : SFiniteKernel α β) : (id α).comp κ = κ := by
  apply DFunLike.ext
  intro a
  ext s hs
  simp only [comp, id, mk_apply, Kernel.comp_apply]
  norm_cast
  rw [Measure.bind_apply hs (Kernel.measurable _)]
  simp only [Kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact Kernel.measurable_coe _ hs

lemma comp_assoc (κ : SFiniteKernel α β) (η : SFiniteKernel β γ) (ξ : SFiniteKernel γ δ) :
    (κ.comp η).comp ξ = κ.comp (η.comp ξ) := by
  simp only [comp]
  norm_cast
  apply DFunLike.ext
  intro a
  simp only [mk_apply]
  rw [Kernel.comp_assoc]

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

end ProbabilityTheory
