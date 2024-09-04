/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import Mathlib.Probability.Kernel.Basic

/-!

# Basic deterministic kernels

-/

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

section KernelId

/-- The identity kernel. -/
protected noncomputable
def id : Kernel α α := Kernel.deterministic id measurable_id

instance : IsMarkovKernel (Kernel.id : Kernel α α) := by rw [Kernel.id]; infer_instance

lemma id_apply (a : α) : Kernel.id a = Measure.dirac a := by
  rw [Kernel.id, deterministic_apply, id_def]

end KernelId

section Copy

/-- The deterministic kernel that maps `x : α` to the Dirac measure at `(x, x) : α × α`. -/
noncomputable
def copy (α : Type*) [MeasurableSpace α] : Kernel α (α × α) :=
  Kernel.deterministic (fun x ↦ (x, x)) (measurable_id.prod measurable_id)

instance : IsMarkovKernel (copy α) := by rw [copy]; infer_instance

lemma copy_apply (a : α) : copy α a = Measure.dirac (a, a) := by simp [copy, deterministic_apply]

end Copy

section Discard

/-- The Markov kernel to the `Unit` type. -/
noncomputable
def discard (α : Type*) [MeasurableSpace α] : Kernel α Unit :=
  Kernel.deterministic (fun _ ↦ ()) measurable_const

instance : IsMarkovKernel (discard α) := by rw [discard]; infer_instance

@[simp]
lemma discard_apply (a : α) : discard α a = Measure.dirac () := deterministic_apply _ _

@[simp]
lemma _root_.MeasureTheory.Measure.comp_discard (μ : Measure α) :
    μ.bind (discard α) = μ .univ • (Measure.dirac ()) := by
  ext s hs; simp [Measure.bind_apply hs (Kernel.measurable _), mul_comm]

end Discard

section Swap

/-- The deterministic kernel that maps `(x, y)` to the Dirac measure at `(y, x)`. -/
noncomputable
def swap (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Kernel (α × β) (β × α) :=
  Kernel.deterministic Prod.swap measurable_swap

instance : IsMarkovKernel (swap α β) := by rw [swap]; infer_instance

lemma swap_apply (ab : α × β) : swap α β ab = Measure.dirac ab.swap := by
  rw [swap, deterministic_apply]

lemma swap_apply' (ab : α × β) {s : Set (β × α)} (hs : MeasurableSet s) :
    swap α β ab s = s.indicator 1 ab.swap := by
  rw [swap_apply, Measure.dirac_apply' _ hs]

end Swap

end ProbabilityTheory.Kernel
