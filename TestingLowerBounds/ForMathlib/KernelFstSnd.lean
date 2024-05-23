import Mathlib.Probability.Kernel.MeasureCompProd

open MeasureTheory

open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

namespace kernel

variable {α β γ ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

section FstSnd

variable {δ : Type*} {mδ : MeasurableSpace δ}

--TODO: PR this to mathlib, a suitable place may be just under
-- `ProbabilityTheory.kernel.snd_swapRight`

--I try to reproduce the code that is already there for kernel.fst and kernel.snd, but in this case
--the fst and snd are referred to the domain of the kernel, not the codomain
--for now I will use the names fst' and snd', maybe there are better ones

/-- Define a `kernel α γ` from a `kernel (α × β) γ` by taking the comap of `fun a ↦ (a, b)` for
a given `b : β`. -/
noncomputable def fst' (κ : kernel (α × β) γ) (b : β) : kernel α γ :=
  comap κ (fun a ↦ (a, b)) (measurable_id.prod_mk measurable_const)

@[simp]
theorem fst'_apply (κ : kernel (α × β) γ) (b : β) (a : α) : fst' κ b a = κ (a, b) := rfl

@[simp]
lemma fst'_zero (b : β) : fst' (0 : kernel (α × β) γ) b = 0 := by simp [fst']

instance (κ : kernel (α × β) γ) (b : β) [IsMarkovKernel κ] : IsMarkovKernel (fst' κ b) := by
  rw [kernel.fst']; infer_instance

instance (κ : kernel (α × β) γ) (b : β) [IsFiniteKernel κ] : IsFiniteKernel (fst' κ b) := by
  rw [kernel.fst']; infer_instance

instance (κ : kernel (α × β) γ) (b : β) [IsSFiniteKernel κ] : IsSFiniteKernel (fst' κ b) := by
  rw [kernel.fst']; infer_instance

instance (κ : kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((fst' κ b) a) := by
  rw [kernel.fst'_apply]; infer_instance

instance (priority := 100) {κ : kernel (α × β) γ} [∀ b, IsMarkovKernel (fst' κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← fst'_apply, measure_univ]

--I'm not sure this lemma is actually useful
lemma comap_fst' (κ : kernel (α × β) γ) (b : β) {f : δ → α} (hf : Measurable f) :
    comap (fst' κ b) f hf = comap κ (fun d ↦ (f d, b)) (hf.prod_mk measurable_const) := by
  ext d s
  rw [comap_apply, fst'_apply, comap_apply]

@[simp]
lemma fst'_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : kernel β γ) (a : α) {b : β} :
    fst' (prodMkLeft α κ) b a = κ b := rfl

@[simp]
lemma fst'_prodMkRight (β : Type*) [MeasurableSpace β] (κ : kernel α γ) (b : β) :
    fst' (prodMkRight β κ) b = κ := rfl

/-- Define a `kernel β γ` from a `kernel (α × β) γ` by taking the comap of `fun b ↦ (a, b)` for
a given `a : α`. -/
noncomputable def snd' (κ : kernel (α × β) γ) (a : α) : kernel β γ :=
  comap κ (fun b ↦ (a, b)) (measurable_const.prod_mk measurable_id)

@[simp]
theorem snd'_apply (κ : kernel (α × β) γ) (b : β) (a : α) : snd' κ a b = κ (a, b) := rfl

@[simp]
lemma snd'_zero (a : α) : snd' (0 : kernel (α × β) γ) a = 0 := by simp [snd']

instance (κ : kernel (α × β) γ) (a : α) [IsMarkovKernel κ] : IsMarkovKernel (snd' κ a) := by
  rw [kernel.snd']; infer_instance

instance (κ : kernel (α × β) γ) (a : α) [IsFiniteKernel κ] : IsFiniteKernel (snd' κ a) := by
  rw [kernel.snd']; infer_instance

instance (κ : kernel (α × β) γ) (a : α) [IsSFiniteKernel κ] : IsSFiniteKernel (snd' κ a) := by
  rw [kernel.snd']; infer_instance

instance (κ : kernel (α × β) γ) (a : α) (b : β) [NeZero (κ (a, b))] : NeZero ((snd' κ a) b) := by
  rw [kernel.snd'_apply]; infer_instance

instance (priority := 100) {κ : kernel (α × β) γ} [∀ b, IsMarkovKernel (snd' κ b)] :
    IsMarkovKernel κ := by
  refine ⟨fun _ ↦ ⟨?_⟩⟩
  rw [← snd'_apply, measure_univ]

--I'm not sure this lemma is actually useful
lemma comap_snd' (κ : kernel (α × β) γ) (a : α) {f : δ → β} (hf : Measurable f) :
    comap (snd' κ a) f hf = comap κ (fun d ↦ (a, f d)) (measurable_const.prod_mk hf) := by
  ext d s
  rw [comap_apply, snd'_apply, comap_apply]

@[simp]
lemma snd'_prodMkLeft (α : Type*) [MeasurableSpace α] (κ : kernel β γ) (a : α) :
    snd' (prodMkLeft α κ) a = κ := rfl

@[simp]
lemma snd'_prodMkRight (β : Type*) [MeasurableSpace β] (κ : kernel α γ) (b : β) {a : α} :
    snd' (prodMkRight β κ) a b = κ a := rfl

@[simp]
lemma fst'_swapRight (κ : kernel (α × β) γ) : fst' (swapLeft κ) = snd' κ := rfl

@[simp]
lemma snd'_swapRight (κ : kernel (α × β) γ) : snd' (swapLeft κ) = fst' κ := rfl

end FstSnd

--this may be put in a different place than the rest, maybe still in the same file, also find a better name
lemma compProd_apply_eq_compProd_snd' (κ : kernel α β) (η : kernel (α × β) γ)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ ⊗ₖ η) a = (κ a) ⊗ₘ (snd' η a) := by
  ext s hs
  simp_rw [compProd_apply _ _ _ hs, Measure.compProd_apply hs, snd'_apply]
  rfl

end kernel

end ProbabilityTheory
