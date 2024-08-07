import Mathlib.Probability.Kernel.Composition

open MeasureTheory

namespace ProbabilityTheory.Kernel

variable {α β ι : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
variable {γ : Type*} {mγ : MeasurableSpace γ}

--TODO: PR this to mathlib, after `comp_deterministic_eq_comap`
-- #check comp_deterministic_eq_comap

--PRed, see #15461
lemma const_comp (μ : Measure γ) (κ : Kernel α β) :
    const β μ ∘ₖ κ = fun a ↦ (κ a) Set.univ • μ := by
  ext _ _ hs
  simp_rw [comp_apply' _ _ _ hs, const_apply, MeasureTheory.lintegral_const, Measure.smul_apply,
    smul_eq_mul, mul_comm]

--PRed, see #15461
@[simp]
lemma const_comp' (μ : Measure γ) (κ : Kernel α β) [IsMarkovKernel κ] :
    const β μ ∘ₖ κ = const α μ := by
  ext; simp_rw [const_comp, measure_univ, one_smul, const_apply]

end ProbabilityTheory.Kernel
