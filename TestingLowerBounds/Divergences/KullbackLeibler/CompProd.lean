/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Lorenzo Luccioli
-/
import TestingLowerBounds.Divergences.KullbackLeibler.KullbackLeibler
import TestingLowerBounds.FDiv.CompProd

/-!
# Kullback-Leibler divergence

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/

open Real MeasureTheory Filter MeasurableSpace

open scoped ENNReal NNReal Topology BigOperators

namespace ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {μ ν : Measure α} {κ η : Kernel α β}

/--Equivalence between two possible versions of the first condition for the finiteness of the
conditional KL divergence, the second version is the preferred one.-/
lemma kl_ae_ne_top_iff : (∀ᵐ a ∂μ, kl (κ a) (η a) ≠ ⊤) ↔
    (∀ᵐ a ∂μ, κ a ≪ η a) ∧ (∀ᵐ a ∂μ, Integrable (llr (κ a) (η a)) (κ a)) := by
  simp_rw [kl_ne_top_iff, eventually_and]

/--Equivalence between two possible versions of the second condition for the finiteness of the
conditional KL divergence, the first version is the preferred one.-/
lemma integrable_kl_iff (h_ac : ∀ᵐ a ∂μ, κ a ≪ η a) :
    Integrable (fun a ↦ (kl (κ a) (η a)).toReal) μ
      ↔ Integrable (fun a ↦ ∫ x, llr (κ a) (η a) x ∂(κ a)) μ := by
  apply integrable_congr
  filter_upwards [h_ac] with a ha1
  rw [kl_toReal_of_ac ha1]

-- lemma kl_compProd_eq_top_iff :
--     kl (μ ⊗ₘ κ) (μ ⊗ₘ η) = ⊤
--       ↔

end ProbabilityTheory
