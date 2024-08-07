import Mathlib.Probability.Kernel.Basic

open MeasureTheory ProbabilityTheory

namespace MeasureTheory

--TODO: put this lemma in a separate file, then PR it to mathlib,
-- I'm not sure it can just go in the same file as integral_congr_ae, since it uses the kernels.
-- maybe we could do a simpler version with 2 probability measures instead of kernels.
-- decide what to do with the 2 vertions, are they both useful?
--I could have proven the second one using the first, but it is probabily easier to do them
-- separately, also in this way we can put them in separate files without worring about dependencies
--also about the names, if we put the two lemmas under different namespaces
-- (the first one could go under something that contains kernel) we can give them the same name
variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ : Measure α}
  {ν : Measure β} {κ : Kernel α β} {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

--PRed, see #15460.
lemma integral_congr_ae₂ {f g : α → β → G} (h : ∀ᵐ a ∂μ, f a =ᵐ[κ a] g a) :
    ∫ a, ∫ b, f a b ∂(κ a) ∂μ = ∫ a, ∫ b, g a b ∂(κ a) ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with a ha
  apply integral_congr_ae
  filter_upwards [ha] with b hb using hb

--PRed as `ProbabilityTheory.Kernel.integral_congr_ae₂`, see #15460.
lemma integral_congr_ae₂' {f g : α → β → G} (h : ∀ᵐ a ∂μ, f a =ᵐ[ν] g a) :
    ∫ a, ∫ b, f a b ∂ν ∂μ = ∫ a, ∫ b, g a b ∂ν ∂μ := by
  apply integral_congr_ae
  filter_upwards [h] with a ha
  apply integral_congr_ae
  filter_upwards [ha] with b hb using hb

end MeasureTheory
