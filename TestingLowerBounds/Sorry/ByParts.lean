import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
Here there is the statement of a version of the integration by parts theorem for the Riemann-Stieltjes integral.
This is a generalization of the integration by parts theorem for the Riemann integral. We state it only for the case of Stieltjes functions, that is right continuous and non decreasing, this is because in that case the functions naturally gives rise to a measure. It may be generalized to the more general case with signed measures, but it is necessary to pinpoint the right conditions for that case and it may be necessary to write the definition of the signed measure that arises from a function (I don't know the exact hp for the function, maybe bounded variation?).
For now I am only stating the theorem and I'm leaving the proof for later.
Some references for potential candidates for the proof are:
http://mathonline.wikidot.com/the-formula-for-integration-by-parts-of-riemann-stieltjes-in [1]
Mathematical analysis, Tom M. Apostol, 5th edition [2] theorem 7.6, page 144 (seems similar to the previous link, in the link it is a bit longer, but maybe it's just that it has more details)
The integrals of Lebesgue, Denjoy, Perron, and Henstock [3], theorem 12.14

See also https://math.ryerson.ca/~niushan/Stieltjes-integrals.pdf [4] and Measure and Integration [5], Wheeden and Zygmund, for some facts about Riemann-Stieltjes and Lebesgue integrals.
Here I am stating the results in terms of interval integrals, since it is what I need and the RS integral is equal to the Lebesgue one if one of the functions is increasing and right continuous and the other is bounded and measurable (see 4.1 in the previous link).
To prove the general result it may be better to develop a theory of the Riemann-Stieltjes integral in mathlib and then prove the results for that integral and translate them for the lebesgue integral when possible.

To be sure that the result is correct:
Our integral is the same as the Lebesgue-Stieltjes integral defined in chapter 11.3 of [5], theorem 11.11 in [4] assures us that this integral corresponds to the Riemann-Stieltjes one in the case of a monotone right-continuous function and a bounded Borel-measurable one, if the Riemann-Stieltjes integral exists.
Then theorem 4.7 in [2] says that for `f α : ℝ → ℝ` such that `f` is Rieman-Stieltjes integrable with respect to `α` on `[a, b]` then `α` is Riemann-Stieltjes integrable with respect to `f` on `[a, b]` and `∫ x in a..b, f x ∂α + ∫ x in a..b, α x ∂f = f b * α b - f a * α a `.
Moreover theorem 7.27 of [2] says that if `f` is continuous on `[a, b]` and `α` is of bounded variation on `[a, b]` then `f` is Riemann-Stieltjes integrable with respect to `α` on `[a, b]`, the same is true if `f` is of bounded variation and `α` is continuous.

In our case both functions are Stieltjes functions, hence they are of bounded variation, bounded on finite intervals and Borel measurable. However we also need to ask for one of the functions to be continuous, otherwise the Riemann-Stieltjes integral may not be true, for example if `f` and `α` have a common point of left discontinuity (see theorem 7.29 in [2]).
-/
-- #check intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right --one of the versions of the integration by parts that is currently in mathlib.

lemma integral_stieltjes_meas_by_parts (f g : StieltjesFunction) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∫ x in a..b, f x ∂g.measure = (f b) * (g b) - (f a) * (g a) - ∫ x in a..b, g x ∂f.measure := by
  sorry
