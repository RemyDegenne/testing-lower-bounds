import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-!
Here there is the statement of a version of the integration by parts theorem for the Riemann-Stieltjes integral.
This is a generalization of the integration by parts theorem for the Riemann integral. We state it only for the case of Stieltjes functions, that is right continuous and non decreasing, this is because in that case the functions naturally gives rise to a measure. It maybe generalized to the more general case with signed measures, but it is necessary to pinpoint the right conditions for that case and it may be necessary to write the definition of the signed measure that arises from a function (I don't know the exact hp for the function, maybe bounded variation?)
For now I am only stating the theorem and I'm leaving the proof for later.
Some references for potential candidates for the proof are:
http://mathonline.wikidot.com/the-formula-for-integration-by-parts-of-riemann-stieltjes-in
Mathematical analysis, Tom M. Apostol, 5th edition theorem 7.6, page 144 (seems similar to the previous link, in the link it is a bit longer, but maybe it's just that it has more details)
The integrals of Lebesgue, Denjoy, Perron, and Henstock, theorem 12.14

See also https://math.ryerson.ca/~niushan/Stieltjes-integrals.pdf for some facts about Riemann-Stieltjes and Lebesgue integrals.
Here I am stating the results in terms of Lebesgue integrals, since it is what I need and the RS integral is equal to the Lebesgue one if one of the functions is increasing and right continuous and the other is bounded and measurable (see 4.1 in the previous link).
To prove the general result it may be better to develop a theory of the Riemann-Stieltjes integral in mathlib adn then prove the results for that integral and translate them for the lebesgue integral when possible.
-/
-- #check intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right --one of the versions of the integratio by parts that is currently in mathlib

lemma integral_stieltjes_meas_by_parts (f g : StieltjesFunction) (a b : ℝ) :
    ∫ x in a..b, f x ∂g.measure = (f b) * (g b) - (f a) * (g a) - ∫ x in a..b, g x ∂f.measure := by
  sorry
--maybe post this on Zulip?
