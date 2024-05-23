import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TestingLowerBounds.FDiv.CondFDiv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import TestingLowerBounds.ForMathlib.LogLikelihoodRatioCompProd
import TestingLowerBounds.ForMathlib.IntegralCongr2
import TestingLowerBounds.ForMathlib.KernelFstSnd

--PRd to mathlib, when it gets accepted and we bump the mathlib version, we can remove this import

open MeasureTheory Filter TopologicalSpace Function Set MeasureTheory.Measure

open ENNReal Topology MeasureTheory NNReal BigOperators


open MeasureTheory

variable {α β M : Type*} {mα : MeasurableSpace α} {mM : MeasurableSpace M}  {μ ν : Measure α}
variable {f g : α → M}

@[to_additive (attr := measurability)]
theorem Measurable.mul_iff_right [CommGroup M] [MeasurableMul₂ M] [MeasurableInv M] (hf : Measurable f) :
    Measurable (f * g) ↔ Measurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive (attr := measurability)]
theorem Measurable.mul_iff_left [CommGroup M] [MeasurableMul₂ M] [MeasurableInv M] (hf : Measurable f) :
    Measurable (g * f) ↔ Measurable g :=
  mul_comm g f ▸ Measurable.mul_iff_right hf


@[to_additive (attr := measurability)]
theorem AEMeasurable.mul_iff_right [CommGroup M] [MeasurableMul₂ M] [MeasurableInv M] (hf : AEMeasurable f μ) :
    AEMeasurable (f * g) μ ↔ AEMeasurable g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive (attr := measurability)]
theorem AEMeasurable.mul_iff_left [CommGroup M] [MeasurableMul₂ M] [MeasurableInv M] (hf : AEMeasurable f μ) :
    AEMeasurable (g * f) μ ↔ AEMeasurable g μ :=
  mul_comm g f ▸ AEMeasurable.mul_iff_right hf

namespace MeasureTheory

variable {f g : α → β}

@[to_additive (attr := measurability)]
theorem StronglyMeasurable.mul_iff_right [TopologicalSpace β] [CommGroup β] [ContinuousMul β] [ContinuousInv β] {f g : α → β} (hf : StronglyMeasurable f) : StronglyMeasurable (f * g) ↔ StronglyMeasurable g :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive (attr := measurability)]
theorem StronglyMeasurable.mul_iff_left [TopologicalSpace β] [CommGroup β] [ContinuousMul β] [ContinuousInv β] {f g : α → β} (hf : StronglyMeasurable f) : StronglyMeasurable (g * f) ↔ StronglyMeasurable g :=
  mul_comm g f ▸ StronglyMeasurable.mul_iff_right hf

@[to_additive (attr := measurability)]
theorem AEStronglyMeasurable.mul_iff_right [TopologicalSpace β] [CommGroup β] [ContinuousMul β] [ContinuousInv β] {f g : α → β} (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (f * g) μ ↔ AEStronglyMeasurable g μ :=
  ⟨fun h ↦ show g = f * g * f⁻¹ by simp only [mul_inv_cancel_comm] ▸ h.mul hf.inv,
    fun h ↦ hf.mul h⟩

@[to_additive (attr := measurability)]
theorem AEStronglyMeasurable.mul_iff_left [TopologicalSpace β] [CommGroup β] [ContinuousMul β] [ContinuousInv β] {f g : α → β} (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (g * f) μ ↔ AEStronglyMeasurable g μ :=
  mul_comm g f ▸ AEStronglyMeasurable.mul_iff_right hf

end MeasureTheory
