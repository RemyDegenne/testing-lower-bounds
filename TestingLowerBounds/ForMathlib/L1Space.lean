import Mathlib.MeasureTheory.Function.L1Space

namespace MeasureTheory.Integrable

variable {α β: Type*} {m : MeasurableSpace α} {μ ν : Measure α}
variable [NormedAddCommGroup β]

--these lemmas could be put near the following one
#check MeasureTheory.Integrable.add

@[simp]
lemma integrable_add_const_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ f x + c) μ ↔ Integrable f μ :=
  ⟨fun h ↦ show f = fun x ↦ f x + c + (-c)
    by simp only [add_neg_cancel_right] ▸ h.add (integrable_const _), fun h ↦ h.add (integrable_const _)⟩

@[simp]
lemma integrable_const_add_iff [IsFiniteMeasure μ] {f : α → β} {c : β} :
    Integrable (fun x ↦ c + f x) μ ↔ Integrable f μ :=
  ⟨fun h ↦ show f = fun x ↦ (c + f x) + (-c)
    by simp only [add_neg_cancel_comm] ▸ Integrable.add h (integrable_const (-c)),
    fun h ↦ Integrable.add (integrable_const _) h⟩

@[simp]
lemma integrable_add_iff_integrable_right {f g : α → β} (hf : Integrable f μ) :
    Integrable (f + g) μ ↔ Integrable g μ :=
  ⟨fun h ↦ show g = f + g + (-f) by simp only [add_neg_cancel_comm] ▸ h.add hf.neg,
    fun h ↦ hf.add h⟩

@[simp]
lemma integrable_add_iff_integrable_left {f g : α → β} (hf : Integrable f μ) :
    Integrable (g + f) μ ↔ Integrable g μ :=
  ⟨fun h ↦ show g = g + f + (-f) by simp only [add_neg_cancel_right] ▸ h.add hf.neg,
    fun h ↦ h.add hf⟩

end MeasureTheory.Integrable
