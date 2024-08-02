import Mathlib.Topology.ContinuousOn

open Filter Set

open scoped  Topology

variable {α β : Type*} [TopologicalSpace β] {f : α → β} {b : β} {l : Filter α}

--I'm not sure if something that easily implies those lemmas already exists in mathlib, they can probably be proved in a simpler and more elegant way than I did.

lemma tendsto_nhdsWithin_of_tendsto_nhds_right {t : Set β} (hf : ∀ᶠ x in l, f x ∈ t)
    (h : Tendsto f l (𝓝 b)) : Tendsto f l (𝓝[t] b) := by
  simp_rw [Tendsto, Filter.le_def, mem_map] at h ⊢
  intro s hs
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hs with ⟨U, hU, hU'⟩
  specialize h (s ∪ tᶜ) (mem_of_superset hU (union_comm _ _ ▸ ((Set.inter_subset _ _ _).mp hU')))
  filter_upwards [hf, h] with x hx hx'
  rw [mem_preimage] at hx' ⊢
  simp_all

lemma tendsto_punctured_nhds_of_tendsto_nhds_right (hf : ∀ᶠ x in l, f x ≠ b)
    (h : Tendsto f l (𝓝 b)) : Tendsto f l (𝓝[≠] b) :=
  tendsto_nhdsWithin_of_tendsto_nhds_right hf h
