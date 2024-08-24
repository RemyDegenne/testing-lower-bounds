import Mathlib.Topology.Order.Basic

open Set Filter Topology

-- Put this in Mathlib, replacing `Monotone.tendsto_nhdsWithin_Iio`
-- PRed, see #15470

lemma MonotoneOn.tendsto_nhdsWithin_Ioo_left {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo y x).Nonempty) (Mf : MonotoneOn f (Ioo y x))
    (h_bdd : BddAbove (f '' Ioo y x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Ioo y x))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, ⟨yz, zx⟩, lz⟩ : ∃ a : α, a ∈ Ioo y x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h_nonempty.image _) hl
    refine mem_of_superset (Ioo_mem_nhdsWithin_Iio' zx) fun w hw => ?_
    exact lz.trans_le <| Mf ⟨yz, zx⟩ ⟨yz.trans_le hw.1.le, hw.2⟩ hw.1.le
  · rcases h_nonempty with ⟨_, hy, hx⟩
    refine mem_of_superset (Ioo_mem_nhdsWithin_Iio' (hy.trans hx)) fun w hw => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hw)

lemma MonotoneOn.tendsto_nhdsWithin_Ioo_right {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x y : α} (h_nonempty : (Ioo x y).Nonempty) (Mf : MonotoneOn f (Ioo x y))
    (h_bdd : BddBelow (f '' Ioo x y)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioo x y))) := by
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · rcases h_nonempty with ⟨p, hy, hx⟩
    refine mem_of_superset (Ioo_mem_nhdsWithin_Ioi' (hy.trans hx)) fun w hw => hl.trans_le ?_
    exact csInf_le h_bdd (mem_image_of_mem _ hw)
  · obtain ⟨z, ⟨xz, zy⟩, zm⟩ : ∃ a : α, a ∈ Ioo x y ∧ f a < m := by
      simpa [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h_nonempty.image _) hm
    refine mem_of_superset (Ioo_mem_nhdsWithin_Ioi' xz) fun w hw => ?_
    exact (Mf ⟨hw.1, hw.2.trans zy⟩ ⟨xz, zy⟩ hw.2.le).trans_lt zm

lemma MonotoneOn.tendsto_nhdsWithin_Iio {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x : α} (Mf : MonotoneOn f (Iio x)) (h_bdd : BddAbove (f '' Iio x)) :
    Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) := by
  rcases eq_empty_or_nonempty (Iio x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · obtain ⟨z, zx, lz⟩ : ∃ a : α, a < x ∧ l < f a := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_lt_csSup (h.image _) hl
    exact mem_of_superset (Ioo_mem_nhdsWithin_Iio' zx) fun y hy => lz.trans_le (Mf zx hy.2 hy.1.le)
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => lt_of_le_of_lt ?_ hm
    exact le_csSup h_bdd (mem_image_of_mem _ hy)

lemma MonotoneOn.tendsto_nhdsWithin_Ioi {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} {x : α} (Mf : MonotoneOn f (Ioi x)) (h_bdd : BddBelow (f '' Ioi x)) :
    Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) := by
  rcases eq_empty_or_nonempty (Ioi x) with (h | h); · simp [h]
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · refine mem_of_superset self_mem_nhdsWithin fun y hy => hl.trans_le ?_
    exact csInf_le h_bdd (mem_image_of_mem _ hy)
  · obtain ⟨z, xz, zm⟩ : ∃ a : α, x < a ∧ f a < m := by
      simpa only [mem_image, exists_prop, exists_exists_and_eq_and] using
        exists_lt_of_csInf_lt (h.image _) hm
    exact mem_of_superset (Ioo_mem_nhdsWithin_Ioi' xz) fun y hy => (Mf hy.1 xz hy.2.le).trans_lt zm

--this is already in mathlib, this is just an alternative proof using the more general version, if we substitute it remove the prime (') at the end of the name
/-- A monotone map has a limit to the left of any point `x`, equal to `sSup (f '' (Iio x))`. -/
theorem Monotone.tendsto_nhdsWithin_Iio' {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[<] x) (𝓝 (sSup (f '' Iio x))) :=
  MonotoneOn.tendsto_nhdsWithin_Iio (Mf.monotoneOn _) (Mf.map_bddAbove bddAbove_Iio)


/-- A monotone map has a limit to the right of any point `x`, equal to `sInf (f '' (Ioi x))`. -/
theorem Monotone.tendsto_nhdsWithin_Ioi' {α β : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (Mf : Monotone f) (x : α) : Tendsto f (𝓝[>] x) (𝓝 (sInf (f '' Ioi x))) :=
  Monotone.tendsto_nhdsWithin_Iio' (α := αᵒᵈ) (β := βᵒᵈ) Mf.dual x
