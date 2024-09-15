/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!

# Giry monad for probability measures

-/

open scoped ENNReal

open CategoryTheory MeasureTheory

universe u v

namespace MeasureTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {f : α → β}

instance[MeasurableSpace α] : MeasurableSpace (ProbabilityMeasure α) :=
  Subtype.instMeasurableSpace

lemma ProbabilityMeasure.measurable_coe {s : Set α} (hs : MeasurableSet s) :
    Measurable fun μ : ProbabilityMeasure α ↦ μ.toMeasure s :=
  (Measure.measurable_coe hs).comp measurable_subtype_coe

lemma ProbabilityMeasure.measurable_of_measurable_coe (f : β → ProbabilityMeasure α)
    (h : ∀ (s : Set α), MeasurableSet s → Measurable fun b ↦ (f b).toMeasure s) : Measurable f := by
  refine Measurable.subtype_mk ?_
  refine Measurable.of_le_map ?_
  refine iSup₂_le fun s hs ↦ ?_
  refine MeasurableSpace.comap_le_iff_le_map.2 ?_
  rw [MeasurableSpace.map_comp]
  exact h s hs

lemma ProbabilityMeasure.measurable_map (f : α → β) (hf : Measurable f) :
    Measurable fun P ↦ ProbabilityMeasure.map P hf.aemeasurable :=
  ((Measure.measurable_map _ hf).comp measurable_subtype_coe).subtype_mk

@[simp]
lemma ProbabilityMeasure.map_id (P : ProbabilityMeasure α) :
    ProbabilityMeasure.map P (f := id) measurable_id.aemeasurable = P := by ext; simp

lemma ProbabilityMeasure.map_map (P : ProbabilityMeasure α)
    {g : β → γ} (hg : Measurable g) {f : α → β} (hf : Measurable f) :
    P.map (hg.comp hf).aemeasurable
      = (P.map hf.aemeasurable).map hg.aemeasurable := by
  ext; simp [Measure.map_map hg hf]

@[simp]
lemma ProbabilityMeasure.map_dirac (hf : Measurable f) (a : α) :
    ProbabilityMeasure.map ⟨Measure.dirac a, inferInstance⟩ hf.aemeasurable
      = ⟨Measure.dirac (f a), inferInstance⟩ := by
  simp [ProbabilityMeasure.map, Measure.map_dirac hf]

noncomputable
def ProbabilityMeasure.join [MeasurableSpace α]
    (m : ProbabilityMeasure (ProbabilityMeasure α)) : ProbabilityMeasure α where
  val := (m.map (f := toMeasure) measurable_subtype_coe.aemeasurable).toMeasure.join
  property := by
    constructor
    simp only [toMeasure_map, MeasurableSet.univ, Measure.join_apply]
    rw [lintegral_map (Measure.measurable_coe MeasurableSet.univ)]
    swap; · exact measurable_subtype_coe
    simp only [measure_univ, lintegral_const, mul_one]

@[simp]
lemma ProbabilityMeasure.join_apply {m : ProbabilityMeasure (ProbabilityMeasure α)} {s : Set α}
    (hs : MeasurableSet s) :
    join m s = ∫⁻ (μ : ProbabilityMeasure α), μ s ∂m := by
  simp only [ennreal_coeFn_eq_coeFn_toMeasure, ProbabilityMeasure.join, coe_mk, toMeasure_map]
  rw [Measure.join_apply hs, lintegral_map (Measure.measurable_coe hs)]
  exact measurable_subtype_coe

@[simp]
lemma ProbabilityMeasure.toMeasure_join_apply {m : ProbabilityMeasure (ProbabilityMeasure α)}
    {s : Set α} (hs : MeasurableSet s) :
    (join m).toMeasure s = ∫⁻ (μ : ProbabilityMeasure α), μ s ∂m := by
  rw [← join_apply hs]
  simp only [ennreal_coeFn_eq_coeFn_toMeasure]

lemma ProbabilityMeasure.measurable_join [MeasurableSpace α] :
    Measurable (ProbabilityMeasure.join (α := α)) := by
  refine ProbabilityMeasure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  simp only [ProbabilityMeasure.toMeasure_join_apply hs, ennreal_coeFn_eq_coeFn_toMeasure]
  refine (Measure.measurable_lintegral
    (f := fun (μ : ProbabilityMeasure α) ↦ μ.toMeasure s) ?_).comp measurable_subtype_coe
  exact measurable_coe hs

lemma ProbabilityMeasure.lintegral_join {m : ProbabilityMeasure (ProbabilityMeasure α)}
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x ∂join m = ∫⁻ (μ : ProbabilityMeasure _), ∫⁻ x, f x ∂μ.toMeasure ∂m := by
  simp only [join, toMeasure_map, coe_mk]
  rw [Measure.lintegral_join hf, lintegral_map]
  · exact Measure.measurable_lintegral hf
  · exact measurable_subtype_coe

/-- Monadic bind on `ProbabilityMeasure`. -/
noncomputable
def ProbabilityMeasure.bind (m : ProbabilityMeasure α) (f : α → ProbabilityMeasure β)
    (hf : Measurable f) :
    ProbabilityMeasure β :=
  join (map m hf.aemeasurable)

@[simp]
lemma ProbabilityMeasure.bind_apply {m : ProbabilityMeasure α} {f : α → ProbabilityMeasure β}
    {s : Set β} (hs : MeasurableSet s) (hf : Measurable f) :
    bind m f hf s = ∫⁻ a, f a s ∂m := by
  rw [bind, join_apply hs]
  simp only [toMeasure_map, ennreal_coeFn_eq_coeFn_toMeasure]
  rw [lintegral_map (measurable_coe hs) hf]

@[simp]
lemma ProbabilityMeasure.toMeasure_bind_apply {m : ProbabilityMeasure α}
    {f : α → ProbabilityMeasure β} {s : Set β} (hs : MeasurableSet s) (hf : Measurable f) :
    (bind m f hf).toMeasure s = ∫⁻ a, f a s ∂m := by
  rw [← bind_apply hs hf]
  simp

lemma ProbabilityMeasure.measurable_bind' {g : α → ProbabilityMeasure β} (hg : Measurable g) :
    Measurable fun m ↦ bind m g hg :=
  measurable_join.comp (measurable_map _ hg)

lemma ProbabilityMeasure.lintegral_bind {m : ProbabilityMeasure α} {μ : α → ProbabilityMeasure β}
    {f : β → ℝ≥0∞} (hμ : Measurable μ) (hf : Measurable f) :
    ∫⁻ x, f x ∂bind m μ hμ = ∫⁻ a, ∫⁻ x, f x ∂μ a ∂m := by
  refine (lintegral_join hf).trans ?_
  simp only [toMeasure_map]
  rw [lintegral_map _ hμ]
  exact (Measure.measurable_lintegral hf).comp measurable_subtype_coe

lemma ProbabilityMeasure.bind_bind {γ} [MeasurableSpace γ] {m : ProbabilityMeasure α}
    {f : α → ProbabilityMeasure β} {g : β → ProbabilityMeasure γ}
    (hf : Measurable f) (hg : Measurable g) :
    bind (bind m f hf) g hg = bind m (fun a ↦ bind (f a) g hg) ((measurable_bind' hg).comp hf) := by
  ext1 s hs
  rw [toMeasure_bind_apply hs hg]
  simp only [ennreal_coeFn_eq_coeFn_toMeasure]
  rw [toMeasure_bind_apply hs, lintegral_bind hf]
  · simp only [ennreal_coeFn_eq_coeFn_toMeasure]
    conv_rhs => enter [2, a]; rw [toMeasure_bind_apply hs hg]
    simp only [ennreal_coeFn_eq_coeFn_toMeasure]
  · exact (measurable_coe hs).comp hg

lemma ProbabilityMeasure.bind_dirac {f : α → ProbabilityMeasure β} (hf : Measurable f) (a : α) :
    bind ⟨Measure.dirac a, inferInstance⟩ f hf = f a := by
  ext1 s hs
  rw [toMeasure_bind_apply hs hf]
  simp only [coe_mk, ennreal_coeFn_eq_coeFn_toMeasure]
  erw [lintegral_dirac' a ((measurable_coe hs).comp hf)]
  rfl

lemma ProbabilityMeasure.dirac_bind {m : ProbabilityMeasure α} :
    bind m (fun a ↦ ⟨Measure.dirac a, inferInstance⟩) Measure.measurable_dirac.subtype_mk = m := by
  ext1 s hs
  rw [toMeasure_bind_apply hs]
  simp only [mk_apply, Measure.dirac_apply' _ hs]
  have : ∫⁻ a, (s.indicator (1 : α → ℝ≥0∞) a).toNNReal ∂m = ∫⁻ a, s.indicator 1 a ∂m := by
    congr with a
    refine ENNReal.coe_toNNReal ?_
    classical
    rw [Set.indicator_apply]
    split_ifs <;> simp
  rw [this, lintegral_indicator 1 hs]
  simp

lemma ProbabilityMeasure.join_eq_bind (μ : ProbabilityMeasure (ProbabilityMeasure α)) :
    join μ = bind μ id measurable_id := by rw [bind, map_id]

lemma ProbabilityMeasure.join_map_map (hf : Measurable f)
    (P : ProbabilityMeasure (ProbabilityMeasure α)) :
    (ProbabilityMeasure.map P (f := fun P ↦ ProbabilityMeasure.map P hf.aemeasurable)
        (ProbabilityMeasure.measurable_map f hf).aemeasurable).join
      = ProbabilityMeasure.map P.join hf.aemeasurable := by
  ext s hs
  simp only [toMeasure_map]
  rw [toMeasure_join_apply hs, Measure.map_apply hf hs, toMeasure_join_apply (hf hs)]
  simp only [toMeasure_map, ennreal_coeFn_eq_coeFn_toMeasure]
  rw [lintegral_map (measurable_coe hs) (measurable_map _ hf)]
  simp only [toMeasure_map, Measure.map_apply hf hs]

lemma ProbabilityMeasure.join_map_join [MeasurableSpace α]
    (P : ProbabilityMeasure (ProbabilityMeasure (ProbabilityMeasure α))) :
    (ProbabilityMeasure.map P (ProbabilityMeasure.measurable_join).aemeasurable).join
      = P.join.join := by
  ext s hs
  rw [toMeasure_join_apply hs, toMeasure_join_apply hs]
  simp only [toMeasure_map, ennreal_coeFn_eq_coeFn_toMeasure]
  rw [lintegral_map (measurable_coe hs) measurable_join]
  rw [lintegral_join (measurable_coe hs)]
  congr with Q
  rw [toMeasure_join_apply hs]
  simp

lemma ProbabilityMeasure.join_dirac [MeasurableSpace α] (P : ProbabilityMeasure α) :
    ProbabilityMeasure.join ⟨Measure.dirac P, inferInstance⟩ = P :=
  (join_eq_bind _).trans (bind_dirac measurable_id _)

lemma ProbabilityMeasure.join_map_dirac [MeasurableSpace α] (P : ProbabilityMeasure α) :
    (ProbabilityMeasure.map P (f := fun a ↦ ⟨Measure.dirac a, inferInstance⟩)
      Measure.measurable_dirac.subtype_mk.aemeasurable).join = P :=
  dirac_bind

end MeasureTheory

namespace MeasCat

attribute [local instance] ConcreteCategory.instFunLike

noncomputable
def Prob : MeasCat ⥤ MeasCat where
  obj X := ⟨@MeasureTheory.ProbabilityMeasure X.1 X.2, inferInstance⟩
  map f := ⟨fun P ↦ ProbabilityMeasure.map P _, ProbabilityMeasure.measurable_map _ f.2⟩
  map_id := fun _ ↦ Subtype.eq <| funext fun _ ↦ ProbabilityMeasure.map_id _
  map_comp := fun ⟨_, hf⟩ ⟨_, hg⟩ ↦ Subtype.eq <| funext fun _ ↦ ProbabilityMeasure.map_map _ hg hf

/-- The Giry monad for probability measures, i.e. the monadic structure associated with `Prob`. -/
noncomputable
def ProbGiry : CategoryTheory.Monad MeasCat where
  toFunctor := Prob
  η :=
    { app := fun X ↦ ⟨fun x ↦ (⟨@Measure.dirac X.1 X.2 x, inferInstance⟩ : ProbabilityMeasure X),
        Measure.measurable_dirac.subtype_mk⟩
      naturality := fun _ _ ⟨_, hf⟩ ↦ Subtype.eq <| funext fun a ↦
        (ProbabilityMeasure.map_dirac hf a).symm }
  μ :=
    { app := fun X ↦ ⟨@ProbabilityMeasure.join X.1 X.2, ProbabilityMeasure.measurable_join⟩
      naturality := fun _ _ ⟨_, hf⟩ ↦ Subtype.eq <| funext <|
        ProbabilityMeasure.join_map_map hf }
  assoc _ := Subtype.eq <| funext ProbabilityMeasure.join_map_join
  left_unit _ := Subtype.eq <| funext ProbabilityMeasure.join_dirac
  right_unit _ := Subtype.eq <| funext ProbabilityMeasure.join_map_dirac

end MeasCat
