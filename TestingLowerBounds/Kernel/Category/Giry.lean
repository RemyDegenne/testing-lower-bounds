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

open CategoryTheory MeasureTheory

universe u v

namespace MeasureTheory

instance {Ω : Type*} [MeasurableSpace Ω] : MeasurableSpace (ProbabilityMeasure Ω) :=
  Subtype.instMeasurableSpace

lemma ProbabilityMeasure.measurable_map {α β : Type*} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} (f : α → β) (hf : Measurable f) :
    Measurable fun P ↦ ProbabilityMeasure.map P hf.aemeasurable :=
  ((Measure.measurable_map _ hf).comp measurable_subtype_coe).subtype_mk

@[simp]
lemma ProbabilityMeasure.map_id {α : Type*} {mα : MeasurableSpace α} (P : ProbabilityMeasure α) :
    ProbabilityMeasure.map P (f := id) measurable_id.aemeasurable = P := by ext; simp

lemma ProbabilityMeasure.map_map {α β γ : Type*} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ} (P : ProbabilityMeasure α)
    {g : β → γ} (hg : Measurable g) {f : α → β} (hf : Measurable f) :
    P.map (hg.comp hf).aemeasurable
      = (P.map hf.aemeasurable).map hg.aemeasurable := by
  ext; simp [Measure.map_map hg hf]

@[simp]
lemma ProbabilityMeasure.map_dirac {α β : Type*} {_ : MeasurableSpace α}
    {_ : MeasurableSpace β} {f : α → β} (hf : Measurable f) (a : α) :
    ProbabilityMeasure.map ⟨Measure.dirac a, inferInstance⟩ hf.aemeasurable
      = ⟨Measure.dirac (f a), inferInstance⟩ := by
  simp [ProbabilityMeasure.map, Measure.map_dirac hf]

noncomputable
def ProbabilityMeasure.join {α : Type*} [MeasurableSpace α]
    (m : ProbabilityMeasure (ProbabilityMeasure α)) : ProbabilityMeasure α :=
  sorry
  -- ⟨Measure.join m, inferInstance⟩

lemma ProbabilityMeasure.measurable_join {α : Type*} [MeasurableSpace α] :
    Measurable (ProbabilityMeasure.join (α := α)) := by
  sorry

lemma ProbabilityMeasure.join_map_map.{u_1, u_2} {α : Type u_1} {β : Type u_2}
    [MeasurableSpace α] [MeasurableSpace β]
    {f : α → β} (hf : Measurable f) (μ : ProbabilityMeasure (ProbabilityMeasure α)) :
    (ProbabilityMeasure.map μ (f := fun P ↦ ProbabilityMeasure.map P hf.aemeasurable)
        (ProbabilityMeasure.measurable_map f hf).aemeasurable).join
      = ProbabilityMeasure.map μ.join hf.aemeasurable := by
  --simp [ProbabilityMeasure.join]
  sorry

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
      naturality := fun _ _ ⟨_, hf⟩ ↦ Subtype.eq <| funext fun μ ↦ sorry } -- Measure.join_map_map hf μ }
  assoc _ := Subtype.eq <| funext fun _ ↦ sorry -- Measure.join_map_join _
  left_unit _ := Subtype.eq <| funext fun _ ↦ sorry -- Measure.join_dirac _
  right_unit _ := Subtype.eq <| funext fun _ ↦ sorry -- Measure.join_map_dirac _

end MeasCat
