/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.CategoryTheory.ChosenFiniteProducts

/-!

# Categories of measurable spaces and kernels

-/

open MeasureTheory CategoryTheory Limits

open scoped ENNReal

namespace ProbabilityTheory

section SFiniteKernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}

def SFiniteKernel (α β : Type*) [MeasurableSpace α] [MeasurableSpace β] : Type _ :=
  { κ : kernel α β // IsSFiniteKernel κ }

namespace SFiniteKernel

@[coe]
def toKernel : SFiniteKernel α β → kernel α β := Subtype.val

instance instCoe : Coe (SFiniteKernel α β) (kernel α β) where
  coe := toKernel

instance isSFiniteKernel (κ : SFiniteKernel α β) : IsSFiniteKernel (κ : kernel α β) := κ.prop

@[simp, norm_cast] lemma coe_mk (κ : kernel α β) (hκ) : toKernel ⟨κ, hκ⟩ = κ := rfl

@[simp]
theorem val_eq_toKernel (κ : SFiniteKernel α β) : κ.val = (κ : kernel α β) :=
  rfl

theorem toKernel_injective : Function.Injective ((↑) : SFiniteKernel α β → kernel α β) :=
  Subtype.coe_injective

instance instFunLike : FunLike (SFiniteKernel α β) α (Measure β) where
  coe κ a := (κ : kernel α β) a
  coe_injective' κ η h := toKernel_injective $ by simp only [DFunLike.coe_fn_eq] at h; exact h

lemma coeFn_def (κ : SFiniteKernel α β) : κ = fun a ↦ (κ : kernel α β) a := rfl

lemma coeFn_mk (κ : kernel α β) (hκ) :
    DFunLike.coe (F := SFiniteKernel α β) ⟨κ, hκ⟩ = fun a ↦ κ a := rfl

@[simp]
lemma mk_apply (κ : kernel α β) (hκ) (a : α) :
    DFunLike.coe (F := SFiniteKernel α β) ⟨κ, hκ⟩ a = κ a := rfl

noncomputable
def id (α : Type*) [MeasurableSpace α] : SFiniteKernel α α := ⟨kernel.id, inferInstance⟩

noncomputable
def comp (κ : SFiniteKernel α β) (η : SFiniteKernel β γ) : SFiniteKernel α γ :=
  ⟨η.toKernel ∘ₖ κ.toKernel, by have := κ.2; have := η.2; infer_instance⟩

@[simp]
lemma comp_id (κ : SFiniteKernel α β) : κ.comp (id β) = κ := by
  apply DFunLike.ext
  intro a
  ext s hs
  simp only [comp, id, mk_apply, kernel.comp_apply]
  norm_cast
  rw [Measure.bind_apply hs (kernel.measurable _)]
  simp only [kernel.id_apply, Measure.dirac_apply' _ hs]
  rw [lintegral_indicator_one hs]
  rfl

@[simp]
lemma id_comp (κ : SFiniteKernel α β) : (id α).comp κ = κ := by
  apply DFunLike.ext
  intro a
  ext s hs
  simp only [comp, id, mk_apply, kernel.comp_apply]
  norm_cast
  rw [Measure.bind_apply hs (kernel.measurable _)]
  simp only [kernel.id_apply]
  rw [lintegral_dirac']
  · rfl
  · exact kernel.measurable_coe _ hs

lemma comp_assoc (κ : SFiniteKernel α β) (η : SFiniteKernel β γ) (ξ : SFiniteKernel γ δ) :
    (κ.comp η).comp ξ = κ.comp (η.comp ξ) := by
  simp only [comp]
  norm_cast
  apply DFunLike.ext
  intro a
  simp only [mk_apply]
  rw [kernel.comp_assoc]

noncomputable
def parallelComp (κ : SFiniteKernel α β) (η : SFiniteKernel γ δ) : SFiniteKernel (α × γ) (β × δ) :=
  ⟨κ ∥ₖ η, inferInstance⟩

@[simp]
lemma parallelComp_id : parallelComp (id α) (id β) = id (α × β) := by
  sorry

@[simp]
lemma parallelComp_left_comp_right (κ : SFiniteKernel α β) (η : SFiniteKernel γ δ) :
    (parallelComp κ (id γ)).comp (parallelComp (id β) η) = parallelComp κ η := by
  sorry

lemma parallelComp_comp {β' δ' : Type*} {_ : MeasurableSpace β'} {_ : MeasurableSpace δ'}
    (κ : SFiniteKernel α β) (η : SFiniteKernel γ δ)
    (κ' : SFiniteKernel β β') (η' : SFiniteKernel δ δ') :
    parallelComp (κ.comp κ') (η.comp η') = (parallelComp κ η).comp (parallelComp κ' η') := by
  sorry

end SFiniteKernel

end SFiniteKernel

universe u v

namespace MeasCat

/-! `MeasCat` is a cartesian symmetric monoidal category. -/

def terminalLimitCone : Limits.LimitCone (Functor.empty MeasCat) where
  cone :=
    { pt := MeasCat.of PUnit
      π := (Functor.uniqueFromEmpty _).hom }
  isLimit :=
    { lift := fun _ => ⟨fun _ ↦ PUnit.unit, measurable_const⟩
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => rfl }

def binaryProductCone (X Y : MeasCat) : BinaryFan X Y :=
  CategoryTheory.Limits.BinaryFan.mk (P := MeasCat.of (X × Y))
    ⟨Prod.fst, measurable_fst⟩ ⟨Prod.snd, measurable_snd⟩

@[simp]
lemma binaryProductCone_fst (X Y : MeasCat) :
    (binaryProductCone X Y).fst = ⟨Prod.fst, measurable_fst⟩ := rfl

@[simp]
theorem binaryProductCone_snd (X Y : MeasCat) :
    (binaryProductCone X Y).snd = ⟨Prod.snd, measurable_snd⟩ := rfl

instance (X : MeasCat) : MeasurableSpace X := X.str

@[simps]
def binaryProductLimit (X Y : MeasCat.{u}) : IsLimit (binaryProductCone.{u} X Y) where
  lift (s : BinaryFan X Y) := ⟨fun x ↦ (s.fst x, s.snd x), by
    letI : MeasurableSpace
        ((forget MeasCat).obj (((Functor.const (Discrete WalkingPair)).obj s.pt).obj
          { as := WalkingPair.left })) :=
      (((Functor.const (Discrete WalkingPair)).obj s.pt).obj { as := WalkingPair.left }).str
    letI : MeasurableSpace ((forget MeasCat).obj ((pair X Y).obj { as := WalkingPair.left })) :=
      ((pair X Y).obj { as := WalkingPair.left }).str
    letI : MeasurableSpace
        ((forget MeasCat).obj (((Functor.const (Discrete WalkingPair)).obj s.pt).obj
          { as := WalkingPair.right })) :=
      (((Functor.const (Discrete WalkingPair)).obj s.pt).obj { as := WalkingPair.right }).str
    letI : MeasurableSpace ((forget MeasCat).obj ((pair X Y).obj { as := WalkingPair.right })) :=
      ((pair X Y).obj { as := WalkingPair.right }).str
    have h1 : Measurable s.fst := s.fst.2
    have h2 : Measurable s.snd := s.snd.2
    exact h1.prod_mk h2⟩
  fac _ j := Discrete.recOn j fun j => WalkingPair.casesOn j rfl rfl
  uniq s m w := by
    refine Subtype.ext ?_
    simp only [Functor.const_obj_obj, pair_obj_left, pair_obj_right]
    have h1 := w ⟨WalkingPair.left⟩
    have h2 := w ⟨WalkingPair.right⟩
    simp only [pair_obj_left, BinaryFan.π_app_left, binaryProductCone_fst, Functor.const_obj_obj]
      at h1
    simp only [pair_obj_right, BinaryFan.π_app_right, binaryProductCone_snd,
      Functor.const_obj_obj] at h2
    rw [← h1, ← h2]
    ext x
    refine Prod.ext rfl rfl

@[simps]
def binaryProductLimitCone (X Y : MeasCat) : LimitCone (pair X Y) :=
  ⟨_, binaryProductLimit X Y⟩

/-- This gives in particular a `SymmetricCategory` instance.
That is, `MeasCat` is a cartesian symmetric monoidal category. -/
@[simps]
instance : ChosenFiniteProducts MeasCat where
  product X Y := binaryProductLimitCone X Y
  terminal := terminalLimitCone

example : HasBinaryProducts MeasCat := inferInstance
example : HasTerminal MeasCat := inferInstance
example : SymmetricCategory MeasCat := inferInstance

end MeasCat

section CommutativeMonad

open MonoidalCategory

class LeftStrong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  leftStr : ((𝟭 C : C ⥤ C).prod (T : C ⥤ C)) ⋙ (tensor C) ⟶ (tensor C) ⋙ (T : C ⥤ C)
  unit_comp (X : C) : (λ_ (T.obj X)).symm.hom ≫ leftStr.app (𝟙_ C, X)
      = T.map (λ_ X).symm.hom := by aesop_cat
  assoc (X Y Z : C) : leftStr.app (X ⊗ Y, Z) ≫ T.map (α_ X Y Z).hom
      = (α_ X Y (T.obj Z)).hom ≫ ((𝟙 X) ⊗ leftStr.app (Y, Z)) ≫ leftStr.app (X, Y ⊗ Z) := by
    aesop_cat
  unit_comm (X Y : C) : ((𝟙 X) ⊗ T.η.app Y) ≫ leftStr.app (X, Y) = T.η.app (X ⊗ Y) := by aesop_cat
  mul_comm (X Y : C) : ((𝟙 X) ⊗ T.μ.app Y) ≫ leftStr.app (X, Y)
      = leftStr.app (X, T.obj Y) ≫ T.map (leftStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

/- This is probably false: it probably needs s-finite measures, since
`measurable_measure_prod_mk_left` (the case where p.2 is constant) requires an s-finite measure.
Why though? Can we find a counter-example if we don't have the s-finite assumption? -/
lemma measurable_measure_prod_mk_left' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × Measure β ↦ p.2 (Prod.mk p.1 ⁻¹' s) := by
  sorry

-- The swap is here to be able to use prod_apply (since the dirac is s-finite).
-- This is probably false, it probably needs s-finite measures (in that case, remove the swap).
lemma Measure.measurable_dirac_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (p : α × Measure β) ↦ (p.2.prod (Measure.dirac p.1)).map Prod.swap) := by
  refine' Measure.measurable_of_measurable_coe _ fun s hs => _
  simp_rw [Measure.map_apply measurable_swap hs]
  simp_rw [Measure.prod_apply (measurable_swap hs)]
  have h_meas : ∀ x, MeasurableSet (Prod.mk x ⁻¹' (Prod.swap ⁻¹' s)) := by
    intro x
    exact measurable_prod_mk_left (measurable_swap hs)
  simp_rw [Measure.dirac_apply' _ (h_meas _)]
  have : ∀ b : α × Measure β, ∫⁻ x, (Prod.mk x ⁻¹' (Prod.swap ⁻¹' s)).indicator 1 b.1 ∂b.2
      = b.2 (Prod.mk b.1 ⁻¹' s) := by
    intro b
    change ∫⁻ x, (Prod.mk x ⁻¹' (Prod.swap ⁻¹' s)).indicator (fun _ ↦ 1) b.1 ∂b.2 = _
    classical
    simp_rw [Set.indicator_apply]
    simp only [Set.mem_preimage, Prod.swap_prod_mk]
    have : ∫⁻ x, if (b.1, x) ∈ s then 1 else 0 ∂b.2
        = ∫⁻ x, (Prod.mk b.1 ⁻¹' s).indicator 1 x ∂b.2 := by
      simp_rw [Set.indicator_apply]
      simp
    rw [this, lintegral_indicator_one]
    exact measurable_prod_mk_left hs
  simp_rw [this]
  exact measurable_measure_prod_mk_left' hs

-- this is probably false, because `Measure.measurable_dirac_prod` probably needs s-finite measures.
noncomputable
instance : LeftStrong MeasCat.Giry where
  leftStr := {
    app := fun P ↦ ⟨fun p ↦ (p.2.prod (Measure.dirac p.1)).map Prod.swap,
      Measure.measurable_dirac_prod⟩
    naturality := fun (P₁, P₂) (Q₁, Q₂) f ↦ by
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, Functor.comp_map,
        Functor.prod_map, Functor.id_map, tensor_map]
      ext x
      rcases x with ⟨x, p⟩
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, comp_apply]
      -- the lines below should be replaced by new simp lemmas?
      simp only [MeasCat.Giry, MeasCat.Measure, Functor.id_obj, Functor.comp_obj, Functor.prod_obj,
        tensor_obj]
      sorry }

class Affine {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  affine : T.obj (𝟙_ C) ≅ 𝟙_ C := by aesop_cat

-- The Giry monad is not affine unless we restrict the measures to probability measures.

end CommutativeMonad

section MarkovCategory

class CopyDiscardCategory (C : Type u) [𝒞 : Category.{u} C] [MonoidalCategory C]
    extends SymmetricCategory C where
  -- todo: copy, del

class MarkovCategory (C : Type u) [𝒞 : Category.{u} C] [MonoidalCategory C]
    extends CopyDiscardCategory C where
  -- todo: affine

end MarkovCategory

-- todo: not really Stoch because it contains all kernels, not only Markov kernels
def Stoch := Kleisli MeasCat.Giry

/- TODO: prove that the Kleisli category of a commutative monad on a cartesian symmetric monoidal
category is a symmetric monoidal category (and a copy-discard category).
If furthermore the monad is affine, the Kleisli category is a Markov category. -/

def SFiniteCat : Type (u + 1) := Bundled MeasurableSpace

namespace SFiniteCat

instance : CoeSort SFiniteCat (Type*) := Bundled.coeSort

instance (X : SFiniteCat) : MeasurableSpace X := X.str

/-- Construct a bundled `SFiniteCat` from the underlying type and the typeclass. -/
def of (α : Type u) [ms : MeasurableSpace α] : SFiniteCat := ⟨α, ms⟩

@[simp]
theorem coe_of (X : Type u) [MeasurableSpace X] : (of X : Type u) = X := rfl

noncomputable
instance : Category SFiniteCat where
  Hom X Y := SFiniteKernel X Y
  id X := SFiniteKernel.id X
  comp := SFiniteKernel.comp
  assoc := SFiniteKernel.comp_assoc

noncomputable
instance : LargeCategory SFiniteCat where

--instance : ConcreteCategory SFiniteCat := by
--  unfold SFiniteCat
--  infer_instance

instance : Inhabited SFiniteCat := ⟨SFiniteCat.of Empty⟩

noncomputable
instance : MonoidalCategoryStruct SFiniteCat where
  tensorObj X Y := SFiniteCat.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := SFiniteKernel.parallelComp (SFiniteKernel.id X) κ
  whiskerRight κ Y := SFiniteKernel.parallelComp κ (SFiniteKernel.id Y)
  tensorHom κ η := SFiniteKernel.parallelComp κ η
  tensorUnit := SFiniteCat.of Unit
  associator X Y Z := sorry
  leftUnitor X := sorry
  rightUnitor X := sorry

noncomputable
instance : MonoidalCategory SFiniteCat where
  tensorHom_def κ η := (SFiniteKernel.parallelComp_left_comp_right κ η).symm
  tensor_id X Y := SFiniteKernel.parallelComp_id
  tensor_comp κ η κ' η' := SFiniteKernel.parallelComp_comp κ η κ' η'
  whiskerLeft_id X Y := SFiniteKernel.parallelComp_id
  id_whiskerRight X Y := SFiniteKernel.parallelComp_id
  associator_naturality κ η ξ := sorry
  leftUnitor_naturality κ := sorry
  rightUnitor_naturality κ := sorry
  pentagon W X Y Z := sorry
  triangle X Y := sorry

noncomputable
def swapIso (X Y : SFiniteCat) :
    (MonoidalCategory.tensorObj X Y) ≅ (MonoidalCategory.tensorObj Y X) where
  hom := sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

noncomputable
instance : BraidedCategory SFiniteCat where
  braiding X Y := sorry
  braiding_naturality_right X Y Z κ := sorry
  braiding_naturality_left κ Z := sorry
  hexagon_forward X Y Z := sorry
  hexagon_reverse X Y Z := sorry

noncomputable
instance : SymmetricCategory SFiniteCat where
  symmetry X Y := sorry

end SFiniteCat

end ProbabilityTheory
