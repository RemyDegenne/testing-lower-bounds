/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Monoidal
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monad.Kleisli
import Mathlib.MeasureTheory.Category.MeasCat
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!

# Categories of measurable spaces and kernels

-/

open MeasureTheory CategoryTheory MonoidalCategory Limits

open scoped ENNReal

namespace MeasureTheory.SFiniteMeasure

variable {Ω : Type*} [MeasurableSpace Ω]

def _root_.MeasureTheory.SFiniteMeasure (Ω : Type*) [MeasurableSpace Ω] : Type _ :=
  { μ : Measure Ω // SFinite μ }

@[coe]
def toMeasure : SFiniteMeasure Ω → Measure Ω := Subtype.val

instance instCoe : Coe (SFiniteMeasure Ω) (MeasureTheory.Measure Ω) where
  coe := toMeasure

instance isFiniteMeasure (μ : SFiniteMeasure Ω) : SFinite (μ : Measure Ω) := μ.prop

@[simp]
theorem val_eq_toMeasure (ν : SFiniteMeasure Ω) : ν.val = (ν : Measure Ω) :=
  rfl

theorem toMeasure_injective : Function.Injective ((↑) : SFiniteMeasure Ω → Measure Ω) :=
  Subtype.coe_injective

instance instFunLike : FunLike (SFiniteMeasure Ω) (Set Ω) ℝ≥0∞ where
  coe μ s := (μ : Measure Ω) s
  coe_injective' _ _ h := toMeasure_injective $ Measure.ext fun s _ ↦  congr_fun h s

lemma coeFn_def (μ : SFiniteMeasure Ω) : μ = fun s ↦ (μ : Measure Ω) s := rfl

lemma coeFn_mk (μ : Measure Ω) (hμ) :
    DFunLike.coe (F := SFiniteMeasure Ω) ⟨μ, hμ⟩ = fun s ↦ μ s := rfl

@[simp]
lemma mk_apply (μ : Measure Ω) (hμ) (s : Set Ω) :
    DFunLike.coe (F := SFiniteMeasure Ω) ⟨μ, hμ⟩ s = μ s := rfl

theorem apply_mono (μ : SFiniteMeasure Ω) {s₁ s₂ : Set Ω} (h : s₁ ⊆ s₂) : μ s₁ ≤ μ s₂ :=
  (μ : Measure Ω).mono h

instance instZero : Zero (SFiniteMeasure Ω) where zero := ⟨0, inferInstance⟩

@[simp, norm_cast] lemma coeFn_zero : ⇑(0 : SFiniteMeasure Ω) = 0 := rfl

@[ext]
theorem eq_of_forall_toMeasure_apply_eq (μ ν : SFiniteMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → (μ : Measure Ω) s = (ν : Measure Ω) s) : μ = ν := by
  apply Subtype.ext
  ext s s_mble
  exact h s s_mble

theorem eq_of_forall_apply_eq (μ ν : SFiniteMeasure Ω)
    (h : ∀ s : Set Ω, MeasurableSet s → μ s = ν s) : μ = ν := by
  ext s s_mble
  exact h s s_mble

instance instInhabited : Inhabited (SFiniteMeasure Ω) := ⟨0⟩

noncomputable
instance instAdd : Add (SFiniteMeasure Ω) where add μ ν := ⟨μ + ν, inferInstance⟩

variable {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]

instance instSMul : SMul R (SFiniteMeasure Ω) where
  smul (c : R) μ := ⟨c • (μ : Measure Ω), sorry⟩

@[simp, norm_cast]
theorem toMeasure_zero : ((↑) : SFiniteMeasure Ω → Measure Ω) 0 = 0 := rfl

-- Porting note: with `simp` here the `coeFn` lemmas below fall prey to `simpNF`: the LHS simplifies
@[norm_cast]
theorem toMeasure_add (μ ν : SFiniteMeasure Ω) : ↑(μ + ν) = (↑μ + ↑ν : Measure Ω) := rfl

@[simp, norm_cast]
theorem toMeasure_smul (c : R) (μ : SFiniteMeasure Ω) : ↑(c • μ) = c • (μ : Measure Ω) := rfl

@[simp, norm_cast]
theorem coeFn_add (μ ν : SFiniteMeasure Ω) : ⇑(μ + ν) = ⇑μ + ⇑ν := by
  funext
  simp only [Pi.add_apply]
  norm_cast

@[simp, norm_cast]
theorem coeFn_smul (c : R) (μ : SFiniteMeasure Ω) : ⇑(c • μ) = c • ⇑μ := rfl

noncomputable
instance instAddCommMonoid : AddCommMonoid (SFiniteMeasure Ω) :=
  toMeasure_injective.addCommMonoid (↑) toMeasure_zero toMeasure_add fun _ _ => toMeasure_smul _ _

/-- Coercion is an `AddMonoidHom`. -/
@[simps]
def toMeasureAddMonoidHom : SFiniteMeasure Ω →+ Measure Ω where
  toFun := (↑)
  map_zero' := toMeasure_zero
  map_add' := toMeasure_add

noncomputable
instance {Ω : Type*} [MeasurableSpace Ω] : Module ℝ≥0∞ (SFiniteMeasure Ω) :=
  Function.Injective.module _ toMeasureAddMonoidHom toMeasure_injective toMeasure_smul

@[simp]
theorem smul_apply (c : R) (μ : SFiniteMeasure Ω) (s : Set Ω) :
    (c • μ) s = c • μ s := by
  rw [coeFn_smul, Pi.smul_apply]

instance : MeasurableSpace (SFiniteMeasure Ω) := Subtype.instMeasurableSpace

end MeasureTheory.SFiniteMeasure

instance {Ω : Type*} [MeasurableSpace Ω] : MeasurableSpace (FiniteMeasure Ω) :=
  Subtype.instMeasurableSpace

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

end ProbabilityTheory

universe u v

namespace MeasCat

/-! `MeasCat` is a cartesian symmetric monoidal category. -/

-- TODO: should we replace the definition of `MeasCat` with one using
-- `CategoryTheory.MonoidalCategory.MonoidalPredicate`?

def terminalLimitCone : Limits.LimitCone (Functor.empty MeasCat) where
  cone :=
    { pt := MeasCat.of PUnit
      π := (Functor.uniqueFromEmpty _).hom }
  isLimit :=
    { lift := fun _ => ⟨fun _ ↦ PUnit.unit, measurable_const⟩
      fac := fun _ => by rintro ⟨⟨⟩⟩
      uniq := fun _ _ _ => rfl }

def binaryProductCone (X Y : MeasCat.{u}) : BinaryFan X Y :=
  CategoryTheory.Limits.BinaryFan.mk (P := MeasCat.of (X × Y))
    ⟨Prod.fst, measurable_fst⟩ ⟨Prod.snd, measurable_snd⟩

@[simp]
lemma binaryProductCone_fst (X Y : MeasCat) :
    (binaryProductCone X Y).fst = ⟨Prod.fst, measurable_fst⟩ := rfl

@[simp]
theorem binaryProductCone_snd (X Y : MeasCat) :
    (binaryProductCone X Y).snd = ⟨Prod.snd, measurable_snd⟩ := rfl

attribute [local instance] ConcreteCategory.instFunLike

@[simps]
def binaryProductLimit (X Y : MeasCat) : IsLimit (binaryProductCone X Y) where
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
    exact Prod.ext rfl rfl

@[simps]
def binaryProductLimitCone (X Y : MeasCat) : LimitCone (pair X Y) :=
  ⟨binaryProductCone X Y, binaryProductLimit X Y⟩

/-- This gives in particular a `SymmetricCategory` instance.
That is, `MeasCat` is a cartesian symmetric monoidal category. -/
@[simps]
instance : ChosenFiniteProducts MeasCat where
  product X Y := binaryProductLimitCone X Y
  terminal := terminalLimitCone

@[simp]
lemma tensor_apply {W X Y Z : MeasCat} (f : W ⟶ X) (g : Y ⟶ Z)
    (p : @tensorObj MeasCat _ _ W Y) :
    (f ⊗ g) p = (f p.1, g p.2) := rfl

@[simp]
lemma whiskerLeft_apply (X : MeasCat) {Y Z : MeasCat} (f : Y ⟶ Z)
    (p : @tensorObj MeasCat _ _ X Y) :
    (X ◁ f) p = (p.1, f p.2) := rfl

@[simp]
lemma whiskerRight_apply {Y Z : MeasCat} (f : Y ⟶ Z) (X : MeasCat)
    (p : @tensorObj MeasCat _ _ Y X) :
    (f ▷ X) p = (f p.1, p.2) :=  rfl

@[simp]
lemma leftUnitor_hom_apply {X : MeasCat} {x : X} {p : PUnit} :
    (λ_ X).hom (p, x) = x := rfl

@[simp]
lemma leftUnitor_inv_apply {X : MeasCat} {x : X} :
    ((λ_ X).inv : X ⟶ 𝟙_ MeasCat ⊗ X) x = (PUnit.unit, x) := rfl

@[simp]
lemma rightUnitor_hom_apply {X : MeasCat} {x : X} {p : PUnit} :
    (ρ_ X).hom (x, p) = x := rfl

@[simp]
lemma rightUnitor_inv_apply {X : MeasCat} {x : X} :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ MeasCat) x = (x, PUnit.unit) := rfl

@[simp]
lemma associator_hom_apply {X Y Z : MeasCat} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).hom ((x, y), z) = (x, (y, z)) := rfl

@[simp]
lemma associator_inv_apply {X Y Z : MeasCat.{u}} {x : X} {y : Y} {z : Z} :
    (α_ X Y Z).inv (x, (y, z)) = ((x, y), z) := rfl

end MeasCat

namespace CategoryTheory

section CommutativeMonad

class LeftStrong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  leftStr : ((𝟭 C : C ⥤ C).prod (T : C ⥤ C)) ⋙ (tensor C) ⟶ (tensor C) ⋙ (T : C ⥤ C)
  left_unit_comp (X : C) : (λ_ (T.obj X)).inv ≫ leftStr.app (𝟙_ C, X)
      = T.map (λ_ X).inv := by aesop_cat
  left_assoc (X Y Z : C) : leftStr.app (X ⊗ Y, Z) ≫ T.map (α_ X Y Z).hom
      = (α_ X Y (T.obj Z)).hom ≫ (X ◁ leftStr.app (Y, Z)) ≫ leftStr.app (X, Y ⊗ Z) := by
    aesop_cat
  left_unit_comm (X Y : C) : (X ◁ T.η.app Y) ≫ leftStr.app (X, Y) = T.η.app (X ⊗ Y) := by
    aesop_cat
  left_mul_comm (X Y : C) : (X ◁ T.μ.app Y) ≫ leftStr.app (X, Y)
      = leftStr.app (X, T.obj Y) ≫ T.map (leftStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

class RightStrong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  rightStr : ((T : C ⥤ C).prod (𝟭 C : C ⥤ C)) ⋙ (tensor C) ⟶ (tensor C) ⋙ (T : C ⥤ C)
  right_unit_comp (X : C) : (ρ_ (T.obj X)).inv ≫ rightStr.app (X, 𝟙_ C)
      = T.map (ρ_ X).inv := by aesop_cat
  right_assoc (X Y Z : C) : rightStr.app (X, Y ⊗ Z) ≫ T.map (α_ X Y Z).inv
      = (α_ (T.obj X) Y Z).inv ≫ (rightStr.app (X, Y) ▷ Z) ≫ rightStr.app (X ⊗ Y, Z) := by
    aesop_cat
  right_unit_comm (X Y : C) : (T.η.app X ▷ Y) ≫ rightStr.app (X, Y) = T.η.app (X ⊗ Y) := by
    aesop_cat
  right_mul_comm (X Y : C) : (T.μ.app X ▷ Y) ≫ rightStr.app (X, Y)
      = rightStr.app (T.obj X, Y) ≫ T.map (rightStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

class Strong {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C)
    extends LeftStrong T, RightStrong T where
  left_right (X Y Z : C) : (leftStr.app (X, Y) ▷ Z) ≫ rightStr.app (X ⊗ Y, Z)
    = (α_ X (T.obj Y) Z).hom ≫ (X ◁ rightStr.app (Y, Z)) ≫ leftStr.app (X, Y ⊗ Z)
      ≫ T.map (α_ _ _ _).inv := by aesop_cat

class CommutativeMonad {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C)
    extends Strong T where
  comm (X Y : C) : leftStr.app (T.obj X, Y) ≫ T.map (rightStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y)
    = rightStr.app (X, T.obj Y) ≫ T.map (leftStr.app (X, Y)) ≫ T.μ.app (X ⊗ Y) := by aesop_cat

section LeftRightStrength

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

def Monad.lStr (T : Monad C) [LeftStrong T] (X Y : C) :
    X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y) :=
  LeftStrong.leftStr.app (X, Y)

@[simp]
lemma Monad.lStr_unit_comp (T : Monad C) [LeftStrong T] (X : C) :
    (λ_ (T.obj X)).inv ≫ T.lStr (𝟙_ C) X = T.map (λ_ X).inv :=
  LeftStrong.left_unit_comp _

lemma Monad.lStr_assoc (T : Monad C) [LeftStrong T] (X Y Z : C) :
    T.lStr (X ⊗ Y) Z ≫ T.map (α_ X Y Z).hom
      = (α_ X Y (T.obj Z)).hom ≫ (X ◁ T.lStr Y Z) ≫ T.lStr X (Y ⊗ Z) :=
  LeftStrong.left_assoc _ _ _

@[simp]
lemma Monad.lStr_unit_comm (T : Monad C) [LeftStrong T] (X Y : C) :
    (X ◁ T.η.app Y) ≫ T.lStr X Y = T.η.app (X ⊗ Y) :=
  LeftStrong.left_unit_comm _ _

lemma Monad.lStr_mul_comm (T : Monad C) [LeftStrong T] (X Y : C) :
    (X ◁ T.μ.app Y) ≫ T.lStr X Y
      = T.lStr X (T.obj Y) ≫ T.map (T.lStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  LeftStrong.left_mul_comm _ _

lemma Monad.lStr_naturality (T : Monad C) [LeftStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f : (X₁, X₂) ⟶ (Y₁, Y₂)) :
    (f.1 ⊗ T.map f.2) ≫ T.lStr Y₁ Y₂ = T.lStr X₁ X₂ ≫ T.map (f.1 ⊗ f.2) := by
  simpa using LeftStrong.leftStr.naturality _

lemma Monad.lStr_naturality' (T : Monad C) [LeftStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (f₁ ⊗ T.map f₂) ≫ T.lStr Y₁ Y₂ = T.lStr X₁ X₂ ≫ T.map (f₁ ⊗ f₂) := T.lStr_naturality (f₁, f₂)

lemma Monad.lStr_naturality_id_left (T : Monad C) [LeftStrong T] {X Y₂ : C} (Y₁ : C)
    (f : X ⟶ Y₂) :
    (Y₁ ◁ T.map f) ≫ T.lStr Y₁ Y₂ = T.lStr Y₁ X ≫ T.map (Y₁ ◁ f) := by
  simpa using T.lStr_naturality (𝟙 Y₁, f)

lemma Monad.lStr_naturality_id_right (T : Monad C) [LeftStrong T] {X Y₁ : C}
    (f : X ⟶ Y₁) (Y₂ : C) :
    (f ▷ T.obj Y₂) ≫ T.lStr Y₁ Y₂ = T.lStr X Y₂ ≫ T.map (f ▷ Y₂) := by
  simpa using T.lStr_naturality (f, 𝟙 Y₂)

def Monad.rStr (T : Monad C) [RightStrong T] (X Y : C) :
    T.obj X ⊗ Y ⟶ T.obj (X ⊗ Y) :=
  RightStrong.rightStr.app (X, Y)

@[simp]
lemma Monad.rStr_unit_comp (T : Monad C) [RightStrong T] (X : C) :
    (ρ_ (T.obj X)).inv ≫ T.rStr X (𝟙_ C) = T.map (ρ_ X).inv :=
  RightStrong.right_unit_comp _

lemma Monad.rStr_assoc (T : Monad C) [RightStrong T] (X Y Z : C) :
    T.rStr X (Y ⊗ Z) ≫ T.map (α_ X Y Z).inv
      = (α_ (T.obj X) Y Z).inv ≫ (T.rStr X Y ▷ Z) ≫ T.rStr (X ⊗ Y) Z :=
  RightStrong.right_assoc _ _ _

@[simp]
lemma Monad.rStr_unit_comm (T : Monad C) [RightStrong T] (X Y : C) :
    T.η.app X ▷ Y ≫ T.rStr X Y = T.η.app (X ⊗ Y) :=
  RightStrong.right_unit_comm _ _

lemma Monad.rStr_mul_comm (T : Monad C) [RightStrong T] (X Y : C) :
    T.μ.app X ▷ Y ≫ T.rStr X Y
      = T.rStr (T.obj X) Y ≫ T.map (T.rStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  RightStrong.right_mul_comm _ _

lemma Monad.rStr_naturality (T : Monad C) [RightStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f : (X₁, X₂) ⟶ (Y₁, Y₂)) :
    (T.map f.1 ⊗ f.2) ≫ T.rStr Y₁ Y₂ = T.rStr X₁ X₂ ≫ T.map (f.1 ⊗ f.2) := by
  simpa using RightStrong.rightStr.naturality _

lemma Monad.rStr_naturality' (T : Monad C) [RightStrong T] {X₁ X₂ Y₁ Y₂ : C}
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) :
    (T.map f₁ ⊗ f₂) ≫ T.rStr Y₁ Y₂ = T.rStr X₁ X₂ ≫ T.map (f₁ ⊗ f₂) := T.rStr_naturality (f₁, f₂)

lemma Monad.rStr_naturality_id_left (T : Monad C) [RightStrong T] {X Y₂ : C} (Y₁ : C)
    (f : X ⟶ Y₂) :
    (T.obj Y₁ ◁ f) ≫ T.rStr Y₁ Y₂ = T.rStr Y₁ X ≫ T.map (Y₁ ◁ f) := by
  simpa using T.rStr_naturality (𝟙 Y₁, f)

lemma Monad.rStr_naturality_id_right (T : Monad C) [RightStrong T] {X Y₁ : C}
    (f : X ⟶ Y₁) (Y₂ : C) :
    (T.map f ▷ Y₂) ≫ T.rStr Y₁ Y₂ = T.rStr X Y₂ ≫ T.map (f ▷ Y₂) := by
  simpa using T.rStr_naturality (f, 𝟙 Y₂)

def Monad.dStr (T : Monad C) [Strong T] (X Y : C) :
    T.obj X ⊗ T.obj Y ⟶ T.obj (X ⊗ Y) :=
  (T.lStr (T.obj X) Y) ≫ T.map (T.rStr X Y) ≫ T.μ.app (X ⊗ Y)

lemma Monad.lStr_rStr (T : Monad C) [Strong T] (X Y Z : C) :
    (T.lStr X Y ▷ Z) ≫ T.rStr (X ⊗ Y) Z
      = (α_ X (T.obj Y) Z).hom ≫ (X ◁ T.rStr Y Z) ≫ T.lStr X (Y ⊗ Z) ≫ T.map (α_ _ _ _).inv :=
  Strong.left_right _ _ _

lemma Monad.lStr_rStr_comm (T : Monad C) [CommutativeMonad T] (X Y : C) :
    T.lStr (T.obj X) Y ≫ T.map (T.rStr X Y) ≫ T.μ.app (X ⊗ Y)
      = T.rStr X (T.obj Y) ≫ T.map (T.lStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  CommutativeMonad.comm _ _

lemma Monad.dStr_eq (T : Monad C) [CommutativeMonad T] (X Y : C) :
    T.dStr X Y = T.rStr X (T.obj Y) ≫ T.map (T.lStr X Y) ≫ T.μ.app (X ⊗ Y) :=
  T.lStr_rStr_comm X Y

@[simp]
lemma Monad.unit_whiskerRight_dStr (T : Monad C) [Strong T] (X Y : C) :
    (T.η.app X ▷ T.obj Y) ≫ T.dStr X Y = T.lStr X Y := by
  simp only [dStr, Functor.id_obj]
  simp_rw [← Category.assoc]
  rw [T.lStr_naturality_id_right (T.η.app X) Y]
  suffices (T.map (T.η.app X ▷ Y) ≫ T.map (T.rStr X Y)) ≫ T.μ.app (X ⊗ Y) = 𝟙 _ by simp [this]
  rw [← T.map_comp]
  simp

@[simp]
lemma Monad.unit_whiskerLeft_dStr (T : Monad C) [CommutativeMonad T] (X Y : C) :
    (T.obj X ◁ T.η.app Y) ≫ T.dStr X Y = T.rStr X Y := by
  simp only [T.dStr_eq, Functor.id_obj]
  simp_rw [← Category.assoc]
  rw [T.rStr_naturality_id_left X (T.η.app Y)]
  suffices (T.map (X ◁ T.η.app Y) ≫ T.map (T.lStr X Y)) ≫ T.μ.app (X ⊗ Y) = 𝟙 _ by simp [this]
  rw [← T.map_comp]
  simp

@[simp]
lemma Monad.unit_dStr_left (T : Monad C) [Strong T] (X : C) {Y₁ Y₂ : C}
    (f : Y₁ ⟶ T.obj Y₂) :
    (T.η.app X ⊗ f) ≫ T.dStr X Y₂ = X ◁ f ≫ T.lStr X Y₂ := by
  simp [tensorHom_def']

@[simp]
lemma Monad.unit_dStr_right (T : Monad C) [CommutativeMonad T] (X : C) {Y₁ Y₂ : C}
    (f : Y₁ ⟶ T.obj Y₂) :
    (f ⊗ T.η.app X) ≫ T.dStr Y₂ X = f ▷ X ≫ T.rStr Y₂ X := by
  simp [tensorHom_def]

end LeftRightStrength

class Affine {C : Type u} [Category.{v} C] [MonoidalCategory C] (T : Monad C) where
  affine : T.obj (𝟙_ C) ≅ 𝟙_ C := by aesop_cat

-- The Giry monad is not affine unless we restrict the measures to probability measures.

end CommutativeMonad

section MarkovCategory

class CopyDiscardCategory (C : Type u) [𝒞 : Category.{u} C] [MonoidalCategory C]
    extends SymmetricCategory C where
  del (X : C) : X ⟶ 𝟙_ C
  copy (X : C) : X ⟶ X ⊗ X
  del_copy (X : C) : copy X ≫ (del X ▷ X) = (λ_ X).inv := by aesop_cat
  copy_del (X : C) : copy X ≫ (X ◁ del X) = (ρ_ X).inv := by aesop_cat
  copy_assoc (X : C) : copy X ≫ (X ◁ copy X) ≫ (α_ X X X).inv = copy X ≫ (copy X ▷ X) := by
    aesop_cat
  copy_braiding (X : C) : copy X ≫ (β_ X X).hom = copy X := by aesop_cat
  copy_tensor (X Y : C) :
    copy (X ⊗ Y) = (copy X ⊗ copy Y) ⊗≫ (𝟙 X ⊗ (β_ X Y).hom ⊗ 𝟙 Y) ≫ ⊗𝟙 := by aesop_cat
  del_tensor (X Y : C) : del (X ⊗ Y) = (del X ⊗ del Y) ≫ ⊗𝟙 := by aesop_cat
  copy_unit : copy (𝟙_ C) = ⊗𝟙 := by aesop_cat
  del_unit : del (𝟙_ C) = ⊗𝟙 := by aesop_cat

class MarkovCategory (C : Type u) [𝒞 : Category.{u} C] [MonoidalCategory C]
    extends CopyDiscardCategory C where
  /-- Every morphism is discardable. -/
  comp_del ⦃X Y : C⦄ (f : X ⟶ Y) : f ≫ del Y = del X := by aesop_cat

end MarkovCategory

section Kleisli

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {T : Monad C}

@[simp]
lemma todo {X Y : C} (f : X ⟶ T.obj Y) :
    T.η.app X ≫ T.map f ≫ T.μ.app Y = f := by
  have h := T.η.naturality f
  simp only [Functor.id_obj, Functor.id_map] at h
  rw [← Category.assoc, ← h, Category.assoc]
  simp

lemma Kleisli.comp_def {X Y Z : Kleisli T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = @CategoryStruct.comp C Category.toCategoryStruct _ _ _ f (T.map g) ≫ T.μ.app Z := by
  simp only [Category.assoc]
  rfl

instance (T : Monad C) [Strong T] :
    MonoidalCategoryStruct (Kleisli T) where
  tensorObj X Y := (Kleisli.Adjunction.toKleisli T).obj (X ⊗ Y)
  whiskerLeft X Y₁ Y₂ f :=
    ((T.η.app X ⊗ f) ≫ T.dStr X Y₂ : @tensorObj C _ _ X Y₁ ⟶ T.obj (X ⊗ Y₂))
  whiskerRight {X₁ X₂} f Y :=
    ((f ⊗ T.η.app Y) ≫ T.dStr X₂ Y : @tensorObj C _ _ X₁ Y ⟶ T.obj (X₂ ⊗ Y))
  tensorUnit := (Kleisli.Adjunction.toKleisli T).obj (𝟙_ C)
  associator X Y Z := (Kleisli.Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.associator C _ _ X Y Z)
  leftUnitor X := (Kleisli.Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.leftUnitor C _ _ X)
  rightUnitor X := (Kleisli.Adjunction.toKleisli T).mapIso
    (@MonoidalCategoryStruct.rightUnitor C _ _ X)

@[simp]
lemma Kleisli.wiskerLeft_id [Strong T] {X Y : Kleisli T} :
    X ◁ 𝟙 Y = 𝟙 (X ⊗ Y) := by
  suffices (T.η.app X ⊗ T.η.app Y) ≫ T.dStr X Y = T.η.app (X ⊗ Y) from this
  simp

@[simp]
lemma Kleisli.id_whiskerRight [Strong T] {X Y : Kleisli T} :
    𝟙 X ▷ Y = 𝟙 (X ⊗ Y) := by
  suffices (T.η.app X ⊗ T.η.app Y) ≫ T.dStr X Y = T.η.app (X ⊗ Y) from this
  simp

lemma Kleisli.tensorObj_def [Strong T] (X Y : Kleisli T) :
    X ⊗ Y = @tensorObj C _ _ X Y := rfl

@[simp]
lemma Kleisli.tensorHom_def [Strong T]
    {X₁ Y₁ X₂ Y₂ : Kleisli T} (f : X₁ ⟶ Y₁) (g: X₂ ⟶ Y₂) :
    f ⊗ g = (f ▷ X₂) ≫ (Y₁ ◁ g) := rfl

lemma Kleisli.whiskerLeft_def [Strong T] (X : Kleisli T) {Y₁ Y₂ : Kleisli T} (f : Y₁ ⟶ Y₂) :
    X ◁ f = (T.η.app X ⊗ f) ≫ T.dStr X Y₂ := rfl

lemma Kleisli.whiskerRight_def [Strong T] {X₁ X₂ : Kleisli T} (f : X₁ ⟶ X₂) (Y : Kleisli T) :
    f ▷ Y = ((f ⊗ T.η.app Y) ≫ T.dStr X₂ Y : @tensorObj C _ _ X₁ Y ⟶ T.obj (X₂ ⊗ Y)) := rfl

lemma Kleisli.tensorUnit_def [Strong T] :
    𝟙_ (Kleisli T) = (Kleisli.Adjunction.toKleisli T).obj (𝟙_ C) := rfl

lemma Kleisli.associator_def [Strong T] (X Y Z : Kleisli T) :
    α_ X Y Z = (Kleisli.Adjunction.toKleisli T).mapIso
      (@MonoidalCategoryStruct.associator C _ _ X Y Z) := rfl

lemma Kleisli.leftUnitor_def [Strong T] (X : Kleisli T) :
    λ_ X = (Kleisli.Adjunction.toKleisli T).mapIso
      (@MonoidalCategoryStruct.leftUnitor C _ _ X) := rfl

lemma Kleisli.rightUnitor_def [Strong T] (X : Kleisli T) :
    ρ_ X = (Kleisli.Adjunction.toKleisli T).mapIso
      (@MonoidalCategoryStruct.rightUnitor C _ _ X) := rfl

@[simp]
lemma Kleisli.whiskerLeft_comp [Strong T] (X : Kleisli T) {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) :
    X ◁ (f ≫ g) = (X ◁ f) ≫ (X ◁ g) := by
  simp only [comp_def, Category.assoc, whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
    MonoidalCategory.whiskerLeft_comp, Functor.map_comp]
  slice_rhs 2 3 => rw [← T.lStr_naturality_id_left]
  simp only [Category.assoc]
  rw [T.lStr_mul_comm]
  rfl

@[simp]
lemma Kleisli.comp_whiskerRight [CommutativeMonad T] {Y₁ Y₂ Y₃ : Kleisli T}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ Y₃) (X : Kleisli T) :
    (f ≫ g) ▷ X = f ▷ X ≫ g ▷ X := by
  simp only [comp_def, Category.assoc, whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight,
    MonoidalCategory.comp_whiskerRight, Functor.map_comp]
  slice_rhs 2 3 => rw [← T.rStr_naturality_id_right]
  simp only [Category.assoc]
  rw [T.rStr_mul_comm]
  rfl

lemma Kleisli.whisker_exchange [CommutativeMonad T] {W X Y Z : Kleisli T}
    (f : W ⟶ X) (g : Y ⟶ Z) :
    W ◁ g ≫ f ▷ Z = f ▷ Y ≫ X ◁ g := by
  simp only [whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left, whiskerRight_def,
    Monad.unit_dStr_right]
  simp only [comp_def, Functor.map_comp, ← Category.assoc]
  slice_rhs 2 3 => rw [← T.rStr_naturality_id_left]
  slice_rhs 1 2 => rw [← MonoidalCategory.whisker_exchange]
  slice_lhs 2 3 => rw [← T.lStr_naturality_id_right]
  simp only [Category.assoc]
  congr 2
  exact T.lStr_rStr_comm X Z

lemma todo' (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ T.η.app (X ⊗ 𝟙_ C ⊗ Y) ≫ T.map (X ◁ (λ_ Y).hom)
      = (ρ_ X).hom ▷ Y ≫ T.η.app (X ⊗ Y) := by
  have h := T.η.naturality
  simp only [Functor.id_obj, Functor.id_map] at h
  slice_lhs 2 3 => rw [← h]
  simp only [triangle_assoc]

instance [CommutativeMonad T] : MonoidalCategory (Kleisli T) where
  tensor_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ := by
    simp only [Kleisli.tensorHom_def, Kleisli.comp_whiskerRight, Kleisli.whiskerLeft_comp,
      Category.assoc]
    slice_lhs 2 3 => rw [← Kleisli.whisker_exchange]
    simp
  associator_naturality f₁ f₂ f₃ := by
    simp only [Kleisli.tensorObj_def, Kleisli.tensorHom_def, Kleisli.comp_whiskerRight,
      Category.assoc, Kleisli.associator_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map,
      Kleisli.whiskerLeft_comp]
    simp only [Kleisli.whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight, Category.assoc,
      Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left, whisker_assoc,
      tensor_whiskerLeft, whiskerRight_tensor, MonoidalCategory.whiskerLeft_comp]
    simp only [Kleisli.comp_def, Functor.map_comp, Category.assoc, Monad.right_unit,
      Category.comp_id]
    have h1 := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at h1
    sorry
  leftUnitor_naturality {X Y} f := by
    simp only [Kleisli.whiskerLeft_def, Monad.unit_dStr_left, Kleisli.leftUnitor_def,
      Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
      Category.assoc, Monad.right_unit, Category.comp_id]
    simp only [Kleisli.tensorUnit_def, Kleisli.Adjunction.toKleisli_obj, id_whiskerLeft,
      Category.assoc, Iso.cancel_iso_hom_left]
    slice_lhs 2 3 => rw [T.lStr_unit_comp Y]
    rw [← T.map_comp]
    simp
  rightUnitor_naturality {X Y} f := by
    simp only [Kleisli.whiskerRight_def, Monad.unit_dStr_right, Kleisli.rightUnitor_def,
      Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
      Category.assoc, Monad.right_unit, Category.comp_id, todo]
    simp only [Kleisli.tensorUnit_def, Kleisli.Adjunction.toKleisli_obj,
      MonoidalCategory.whiskerRight_id, Category.assoc, Iso.cancel_iso_hom_left]
    slice_lhs 2 3 => rw [T.rStr_unit_comp Y]
    rw [← T.map_comp]
    simp
  pentagon W X Y Z := by
    simp only [Kleisli.associator_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map]
    simp only [Kleisli.whiskerRight_def, Kleisli.whiskerLeft_def, Functor.id_obj]
    simp only [Kleisli.tensorObj_def, Monad.unit_dStr_right, comp_whiskerRight, Category.assoc,
      Monad.rStr_unit_comm, Monad.unit_dStr_left, MonoidalCategory.whiskerLeft_comp,
      Monad.lStr_unit_comm, Kleisli.comp_def, Functor.map_comp, Monad.right_unit, Category.comp_id]
    have h := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at h
    slice_rhs 2 3 => rw [← h]
    slice_lhs 1 2 => rw [h]
    slice_lhs 2 3 => rw [← T.map_comp]
    slice_lhs 2 3 => rw [← T.map_comp]
    rw [← T.map_comp]
    rw [todo]
    simp only [Category.assoc]
    rw [← h]
    simp only [pentagon_assoc]
  triangle X Y := by
    simp only [Kleisli.associator_def, Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map,
      Kleisli.leftUnitor_def, Kleisli.rightUnitor_def]
    simp only [Kleisli.tensorUnit_def, Kleisli.Adjunction.toKleisli_obj]
    simp only [Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      MonoidalCategory.whiskerLeft_comp, Category.assoc, Monad.lStr_unit_comm, Kleisli.comp_def,
      Functor.map_comp, Kleisli.whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight,
      Monad.rStr_unit_comm]
    simp only [Kleisli.tensorObj_def, Monad.right_unit, Category.comp_id]
    exact todo' _ _

@[simp] -- todo: not provable and should be turned into a class?
lemma Monad.lStr_comp_braiding [SymmetricCategory C] [CommutativeMonad T] (X Y : C) :
    T.lStr X Y ≫ T.map (β_ X Y).hom = (β_ X (T.obj Y)).hom ≫ T.rStr Y X := by
  sorry

@[simp] -- todo: not provable and should be turned into a class?
lemma Monad.rStr_comp_braiding [SymmetricCategory C] [CommutativeMonad T] (X Y : C) :
    T.rStr X Y ≫ T.map (β_ X Y).hom = (β_ (T.obj X) Y).hom ≫ T.lStr Y X := by
  sorry

instance [SymmetricCategory C] [CommutativeMonad T] : BraidedCategory (Kleisli T) where
  braiding X Y := (Kleisli.Adjunction.toKleisli T).mapIso
    (@BraidedCategory.braiding C _ _ _ X Y)
  braiding_naturality_right X Y Z f := by
    simp only [Kleisli.tensorObj_def, Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
      Category.assoc, Monad.right_unit, Category.comp_id, Kleisli.whiskerRight_def,
      Monad.unit_dStr_right]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_rhs 2 3 => rw [← hη]
    slice_rhs 1 2 => rw [← BraidedCategory.braiding_naturality_right]
    simp
  braiding_naturality_left {X Y} f Z := by
    simp only [Kleisli.tensorObj_def, Kleisli.whiskerRight_def, Monad.unit_dStr_right,
      Functor.mapIso_hom, Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp,
      Category.assoc, Monad.right_unit, Category.comp_id, Kleisli.whiskerLeft_def, Functor.id_obj,
      Monad.unit_dStr_left]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_rhs 2 3 => rw [← hη]
    slice_rhs 1 2 => rw [← BraidedCategory.braiding_naturality_left]
    simp
  hexagon_forward X Y Z := by
    simp only [Kleisli.tensorObj_def, Kleisli.associator_def, Functor.mapIso_hom,
      Kleisli.Adjunction.toKleisli_map, BraidedCategory.braiding_tensor_right, Category.assoc,
      Kleisli.comp_def, Functor.map_comp, Monad.right_unit, Category.comp_id,
      Kleisli.whiskerRight_def, Monad.unit_dStr_right, comp_whiskerRight, Monad.rStr_unit_comm,
      Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      MonoidalCategory.whiskerLeft_comp, Monad.lStr_unit_comm]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_lhs 1 2 => rw [hη]
    slice_lhs 2 3 => rw [← T.map_comp, Iso.hom_inv_id, Functor.map_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 5 6 => rw [← T.map_comp, hη, T.map_comp]
    slice_lhs 6 7 => rw [← T.map_comp, ← T.map_comp, Iso.inv_hom_id]
    simp only [Functor.map_id, Category.id_comp, Monad.right_unit, Category.comp_id]
    simp_rw [← T.map_comp, ← @BraidedCategory.hexagon_forward C _ _ _ X Y Z]
    slice_rhs 1 2 => rw [hη]
    simp only [BraidedCategory.braiding_tensor_right, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, Iso.hom_inv_id_assoc, Functor.map_comp]
    congr 3
    slice_rhs 1 2 => rw [← T.map_comp, ← hη]
    simp
  hexagon_reverse X Y Z := by
    simp only [Kleisli.tensorObj_def, Kleisli.associator_def, Functor.mapIso_inv,
      Kleisli.Adjunction.toKleisli_map, Functor.mapIso_hom, BraidedCategory.braiding_tensor_left,
      Category.assoc, Kleisli.comp_def, Functor.map_comp, Monad.right_unit, Category.comp_id,
      Kleisli.whiskerLeft_def, Functor.id_obj, Monad.unit_dStr_left,
      MonoidalCategory.whiskerLeft_comp, Monad.lStr_unit_comm, Kleisli.whiskerRight_def,
      Monad.unit_dStr_right, comp_whiskerRight, Monad.rStr_unit_comm]
    have hη := T.η.naturality
    simp only [Functor.id_obj, Functor.id_map] at hη
    slice_lhs 1 2 => rw [hη]
    slice_lhs 2 3 => rw [← T.map_comp, Iso.inv_hom_id, Functor.map_id]
    simp only [Category.id_comp, Category.assoc]
    slice_lhs 5 6 => rw [← T.map_comp, hη, T.map_comp]
    slice_lhs 6 7 => rw [← T.map_comp, ← T.map_comp, Iso.hom_inv_id]
    simp only [Functor.map_id, Category.id_comp, Monad.right_unit, Category.comp_id]
    simp_rw [← T.map_comp, ← @BraidedCategory.hexagon_reverse C _ _ _ X Y Z]
    slice_rhs 1 2 => rw [hη]
    simp only [BraidedCategory.braiding_tensor_left, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.inv_hom_id_assoc, Functor.map_comp]
    congr 3
    slice_rhs 1 2 => rw [← T.map_comp, ← hη]
    simp

lemma Kleisli.braiding_def [SymmetricCategory C] [CommutativeMonad T] (X Y : Kleisli T) :
    β_ X Y = (Kleisli.Adjunction.toKleisli T).mapIso (@BraidedCategory.braiding C _ _ _ X Y) := rfl

instance [SymmetricCategory C] [CommutativeMonad T] : SymmetricCategory (Kleisli T) where
  symmetry X Y := by
    simp only [Kleisli.tensorObj_def, Kleisli.braiding_def, Functor.mapIso_hom,
      Kleisli.Adjunction.toKleisli_map, Kleisli.comp_def, Functor.map_comp, Category.assoc,
      Monad.right_unit, Category.comp_id]
    rw [← T.η.naturality]
    simp only [Functor.id_obj, Functor.id_map, SymmetricCategory.symmetry_assoc]
    rfl

end Kleisli

end CategoryTheory

namespace ProbabilityTheory

/- This is probably false: it probably needs s-finite measures, since
`measurable_measure_prod_mk_left` (the case where p.2 is constant) requires an s-finite measure.
Why though? Can we find a counter-example if we don't have the s-finite assumption? -/
lemma measurable_measure_prod_mk_left' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × Measure β ↦ p.2 (Prod.mk p.1 ⁻¹' s) := by
  sorry

lemma measurable_measure_prod_mk_left'' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    Measurable fun p : α × SFiniteMeasure β ↦ p.2 (Prod.mk p.1 ⁻¹' s) := by
  sorry

-- This is probably false, it probably needs s-finite measures.
lemma Measure.measurable_map_prod_mk {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] :
    Measurable (fun (p : α × Measure β) ↦ p.2.map (Prod.mk p.1)) := by
  refine' Measure.measurable_of_measurable_coe _ fun s hs => _
  simp_rw [Measure.map_apply measurable_prod_mk_left hs]
  exact measurable_measure_prod_mk_left' hs

-- this is probably false, because `Measure.measurable_map_prod_mk` probably needs s-finite measures.
noncomputable
instance : LeftStrong MeasCat.Giry where
  leftStr := {
    app := fun P ↦ ⟨fun p ↦ p.2.map (Prod.mk p.1), Measure.measurable_map_prod_mk⟩
    naturality := fun (P₁, P₂) (Q₁, Q₂) f ↦ by
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, Functor.comp_map,
        Functor.prod_map, Functor.id_map, tensor_map]
      simp [MeasCat.Giry, MeasCat.Measure] -- todo: add API
      ext x
      simp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj, tensor_obj, comp_apply,
        MeasCat.tensor_apply]
      -- up to the weird types: rw [Measure.map_map] twice should do it
      sorry }

end ProbabilityTheory

-- todo: not really Stoch because it contains all kernels, not only Markov kernels
def Stoch := Kleisli MeasCat.Giry

/- TODO: prove that the Kleisli category of a commutative monad on a cartesian symmetric monoidal
category is a symmetric monoidal category (and a copy-discard category).
If furthermore the monad is affine, the Kleisli category is a Markov category. -/

namespace ProbabilityTheory

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
