/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.MeasureTheory.Category.MeasCat

/-!

# Categories of measurable spaces and Kernels

-/

open CategoryTheory MonoidalCategory Limits

universe u v

namespace MeasCat

/-! `MeasCat` is a cartesian symmetric monoidal category. -/

-- TODO: should we replace the definition of `MeasCat` with one using
-- `CategoryTheory.MonoidalCategory.MonoidalPredicate`?

@[simps]
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
