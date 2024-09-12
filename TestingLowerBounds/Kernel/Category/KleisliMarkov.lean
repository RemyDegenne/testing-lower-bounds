/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import TestingLowerBounds.Kernel.Category.Kleisli
import TestingLowerBounds.Kernel.Category.Markov

/-!

# Markov category structure of a Kleisli category

-/

open CategoryTheory MonoidalCategory

universe u v

namespace CategoryTheory

namespace Kleisli

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {T : Monad C}

lemma Adjunction.toKleisli.map_tensorHom [SymmetricCategory C] [SymmetricMonad T]
    (X₁ X₂ Y₁ Y₂ : C) (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (toKleisli T).map (f ⊗ g) = (toKleisli T).map f ⊗ (toKleisli T).map g := by
  simp only [toKleisli_obj, toKleisli_map, tensorHom_def, whiskerRight_def, Monad.unit_dStr_right,
    MonoidalCategory.comp_whiskerRight, Category.assoc, Monad.rStr_unit_comm, whiskerLeft_def,
    Functor.id_obj, Monad.unit_dStr_left, MonoidalCategory.whiskerLeft_comp, Monad.lStr_unit_comm,
    comp_def, Functor.map_comp, η_naturality_assoc, η_naturality, Monad.left_unit, Category.comp_id]
  rw [MonoidalCategory.tensorHom_def]
  simp

variable [CopyDiscardCategory C] [SymmetricMonad T]

instance : CopyDiscardCategoryStruct (Kleisli T) where
  del X := (Adjunction.toKleisli T).map (del (C := C) X)
  copy X := (Adjunction.toKleisli T).map (copy (C := C) X)

lemma del_def (X : Kleisli T) : del X = (Adjunction.toKleisli T).map (del (C := C) X) := rfl

lemma copy_def (X : Kleisli T) : copy X = (Adjunction.toKleisli T).map (copy (C := C) X) := rfl

instance : CopyDiscardCategory (Kleisli T) where
  del_copy X := by
    rw [copy_def, del_def, ← tensorHom_id]
    have : 𝟙 X = (Adjunction.toKleisli T).map (CategoryStruct.id (obj := C) (X : C)) := by
      rw [(Adjunction.toKleisli T).map_id]
      rfl
    rw [this, ← Adjunction.toKleisli.map_tensorHom, ← (Adjunction.toKleisli T).map_comp,
      tensorHom_id, CopyDiscardCategory.copy_del_right]
    simp [leftUnitor_def]
  copy_del_left X := by
    rw [copy_def, del_def, ← id_tensorHom]
    have : 𝟙 X = (Adjunction.toKleisli T).map (CategoryStruct.id (obj := C) (X : C)) := by
      rw [(Adjunction.toKleisli T).map_id]
      rfl
    rw [this, ← Adjunction.toKleisli.map_tensorHom, ← (Adjunction.toKleisli T).map_comp,
      id_tensorHom, CopyDiscardCategory.copy_del_left]
    simp [rightUnitor_def]
  copy_del_right X := by
    rw [copy_def, del_def, ← tensorHom_id]
    have : 𝟙 X = (Adjunction.toKleisli T).map (CategoryStruct.id (obj := C) (X : C)) := by
      rw [(Adjunction.toKleisli T).map_id]
      rfl
    rw [this, ← Adjunction.toKleisli.map_tensorHom, ← (Adjunction.toKleisli T).map_comp,
      tensorHom_id, CopyDiscardCategory.copy_del_right]
    simp [leftUnitor_def]
  copy_assoc X := by
    rw [copy_def, ← id_tensorHom, ← tensorHom_id]
    have : 𝟙 X = (Adjunction.toKleisli T).map (CategoryStruct.id (obj := C) (X : C)) := by
      rw [(Adjunction.toKleisli T).map_id]
      rfl
    rw [this, ← Adjunction.toKleisli.map_tensorHom, ← Adjunction.toKleisli.map_tensorHom,
      associator_def, Functor.mapIso_inv,
      ← (Adjunction.toKleisli T).map_comp, ← (Adjunction.toKleisli T).map_comp,
      ← (Adjunction.toKleisli T).map_comp, id_tensorHom, tensorHom_id,
      CopyDiscardCategory.copy_assoc (C := C) X]
  copy_braiding X := by
    rw [copy_def, braiding_def, Functor.mapIso_hom, ← (Adjunction.toKleisli T).map_comp,
      CopyDiscardCategory.copy_braiding]
  copy_tensor X Y := by
    simp only [tensorObj_def, copy_def]
    rw [CopyDiscardCategory.copy_tensor, ← Adjunction.toKleisli.map_tensorHom]
    simp only [tensorHom_id, id_tensorHom, (Adjunction.toKleisli T).map_comp,
      Adjunction.toKleisli.map_tensorHom]
    simp [associator_def, Functor.mapIso_hom, braiding_def,Functor.mapIso_inv,
      whiskerLeft_def, whiskerRight_def]
  del_tensor X Y := by
    rw [del_def, del_def, del_def,← Adjunction.toKleisli.map_tensorHom, leftUnitor_def,
      Functor.mapIso_hom, ← (Adjunction.toKleisli T).map_comp]
    simp [tensorObj_def]
    rfl
  copy_unit := by simp [copy_def, tensorUnit_def, leftUnitor_def]
  del_unit := by simp [del_def, tensorUnit_def, id_def]

end Kleisli

end CategoryTheory
