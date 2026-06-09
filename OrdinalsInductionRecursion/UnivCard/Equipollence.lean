/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Axioms
import OrdinalsInductionRecursion.UnivOrd.Cardinals

universe u

namespace UnivCard

open UnivSets
open UnivOrd.Cardinals

-- ==========================================
-- Biyecciones y Equipotencia sobre USet
-- ==========================================

/-- El tipo de las inyecciones entre los elementos de dos conjuntos materiales. -/
def Injection (x y : USet.{u}) : Type (u+1) :=
  { f : {a : USet.{u} // a ∈ x} → {b : USet.{u} // b ∈ y} // Injective f }

/-- El tipo de las biyecciones entre los elementos de dos conjuntos materiales. -/
def Bijection (x y : USet.{u}) : Type (u+1) :=
  { f : {a : USet.{u} // a ∈ x} → {b : USet.{u} // b ∈ y} // Bijective f }

/-- Dos conjuntos de USet son equipotentes si existe una biyección entre ellos. -/
def Equipotent (x y : USet.{u}) : Prop :=
  Nonempty (Bijection x y)

-- Notación para la equipotencia
infix:50 " ≈ " => Equipotent

theorem Equipotent.refl (x : USet.{u}) : x ≈ x := by
  let f : {a : USet.{u} // a ∈ x} → {b : USet.{u} // b ∈ x} := id
  have h_inj : Injective f := fun _ _ h => h
  have h_surj : Surjective f := fun b => ⟨b, rfl⟩
  exact ⟨⟨f, ⟨h_inj, h_surj⟩⟩⟩

theorem Equipotent.symm {x y : USet.{u}} (h : x ≈ y) : y ≈ x := by
  let b_xy := Classical.choice h
  let f := b_xy.val
  have h_inj : Injective f := b_xy.property.left
  have h_surj : Surjective f := b_xy.property.right
  let g : {b : USet.{u} // b ∈ y} → {a : USet.{u} // a ∈ x} := fun b =>
    Classical.choose (h_surj b)
  have hg : ∀ b, f (g b) = b := fun b => Classical.choose_spec (h_surj b)
  have g_inj : Injective g := by
    intro b1 b2 h_eq
    have h1 : f (g b1) = b1 := hg b1
    have h2 : f (g b2) = b2 := hg b2
    rw [h_eq] at h1
    exact h1.symm.trans h2
  have g_surj : Surjective g := by
    intro a
    exact ⟨f a, by
      apply h_inj
      exact hg (f a)⟩
  exact Nonempty.intro ⟨g, ⟨g_inj, g_surj⟩⟩

theorem Equipotent.trans {x y z : USet.{u}} (h1 : x ≈ y) (h2 : y ≈ z) : x ≈ z := by
  let b_xy := Classical.choice h1
  let f := b_xy.val
  have f_inj : Injective f := b_xy.property.left
  have f_surj : Surjective f := b_xy.property.right
  let b_yz := Classical.choice h2
  let g := b_yz.val
  have g_inj : Injective g := b_yz.property.left
  have g_surj : Surjective g := b_yz.property.right
  let h_comp := fun a => g (f a)
  have h_inj : Injective h_comp := by
    intro a1 a2 h_eq
    apply f_inj
    apply g_inj
    exact h_eq
  have h_surj : Surjective h_comp := by
    intro c
    let b := Classical.choose (g_surj c)
    let hb := Classical.choose_spec (g_surj c)
    let a := Classical.choose (f_surj b)
    let ha := Classical.choose_spec (f_surj b)
    exact ⟨a, by
      simp [h_comp]
      rw [ha, hb]⟩
  exact Nonempty.intro ⟨h_comp, ⟨h_inj, h_surj⟩⟩

end UnivCard
