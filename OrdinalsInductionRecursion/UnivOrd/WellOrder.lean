/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.OrdinalsLattice

universe u

namespace UnivOrd
namespace PreOrd

theorem acc_mem (x : PreOrd.{u}) : Acc Mem x := by
  induction x with
  | zero =>
    constructor
    intro y hy
    cases hy
  | succ x' ih =>
    constructor
    intro y hy
    cases hy with
    | mem_succ hsub =>
      constructor
      intro z hz
      exact Acc.inv ih (Mem_Subset_trans hz hsub)
  | sup f ih =>
    constructor
    intro y hy
    cases hy with
    | mem_sup a hmem =>
      exact Acc.inv (ih a) hmem

theorem well_founded_mem : WellFounded (@Mem.{u}) :=
  ⟨acc_mem⟩

end PreOrd


namespace Ordinal

theorem acc_lt_of_acc_mem {x : PreOrd.{u}} (h : Acc PreOrd.Mem x) : Acc (· < · : Ordinal.{u} → Ordinal.{u} → Prop) (Quotient.mk PreOrd.Setoid x) := by
  induction h with
  | intro x' _ ih =>
    constructor
    intro q hq
    rcases Quotient.exists_rep q with ⟨y, rfl⟩
    have hq' : PreOrd.Mem y x' := hq
    exact ih y hq'

theorem well_founded_lt : WellFounded ((· < ·) : Ordinal.{u} → Ordinal.{u} → Prop) :=
  ⟨fun q => Quotient.inductionOn q fun x => acc_lt_of_acc_mem (PreOrd.acc_mem x)⟩

instance : WellFoundedRelation Ordinal.{u} where
  rel := (· < ·)
  wf := well_founded_lt

theorem lt_trichotomy (x y : Ordinal.{u}) : x < y ∨ x = y ∨ y < x :=
  Quotient.inductionOn₂ x y fun a b =>
    match (PreOrd.total_prop a b).2.1 with
    | Or.inl h_a_lt_b => Or.inl h_a_lt_b
    | Or.inr h_b_le_a =>
      match (PreOrd.total_prop a b).2.2 with
      | Or.inl h_b_lt_a => Or.inr (Or.inr h_b_lt_a)
      | Or.inr h_a_le_b => Or.inr (Or.inl (Quotient.sound ⟨h_a_le_b, h_b_le_a⟩))

theorem lt_irrefl (x : Ordinal.{u}) : ¬ x < x := by
  intro h
  have wf : Acc (· < ·) x := well_founded_lt.apply x
  induction wf with
  | intro x' _ ih => exact ih x' h h

end Ordinal
end UnivOrd
