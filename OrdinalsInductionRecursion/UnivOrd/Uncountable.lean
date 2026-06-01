/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.CountableOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Ordinals

universe u

namespace UnivOrd

open CountableOrd (PreOrd)

/-- Inyección de ordinales numerables a ordinales universales -/
def embedCountableOrd : CountableOrd.PreOrd → UnivOrd.PreOrd.{u}
  | .zero => .zero
  | .succ x => .succ (embedCountableOrd x)
  | .sup f => .sup (α := ULift.{u, 0} Peano.ℕ₀) fun n => embedCountableOrd (f n.down)

mutual
  theorem embedCountableOrd_subset {x y : CountableOrd.PreOrd} (h : CountableOrd.PreOrd.Subset x y) : UnivOrd.PreOrd.Subset (embedCountableOrd x) (embedCountableOrd y) :=
    match x, y, h with
    | _, _, .zero_subset y => UnivOrd.PreOrd.Subset.zero_subset _
    | _, _, .succ_subset hmem => UnivOrd.PreOrd.Subset.succ_subset (embedCountableOrd_mem hmem)
    | _, _, .sup_subset hsub => UnivOrd.PreOrd.Subset.sup_subset fun n => embedCountableOrd_subset (hsub n.down)

  theorem embedCountableOrd_mem {x y : CountableOrd.PreOrd} (h : CountableOrd.PreOrd.Mem x y) : UnivOrd.PreOrd.Mem (embedCountableOrd x) (embedCountableOrd y) :=
    match x, y, h with
    | _, _, .mem_succ hsub => UnivOrd.PreOrd.Mem.mem_succ (embedCountableOrd_subset hsub)
    | _, _, .mem_sup n hmem => UnivOrd.PreOrd.Mem.mem_sup (ULift.up n) (embedCountableOrd_mem hmem)
end

theorem embedCountableOrd_respects {x y : CountableOrd.PreOrd} (h : CountableOrd.PreOrd.Equiv x y) : UnivOrd.PreOrd.Equiv (embedCountableOrd x) (embedCountableOrd y) :=
  ⟨embedCountableOrd_subset h.left, embedCountableOrd_subset h.right⟩

def embedCountableOrdOrdinal (x : CountableOrd.Ordinal) : UnivOrd.Ordinal.{u} :=
  Quotient.lift (fun t => Quotient.mk UnivOrd.PreOrd.Setoid (embedCountableOrd t))
    (fun _ _ h => Quotient.sound (embedCountableOrd_respects h)) x

instance : Coe CountableOrd.Ordinal UnivOrd.Ordinal.{u} := ⟨embedCountableOrdOrdinal⟩

-- ==========================================
-- El Primer Ordinal No Numerable (ω₁)
-- ==========================================

/-- El pre-ordinal correspondiente a ω₁ -/
def omega1_PreOrd : UnivOrd.PreOrd.{u} :=
  UnivOrd.PreOrd.sup (α := ULift.{u, 0} CountableOrd.PreOrd) fun x => embedCountableOrd x.down

/-- El primer ordinal no numerable (ω₁) en el universo de ordinales universales -/
def Omega1 : UnivOrd.Ordinal.{u} :=
  Quotient.mk UnivOrd.PreOrd.Setoid omega1_PreOrd

notation "ω₁" => Omega1

theorem embedCountableOrd_preFromNat (n : Peano.ℕ₀) : embedCountableOrd (CountableOrd.PreOrd.preFromNat n) = UnivOrd.PreOrd.preFromNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change UnivOrd.PreOrd.succ (embedCountableOrd (CountableOrd.PreOrd.preFromNat n)) = UnivOrd.PreOrd.succ (UnivOrd.PreOrd.preFromNat n)
    rw [ih]

theorem embedCountableOrd_preomega : embedCountableOrd CountableOrd.PreOrd.preomega = UnivOrd.PreOrd.preomega := by
  change UnivOrd.PreOrd.sup _ = UnivOrd.PreOrd.sup _
  congr
  funext n
  exact embedCountableOrd_preFromNat n.down

theorem omega_mem_omega1 : UnivOrd.PreOrd.Mem UnivOrd.PreOrd.preomega omega1_PreOrd := by
  apply UnivOrd.PreOrd.Mem.mem_sup (ULift.up (CountableOrd.PreOrd.succ CountableOrd.PreOrd.preomega))
  change UnivOrd.PreOrd.Mem _ (UnivOrd.PreOrd.succ (embedCountableOrd CountableOrd.PreOrd.preomega))
  apply UnivOrd.PreOrd.Mem.mem_succ
  rw [embedCountableOrd_preomega]
  exact UnivOrd.PreOrd.Subset_refl _

end UnivOrd
