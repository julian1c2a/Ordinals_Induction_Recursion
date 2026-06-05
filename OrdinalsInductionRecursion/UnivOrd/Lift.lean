/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivOrd.Ordinals

universe u v

set_option linter.unusedVariables false

namespace UnivOrd

open PreOrd

-- ==========================================
-- Levantamiento de Órdenes y Ordinales
-- ==========================================

def liftPreOrd (a : PreOrd.{u}) : PreOrd.{max u v} :=
  match a with
  | .zero => .zero
  | .succ a' => .succ (liftPreOrd a')
  | @PreOrd.sup α f => PreOrd.sup (α := ULift.{v, u} α) fun i => liftPreOrd (f i.down)

theorem liftPreOrd_subset {a b : PreOrd.{u}} (h : PreOrd.Subset a b) : PreOrd.Subset (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b) :=
  @PreOrd.Subset.rec
    (fun a b _ => PreOrd.Subset (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b))
    (fun a b _ => PreOrd.Mem (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b))
    (fun y => PreOrd.Subset.zero_subset (liftPreOrd y))
    (fun {x y} _ ih => PreOrd.Subset.succ_subset ih)
    (fun {α f y} _ ih => PreOrd.Subset.sup_subset fun (i : ULift.{v, u} α) => ih i.down)
    (fun {x y} _ ih => PreOrd.Mem.mem_succ ih)
    (fun {α x f} a _ ih => PreOrd.Mem.mem_sup (ULift.up a) ih)
    a b h

theorem liftPreOrd_mem {a b : PreOrd.{u}} (h : PreOrd.Mem a b) : PreOrd.Mem (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b) :=
  @PreOrd.Mem.rec
    (fun a b _ => PreOrd.Subset (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b))
    (fun a b _ => PreOrd.Mem (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b))
    (fun y => PreOrd.Subset.zero_subset (liftPreOrd y))
    (fun {x y} _ ih => PreOrd.Subset.succ_subset ih)
    (fun {α f y} _ ih => PreOrd.Subset.sup_subset fun (i : ULift.{v, u} α) => ih i.down)
    (fun {x y} _ ih => PreOrd.Mem.mem_succ ih)
    (fun {α x f} a _ ih => PreOrd.Mem.mem_sup (ULift.up a) ih)
    a b h

theorem liftPreOrd_respects (a b : PreOrd.{u}) (h : PreOrd.Equiv a b) : PreOrd.Equiv (liftPreOrd.{u, v} a) (liftPreOrd.{u, v} b) :=
  ⟨liftPreOrd_subset h.left, liftPreOrd_subset h.right⟩

/-- Inmersión del universo de ordinales de nivel u al nivel max u v -/
def lift (a : Ordinal.{u}) : Ordinal.{max u v} :=
  Quotient.lift (fun x => Quotient.mk Setoid (liftPreOrd.{u, v} x))
    (fun _ _ h => Quotient.sound (liftPreOrd_respects _ _ h)) a

end UnivOrd
