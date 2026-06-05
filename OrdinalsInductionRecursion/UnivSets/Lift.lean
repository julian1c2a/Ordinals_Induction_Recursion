/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Tree

universe u v

set_option linter.unusedVariables false

namespace UnivSets

open Tree

-- ==========================================
-- Levantamiento (Lift) de Universos
-- ==========================================

/-- Inmersión de un árbol de nivel u a nivel max u v -/
def liftTree (a : Tree.{u}) : Tree.{max u v} :=
  match a with
  | @sup α f => sup (α := ULift.{v, u} α) fun i => liftTree (f i.down)

theorem liftTree_subset {a b : Tree.{u}} (h : Tree.Subset a b) : Tree.Subset (liftTree.{u, v} a) (liftTree.{u, v} b) :=
  @Tree.Subset.rec (fun a b _ => Tree.Subset (liftTree.{u, v} a) (liftTree.{u, v} b)) (fun a b _ => Tree.Mem (liftTree.{u, v} a) (liftTree.{u, v} b))
    (fun {α} {f} {y} _ ih => Tree.Subset.sup_subset fun (i : ULift.{v, u} α) => ih i.down)
    (fun {α} {x} {f} a _ _ ih1 ih2 => Tree.Mem.mem_sup (ULift.up a) ih1 ih2)
    a b h

theorem liftTree_mem {a b : Tree.{u}} (h : Tree.Mem a b) : Tree.Mem (liftTree.{u, v} a) (liftTree.{u, v} b) :=
  @Tree.Mem.rec (fun a b _ => Tree.Subset (liftTree.{u, v} a) (liftTree.{u, v} b)) (fun a b _ => Tree.Mem (liftTree.{u, v} a) (liftTree.{u, v} b))
    (fun {α} {f} {y} _ ih => Tree.Subset.sup_subset fun (i : ULift.{v, u} α) => ih i.down)
    (fun {α} {x} {f} a _ _ ih1 ih2 => Tree.Mem.mem_sup (ULift.up a) ih1 ih2)
    a b h

theorem liftTree_respects (a b : Tree.{u}) (h : Equiv a b) : Equiv (liftTree.{u, v} a) (liftTree.{u, v} b) :=
  Equiv.intro (liftTree_subset h.left) (liftTree_subset h.right)

/-- Inmersión del universo de conjuntos de nivel u al nivel max u v -/
def lift (a : USet.{u}) : USet.{max u v} :=
  Quotient.lift (fun x => Quotient.mk Setoid (liftTree.{u, v} x))
    (fun _ _ h => Quotient.sound (liftTree_respects _ _ h)) a

end UnivSets
