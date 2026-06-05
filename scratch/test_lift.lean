import OrdinalsInductionRecursion.UnivSets.Tree

universe u v

namespace UnivSets

open Tree

def liftTree (a : Tree.{u}) : Tree.{max u v} :=
  match a with
  | @Tree.sup α f => Tree.sup (α := ULift.{v, u} α) fun i => liftTree (f i.down)

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

end UnivSets
