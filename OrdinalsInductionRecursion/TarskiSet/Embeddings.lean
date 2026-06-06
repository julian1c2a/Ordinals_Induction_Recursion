import OrdinalsInductionRecursion.TarskiSet.Axioms
import OrdinalsInductionRecursion.UnivSets.Axioms

universe u

namespace TarskiSet

open UnivSets

-- ==========================================
-- Embedding from TarskiSet to UnivSets
-- ==========================================

/-- Inyección de los árboles de conjuntos de Tarski en los árboles de conjuntos universales -/
def embedTarskiSetTree : TarskiSet.Tree → UnivSets.Tree.{u}
  | .zero => emptyTree
  | .succ x => UnivSets.Tree.sup (α := Unit) fun _ => embedTarskiSetTree x
  | .sup c f => UnivSets.Tree.sup (α := TarskiOrd.El c) fun a => embedTarskiSetTree (f a)

mutual
  theorem embedTarskiSetTree_subset {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Subset x y) : UnivSets.Tree.Subset (embedTarskiSetTree x) (embedTarskiSetTree y) :=
    match x, y, h with
    | _, _, TarskiSet.Tree.Subset.zero_subset _ => UnivSets.Tree.Subset.sup_subset fun a => PEmpty.elim a
    | _, _, @TarskiSet.Tree.Subset.succ_subset _ _ hmem =>
      UnivSets.Tree.Subset.sup_subset fun _ => embedTarskiSetTree_mem hmem
    | _, _, @TarskiSet.Tree.Subset.sup_subset _ _ _ hsub =>
      UnivSets.Tree.Subset.sup_subset fun a => embedTarskiSetTree_mem (hsub a)

  theorem embedTarskiSetTree_mem {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Mem x y) : UnivSets.Tree.Mem (embedTarskiSetTree x) (embedTarskiSetTree y) :=
    match x, y, h with
    | _, _, @TarskiSet.Tree.Mem.mem_succ _ _ hsub1 hsub2 =>
      UnivSets.Tree.Mem.mem_sup () (embedTarskiSetTree_subset hsub1) (embedTarskiSetTree_subset hsub2)
    | _, _, @TarskiSet.Tree.Mem.mem_sup _ _ _ a hsub1 hsub2 =>
      UnivSets.Tree.Mem.mem_sup a (embedTarskiSetTree_subset hsub1) (embedTarskiSetTree_subset hsub2)
end

theorem embedTarskiSetTree_respects {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Equiv x y) : UnivSets.Tree.Equiv (embedTarskiSetTree x) (embedTarskiSetTree y) :=
  UnivSets.Tree.Equiv.intro (embedTarskiSetTree_subset h.left) (embedTarskiSetTree_subset h.right)

/-- Inyección de TSet en USet.{u} -/
def embedTarskiSet (x : TSet) : USet.{u} :=
  Quotient.lift (fun t => Quotient.mk UnivSets.Tree.Setoid (embedTarskiSetTree t))
    (fun _ _ h => Quotient.sound (embedTarskiSetTree_respects h)) x

instance : Coe TSet USet.{u} := ⟨embedTarskiSet⟩

end TarskiSet
