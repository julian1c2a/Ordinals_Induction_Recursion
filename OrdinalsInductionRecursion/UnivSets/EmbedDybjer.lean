import OrdinalsInductionRecursion.DybjerSet.Axioms
import OrdinalsInductionRecursion.UnivSets.Axioms

universe u

namespace UnivSets

/--
  Inmersión del árbol de Dybjer (ZFC constructivo) en el árbol general de Aczel (UnivSets).
-/
def embedDybjerTree : DybjerSet.Tree → UnivSets.Tree.{u+1}
  | .zero => UnivSets.emptyTree
  | .succ x => UnivSets.Tree.sup (α := ULift Unit) fun _ => embedDybjerTree x
  | .sup (A := A) c f => UnivSets.Tree.sup (α := ULift.{u+1, 0} A) fun a => embedDybjerTree (f a.down)

axiom embedDybjerTree_subset {x y : DybjerSet.Tree} (h : DybjerSet.Tree.Subset x y) : UnivSets.Tree.Subset (embedDybjerTree x) (embedDybjerTree y)
axiom embedDybjerTree_mem {x y : DybjerSet.Tree} (h : DybjerSet.Tree.Mem x y) : UnivSets.Tree.Mem (embedDybjerTree x) (embedDybjerTree y)
axiom embedDybjerTree_subset_rev {x y : DybjerSet.Tree} (h : UnivSets.Tree.Subset (embedDybjerTree x) (embedDybjerTree y)) : DybjerSet.Tree.Subset x y
axiom embedDybjerTree_mem_rev {x y : DybjerSet.Tree} (h : UnivSets.Tree.Mem (embedDybjerTree x) (embedDybjerTree y)) : DybjerSet.Tree.Mem x y

theorem embedDybjerTree_respects {x y : DybjerSet.Tree} (h : DybjerSet.Tree.Equiv x y) : UnivSets.Tree.Equiv (embedDybjerTree x) (embedDybjerTree y) :=
  UnivSets.Tree.Equiv.intro (embedDybjerTree_subset h.left) (embedDybjerTree_subset h.right)

/-- Inmersión del modelo DSet en UnivSets.USet -/
def embedDSet (d : DybjerSet.DSet) : UnivSets.USet.{u+1} :=
  Quotient.lift (fun t => Quotient.mk UnivSets.Tree.Setoid (embedDybjerTree t))
    (fun _ _ h => Quotient.sound (embedDybjerTree_respects h)) d

theorem embedDSet_inj {x y : DybjerSet.DSet} (h_eq : embedDSet x = embedDSet y) : x = y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  rename_i a b
  have h_eq_trees : UnivSets.Tree.Equiv (embedDybjerTree a) (embedDybjerTree b) := Quotient.exact h_eq
  have h_sub_1 := embedDybjerTree_subset_rev h_eq_trees.left
  have h_sub_2 := embedDybjerTree_subset_rev h_eq_trees.right
  exact Quotient.sound ⟨h_sub_1, h_sub_2⟩

theorem embedDSet_mem {x y : DybjerSet.DSet} (h : x ∈ y) : embedDSet x ∈ embedDSet y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  rename_i a b
  exact embedDybjerTree_mem h

theorem embedDSet_mem_rev {x y : DybjerSet.DSet} (h : embedDSet x ∈ embedDSet y) : x ∈ y := by
  induction x using Quotient.ind
  induction y using Quotient.ind
  rename_i a b
  exact embedDybjerTree_mem_rev h

end UnivSets
