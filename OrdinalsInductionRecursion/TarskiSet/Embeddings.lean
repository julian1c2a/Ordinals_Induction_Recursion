import OrdinalsInductionRecursion.TarskiSet.Tree
import OrdinalsInductionRecursion.UnivSets.Axioms

universe u

namespace TarskiSet

open UnivSets

/-- 
  Inyectamos el árbol de conjuntos de Tarski (`TarskiSet.Tree`)
  en el árbol de conjuntos de Grothendieck (`UnivSets.Tree.{u}`)
-/
def embedTarskiSetTree : TarskiSet.Tree → UnivSets.Tree.{u}
  | .zero => UnivSets.emptyTree
  | .succ x => UnivSets.Tree.sup (α := ULift Unit) fun _ => embedTarskiSetTree x
  | .sup c f => UnivSets.Tree.sup (α := ULift (TarskiOrd.El c)) fun a => embedTarskiSetTree (f a.down)

axiom embedTarskiSetTree_subset {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Subset x y) : UnivSets.Tree.Subset (embedTarskiSetTree x) (embedTarskiSetTree y)
axiom embedTarskiSetTree_mem {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Mem x y) : UnivSets.Tree.Mem (embedTarskiSetTree x) (embedTarskiSetTree y)
axiom embedTarskiSetTree_subset_rev {x y : TarskiSet.Tree} (h : UnivSets.Tree.Subset (embedTarskiSetTree x) (embedTarskiSetTree y)) : TarskiSet.Tree.Subset x y
axiom embedTarskiSetTree_mem_rev {x y : TarskiSet.Tree} (h : UnivSets.Tree.Mem (embedTarskiSetTree x) (embedTarskiSetTree y)) : TarskiSet.Tree.Mem x y

theorem embedTarskiSetTree_respects {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Equiv x y) : UnivSets.Tree.Equiv (embedTarskiSetTree x) (embedTarskiSetTree y) :=
  UnivSets.Tree.Equiv.intro (embedTarskiSetTree_subset h.left) (embedTarskiSetTree_subset h.right)

/-- La inyección levantada a los cocientes (TSet ↪ USet) -/
def embedTarskiSet (x : TSet) : USet.{u} :=
  Quotient.lift (fun t => Quotient.mk UnivSets.Tree.Setoid (embedTarskiSetTree t))
    (fun _ _ h => Quotient.sound (embedTarskiSetTree_respects h)) x

instance : Coe TSet USet.{u} := ⟨embedTarskiSet⟩

theorem embedTarskiSet_subset_iff {a b : TSet} : (embedTarskiSet.{u} a) ⊆ (embedTarskiSet.{u} b) ↔ a ⊆ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact ⟨fun h => embedTarskiSetTree_subset_rev h, fun h => embedTarskiSetTree_subset h⟩

theorem embedTarskiSet_mem_iff {a b : TSet} : (embedTarskiSet.{u} a) ∈ (embedTarskiSet.{u} b) ↔ a ∈ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact ⟨fun h => embedTarskiSetTree_mem_rev h, fun h => embedTarskiSetTree_mem h⟩

theorem embedTarskiSet_injective : ∀ a b : TSet, embedTarskiSet.{u} a = embedTarskiSet.{u} b → a = b := by
  intro a b h_eq
  rw [UnivSets.USet.ext_iff] at h_eq
  have h1 := embedTarskiSet_subset_iff.mp h_eq.1
  have h2 := embedTarskiSet_subset_iff.mp h_eq.2
  exact TSet.ext h1 h2

end TarskiSet
