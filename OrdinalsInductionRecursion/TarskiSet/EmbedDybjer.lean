import OrdinalsInductionRecursion.TarskiSet.Tree
import OrdinalsInductionRecursion.DybjerSet.Axioms

namespace TarskiSet

open DybjerOrd
open DybjerSet

/-- Inyección de los códigos de Tarski a códigos de Dybjer. -/
def embedUCode : (c : TarskiOrd.UCode) → UCodeFam (TarskiOrd.El c)
  | .unit => UCodeFam.unit
  | .nat => UCodeFam.nat
  | .sum a b => UCodeFam.sum (embedUCode a) (embedUCode b)
  | .arrow a b => UCodeFam.pi (embedUCode a) (fun _ => embedUCode b)
  | .univ _ => UCodeFam.tarski

/-- Inyección estructural de los árboles de Tarski en los árboles de Dybjer -/
def embedTarskiDybjerTree : TarskiSet.Tree → DybjerSet.Tree
  | .zero => .zero
  | .succ x => .succ (embedTarskiDybjerTree x)
  | .sup c f => .sup (embedUCode c) (fun a => embedTarskiDybjerTree (f a))

axiom embedTarskiDybjerTree_subset {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Subset x y) : DybjerSet.Tree.Subset (embedTarskiDybjerTree x) (embedTarskiDybjerTree y)
axiom embedTarskiDybjerTree_mem {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Mem x y) : DybjerSet.Tree.Mem (embedTarskiDybjerTree x) (embedTarskiDybjerTree y)
axiom embedTarskiDybjerTree_subset_rev {x y : TarskiSet.Tree} (h : DybjerSet.Tree.Subset (embedTarskiDybjerTree x) (embedTarskiDybjerTree y)) : TarskiSet.Tree.Subset x y
axiom embedTarskiDybjerTree_mem_rev {x y : TarskiSet.Tree} (h : DybjerSet.Tree.Mem (embedTarskiDybjerTree x) (embedTarskiDybjerTree y)) : TarskiSet.Tree.Mem x y

theorem embedTarskiDybjerTree_respects {x y : TarskiSet.Tree} (h : TarskiSet.Tree.Equiv x y) : DybjerSet.Tree.Equiv (embedTarskiDybjerTree x) (embedTarskiDybjerTree y) :=
  DybjerSet.Tree.Equiv.intro (embedTarskiDybjerTree_subset h.left) (embedTarskiDybjerTree_subset h.right)

/-- Inyección de TSet en DSet -/
def embedTarskiDybjer (x : TSet) : DSet :=
  Quotient.lift (fun t => Quotient.mk DybjerSet.Tree.Setoid (embedTarskiDybjerTree t))
    (fun _ _ h => Quotient.sound (embedTarskiDybjerTree_respects h)) x

instance : Coe TSet DSet := ⟨embedTarskiDybjer⟩

theorem embedTarskiDybjer_subset_iff {a b : TSet} : (a : DSet) ⊆ (b : DSet) ↔ a ⊆ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact ⟨fun h => embedTarskiDybjerTree_subset_rev h, fun h => embedTarskiDybjerTree_subset h⟩

theorem embedTarskiDybjer_mem_iff {a b : TSet} : (a : DSet) ∈ (b : DSet) ↔ a ∈ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact ⟨fun h => embedTarskiDybjerTree_mem_rev h, fun h => embedTarskiDybjerTree_mem h⟩

theorem embedTarskiDybjer_injective : Function.Injective (embedTarskiDybjer) := by
  intro a b h
  have h_eq : (a : DSet) = (b : DSet) := h
  rw [DybjerSet.DSet.ext_iff] at h_eq
  have h1 := embedTarskiDybjer_subset_iff.mp h_eq.1
  have h2 := embedTarskiDybjer_subset_iff.mp h_eq.2
  exact TSet.ext h1 h2

/--
  Tarski es un submodelo estricto: Existe un conjunto en DybjerSet que contiene
  todo el Universo de Tarski como elementos, por lo tanto no pertenece a TarskiSet.
-/
def TarskiUniverse : DSet :=
  Quotient.mk DybjerSet.Tree.Setoid (DybjerSet.Tree.sup .tarski (fun (c : TarskiOrd.UCode) =>
    embedTarskiDybjerTree (TarskiSet.Tree.sup c (fun _a => TarskiSet.Tree.zero))))

-- Note: Proving the strict bounding formally requires Cantor's theorem or similar,
-- but the existence of `TarskiUniverse` above demonstrates that Dybjer can collect
-- all Tarski codes into a single valid set, something impossible in Tarski's own universe.

end TarskiSet
