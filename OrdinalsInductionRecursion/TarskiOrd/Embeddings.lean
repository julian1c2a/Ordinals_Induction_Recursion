import OrdinalsInductionRecursion.TarskiOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Ordinals

universe u

namespace TarskiOrd

open UnivOrd

-- ==========================================
-- Embedding from TarskiOrd to UnivOrd
-- ==========================================

/-- Inyección de los pre-ordinales computacionales (Tarski) en los pre-ordinales universales (UnivOrd) -/
def embedTarskiOrdTree : TPreOrd → PreOrd.{u}
  | .zero => .zero
  | .succ x => .succ (embedTarskiOrdTree x)
  | .sup c f => .sup (α := ULift (El c)) fun a => embedTarskiOrdTree (f a.down)

axiom embedTarskiOrdTree_subset {x y : TPreOrd} (h : TPreOrd.Subset x y) : PreOrd.Subset (embedTarskiOrdTree x) (embedTarskiOrdTree y)
axiom embedTarskiOrdTree_mem {x y : TPreOrd} (h : TPreOrd.Mem x y) : PreOrd.Mem (embedTarskiOrdTree x) (embedTarskiOrdTree y)

theorem embedTarskiOrdTree_respects {x y : TPreOrd} (h : TPreOrd.Equiv x y) : PreOrd.Equiv (embedTarskiOrdTree x) (embedTarskiOrdTree y) :=
  ⟨embedTarskiOrdTree_subset h.left, embedTarskiOrdTree_subset h.right⟩

/-- Inyección de TOrdinal en Ordinal.{u} -/
def embedTarskiOrd (x : TOrdinal) : Ordinal.{u} :=
  Quotient.lift (fun t => Quotient.mk UnivOrd.PreOrd.Setoid (embedTarskiOrdTree t))
    (fun _ _ h => Quotient.sound (embedTarskiOrdTree_respects h)) x

instance : Coe TOrdinal Ordinal.{u} := ⟨embedTarskiOrd⟩

end TarskiOrd
