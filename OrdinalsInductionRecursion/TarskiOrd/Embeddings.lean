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
  | .sup c f => .sup (El c) fun a => embedTarskiOrdTree (f a)

mutual
  theorem embedTarskiOrdTree_subset {x y : TPreOrd} (h : TPreOrd.Subset x y) : PreOrd.Subset (embedTarskiOrdTree x) (embedTarskiOrdTree y) :=
    match x, y, h with
    | _, _, TPreOrd.Subset.zero_subset _ => PreOrd.Subset.zero_subset _
    | _, _, @TPreOrd.Subset.succ_subset _ _ hmem => PreOrd.Subset.succ_subset (embedTarskiOrdTree_mem hmem)
    | _, _, @TPreOrd.Subset.sup_subset _ _ _ hsub => PreOrd.Subset.sup_subset fun a => embedTarskiOrdTree_mem (hsub a)

  theorem embedTarskiOrdTree_mem {x y : TPreOrd} (h : TPreOrd.Mem x y) : PreOrd.Mem (embedTarskiOrdTree x) (embedTarskiOrdTree y) :=
    match x, y, h with
    | _, _, @TPreOrd.Mem.mem_succ _ _ hsub => PreOrd.Mem.mem_succ (embedTarskiOrdTree_subset hsub)
    | _, _, @TPreOrd.Mem.mem_sup _ _ _ a hmem => PreOrd.Mem.mem_sup a (embedTarskiOrdTree_subset hmem)
end

theorem embedTarskiOrdTree_respects {x y : TPreOrd} (h : TPreOrd.Equiv x y) : PreOrd.Equiv (embedTarskiOrdTree x) (embedTarskiOrdTree y) :=
  ⟨embedTarskiOrdTree_subset h.left, embedTarskiOrdTree_subset h.right⟩

/-- Inyección de TOrdinal en Ordinal.{u} -/
def embedTarskiOrd (x : TOrdinal) : Ordinal.{u} :=
  Quotient.lift (fun t => Quotient.mk UnivOrd.PreOrd.Setoid (embedTarskiOrdTree t))
    (fun _ _ h => Quotient.sound (embedTarskiOrdTree_respects h)) x

instance : Coe TOrdinal Ordinal.{u} := ⟨embedTarskiOrd⟩

end TarskiOrd
