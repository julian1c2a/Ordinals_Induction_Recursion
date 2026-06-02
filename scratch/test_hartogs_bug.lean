import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Isomorphism
import OrdinalsInductionRecursion.UnivOrd.Cardinals

universe u

namespace UnivOrd
namespace Cardinals

open PreOrd
open Isomorphism

def a1 : PreOrd.{u} := PreOrd.zero
def a2 : PreOrd.{u} := PreOrd.sup (α := Unit) fun _ => PreOrd.zero

theorem a1_equiv_a2 : PreOrd.Equiv a1 a2 := by
  constructor
  · apply PreOrd.Subset.zero_subset
  · apply PreOrd.Subset.sup_subset
    intro x
    apply PreOrd.Subset.zero_subset

def unitWO : WellOrderOnSubset Unit := {
  S := fun _ => True
  R := fun _ _ => False
  hwf := by
    apply wellFounded_iff_has_min.mpr
    intro s hs
    cases hs with
    | intro x hx =>
      exists x
      constructor
      · exact hx
      · intro y _ hxy
        exact hxy
}

theorem hartogs_a2_not_zero : PreOrd.Mem PreOrd.zero (hartogsPreOrd a2) := by
  -- hartogsPreOrd a2 = sup fun wo => ordinalOfWO wo
  -- So we just need Mem zero (ordinalOfWO unitWO)
  have h_eq : hartogsPreOrd a2 = PreOrd.sup (α := WellOrderOnSubset Unit) ordinalOfWO := rfl
  rw [h_eq]
  -- We just need Mem zero (ordinalOfWO unitWO)
  sorry

end Cardinals
end UnivOrd
