import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Isomorphism
import OrdinalsInductionRecursion.UnivOrd.Cardinals

universe u

namespace UnivOrd
namespace Cardinals

open PreOrd
open Isomorphism

theorem alephPreOrd_subset {a b : PreOrd.{u}} (h : PreOrd.Subset a b) : PreOrd.Subset (alephPreOrd a) (alephPreOrd b) :=
  @PreOrd.Subset.rec
    (fun a b _ => PreOrd.Subset (alephPreOrd a) (alephPreOrd b))
    (fun a b _ => PreOrd.Mem (alephPreOrd a) (alephPreOrd b))
    (fun y => sorry)
    (fun {x y} _ ih => sorry)
    (fun {α f y} _ ih => PreOrd.Subset.sup_subset fun i => ih i)
    (fun {x y} _ ih => sorry)
    (fun {α x f} a _ ih => PreOrd.Mem.mem_sup a ih)
    a b h

end Cardinals
end UnivOrd
