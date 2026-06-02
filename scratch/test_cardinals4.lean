import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Induction

universe u

namespace UnivOrd
namespace Cardinals

open PreOrd
open Ordinal

-- Supongamos f es monótona
def sup_over_lt (β : Ordinal.{u}) (f : (γ : Ordinal.{u}) → γ < β → Ordinal.{u}) : Ordinal.{u} :=
  let b := Quotient.out β
  match b with
  | @PreOrd.sup α g =>
      -- Obtenemos el conjunto cofinal
      Quotient.mk Setoid (PreOrd.sup fun i =>
        Quotient.out (f (Quotient.mk Setoid (g i)) sorry))
  | _ => zero

end Cardinals
end UnivOrd
