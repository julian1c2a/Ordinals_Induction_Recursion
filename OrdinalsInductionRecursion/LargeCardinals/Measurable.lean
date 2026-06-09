import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.LargeCardinals.Inaccessible
import OrdinalsInductionRecursion.LargeCardinals.Filters
import OrdinalsInductionRecursion.ModelTheory.Embeddings

universe u

namespace LargeCardinals

open UnivOrd
open UnivOrd.Ordinal
open LargeCardinals.Inaccessible
open ModelTheory

/-- 
  Definición Clásica: Un cardinal es medible si es no numerable y existe sobre él
  un ultrafiltro que es no principal y κ-completo.
  (Nota: en Lean, `IsUniverse` engloba ser regular y límite fuerte, lo que implica inaccesibilidad).
-/
def IsMeasurable (κ : Ordinal.{u}) : Prop :=
  IsUniverse κ ∧ ∃ (F : Filter κ), IsUltrafilter κ F ∧ IsNonPrincipal κ F ∧ IsCompleteFilter κ κ F

/-- 
  El punto crítico de una inmersión elemental $j : V \to M$.
  Formalmente, es el menor ordinal $\alpha$ tal que $j(\alpha) > \alpha$.
  Dado que los ordinales de Dybjer están integrados en DSet, esta función
  extrae (matemáticamente) ese ordinal.
-/
axiom crit (j : DSet → DSet) (hj : IsElementaryEmbedding j) : Ordinal.{u}

/-- 
  Teorema de Scott: Un cardinal κ es medible si y solo si existe una inmersión
  elemental j del Universo V en un modelo transitivo M tal que κ es el punto
  crítico de j.
  
  Lo axiomatizamos para poder construir la jerarquía hacia Vopěnka sin sumergirnos
  computacionalmente en el ultraproducto de V por el ultrafiltro U.
-/
axiom Measurable_iff_Crit (κ : Ordinal.{u}) :
  IsMeasurable κ ↔ ∃ (j : DSet → DSet) (hj : IsElementaryEmbedding j), crit j hj = κ

end LargeCardinals
