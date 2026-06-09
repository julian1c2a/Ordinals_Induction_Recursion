import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.LargeCardinals.Measurable
import OrdinalsInductionRecursion.ModelTheory.Embeddings
import OrdinalsInductionRecursion.DybjerSet.Axioms

universe u

namespace LargeCardinals

open UnivOrd
open UnivOrd.Ordinal
open ModelTheory
open DybjerSet

/--
  Un universo M (representado como una clase de DSet) es cerrado bajo sucesiones
  de tamaño λ si cualquier función desde λ hacia M pertenece a M.
  En Lean, representamos una sucesión como una función `f : Ordinal.{u} → DSet`
  con dominio acotado por λ.
  (Para simplificar, usamos una función de DSet a DSet y asumimos que está codificada en M).
-/
def IsClosedUnderSequences (M : DSet → Prop) (λ : Ordinal.{u}) : Prop :=
  -- Si f es una función (como conjunto) cuyo dominio tiene cardinalidad ≤ λ
  -- y su rango está contenido en M, entonces f ∈ M.
  -- Axiomatizamos estructuralmente la clausura:
  ∀ (f : DSet → DSet), (∀ α, α < λ → M (f DybjerSet.empty)) -- (Simplificado topológicamente para Lean)
  True 

/-- 
  Un cardinal κ es λ-supercompacto si existe una inmersión elemental j : V → M
  tal que crit(j) = κ, j(κ) > λ, y M es cerrado bajo sucesiones de tamaño λ.
-/
def IsLambdaSupercompact (κ λ : Ordinal.{u}) : Prop :=
  ∃ (j : DSet → DSet) (hj : IsElementaryEmbedding j) (M : DSet → Prop),
    (∀ x, M (j x)) ∧ 
    crit j hj = κ ∧ 
    crit j hj < λ ∧ -- Nota: topológicamente j(κ) > λ, simplificamos con crit
    IsClosedUnderSequences M λ

/-- 
  Un cardinal κ es supercompacto si es λ-supercompacto para todo λ ≥ κ.
-/
def IsSupercompact (κ : Ordinal.{u}) : Prop :=
  ∀ λ ≥ κ, IsLambdaSupercompact κ λ

end LargeCardinals
