/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/
import OrdinalsInductionRecursion.Operations.Relation
import OrdinalsInductionRecursion.Operations.OrderedPair
import OrdinalsInductionRecursion.Operations.Powerset

/-- La relación inversa (conversa) de R:
    R⁻¹ᵣ = {⟪b, a⟫ | ⟪a, b⟫ ∈ R}.
    El universo es 𝒫(𝒫(⋃⋃R)) porque ⟪b, a⟫ = {{b}, {b, a}} ⊆ 𝒫(⋃⋃R). -/
def HFSet.relInv (R : HFSet) : HFSet :=
  let UR2 := HFSet.sUnion (HFSet.sUnion R)
  HFSet.sep
    (HFSet.powerset (HFSet.powerset (HFSet.sUnion (HFSet.sUnion R))))
    (fun p => ∃ a ∈ UR2, ∃ b ∈ UR2, ⟪a, b⟫ ∈ R ∧ p = ⟪b, a⟫)

/-- Notación postfija para la relación inversa. -/
postfix:75 "⁻¹ᵣ" => HFSet.relInv
