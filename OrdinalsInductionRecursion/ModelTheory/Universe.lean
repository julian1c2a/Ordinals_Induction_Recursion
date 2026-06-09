import FOL_poli.Semantics
import OrdinalsInductionRecursion.DybjerSet.Axioms

namespace ModelTheory

open DybjerSet
open FOL_poli.Metamath.Semantics

/-- El universo de conjuntos de Dybjer V -/
def V : Model DSet where
  func _ _ := DybjerSet.empty
  rel name args :=
    match name, args with
    | "∈", [a, b] => a ∈ b
    | _, _ => False

end ModelTheory
