import FOL_poli.Semantics
import OrdinalsInductionRecursion.DybjerSet.Axioms
import OrdinalsInductionRecursion.ModelTheory.Universe

namespace ModelTheory

open DybjerSet
open FOL_poli.Metamath.Semantics

/-- Una inmersión elemental j : V → M conserva la verdad de toda fórmula de primer orden.
    Dado que V y M son ambos el universo DSet en nuestro caso, consideramos
    inmersiones elementales j : V → V.
    
    Por ahora, se define a nivel del Model V de FOL.
-/

structure ElementaryEmbedding (M N : Model DSet) where
  f : DSet → DSet
  preserves_rel : ∀ (name : String) (args : List DSet),
    M.rel name args ↔ N.rel name (args.map f)
  -- Para una definición completa, hay que añadir `preserves_func` 
  -- y la preservación sobre cualquier fórmula phi.

end ModelTheory
