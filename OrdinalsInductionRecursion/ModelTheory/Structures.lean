import OrdinalsInductionRecursion.DybjerSet.Axioms

namespace ModelTheory

open DybjerSet

/-- 
  Una estructura relacional ligera definida sobre el universo de conjuntos extensionales (DSet).
  Consta de un dominio (un conjunto) y una relación binaria sobre ese conjunto.
  (Para Vopěnka, usamos estructuras de la misma firma. Asumimos la firma de grafos
  dirigidos/relaciones binarias como paradigma base para Lean).
-/
structure RelationalStructure where
  domain : DSet
  -- R ⊆ domain × domain (formalmente una función booleana o proposición,
  -- simplificaremos a predicado puramente lógico por ahora)
  rel : DSet → DSet → Prop
  -- En una formalización estricta deberíamos pedir que rel solo sea cierto
  -- para elementos dentro de domain.
  rel_domain : ∀ x y, rel x y → (x ∈ domain ∧ y ∈ domain)

/--
  Una inmersión entre dos estructuras preserva la relación de la firma.
  Es una inyección f : dom(A) → dom(B) tal que R_A(x, y) ↔ R_B(f(x), f(y)).
-/
def IsStructureEmbedding (A B : RelationalStructure) (j : DSet → DSet) : Prop :=
  -- j mapea el dominio de A en el dominio de B
  (∀ x ∈ A.domain, j x ∈ B.domain) ∧
  -- j es inyectiva en el dominio de A
  (∀ x y, x ∈ A.domain → y ∈ A.domain → j x = j y → x = y) ∧
  -- j preserva fuertemente la relación
  ∀ x y, x ∈ A.domain → y ∈ A.domain → (A.rel x y ↔ B.rel (j x) (j y))

end ModelTheory
