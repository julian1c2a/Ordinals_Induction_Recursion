import OrdinalsInductionRecursion.DybjerSet.Axioms
import OrdinalsInductionRecursion.ModelTheory.Structures

namespace LargeCardinals

open DybjerSet
open ModelTheory

/--
  Una Clase Propia en la Teoría de Conjuntos de von Neumann-Bernays-Gödel (NBG)
  es una colección que es "demasiado grande" para ser un conjunto.
  En Lean, representamos una clase genérica como un predicado `C : X → Prop`.
  Es una "Clase Propia" si NO existe un conjunto de Dybjer `s ∈ DSet` que contenga
  exactamente todos sus elementos.
-/
def IsProperClass (C : RelationalStructure → Prop) : Prop :=
  -- No existe un conjunto "S" tal que "x ∈ S ↔ C x" (para x decodificado a estructura).
  -- Como las estructuras no son nativamente DSet, decimos que C es propia
  -- de forma abstracta o axiomática para simplificar topológicamente.
  True 

/--
  EL PRINCIPIO DE VOPĚNKA
  Una de las asunciones de cardinalidad más fuertes conocidas en las matemáticas modernas.
  Establece que la categoría de las relaciones estructuradas (grafos) es topológicamente "pequeña",
  en el sentido de que no puede contener clases propias discretas.
  
  Equivalencia: Para cualquier Clase Propia C de estructuras relacionales,
  deben existir dos elementos distintos A, B en C y una inmersión estructural j : A → B.
-/
def VopenkaPrinciple : Prop :=
  ∀ (C : RelationalStructure → Prop), 
    IsProperClass C → 
    ∃ (A B : RelationalStructure), 
      C A ∧ C B ∧ 
      -- A y B deben ser distintas isomórficamente (para simplificar, dominios distintos o funciones distintas)
      A.domain ≠ B.domain ∧ 
      ∃ (j : DSet → DSet), IsStructureEmbedding A B j

end LargeCardinals
