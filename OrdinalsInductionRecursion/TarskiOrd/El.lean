import OrdinalsInductionRecursion.TarskiOrd.UCode

namespace TarskiOrd

/-- 
La función decodificadora (El) que mapea un código de Tarski 
a un verdadero tipo en el metalenguaje (Lean 4).
-/
def El : UCode → Type
  | .unit => Unit
  | .nat => Nat
  | .sum a b => Sum (El a) (El b)
  | .arrow a b => El a → El b
  -- Un universo de nivel n contiene todos los UCode.
  -- Para mantener consistencia de tipos predicativos de manera simple,
  -- consideramos que un universo es el tipo de los UCode en sí mismo.
  | .univ _ => UCode

end TarskiOrd
