import OrdinalsInductionRecursion.TarskiOrd.PreOrd

universe u

namespace TarskiOrd

/-- 
El tipo Ordinal de Tarski es el cociente de los árboles de Brouwer limitados por códigos (TPreOrd)
bajo la relación de equivalencia extensional.
-/
def TOrdinal := Quotient TPreOrd.Setoid

end TarskiOrd
