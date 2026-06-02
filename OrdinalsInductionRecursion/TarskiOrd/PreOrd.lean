import OrdinalsInductionRecursion.TarskiOrd.UCode
import OrdinalsInductionRecursion.TarskiOrd.El

namespace TarskiOrd

/-- 
El árbol de Brouwer que modela los ordinales de forma constructiva,
limitando la ramificación estrictamente a tipos decodificados desde `UCode`.
Esto garantiza que la iteración se mantenga completamente interna y computable,
esquivando la barrera sintáctica de `Sort u`.
-/
inductive TPreOrd : Type
  | zero : TPreOrd
  | succ : TPreOrd → TPreOrd
  | sup  : (c : UCode) → (El c → TPreOrd) → TPreOrd

end TarskiOrd
