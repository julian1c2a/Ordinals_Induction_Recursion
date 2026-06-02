universe u

namespace TarskiOrd

/-- 
Códigos para tipos en nuestro universo interno computacional.
Para mantener computabilidad plena en Lean 4 sin Inducción-Recursión,
usamos tipos simples (arrow en lugar de pi dependiente).
-/
inductive UCode : Type
  | unit  : UCode
  | nat   : UCode
  | sum   : UCode → UCode → UCode
  | arrow : UCode → UCode → UCode
  | univ  : Nat → UCode

end TarskiOrd
