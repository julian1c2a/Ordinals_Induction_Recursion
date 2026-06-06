import OrdinalsInductionRecursion.DybjerOrd.Cardinals
import OrdinalsInductionRecursion.DybjerOrd.Univ
import OrdinalsInductionRecursion.DybjerOrd.Mostowski

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Familias Cardinales usando UCodeFam
-- ==========================================

/-- Suma cardinal basada en tipos dependientes.
Usamos `UCodeFam.sigma` para codificar la unión disjunta de la familia. -/
noncomputable def cardSum {A : Type} (cA : UCodeFam A) {B : A → Type} (cB : (a : A) → UCodeFam (B a)) : DOrdinal :=
  -- Construimos el código Sigma
  let cSigma := UCodeFam.sigma cA cB
  -- El tipo subyacente es Σ (a : A), B a
  -- La cardinalidad de este tipo se obtiene asignándole un pre-ordinal
  -- a través de un colapso si estuviera bien ordenado.
  -- Para una familia genérica, su cardinalidad axiomática (basada en Hartogs):
  card (hartogs (Quotient.mk Setoid .zero)) -- Placeholder estructural hasta axiomatizar el mapeo de `Sigma` a `DPreOrd`

/-- Producto cardinal basado en tipos dependientes.
Usamos `UCodeFam.pi` para codificar el producto (funciones de A en B). -/
noncomputable def cardProd {A : Type} (cA : UCodeFam A) {B : A → Type} (cB : (a : A) → UCodeFam (B a)) : DOrdinal :=
  -- Construimos el código Pi
  let cPi := UCodeFam.pi cA cB
  -- Su cardinalidad se asigna de manera homóloga a la suma:
  card (hartogs (Quotient.mk Setoid .zero)) -- Placeholder estructural

end DybjerOrd
