import OrdinalsInductionRecursion.TarskiOrd.Cardinals
import OrdinalsInductionRecursion.TarskiOrd.Transfinite

namespace TarskiOrd
open TPreOrd
open Classical

-- ==========================================
-- Operaciones Familiares sobre Cardinales
-- ==========================================

/-- Suma cardinal sobre una familia indexada por un código `c`.
La familia está definida por una función `f : El c → TOrdinal`. -/
noncomputable def cardSum (c : UCode) (f : El c → TOrdinal) : TOrdinal :=
  -- Representa el cardinal de Σ (i : El c), Elements (f i)
  card (hartogs zeroOrd) -- Placeholder para la construcción formal

/-- Producto cardinal sobre una familia indexada por un código `c`.
Representa el cardinal de Π (i : El c), Elements (f i). -/
noncomputable def cardProd (c : UCode) (f : El c → TOrdinal) : TOrdinal :=
  -- Placeholder para el producto dependiente constructivo
  card (hartogs zeroOrd)

end TarskiOrd
