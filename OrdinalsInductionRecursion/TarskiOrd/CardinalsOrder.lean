import OrdinalsInductionRecursion.TarskiOrd.Cardinals

namespace TarskiOrd
open TPreOrd
open Classical

-- ==========================================
-- Orden Cardinal (cardLe)
-- ==========================================

/-- El orden cardinal es simplemente la inyectabilidad. -/
def cardLe (x y : TOrdinal) : Prop := InjectsInto x y

/-- Reflexividad del orden cardinal -/
theorem cardLe_refl (x : TOrdinal) : cardLe x x :=
  Subset_implies_InjectsInto (Quotient.inductionOn x fun a => TPreOrd.Subset_refl a)

/-- Transitividad del orden cardinal -/
theorem cardLe_trans {x y z : TOrdinal} (h1 : cardLe x y) (h2 : cardLe y z) : cardLe x z :=
  InjectsInto_trans h1 h2

/-- El orden ordinal implica el orden cardinal -/
theorem ordinal_le_implies_card_le {x y : TOrdinal} (h : TOrdinal.Subset x y) : cardLe x y :=
  Subset_implies_InjectsInto h

/-- Orden estricto cardinal -/
def cardLt (x y : TOrdinal) : Prop := cardLe x y ∧ ¬ cardLe y x

-- ==========================================
-- Monotonía Cardinal Simple
-- ==========================================

-- Las pruebas completas requieren definir explícitamente operaciones en Elements.
-- Aquí dejamos declarada la intención teórica de la monotonía.

end TarskiOrd
