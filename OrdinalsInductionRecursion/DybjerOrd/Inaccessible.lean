import OrdinalsInductionRecursion.DybjerOrd.Ordinals
import OrdinalsInductionRecursion.DybjerOrd.Cardinals
import OrdinalsInductionRecursion.DybjerOrd.Cofinality
import OrdinalsInductionRecursion.DybjerOrd.Beth
import OrdinalsInductionRecursion.DybjerOrd.Transfinite

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Definición de Límites Fuertes
-- ==========================================

/-- Un cardinal límite fuerte es aquel cerrado bajo exponenciación. -/
def IsStrongLimit (k : DCardinal) : Prop :=
  ∀ y : DOrdinal, DOrdinal.Mem y k.val → DOrdinal.Mem (cardPow y) k.val

/-- Un ordinal es no numerable si es estrictamente mayor que ω. -/
def IsUncountable (x : DOrdinal) : Prop :=
  DOrdinal.Mem omega x

-- ==========================================
-- Definición de Universo Inaccesible
-- ==========================================

/-- 
Un Universo (en el sentido de Grothendieck/inaccesible) es un cardinal 
que es regular, límite fuerte y no numerable. 
-/
def IsUniverse (k : DCardinal) : Prop :=
  IsRegular k ∧ IsStrongLimit k ∧ IsUncountable k.val

-- ==========================================
-- Axioma y Sucesión de Universos de Grothendieck
-- ==========================================

/-- Axioma de Universos de Grothendieck: Para todo ordinal, existe un universo que lo contiene. -/
axiom grothendieck_universes (x : DOrdinal) : ∃ U : DCardinal, DOrdinal.Mem x U.val ∧ IsUniverse U

/-- Obtiene el siguiente universo estrictamente mayor a partir de un ordinal dado. -/
noncomputable def nextUniverse (x : DOrdinal) : DOrdinal :=
  (Classical.choose (grothendieck_universes x)).val

noncomputable def nextUniverse_pre (x : DPreOrd) : DPreOrd :=
  out (nextUniverse (Quotient.mk Setoid x))

/-- 
Jerarquía de Universos (Ω_α) iterada constructivamente sobre DPreOrd. 
-/
noncomputable def omega_hierarchy_pre : DPreOrd → DPreOrd
  | .zero => nextUniverse_pre .zero
  | .succ x' => nextUniverse_pre (omega_hierarchy_pre x')
  | .sup c f => .sup c (fun a => omega_hierarchy_pre (f a))

-- (Placeholder axiomático para la equivalencia del lifting de la jerarquía omega)
axiom omega_hierarchy_respects_Equiv {x y : DPreOrd} (h : Equiv x y) : Equiv (omega_hierarchy_pre x) (omega_hierarchy_pre y)

/-- La sucesión de los Universos de Grothendieck iterada transfinitamente (Ω_α). -/
noncomputable def omega_hierarchy (x : DOrdinal) : DOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk Setoid (omega_hierarchy_pre a) : DOrdinal))
    (fun _ _ h => Quotient.sound (omega_hierarchy_respects_Equiv h))

-- Ejemplos concretos de la jerarquía
noncomputable def omega_zero : DOrdinal := omega_hierarchy zeroOrd
noncomputable def omega_one  : DOrdinal := omega_hierarchy (succOrd zeroOrd)

end DybjerOrd
