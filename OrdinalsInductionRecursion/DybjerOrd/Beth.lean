import OrdinalsInductionRecursion.DybjerOrd.Cardinals
import OrdinalsInductionRecursion.DybjerOrd.Transfinite
import OrdinalsInductionRecursion.DybjerOrd.Alephs

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Exponenciación Cardinal
-- ==========================================

/-- Axioma para garantizar que la exponenciación (conjunto potencia) 
  tiene una cota cardinal superior en el universo de DybjerOrd. -/
axiom cardPow_exists (k : DOrdinal) : ∃ y : DOrdinal, ¬ InjectsInto y k

/-- Exponenciación Cardinal (2^k). -/
noncomputable def cardPow (k : DOrdinal) : DOrdinal :=
  card (wf_min ordinal_mem_wf (fun y => ¬ InjectsInto y k) (cardPow_exists k))

-- ==========================================
-- Sucesión de los números Beth (ℶ)
-- ==========================================

noncomputable def cardPow_pre (x : DPreOrd) : DPreOrd :=
  out (cardPow (Quotient.mk Setoid x))

/-- Definición por recursión estructural de la sucesión ℶ (Beth) -/
noncomputable def beth_pre : DPreOrd → DPreOrd
  | .zero => omega_pre
  | .succ x' => cardPow_pre (beth_pre x')
  | .sup c f => .sup c (fun a => beth_pre (f a))

-- (Placeholder axiomático para la equivalencia de beth)
axiom beth_respects_Equiv {x y : DPreOrd} (h : Equiv x y) : Equiv (beth_pre x) (beth_pre y)

noncomputable def beth (x : DOrdinal) : DOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk Setoid (beth_pre a) : DOrdinal))
    (fun _ _ h => Quotient.sound (beth_respects_Equiv h))

-- Algunos valores explícitos de la sucesión Beth
noncomputable def beth_zero : DOrdinal := beth zeroOrd
noncomputable def beth_one  : DOrdinal := beth (succOrd zeroOrd)
noncomputable def beth_omega: DOrdinal := beth omega

end DybjerOrd
