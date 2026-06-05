import OrdinalsInductionRecursion.DybjerOrd.Ordinals

namespace DybjerOrd

open DPreOrd

-- ==========================================
-- Aritmética Básica Computable
-- ==========================================

/-- Convertir números naturales estándar de Lean a Ordinales de Dybjer. -/
def fromNat : Nat → DPreOrd
  | 0 => .zero
  | Nat.succ n => .succ (fromNat n)

-- ==========================================
-- Construcción de ω (Infinito Contable)
-- ==========================================

/-- 
El primer ordinal límite (ω).
Se construye explícitamente evaluando la función identidad 
sobre el código `.nat`, el cual es decodificado en `Nat`.
-/
def omega_pre : DPreOrd := 
  .sup .nat (fun (n : Nat) => fromNat n)

def omega : DOrdinal := 
  Quotient.mk Setoid omega_pre

end DybjerOrd
