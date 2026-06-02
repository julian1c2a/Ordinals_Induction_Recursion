import OrdinalsInductionRecursion.TarskiOrd.Ordinals

namespace TarskiOrd

open TPreOrd

-- ==========================================
-- Aritmética Básica Computable
-- ==========================================

/-- Convertir números naturales estándar de Lean a Ordinales de Tarski. -/
def fromNat : Nat → TPreOrd
  | 0 => zero
  | Nat.succ n => succ (fromNat n)

-- ==========================================
-- Construcción de ω (Infinito Contable)
-- ==========================================

/-- 
El primer ordinal límite (ω).
Se construye explícitamente evaluando la función identidad 
sobre el código `.nat`, el cual es decodificado en `El .nat = Nat`.
Esto demuestra la pureza computacional de este esqueleto.
-/
def omega_pre : TPreOrd := 
  sup .nat (fun (n : Nat) => fromNat n)

def omega : TOrdinal := 
  Quotient.mk Setoid omega_pre

-- ==========================================
-- Construcción del Primer Universo de Grothendieck Interno (Ω_0)
-- ==========================================

/-- 
Para modelar un universo, necesitamos asignar a cada tipo en UCode
su supremo ordinal correspondiente.
Para simplificar, asignaremos a cada código un ordinal acotador.
-/
def code_bound : UCode → TPreOrd
  | .unit => succ zero
  | .nat => omega_pre
  | .sum a _b => succ (sup .unit (fun _ => code_bound a)) -- Simplificación para no calcular la suma real
  | .arrow _a b => succ (sup .unit (fun _ => code_bound b)) 
  | .univ _n => succ zero -- Un nivel base para evitar ciclos

/-- 
El primer Universo de Grothendieck de Tarski (Ω_0).
Se construye evaluando sobre todo el universo interno `UCode`.
Es decir, toma el supremo de todos los ordinales representables por cualquier código.
A diferencia de `UnivOrd`, esto no choca con `Type (u+1)`.
-/
def omega_univ_0_pre : TPreOrd :=
  sup (.univ 0) (fun (c : UCode) => code_bound c)

def omega_univ_0 : TOrdinal :=
  Quotient.mk Setoid omega_univ_0_pre

end TarskiOrd
