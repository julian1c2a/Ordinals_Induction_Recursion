import OrdinalsInductionRecursion.DybjerOrd.Cardinals
import OrdinalsInductionRecursion.DybjerOrd.Transfinite

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Cofinalidad
-- ==========================================

/-- Una función `f` de los elementos de `x` a los elementos de `y` es cofinal
  si para todo elemento `a` en `y`, existe un elemento `b` en `x` tal que `a ≤ f(b)`. -/
def IsCofinal (x y : DOrdinal) (f : Elements x → Elements y) : Prop :=
  ∀ a : Elements y, ∃ b : Elements x, DOrdinal.Subset a.val (f b).val

/-- Dos ordinales están en relación cofinal si existe una función cofinal. -/
def Cofinal (x y : DOrdinal) : Prop :=
  ∃ f : Elements x → Elements y, IsCofinal x y f

/-- La cofinalidad de `y` es el mínimo ordinal `x` tal que existe un mapeo cofinal de `x` a `y`. -/
noncomputable def cf (y : DOrdinal) : DOrdinal :=
  if h : ∃ x, Cofinal x y then
    wf_min ordinal_mem_wf (fun x => Cofinal x y) h
  else
    zeroOrd

/-- Un cardinal es regular si su cofinalidad es él mismo. -/
def IsRegular (k : DCardinal) : Prop :=
  cf k.val = k.val

/-- Un cardinal es singular si su cofinalidad es estrictamente menor. -/
def IsSingular (k : DCardinal) : Prop :=
  DOrdinal.Mem (cf k.val) k.val

end DybjerOrd
