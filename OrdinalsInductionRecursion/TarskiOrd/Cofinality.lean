import OrdinalsInductionRecursion.TarskiOrd.Cardinals
import OrdinalsInductionRecursion.TarskiOrd.Transfinite

namespace TarskiOrd
open TPreOrd
open Classical

-- ==========================================
-- Cofinalidad
-- ==========================================

/-- Una función `f` de los elementos de `x` a los elementos de `y` es cofinal
  si para todo elemento `a` en `y`, existe un elemento `b` en `x` tal que `a ≤ f(b)`. -/
def IsCofinal (x y : TOrdinal) (f : Elements x → Elements y) : Prop :=
  ∀ a : Elements y, ∃ b : Elements x, TOrdinal.Subset a.val (f b).val

/-- Dos ordinales están en relación cofinal si existe una función cofinal. -/
def Cofinal (x y : TOrdinal) : Prop :=
  ∃ f : Elements x → Elements y, IsCofinal x y f

/-- La cofinalidad de `y` es el mínimo ordinal `x` tal que existe un mapeo cofinal de `x` a `y`. -/
noncomputable def cf (y : TOrdinal) : TOrdinal :=
  if h : ∃ x, Cofinal x y then
    wf_min ordinal_mem_wf (fun x => Cofinal x y) h
  else
    zeroOrd -- Fallback

/-- Un cardinal es regular si su cofinalidad es él mismo. -/
def IsRegular (k : TCardinal) : Prop :=
  cf k.val = k.val

/-- Un cardinal es singular si su cofinalidad es estrictamente menor. -/
def IsSingular (k : TCardinal) : Prop :=
  TOrdinal.Mem (cf k.val) k.val

end TarskiOrd
