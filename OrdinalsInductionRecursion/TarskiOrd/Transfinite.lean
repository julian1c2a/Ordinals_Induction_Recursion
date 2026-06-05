import OrdinalsInductionRecursion.TarskiOrd.Order
import OrdinalsInductionRecursion.TarskiOrd.Ordinals
import OrdinalsInductionRecursion.TarskiOrd.Universes
import OrdinalsInductionRecursion.TarskiOrd.Cardinals

namespace TarskiOrd
open TPreOrd
open Classical

-- ==========================================
-- Constantes y Operaciones Básicas
-- ==========================================

def zeroOrd : TOrdinal := Quotient.mk TPreOrd.Setoid zero

theorem succ_respects_Equiv {x y : TPreOrd} (h : Equiv x y) : Equiv (succ x) (succ y) :=
  ⟨TPreOrd.Subset.succ_subset ((TOrdinal.Mem_respects_Equiv h (Equiv_refl (succ y))).mpr (TPreOrd.Mem_self_succ y)),
   TPreOrd.Subset.succ_subset ((TOrdinal.Mem_respects_Equiv h.symm (Equiv_refl (succ x))).mpr (TPreOrd.Mem_self_succ x))⟩

def succOrd (x : TOrdinal) : TOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk TPreOrd.Setoid (succ a) : TOrdinal))
    (fun _ _ h => Quotient.sound (succ_respects_Equiv h))

theorem mem_self_succ_ord (x : TOrdinal) : TOrdinal.Mem x (succOrd x) :=
  Quotient.inductionOn x fun a => TPreOrd.Mem_self_succ a

-- ==========================================
-- Clasificadores de Ordinales
-- ==========================================

/-- Un ordinal es cero si es igual al ordinal cero. -/
def IsZero (x : TOrdinal) : Prop := x = zeroOrd

/-- Un ordinal es sucesor si existe algún y tal que x = succ y. -/
def IsSucc (x : TOrdinal) : Prop := ∃ y, x = succOrd y

/-- Un ordinal es límite si no es cero y no es sucesor. -/
def IsLimit (x : TOrdinal) : Prop := ¬ IsZero x ∧ ¬ IsSucc x

-- ==========================================
-- Inducción Transfinita
-- ==========================================

/-- 
Principio de Inducción Transfinita Clásica.
Divide la inducción sobre ordinales en tres casos: cero, sucesor y límite.
-/
theorem transfinite_induction (p : TOrdinal → Prop)
  (h_zero : p zeroOrd)
  (h_succ : ∀ x, p x → p (succOrd x))
  (h_limit : ∀ x, IsLimit x → (∀ y, TOrdinal.Mem y x → p y) → p x) :
  ∀ x, p x := by
  intro x
  apply WellFounded.induction ordinal_mem_wf x
  intro y ih
  by_cases hz : IsZero y
  · rw [hz]
    exact h_zero
  · by_cases hs : IsSucc y
    · have hs_copy := hs
      rcases hs_copy with ⟨z, hz_eq⟩
      rw [hz_eq]
      apply h_succ
      apply ih
      rw [hz_eq]
      exact mem_self_succ_ord z
    · exact h_limit y ⟨hz, hs⟩ ih

-- ==========================================
-- Recursión Transfinita (Limit Rec)
-- ==========================================

/-- 
Recursión Transfinita usando WellFounded.fix.
A diferencia de Inducción, esto devuelve un valor de tipo genérico α.
Se requiere poder definir la función en los tres casos basándose en los resultados anteriores.
-/
noncomputable def transfinite_rec {α : Sort u}
  (f_zero : α)
  (f_succ : TOrdinal → α → α)
  (f_limit : (x : TOrdinal) → IsLimit x → ((y : TOrdinal) → TOrdinal.Mem y x → α) → α) :
  TOrdinal → α :=
  WellFounded.fix ordinal_mem_wf (fun x ih =>
    if hz : IsZero x then
      f_zero
    else if hs : IsSucc x then
      -- Extraemos el predecesor usando el Axioma de Elección (o get!)
      -- Nota: dado que x es sucesor, existe un único predecesor en TOrdinal.
      -- Para Lean, es más fácil hacer un `choose` sobre `hs`.
      let z := Classical.choose hs
      have hz_eq : x = succOrd z := Classical.choose_spec hs
      f_succ z (ih z (by rw [hz_eq]; exact mem_self_succ_ord z))
    else
      f_limit x ⟨hz, hs⟩ ih
  )

end TarskiOrd
