import OrdinalsInductionRecursion.DybjerOrd.Order
import OrdinalsInductionRecursion.DybjerOrd.Ordinals
import OrdinalsInductionRecursion.DybjerOrd.Cardinals

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Constantes y Operaciones Básicas
-- ==========================================

def zeroOrd : DOrdinal := Quotient.mk Setoid .zero

theorem succ_respects_Equiv {x y : DPreOrd} (h : Equiv x y) : Equiv (.succ x) (.succ y) :=
  ⟨DSubset.succ_subset ((DOrdinal.Mem_respects_Equiv h (Equiv_refl (.succ y))).mpr (DMem_self_succ y)),
   DSubset.succ_subset ((DOrdinal.Mem_respects_Equiv h.symm (Equiv_refl (.succ x))).mpr (DMem_self_succ x))⟩

def succOrd (x : DOrdinal) : DOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk Setoid (.succ a) : DOrdinal))
    (fun _ _ h => Quotient.sound (succ_respects_Equiv h))

theorem mem_self_succ_ord (x : DOrdinal) : DOrdinal.Mem x (succOrd x) :=
  Quotient.inductionOn x fun a => DMem_self_succ a

-- ==========================================
-- Clasificadores de Ordinales
-- ==========================================

/-- Un ordinal es cero si es igual al ordinal cero. -/
def IsZero (x : DOrdinal) : Prop := x = zeroOrd

/-- Un ordinal es sucesor si existe algún y tal que x = succ y. -/
def IsSucc (x : DOrdinal) : Prop := ∃ y, x = succOrd y

/-- Un ordinal es límite si no es cero y no es sucesor. -/
def IsLimit (x : DOrdinal) : Prop := ¬ IsZero x ∧ ¬ IsSucc x

-- ==========================================
-- Inducción Transfinita
-- ==========================================

/-- 
Principio de Inducción Transfinita Clásica.
Divide la inducción sobre ordinales en tres casos: cero, sucesor y límite.
-/
theorem transfinite_induction (p : DOrdinal → Prop)
  (h_zero : p zeroOrd)
  (h_succ : ∀ x, p x → p (succOrd x))
  (h_limit : ∀ x, IsLimit x → (∀ y, DOrdinal.Mem y x → p y) → p x) :
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
  (f_succ : DOrdinal → α → α)
  (f_limit : (x : DOrdinal) → IsLimit x → ((y : DOrdinal) → DOrdinal.Mem y x → α) → α) :
  DOrdinal → α :=
  WellFounded.fix ordinal_mem_wf (fun x ih =>
    if hz : IsZero x then
      f_zero
    else if hs : IsSucc x then
      let z := Classical.choose hs
      have hz_eq : x = succOrd z := Classical.choose_spec hs
      f_succ z (ih z (by rw [hz_eq]; exact mem_self_succ_ord z))
    else
      f_limit x ⟨hz, hs⟩ ih
  )

end DybjerOrd
