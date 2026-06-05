import OrdinalsInductionRecursion.DybjerOrd.Ordinals

namespace DybjerOrd
open DPreOrd

/-- 
El colapso de Mostowski constructivo de Dybjer. 
Dada una relación bien fundada `r` sobre un tipo `A` que tiene un código `cA` en `UCodeFam A`, 
mapea cada elemento `x : A` a un pre-ordinal.
La idea es tomar el supremo sobre todos los `y : A`, pero si `y` no es un predecesor de `x`, se le asigna `0`.
-/
noncomputable def mostowski_preord {A : Type} (cA : UCodeFam A) (r : A → A → Prop) [DecidableRel r] (hwf : WellFounded r) : A → DPreOrd :=
  WellFounded.fix hwf (fun x ih =>
    .sup cA (fun y => 
      if h : r y x then 
        .succ (ih y h)
      else 
        .zero)
  )

theorem mostowski_preord_eq {A : Type} (cA : UCodeFam A) (r : A → A → Prop) [DecidableRel r] (hwf : WellFounded r) (x : A) :
  mostowski_preord cA r hwf x = DPreOrd.sup cA (fun y => if _h : r y x then DPreOrd.succ (mostowski_preord cA r hwf y) else DPreOrd.zero) := by
  unfold mostowski_preord
  exact WellFounded.fix_eq hwf (fun x ih => DPreOrd.sup cA (fun y => if h : r y x then DPreOrd.succ (ih y h) else DPreOrd.zero)) x

theorem mostowski_preord_mem {A : Type} (cA : UCodeFam A) (r : A → A → Prop) [DecidableRel r] (hwf : WellFounded r) {x y : A} (h : r y x) :
  DMem (mostowski_preord cA r hwf y) (mostowski_preord cA r hwf x) := by
  have heq : mostowski_preord cA r hwf x = DPreOrd.sup cA (fun z => if h' : r z x then DPreOrd.succ (mostowski_preord cA r hwf z) else DPreOrd.zero) := mostowski_preord_eq cA r hwf x
  rw [heq]
  have h_y : (if h' : r y x then DPreOrd.succ (mostowski_preord cA r hwf y) else DPreOrd.zero) = DPreOrd.succ (mostowski_preord cA r hwf y) := by
    simp [h]
  have h_mem : DMem (mostowski_preord cA r hwf y) (DPreOrd.succ (mostowski_preord cA r hwf y)) := DMem.mem_succ (DSubset_refl _)
  have h_eq' : (DPreOrd.succ (mostowski_preord cA r hwf y)) = (if h' : r y x then DPreOrd.succ (mostowski_preord cA r hwf y) else DPreOrd.zero) := Eq.symm h_y
  rw [h_eq'] at h_mem
  exact DMem.mem_sup y h_mem

/-- El colapso de Mostowski, elevado a `DOrdinal`. -/
noncomputable def mostowski_collapse {A : Type} (cA : UCodeFam A) (r : A → A → Prop) [DecidableRel r] (hwf : WellFounded r) (x : A) : DOrdinal :=
  Quotient.mk Setoid (mostowski_preord cA r hwf x)

theorem mostowski_collapse_mem {A : Type} (cA : UCodeFam A) (r : A → A → Prop) [DecidableRel r] (hwf : WellFounded r) {x y : A} (h : r y x) :
  DOrdinal.Mem (mostowski_collapse cA r hwf y) (mostowski_collapse cA r hwf x) := by
  exact mostowski_preord_mem cA r hwf h

end DybjerOrd
