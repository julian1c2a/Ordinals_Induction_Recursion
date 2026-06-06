import OrdinalsInductionRecursion.TarskiOrd.Ordinals

namespace TarskiOrd
open TPreOrd

/-- 
El colapso de Mostowski constructivo de Tarski. 
Dada una relación bien fundada `r` sobre un tipo decodificado `El c` a partir de un `c : UCode`, 
mapea cada elemento `x : El c` a un pre-ordinal.
-/
noncomputable def mostowski_preord (c : UCode) (r : El c → El c → Prop) [DecidableRel r] (hwf : WellFounded r) : El c → TPreOrd :=
  WellFounded.fix hwf (fun x ih =>
    .sup c (fun y => 
      if h : r y x then 
        .succ (ih y h)
      else 
        .zero)
  )

theorem mostowski_preord_eq (c : UCode) (r : El c → El c → Prop) [DecidableRel r] (hwf : WellFounded r) (x : El c) :
  mostowski_preord c r hwf x = TPreOrd.sup c (fun y => if _h : r y x then TPreOrd.succ (mostowski_preord c r hwf y) else TPreOrd.zero) := by
  unfold mostowski_preord
  exact WellFounded.fix_eq hwf (fun x ih => TPreOrd.sup c (fun y => if h : r y x then TPreOrd.succ (ih y h) else TPreOrd.zero)) x

theorem mostowski_preord_mem (c : UCode) (r : El c → El c → Prop) [DecidableRel r] (hwf : WellFounded r) {x y : El c} (h : r y x) :
  TPreOrd.Mem (mostowski_preord c r hwf y) (mostowski_preord c r hwf x) := by
  have heq : mostowski_preord c r hwf x = TPreOrd.sup c (fun z => if h' : r z x then TPreOrd.succ (mostowski_preord c r hwf z) else TPreOrd.zero) := mostowski_preord_eq c r hwf x
  rw [heq]
  have h_y : (if h' : r y x then TPreOrd.succ (mostowski_preord c r hwf y) else TPreOrd.zero) = TPreOrd.succ (mostowski_preord c r hwf y) := by
    simp [h]
  have h_mem : TPreOrd.Mem (mostowski_preord c r hwf y) (TPreOrd.succ (mostowski_preord c r hwf y)) := TPreOrd.Mem_self_succ (mostowski_preord c r hwf y)
  have h_eq' : (TPreOrd.succ (mostowski_preord c r hwf y)) = (if h' : r y x then TPreOrd.succ (mostowski_preord c r hwf y) else TPreOrd.zero) := Eq.symm h_y
  rw [h_eq'] at h_mem
  exact TPreOrd.Mem.mem_sup y h_mem

/-- El colapso de Mostowski, elevado a `TOrdinal`. -/
noncomputable def mostowski_collapse (c : UCode) (r : El c → El c → Prop) [DecidableRel r] (hwf : WellFounded r) (x : El c) : TOrdinal :=
  Quotient.mk TPreOrd.Setoid (mostowski_preord c r hwf x)

theorem mostowski_collapse_mem (c : UCode) (r : El c → El c → Prop) [DecidableRel r] (hwf : WellFounded r) {x y : El c} (h : r y x) :
  TOrdinal.Mem (mostowski_collapse c r hwf y) (mostowski_collapse c r hwf x) := by
  exact mostowski_preord_mem c r hwf h

end TarskiOrd
