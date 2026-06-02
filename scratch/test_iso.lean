import OrdinalsInductionRecursion.UnivOrd.Ordinals

universe u

namespace UnivOrd
namespace Isomorphism

open PreOrd

variable {α : Type u} (r : α → α → Prop)

def collapse_F (x : α) (f : (y : α) → r y x → PreOrd.{u}) : PreOrd.{u} :=
  PreOrd.sup (α := {y : α // r y x}) fun y => PreOrd.succ (f y.val y.property)

def collapse_aux (hwf : WellFounded r) (a : α) : PreOrd.{u} :=
  WellFounded.fix hwf (collapse_F r) a

theorem mem_collapse_aux {hwf : WellFounded r} {a b : α} (h : r a b) : 
    PreOrd.Mem (collapse_aux r hwf a) (collapse_aux r hwf b) := by
  have hb : collapse_aux r hwf b = collapse_F r b (fun y _ => collapse_aux r hwf y) := 
    WellFounded.fix_eq hwf (collapse_F r) b
  rw [hb, collapse_F]
  apply PreOrd.Mem.mem_sup (⟨a, h⟩ : {y // r y b})
  apply PreOrd.Mem_self_succ

end Isomorphism
end UnivOrd
