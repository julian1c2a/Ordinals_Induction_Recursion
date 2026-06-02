import OrdinalsInductionRecursion.CountableOrd.Ordinals

open CountableOrd.PreOrd
open CountableOrd

namespace CountableOrd.PreOrd

theorem succ_respects {a1 a2 : PreOrd} (ha : Equiv a1 a2) : Equiv (succ a1) (succ a2) :=
  ⟨Subset.succ_subset (Subset_Mem_trans ha.left (Mem_self_succ a2)),
   Subset.succ_subset (Subset_Mem_trans ha.right (Mem_self_succ a1))⟩

end CountableOrd.PreOrd

namespace CountableOrd.Ordinal

def succ (x : Ordinal) : Ordinal :=
  Quotient.lift (fun a => Quotient.mk PreOrd.Setoid (PreOrd.succ a)) (fun _ _ h => Quotient.sound (PreOrd.succ_respects h)) x

def zero : Ordinal := Quotient.mk PreOrd.Setoid PreOrd.zero

def IsLimit (x : Ordinal) : Prop := x ≠ zero ∧ ∀ y < x, succ y < x ∨ succ y = x

theorem zero_succ_limit (x : Ordinal) : x = zero ∨ (∃ y, x = succ y) ∨ IsLimit x := sorry

end CountableOrd.Ordinal
