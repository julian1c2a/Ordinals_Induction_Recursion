import OrdinalsInductionRecursion.Ordinals

namespace Ordinal

theorem le_refl (x : Ordinal) : x ≤ x :=
  Quotient.inductionOn x fun a => PreOrd.Subset_refl a

theorem le_trans {x y z : Ordinal} : x ≤ y → y ≤ z → x ≤ z :=
  Quotient.inductionOn₃ x y z fun a b c h1 h2 => PreOrd.Subset_trans h1 h2

theorem le_antisymm {x y : Ordinal} : x ≤ y → y ≤ x → x = y :=
  Quotient.inductionOn₂ x y fun a b h1 h2 => Quotient.sound ⟨h1, h2⟩

instance : PartialOrder Ordinal where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

theorem le_sup_left (x y : Ordinal) : x ≤ union x y :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.subset_union_left a b

theorem le_sup_right (x y : Ordinal) : y ≤ union x y :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.subset_union_right a b

theorem sup_le {x y z : Ordinal} : x ≤ z → y ≤ z → union x y ≤ z :=
  Quotient.inductionOn₃ x y z fun a b c h1 h2 => PreOrd.union_subset h1 h2

instance : SemilatticeSup Ordinal where
  sup := union
  le_sup_left := le_sup_left
  le_sup_right := le_sup_right
  sup_le _ _ _ := sup_le

theorem inf_le_left (x y : Ordinal) : inter x y ≤ x :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.inter_subset_left a b

theorem inf_le_right (x y : Ordinal) : inter x y ≤ y :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.inter_subset_right a b

theorem le_inf {x y z : Ordinal} : x ≤ y → x ≤ z → x ≤ inter y z :=
  Quotient.inductionOn₃ x y z fun a b c h1 h2 => PreOrd.subset_inter h1 h2

instance : SemilatticeInf Ordinal where
  inf := inter
  inf_le_left := inf_le_left
  inf_le_right := inf_le_right
  le_inf _ _ _ := le_inf

instance : Lattice Ordinal where

end Ordinal
