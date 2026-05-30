import OrdinalsInductionRecursion.Ordinals

namespace Ordinal

theorem le_refl (x : Ordinal) : x ≤ x :=
  Quotient.inductionOn x fun a => PreOrd.Subset_refl a

theorem le_trans {x y z : Ordinal} : x ≤ y → y ≤ z → x ≤ z :=
  Quotient.inductionOn₃ x y z fun a b c h1 h2 => PreOrd.Subset_trans h1 h2

theorem le_antisymm {x y : Ordinal} : x ≤ y → y ≤ x → x = y :=
  Quotient.inductionOn₂ x y fun a b h1 h2 => Quotient.sound ⟨h1, h2⟩

theorem subset_union_left (x y : Ordinal) : x ≤ union x y :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.subset_union_left a b

theorem subset_union_right (x y : Ordinal) : y ≤ union x y :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.subset_union_right a b

theorem union_subset {x y z : Ordinal} (hx : x ≤ z) (hy : y ≤ z) : union x y ≤ z :=
  Quotient.inductionOn₃ x y z fun a b c h1 h2 => PreOrd.union_subset h1 h2

theorem inter_subset_left (x y : Ordinal) : inter x y ≤ x :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.inter_subset_left a b

theorem inter_subset_right (x y : Ordinal) : inter x y ≤ y :=
  Quotient.inductionOn₂ x y fun a b => PreOrd.inter_subset_right a b

theorem subset_inter {x y z : Ordinal} (hx : z ≤ x) (hy : z ≤ y) : z ≤ inter x y :=
  Quotient.inductionOn₃ x y z fun a b c h1 h2 => PreOrd.subset_inter h1 h2

theorem union_comm (x y : Ordinal) : union x y = union y x :=
  le_antisymm (union_subset (subset_union_right y x) (subset_union_left y x))
              (union_subset (subset_union_right x y) (subset_union_left x y))

theorem inter_comm (x y : Ordinal) : inter x y = inter y x :=
  le_antisymm (subset_inter (inter_subset_right y x) (inter_subset_left y x))
              (subset_inter (inter_subset_right x y) (inter_subset_left x y))

end Ordinal
