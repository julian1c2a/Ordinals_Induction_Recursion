import OrdinalsInductionRecursion.CountableOrd.Ordinals
import OrdinalsInductionRecursion.CountableOrd.ExtPreOrd

namespace CountableOrd
namespace Ordinal

theorem le_refl (x : Ordinal) : x ≤ x :=
  Quotient.inductionOn x fun _ => PreOrd.Subset_refl _

theorem le_trans {x y z : Ordinal} : x ≤ y → y ≤ z → x ≤ z :=
  Quotient.inductionOn₃ x y z fun _ _ _ h1 h2 => PreOrd.Subset_trans h1 h2

theorem le_antisymm {x y : Ordinal} : x ≤ y → y ≤ x → x = y :=
  Quotient.inductionOn₂ x y fun _ _ h1 h2 => Quotient.sound ⟨h1, h2⟩

theorem subset_union_left (x y : Ordinal) : x ≤ union x y :=
  Quotient.inductionOn₂ x y fun _ _ => PreOrd.subset_union_left _ _

theorem subset_union_right (x y : Ordinal) : y ≤ union x y :=
  Quotient.inductionOn₂ x y fun _ _ => PreOrd.subset_union_right _ _

theorem union_subset {x y z : Ordinal} : x ≤ z → y ≤ z → union x y ≤ z :=
  Quotient.inductionOn₃ x y z fun _ _ _ h1 h2 => PreOrd.union_subset h1 h2

theorem inter_subset_left (x y : Ordinal) : inter x y ≤ x :=
  Quotient.inductionOn₂ x y fun _ _ => PreOrd.inter_subset_left _ _

theorem inter_subset_right (x y : Ordinal) : inter x y ≤ y :=
  Quotient.inductionOn₂ x y fun _ _ => PreOrd.inter_subset_right _ _

theorem subset_inter {x y z : Ordinal} : z ≤ x → z ≤ y → z ≤ inter x y :=
  Quotient.inductionOn₃ x y z fun _ _ _ h1 h2 => PreOrd.subset_inter h1 h2

theorem union_comm (x y : Ordinal) : union x y = union y x :=
  le_antisymm (union_subset (subset_union_right y x) (subset_union_left y x))
              (union_subset (subset_union_right x y) (subset_union_left x y))

theorem inter_comm (x y : Ordinal) : inter x y = inter y x :=
  le_antisymm (subset_inter (z := inter x y) (x := y) (y := x) (inter_subset_right x y) (inter_subset_left x y))
              (subset_inter (z := inter y x) (x := x) (y := y) (inter_subset_right y x) (inter_subset_left y x))

theorem le_total (x y : Ordinal) : x ≤ y ∨ y ≤ x :=
  Quotient.inductionOn₂ x y fun _ _ => PreOrd.le_total _ _

theorem inter_union_distrib_left (x y z : Ordinal) : inter x (union y z) = union (inter x y) (inter x z) := by
  match le_total y z with
  | .inl hyz =>
    have H1 : union y z = z := le_antisymm (union_subset hyz (le_refl _)) (subset_union_right y z)
    rw [H1]
    have H2 : inter x y ≤ inter x z := subset_inter (inter_subset_left _ _) (le_trans (inter_subset_right _ _) hyz)
    have H3 : union (inter x y) (inter x z) = inter x z := le_antisymm (union_subset H2 (le_refl _)) (subset_union_right _ _)
    rw [H3]
  | .inr hzy =>
    have H1 : union y z = y := le_antisymm (union_subset (le_refl _) hzy) (subset_union_left y z)
    rw [H1]
    have H2 : inter x z ≤ inter x y := subset_inter (inter_subset_left _ _) (le_trans (inter_subset_right _ _) hzy)
    have H3 : union (inter x y) (inter x z) = inter x y := le_antisymm (union_subset (le_refl _) H2) (subset_union_left _ _)
    rw [H3]

end Ordinal
end CountableOrd
