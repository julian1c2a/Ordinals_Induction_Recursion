import OrdinalsInductionRecursion.ExtPreOrd

namespace PreOrd

theorem inter_succ_y_subset {x' : PreOrd}
  (ih : ∀ y, Subset (inter x' y) x') (y : PreOrd) : Subset (inter_succ_y (inter x') y) (succ x') :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih y'))
  | .sup g => .sup_subset fun n => inter_succ_y_subset ih (g n)

theorem inter_subset_left (x y : PreOrd) : Subset (inter x y) x :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => inter_succ_y_subset (fun y => inter_subset_left x' y) y
  | .sup f => .sup_subset fun n => Subset_sup (inter_subset_left (f n) y) n rfl

theorem inter_succ_y_subset_right {x' y : PreOrd}
  (ih : ∀ y, Subset (inter x' y) y) : Subset (inter_succ_y (inter x') y) y :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih y'))
  | .sup g => .sup_subset fun n => Subset_sup (inter_succ_y_subset_right ih) n rfl

theorem inter_subset_right (x y : PreOrd) : Subset (inter x y) y :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => inter_succ_y_subset_right (fun y => inter_subset_right x' y)
  | .sup f => .sup_subset fun n => inter_subset_right (f n) y

end PreOrd
