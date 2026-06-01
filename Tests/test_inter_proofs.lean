import OrdinalsInductionRecursion.ExtPreOrd

namespace PreOrd

theorem zero_inter_subset (y : PreOrd) : Subset (inter zero y) zero :=
  .zero_subset _

theorem inter_zero_subset (x : PreOrd) : Subset (inter x zero) zero :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => .zero_subset _
  | .sup f => .sup_subset fun n => inter_zero_subset (f n)

mutual
  theorem inter_mono_right_subset_succ (x' : PreOrd)
    (ih_subset : ∀ {y₁ y₂}, Subset y₁ y₂ → Subset (inter x' y₁) (inter x' y₂))
    {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (inter (succ x') y₁) (inter (succ x') y₂) :=
    match y₁, y₂, h with
    | _, _, .zero_subset _ => Subset_trans (inter_zero_subset _) (.zero_subset _)
    | _, _, .succ_subset hmem => inter_mono_right_mem_succ x' @ih_subset hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => inter_mono_right_subset_succ x' @ih_subset (hsub n)

  theorem inter_mono_right_mem_succ (x' : PreOrd)
    (ih_subset : ∀ {y₁ y₂}, Subset y₁ y₂ → Subset (inter x' y₁) (inter x' y₂))
    {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Subset (inter (succ x') (succ y₁)) (inter (succ x') y₂) :=
    match y₂, h with
    | _, .mem_succ hsub => .succ_subset (.mem_succ (ih_subset hsub))
    | _, .mem_sup n hmem =>
      Subset_trans (inter_mono_right_mem_succ x' @ih_subset hmem)
        (Subset_sup (f := fun k => inter (succ x') _) (Subset_refl _) n rfl)
end

theorem inter_mono_right_subset (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (inter x y₁) (inter x y₂) :=
  match x with
  | .zero => Subset_trans (inter_zero_subset zero) (.zero_subset _)
  | .sup f => .sup_subset fun n => Subset_sup (f := fun k => inter (f k) y₂) (inter_mono_right_subset (f n) h) n rfl
  | .succ x' => inter_mono_right_subset_succ x' (fun h' => inter_mono_right_subset x' h') h

theorem inter_mono_right_mem (x : PreOrd) {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Subset (inter x (succ y₁)) (inter x y₂) :=
  match x with
  | .zero => .zero_subset _
  | .sup f => .sup_subset fun n => Subset_sup (f := fun k => inter (f k) y₂) (inter_mono_right_mem (f n) h) n rfl
  | .succ x' => inter_mono_right_mem_succ x' (fun h' => inter_mono_right_subset x' h') h

theorem inter_mono_left_mem_mem_succ {x₁ x₂' : PreOrd} (hsub : Subset x₁ x₂')
  (ih_subset : ∀ y, Subset (inter x₁ y) (inter x₂' y)) (y : PreOrd) :
  Subset (inter (succ x₁) y) (inter (succ x₂') y) :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih_subset y'))
  | .sup g => .sup_subset fun n => Subset_sup (f := fun k => inter (succ x₂') (g k)) (inter_mono_left_mem_mem_succ hsub ih_subset (g n)) n rfl

mutual
  theorem inter_mono_left_subset {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (inter x₁ y) (inter x₂ y) :=
    match x₁, x₂, h with
    | _, _, .zero_subset _ => Subset_trans (zero_inter_subset y) (.zero_subset _)
    | _, _, .succ_subset hmem => inter_mono_left_mem hmem y
    | _, _, .sup_subset hsub => .sup_subset fun n => inter_mono_left_subset (hsub n) y

  theorem inter_mono_left_mem {x₁ x₂ : PreOrd} (h : Mem x₁ x₂) (y : PreOrd) : Subset (inter (succ x₁) y) (inter x₂ y) :=
    match x₂, h with
    | .succ x₂', .mem_succ hsub => inter_mono_left_mem_mem_succ hsub (fun y => inter_mono_left_subset hsub y) y
    | .sup f, .mem_sup n hmem =>
      Subset_trans (inter_mono_left_mem hmem y) (Subset_sup (f := fun k => inter (f k) y) (Subset_refl _) n rfl)
end

theorem inter_respects_proof {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (inter x₁ y₁) (inter x₂ y₂) :=
  ⟨Subset_trans (inter_mono_left_subset hx.left y₁) (inter_mono_right_subset x₂ hy.left),
   Subset_trans (inter_mono_left_subset hx.right y₂) (inter_mono_right_subset x₁ hy.right)⟩

end PreOrd
