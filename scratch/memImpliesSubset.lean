import OrdinalsInductionRecursion.UnivOrd.Ordinals

universe u
namespace PreOrd

def trans_y (y : PreOrd.{u}) :
  (Subset y (succ y)) ∧
  (∀ {x}, Mem x y → Subset x y) :=
  match y with
  | .zero =>
    ⟨Subset.zero_subset _, fun h => nomatch h⟩
  | .succ a =>
    let ih := trans_y a
    let self_succ := Subset.succ_subset (Mem.mem_succ ih.1)
    let rec sub_succ_a {x} (h : Subset x a) : Subset x (succ a) :=
      match x, h with
      | _, Subset.zero_subset _ => Subset.zero_subset _
      | _, @Subset.succ_subset z _ hmem =>
        Subset.succ_subset (Mem.mem_succ (ih.2 hmem))
      | _, @Subset.sup_subset _ g _ hsub =>
        Subset.sup_subset fun j => sub_succ_a (hsub j)
    let mem_sub := fun {x} (h : Mem x (succ a)) =>
      match x, h with
      | _, Mem.mem_succ hsub => sub_succ_a hsub
    ⟨self_succ, mem_sub⟩
  | .sup f =>
    let ih := fun i => trans_y (f i)
    let mem_sub := fun {x} (h : Mem x (sup f)) =>
      match x, h with
      | _, Mem.mem_sup i hmem => Subset_sup ((ih i).2 hmem) i rfl
    let rec sub_succ_sup {x} (h : Subset x (sup f)) : Subset x (succ (sup f)) :=
      match x, h with
      | _, Subset.zero_subset _ => Subset.zero_subset _
      | _, @Subset.succ_subset z _ hmem =>
        Subset.succ_subset (Mem.mem_succ (mem_sub hmem))
      | _, @Subset.sup_subset _ g _ hsub =>
        Subset.sup_subset fun j => sub_succ_sup (hsub j)
    let self_succ := Subset.sup_subset fun i => sub_succ_sup (Subset_sup (Subset_refl _) i rfl)
    ⟨self_succ, mem_sub⟩

theorem mem_implies_subset {x y : PreOrd.{u}} (h : Mem x y) : Subset x y :=
  (trans_y y).2 h

end PreOrd
