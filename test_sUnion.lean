import OrdinalsInductionRecursion.ExtPreOrd

namespace PreOrd

mutual
  theorem mem_subset_proof {a b : PreOrd} (h : Mem a b) : Subset a b :=
    match b, h with
    | _, .mem_succ hsub => subset_succ_mono_proof hsub
    | _, .mem_sup n hmem => Subset_sup (mem_subset_proof hmem) n rfl

  theorem subset_succ_mono_proof {a b : PreOrd} (h : Subset a b) : Subset a (succ b) :=
    match a, b, h with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem => .succ_subset (.mem_succ (mem_subset_proof hmem))
    | _, _, .sup_subset hsub => .sup_subset fun n => subset_succ_mono_proof (hsub n)
end

theorem sUnion_subset_self_proof (x : PreOrd) : Subset (sUnion x) x :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => subset_succ_mono_proof (Subset_refl x')
  | .sup f => .sup_subset fun n => Subset_sup (sUnion_subset_self_proof (f n)) n rfl

theorem sUnion_mono_mem_proof {x y : PreOrd} (h : Mem x y) : Subset (sUnion x) y :=
  Subset_trans (sUnion_subset_self_proof x) (mem_subset_proof h)

theorem mem_sUnion_proof {a b : PreOrd} (h : Mem a b) : Subset a (sUnion b) :=
  match b, h with
  | _, .mem_succ hsub => hsub
  | _, .mem_sup n hmem => Subset_sup (mem_sUnion_proof hmem) n rfl

theorem sUnion_mono_subset_proof {x y : PreOrd} (h : Subset x y) : Subset (sUnion x) (sUnion y) :=
  match x, y, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => mem_sUnion_proof hmem
  | _, _, .sup_subset hsub => .sup_subset fun n => sUnion_mono_subset_proof (hsub n)

end PreOrd
