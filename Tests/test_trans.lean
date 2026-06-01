import OrdinalsInductionRecursion.PreOrd

open PreOrd

mutual
  theorem Subset_trans' {x y z : PreOrd} (h1 : Subset x y) (h2 : Subset y z) : Subset x z :=
    match x, y, h1 with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem1 => .succ_subset (Mem_Subset_trans' hmem1 h2)
    | _, _, .sup_subset hsub1 => .sup_subset fun n => Subset_trans' (hsub1 n) h2

  theorem Mem_Subset_trans' {x y z : PreOrd} (h1 : Mem x y) (h2 : Subset y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, .succ_subset hmem2 =>
      match x, y, h1 with
      | _, _, .mem_succ hsub1 => Subset_Mem_trans' hsub1 hmem2
    | _, _, .sup_subset hsub2 =>
      match x, y, h1 with
      | _, _, .mem_sup n hmem1 => Mem_Subset_trans' hmem1 (hsub2 n)

  theorem Subset_Mem_trans' {x y z : PreOrd} (h1 : Subset x y) (h2 : Mem y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .mem_succ hsub2 => .mem_succ (Subset_trans' h1 hsub2)
    | _, _, .mem_sup n hmem2 => .mem_sup n (Subset_Mem_trans' h1 hmem2)
end
