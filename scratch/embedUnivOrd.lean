import OrdinalsInductionRecursion.UnivSets.Embeddings

universe u
namespace UnivSets

open Tree

mutual
  theorem embedUnivOrdTree_subset {x y : PreOrd.{u}} (h : PreOrd.Subset x y) : Tree.Subset (embedUnivOrdTree x) (embedUnivOrdTree y) :=
    match x, y, h with
    | _, _, .zero_subset y => Tree.Subset.sup_subset (fun a => nomatch a)
    | _, _, .succ_subset hmem =>
      Tree.Subset.sup_subset fun i => match i with
        | none => embedUnivOrdTree_mem hmem
        | some a => Tree.Mem_Subset_trans (Tree.Mem.mem_sup (some a) (Tree.Subset_refl _) (Tree.Subset_refl _)) (embedUnivOrdTree_subset (PreOrd.mem_implies_subset hmem))
    | _, _, .sup_subset hsub =>
      Tree.Subset.sup_subset fun a => embedUnivOrdTree_mem (hsub a)

  theorem embedUnivOrdTree_mem {x y : PreOrd.{u}} (h : PreOrd.Mem x y) : Tree.Mem (embedUnivOrdTree x) (embedUnivOrdTree y) :=
    match x, y, h with
    | _, _, .mem_succ hsub =>
      Tree.Mem.mem_sup none (embedUnivOrdTree_subset hsub) (embedUnivOrdTree_subset (sorry))
    | _, _, .mem_sup a hmem =>
      Tree.Mem.mem_sup ⟨a, sorry⟩ (embedUnivOrdTree_subset sorry) (embedUnivOrdTree_subset sorry)
end

theorem embedUnivOrdTree_respects_scratch {x y : PreOrd.{u}} (h : PreOrd.Equiv x y) : Tree.Equiv (embedUnivOrdTree x) (embedUnivOrdTree y) :=
  ⟨embedUnivOrdTree_subset h.left, embedUnivOrdTree_subset h.right⟩

end UnivSets
