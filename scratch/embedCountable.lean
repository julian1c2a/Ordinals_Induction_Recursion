import OrdinalsInductionRecursion.UnivSets.Embeddings

universe u
namespace UnivSets

open Tree

mutual
  theorem embedCountableSetsTree_subset {x y : CountableSets.Tree} (h : CountableSets.Subset x y) : Tree.Subset (embedCountableSetsTree x) (embedCountableSetsTree y) :=
    match x, y, h with
    | _, _, .zero_subset y => Tree.Subset.sup_subset (fun a => nomatch a)
    | _, _, .succ_subset hmem =>
      -- y is some tree, x is .succ a. hmem : Mem a y
      -- embed (.succ a) = insertTree (embed a) emptyTree
      -- We must show Subset (insert (embed a) emptyTree) (embed y)
      -- This means all elements of (insert (embed a) emptyTree) are in (embed y).
      -- Elements of insert are either the elements of emptyTree (none) or (embed a).
      Tree.Subset.sup_subset fun i => match i with
        | none => embedCountableSetsTree_mem hmem
        | some a => nomatch a
    | _, _, .sup_subset hsub =>
      Tree.Subset.sup_subset fun n => embedCountableSetsTree_mem (hsub n.down)

  theorem embedCountableSetsTree_mem {x y : CountableSets.Tree} (h : CountableSets.Mem x y) : Tree.Mem (embedCountableSetsTree x) (embedCountableSetsTree y) :=
    match x, y, h with
    | _, _, .mem_succ hsub1 hsub2 =>
      -- embed (.succ y') = insert (embed y') emptyTree
      -- We must show Mem (embed x) (insert (embed y') emptyTree)
      -- By insert, it's either in emptyTree or it's `embed y'`.
      -- We can pick `none`, meaning `embed x` is equivalent to `embed y'`.
      Tree.Mem.mem_sup none (embedCountableSetsTree_subset hsub1) (embedCountableSetsTree_subset hsub2)
    | _, _, .mem_sup n hsub1 hsub2 =>
      Tree.Mem.mem_sup (ULift.up n) (embedCountableSetsTree_subset hsub1) (embedCountableSetsTree_subset hsub2)
end

theorem embedCountableSetsTree_respects_scratch {x y : CountableSets.Tree} (h : CountableSets.Equiv x y) : Tree.Equiv (embedCountableSetsTree x) (embedCountableSetsTree y) :=
  ⟨embedCountableSetsTree_subset h.left, embedCountableSetsTree_subset h.right⟩

end UnivSets
