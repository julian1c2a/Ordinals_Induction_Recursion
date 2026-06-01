import OrdinalsInductionRecursion.UnivSets.Axioms

universe u
namespace UnivSets

open Tree

theorem unionTree_subset_unionTree_scratch {a1 a2 : Tree.{u}} (h : Tree.Subset a1 a2) : Tree.Subset (unionTree a1) (unionTree a2) := by
  cases a1; cases a2
  rename_i α1 f1 α2 f2
  cases h
  rename_i hsub
  apply Tree.Subset.sup_subset
  intro p
  let x1 := p.1
  let y1 := p.2
  have h_mem_f1_f2 := hsub x1
  cases h_mem_f1_f2
  rename_i x2 h_f1_sub_f2 h_f2_sub_f1
  have h_eta1 : f1 x1 = sup (indexFun (f1 x1)) := tree_eta (f1 x1)
  have h_eta2 : f2 x2 = sup (indexFun (f2 x2)) := tree_eta (f2 x2)
  rw [h_eta1] at h_f1_sub_f2
  cases h_f1_sub_f2
  rename_i h_inner
  have h_mem_y1 := h_inner y1
  -- h_mem_y1 : Mem (indexFun (f1 x1) y1) (f2 x2)
  rw [h_eta2] at h_mem_y1
  cases h_mem_y1
  rename_i y2 h_sub1 h_sub2
  exact Tree.Mem.mem_sup (⟨x2, y2⟩ : Σ x, indexType (f2 x)) h_sub1 h_sub2
