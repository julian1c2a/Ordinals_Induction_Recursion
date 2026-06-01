import OrdinalsInductionRecursion.UnivSets.Embeddings

universe u
namespace UnivSets

open Tree

theorem mem_insertTree_of_mem {a x b : Tree.{u}} (h : Tree.Mem x b) : Tree.Mem x (insertTree a b) := by
  cases b
  rename_i β f
  cases h
  rename_i i h1 h2
  exact Tree.Mem.mem_sup (some i) h1 h2

theorem mem_insertTree_of_equiv {a x b : Tree.{u}} (h : Tree.Equiv x a) : Tree.Mem x (insertTree a b) := by
  cases b
  exact Tree.Mem.mem_sup none h.left h.right

theorem mem_unionTree_of_mem_sup {x : Tree.{u}} {α : Type u} {f : α → Tree.{u}} (a : α) (h : Tree.Mem x (f a)) : Tree.Mem x (unionTree (sup f)) := by
  have h_eta : f a = sup (indexFun (f a)) := tree_eta (f a)
  rw [h_eta] at h
  cases h
  rename_i j h1 h2
  exact Tree.Mem.mem_sup ⟨a, j⟩ h1 h2

theorem subset_insertTree_of_subset_and_mem {a b y : Tree.{u}} (hsub : Tree.Subset b y) (hmem : Tree.Mem a y) : Tree.Subset (insertTree a b) y := by
  cases b
  rename_i β f
  apply Tree.Subset.sup_subset
  intro i
  cases i with
  | none => exact hmem
  | some j =>
    cases hsub
    rename_i hsub_all
    exact hsub_all j

theorem subset_unionTree_of_subset {α : Type u} {f : α → Tree.{u}} {y : Tree.{u}} (h : ∀ a, Tree.Subset (f a) y) : Tree.Subset (unionTree (sup f)) y := by
  apply Tree.Subset.sup_subset
  intro p
  let a := p.1
  let j := p.2
  have hsub_a := h a
  have h_eta : f a = sup (indexFun (f a)) := tree_eta (f a)
  rw [h_eta] at hsub_a
  cases hsub_a
  rename_i h_all
  exact h_all j

def embed_all (x : PreOrd.{u}) :
  (∀ {y}, PreOrd.Subset x y → Tree.Subset (embedUnivOrdTree x) (embedUnivOrdTree y)) ∧
  (∀ {y}, PreOrd.Subset y x → Tree.Subset (embedUnivOrdTree y) (embedUnivOrdTree x)) ∧
  (∀ {y}, PreOrd.Mem x y → Tree.Mem (embedUnivOrdTree x) (embedUnivOrdTree y)) ∧
  (∀ {y}, PreOrd.Mem y x → Tree.Mem (embedUnivOrdTree y) (embedUnivOrdTree x)) :=
  match x with
  | .zero =>
    let p1 := fun {y} (h : PreOrd.Subset zero y) => Tree.Subset.sup_subset fun a => nomatch a
    let p4 := fun {y} (h : PreOrd.Mem y zero) => nomatch h
    let rec p2_zero {y} (h : PreOrd.Subset y zero) : Tree.Subset (embedUnivOrdTree y) emptyTree :=
      match y, h with
      | _, PreOrd.Subset.zero_subset _ => Tree.Subset.sup_subset fun a => nomatch a
      | _, @PreOrd.Subset.sup_subset _ f _ hsub =>
        subset_unionTree_of_subset fun i => p2_zero (hsub i)
    let rec p3_zero {y} (h : PreOrd.Mem zero y) : Tree.Mem emptyTree (embedUnivOrdTree y) :=
      match y, h with
      | _, @PreOrd.Mem.mem_succ _ b hsub =>
        match (PreOrd.total_prop zero b).2.1 with
        | Or.inl hmem => mem_insertTree_of_mem (p3_zero hmem)
        | Or.inr hsub2 => mem_insertTree_of_equiv ⟨p1 hsub, p2_zero hsub2⟩
      | _, @PreOrd.Mem.mem_sup _ _ f i hmem =>
        mem_unionTree_of_mem_sup i (p3_zero hmem)
    ⟨p1, p2_zero, p3_zero, p4⟩
  | .succ a =>
    let ih := embed_all a
    let p1 := fun {y} (h : PreOrd.Subset (PreOrd.succ a) y) =>
      match h with
      | @PreOrd.Subset.succ_subset _ _ hmem =>
        subset_insertTree_of_subset_and_mem (ih.1 (PreOrd.mem_implies_subset hmem)) (ih.2.2.1 hmem)
    let p4 := fun {y} (h : PreOrd.Mem y (PreOrd.succ a)) =>
      match h with
      | PreOrd.Mem.mem_succ hsub =>
        match (PreOrd.total_prop y a).2.1 with
        | Or.inl hmem => mem_insertTree_of_mem (ih.2.2.2 hmem)
        | Or.inr hsub2 => mem_insertTree_of_equiv ⟨ih.2.1 hsub, ih.1 hsub2⟩
    let rec p2_succ {y} (h : PreOrd.Subset y (PreOrd.succ a)) : Tree.Subset (embedUnivOrdTree y) (embedUnivOrdTree (PreOrd.succ a)) :=
      match y, h with
      | _, PreOrd.Subset.zero_subset _ => Tree.Subset.sup_subset fun i => nomatch i
      | _, @PreOrd.Subset.succ_subset b _ hmem =>
        subset_insertTree_of_subset_and_mem (p2_succ (PreOrd.mem_implies_subset hmem)) (p4 hmem)
      | _, @PreOrd.Subset.sup_subset _ f _ hsub =>
        subset_unionTree_of_subset fun i => p2_succ (hsub i)
    let rec p3_succ {y} (h : PreOrd.Mem (PreOrd.succ a) y) : Tree.Mem (embedUnivOrdTree (PreOrd.succ a)) (embedUnivOrdTree y) :=
      match y, h with
      | _, @PreOrd.Mem.mem_succ _ b hsub =>
        match (PreOrd.total_prop (PreOrd.succ a) b).2.1 with
        | Or.inl hmem => mem_insertTree_of_mem (p3_succ hmem)
        | Or.inr hsub2 => mem_insertTree_of_equiv ⟨p1 hsub, p2_succ hsub2⟩
      | _, @PreOrd.Mem.mem_sup _ _ f i hmem =>
        mem_unionTree_of_mem_sup i (p3_succ hmem)
    ⟨p1, p2_succ, p3_succ, p4⟩
  | .sup g =>
    let ih := fun i => embed_all (g i)
    let p1 := fun {y} (h : PreOrd.Subset (PreOrd.sup g) y) =>
      match h with
      | @PreOrd.Subset.sup_subset _ _ _ hsub =>
        subset_unionTree_of_subset fun i => (ih i).1 (hsub i)
    let p4 := fun {y} (h : PreOrd.Mem y (PreOrd.sup g)) =>
      match h with
      | @PreOrd.Mem.mem_sup _ _ _ i hmem =>
        mem_unionTree_of_mem_sup i ((ih i).2.2.2 hmem)
    let rec p2_sup {y} (h : PreOrd.Subset y (PreOrd.sup g)) : Tree.Subset (embedUnivOrdTree y) (embedUnivOrdTree (PreOrd.sup g)) :=
      match y, h with
      | _, PreOrd.Subset.zero_subset _ => Tree.Subset.sup_subset fun i => nomatch i
      | _, @PreOrd.Subset.succ_subset b _ hmem =>
        subset_insertTree_of_subset_and_mem (p2_sup (PreOrd.mem_implies_subset hmem)) (p4 hmem)
      | _, @PreOrd.Subset.sup_subset _ f _ hsub =>
        subset_unionTree_of_subset fun i => p2_sup (hsub i)
    let rec p3_sup {y} (h : PreOrd.Mem (PreOrd.sup g) y) : Tree.Mem (embedUnivOrdTree (PreOrd.sup g)) (embedUnivOrdTree y) :=
      match y, h with
      | _, @PreOrd.Mem.mem_succ _ b hsub =>
        match (PreOrd.total_prop (PreOrd.sup g) b).2.1 with
        | Or.inl hmem => mem_insertTree_of_mem (p3_sup hmem)
        | Or.inr hsub2 => mem_insertTree_of_equiv ⟨p1 hsub, p2_sup hsub2⟩
      | _, @PreOrd.Mem.mem_sup _ _ f i hmem =>
        mem_unionTree_of_mem_sup i (p3_sup hmem)
    ⟨p1, p2_sup, p3_sup, p4⟩

theorem embedUnivOrdTree_respects_scratch {x y : PreOrd.{u}} (h : PreOrd.Equiv x y) : Tree.Equiv (embedUnivOrdTree x) (embedUnivOrdTree y) :=
  ⟨(embed_all x).1 h.left, (embed_all y).1 h.right⟩

end UnivSets
