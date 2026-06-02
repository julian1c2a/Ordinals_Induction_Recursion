import Peano

open Peano

inductive Tree : Type where
  | zero : Tree
  | succ : Tree → Tree
  | sup  : (ℕ₀ → Tree) → Tree

mutual
  inductive Subset : Tree → Tree → Prop where
    | zero_subset (y : Tree) : Subset .zero y
    | succ_subset {x y : Tree} : Mem x y → Subset (.succ x) y
    | sup_subset {f : ℕ₀ → Tree} {y : Tree} : (∀ n, Mem (f n) y) → Subset (.sup f) y

  inductive Mem : Tree → Tree → Prop where
    | mem_succ {x y : Tree} : Subset x y → Subset y x → Mem x (.succ y)
    | mem_sup {x : Tree} {f : ℕ₀ → Tree} (n : ℕ₀) : Subset x (f n) → Subset (f n) x → Mem x (.sup f)
end

def Equiv (x y : Tree) : Prop := Subset x y ∧ Subset y x

theorem Subset_refl (x : Tree) : Subset x x :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => .succ_subset (.mem_succ (Subset_refl x') (Subset_refl x'))
  | .sup f => .sup_subset fun n => .mem_sup n (Subset_refl (f n)) (Subset_refl (f n))

theorem mem_self_succ (x : Tree) : Mem x (.succ x) :=
  .mem_succ (Subset_refl x) (Subset_refl x)

def trans_all (y : Tree) :
  (∀ {x z}, Subset x y → Subset y z → Subset x z) ∧
  (∀ {x z}, Mem x y → Subset y z → Mem x z) ∧
  (∀ {x z}, Subset y x → Subset x y → Mem y z → Mem x z) :=
  let mem_sub : ∀ {x z}, Mem x y → Subset y z → Mem x z := fun {x z} h1 h2 =>
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, @Subset.succ_subset a _ hmem2 =>
      match h1 with
      | @Mem.mem_succ _ _ hx_a ha_x => (trans_all a).2.2 ha_x hx_a hmem2
    | _, _, @Subset.sup_subset f _ hsub2 =>
      match h1 with
      | @Mem.mem_sup _ _ n hx_fn hfn_x => (trans_all (f n)).2.2 hfn_x hx_fn (hsub2 n)

  let sub_sub : ∀ {x z}, Subset x y → Subset y z → Subset x z := fun {x z} h1 h2 =>
    match x, h1 with
    | _, .zero_subset _ => .zero_subset _
    | _, @Subset.succ_subset d _ hmem => .succ_subset (mem_sub hmem h2)
    | _, @Subset.sup_subset f _ hsub => .sup_subset fun n => mem_sub (hsub n) h2

  let eq_mem : ∀ {x z}, Subset y x → Subset x y → Mem y z → Mem x z := fun {x z} hyx hxy hyz =>
    match z, hyz with
    | _, @Mem.mem_succ _ b hyb hby =>
      .mem_succ (sub_sub hxy hyb) (sub_sub hby hyx)
    | _, @Mem.mem_sup _ g n hyg hgy =>
      .mem_sup n (sub_sub hxy hyg) (sub_sub hgy hyx)

  ⟨sub_sub, mem_sub, eq_mem⟩
