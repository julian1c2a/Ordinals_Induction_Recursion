import OrdinalsInductionRecursion.TarskiOrd.Ordinals

namespace TarskiOrd
open TPreOrd

-- ==========================================
-- Buen Orden (Well-Foundedness)
-- ==========================================

theorem acc_of_subset {y z : TPreOrd} (hz : Acc Mem z) (hsub : TPreOrd.Subset y z) : Acc Mem y :=
  Acc.intro y (fun _w hw => hz.inv (Mem_Subset_trans hw hsub))

theorem preord_mem_acc (x : TPreOrd) : Acc Mem x :=
  match x with
  | .zero => Acc.intro _ (fun _ hy => nomatch hy)
  | .succ x' => 
    let acc_x' := preord_mem_acc x'
    Acc.intro _ (fun y hy => 
      match y, hy with
      | _, Mem.mem_succ hsub => acc_of_subset acc_x' hsub)
  | .sup _ f => 
    let acc_f := fun a => preord_mem_acc (f a)
    Acc.intro _ (fun y hy => 
      match y, hy with
      | _, Mem.mem_sup a hmem => (acc_f a).inv hmem)

theorem preord_mem_wf : WellFounded Mem :=
  ⟨preord_mem_acc⟩

theorem acc_lift {x : TPreOrd} (hx : Acc TPreOrd.Mem x) : Acc TOrdinal.Mem (Quotient.mk TPreOrd.Setoid x) :=
  hx.recOn fun _ _ IH =>
    Acc.intro _ fun y hy =>
      Quotient.inductionOn y (fun y' hy' => IH y' hy') hy

theorem ordinal_mem_wf : WellFounded TOrdinal.Mem :=
  ⟨fun a => Quotient.inductionOn a fun x => acc_lift (preord_mem_acc x)⟩

-- ==========================================
-- Orden Total (Trichotomy)
-- ==========================================

open Classical

theorem preord_total_order_and_lemma (x : TPreOrd) : 
  (∀ y, TPreOrd.Subset x y ∨ TPreOrd.Subset y x) ∧ 
  (∀ y, TPreOrd.Subset x y → ¬ TPreOrd.Mem x y → TPreOrd.Subset y (succ x)) := by
  induction x with
  | zero => 
    constructor
    · intro y; exact Or.inl (TPreOrd.Subset.zero_subset _)
    · intro y h1 h2
      induction y with
      | zero => exact TPreOrd.Subset.zero_subset _
      | succ y' _ => 
        have h_mem : TPreOrd.Mem zero (succ y') := TPreOrd.Mem.mem_succ (TPreOrd.Subset.zero_subset _)
        exact False.elim (h2 h_mem)
      | sup d g IHg =>
        exact TPreOrd.Subset.sup_subset fun a => IHg a (TPreOrd.Subset.zero_subset _) (fun h => h2 (TPreOrd.Mem.mem_sup a h))
  | succ x' IHx =>
    have part1 : ∀ y, TPreOrd.Subset (succ x') y ∨ TPreOrd.Subset y (succ x') := by
      intro y
      if h : TPreOrd.Mem x' y then
        exact Or.inl (TPreOrd.Subset.succ_subset h)
      else
        match IHx.1 y with
        | Or.inl hsub => exact Or.inr (IHx.2 y hsub h)
        | Or.inr hsub => exact Or.inr (TPreOrd.Subset_trans hsub (TPreOrd.mem_implies_subset (TPreOrd.Mem_self_succ x')))
    constructor
    · exact part1
    · intro y h1 h2
      induction y with
      | zero => exact TPreOrd.Subset.zero_subset _
      | succ y' _ =>
        match part1 y' with
        | Or.inl hsub => exact False.elim (h2 (TPreOrd.Mem.mem_succ hsub))
        | Or.inr hsub => exact TPreOrd.Subset.succ_subset (TPreOrd.Mem.mem_succ hsub)
      | sup d g IHg =>
        exact TPreOrd.Subset.sup_subset fun a =>
          match part1 (g a) with
          | Or.inl hsub => IHg a hsub (fun h => h2 (TPreOrd.Mem.mem_sup a h))
          | Or.inr hsub => TPreOrd.Subset_trans hsub (TPreOrd.mem_implies_subset (TPreOrd.Mem_self_succ (succ x')))
  | sup c f IHf =>
    have part1 : ∀ y, TPreOrd.Subset (sup c f) y ∨ TPreOrd.Subset y (sup c f) := by
      intro y
      if h : ∀ a, TPreOrd.Subset (f a) y then
        exact Or.inl (TPreOrd.Subset.sup_subset h)
      else
        have h_ex : ∃ a, ¬ TPreOrd.Subset (f a) y := by
          apply Classical.byContradiction
          intro hnot
          apply h
          intro a
          apply Classical.byContradiction
          intro hnot_a
          exact hnot ⟨a, hnot_a⟩
        let ⟨a, hna⟩ := Classical.indefiniteDescription _ h_ex
        match (IHf a).1 y with
        | Or.inl hsub => exact False.elim (hna hsub)
        | Or.inr hsub => exact Or.inr (TPreOrd.Subset_trans hsub (TPreOrd.Subset_sup (TPreOrd.Subset_refl _) a rfl))
    constructor
    · exact part1
    · intro y h1 h2
      induction y with
      | zero => exact TPreOrd.Subset.zero_subset _
      | succ y' _ =>
        match part1 y' with
        | Or.inl hsub => exact False.elim (h2 (TPreOrd.Mem.mem_succ hsub))
        | Or.inr hsub => exact TPreOrd.Subset.succ_subset (TPreOrd.Mem.mem_succ hsub)
      | sup d g IHg =>
        exact TPreOrd.Subset.sup_subset fun a =>
          match part1 (g a) with
          | Or.inl hsub => IHg a hsub (fun h => h2 (TPreOrd.Mem.mem_sup a h))
          | Or.inr hsub => TPreOrd.Subset_trans hsub (TPreOrd.mem_implies_subset (TPreOrd.Mem_self_succ (sup c f)))

theorem mem_succ_iff_subset (x y : TPreOrd) : TPreOrd.Mem x (succ y) ↔ TPreOrd.Subset x y :=
  ⟨fun h => by cases h with | mem_succ hsub => exact hsub, fun h => TPreOrd.Mem.mem_succ h⟩

theorem succ_subset_iff_mem (x y : TPreOrd) : TPreOrd.Subset (succ x) y ↔ TPreOrd.Mem x y :=
  ⟨fun h => by cases h with | succ_subset hmem => exact hmem, fun h => TPreOrd.Subset.succ_subset h⟩

theorem sup_subset_iff {c : UCode} {f : El c → TPreOrd} {y : TPreOrd} : TPreOrd.Subset (sup c f) y ↔ ∀ a, TPreOrd.Subset (f a) y :=
  ⟨fun h => by cases h with | sup_subset hall => exact hall, fun h => TPreOrd.Subset.sup_subset h⟩

theorem preord_total_order (x y : TPreOrd) : TPreOrd.Subset x y ∨ TPreOrd.Subset y x :=
  (preord_total_order_and_lemma x).1 y

theorem preord_subset_succ (x y : TPreOrd) : TPreOrd.Subset x y → ¬ TPreOrd.Mem x y → TPreOrd.Subset y (succ x) :=
  (preord_total_order_and_lemma x).2 y

theorem subset_succ_implies (y x : TPreOrd) (ih : ∀ z, TPreOrd.Subset z x → ¬ TPreOrd.Subset x z → TPreOrd.Mem z x) : TPreOrd.Subset y (succ x) → TPreOrd.Subset y x ∨ TPreOrd.Mem x y := by
  induction y with
  | zero => 
    intro _
    exact Or.inl (TPreOrd.Subset.zero_subset x)
  | succ y' ih_y =>
    intro hz_succ
    have h_mem_y_succ : TPreOrd.Mem y' (succ x) := (succ_subset_iff_mem y' (succ x)).1 hz_succ
    have h_sub : TPreOrd.Subset y' x := (mem_succ_iff_subset y' x).1 h_mem_y_succ
    if h_eq : TPreOrd.Subset x y' then
      exact Or.inr (TPreOrd.Mem.mem_succ h_eq)
    else
      exact Or.inl (TPreOrd.Subset.succ_subset (ih y' h_sub h_eq))
  | sup d g ih_g =>
    intro hz_succ
    if h_ex : ∃ a, TPreOrd.Mem x (g a) then
      let ⟨a, ha⟩ := h_ex
      exact Or.inr (TPreOrd.Mem.mem_sup a ha)
    else
      have h_all : ∀ a, TPreOrd.Subset (g a) x := by
        intro a
        have h_sub_ga_succ : TPreOrd.Subset (g a) (succ x) := (sup_subset_iff.1 hz_succ) a
        match ih_g a h_sub_ga_succ with
        | Or.inl hsub => exact hsub
        | Or.inr hmem => exact False.elim (h_ex ⟨a, hmem⟩)
      exact Or.inl (TPreOrd.Subset.sup_subset h_all)

theorem strict_subset_implies_mem (x : TPreOrd) : ∀ y, TPreOrd.Subset y x → ¬ TPreOrd.Subset x y → TPreOrd.Mem y x := by
  induction x with
  | zero =>
    intro y h1 h2
    have hz : Equiv y zero := ⟨h1, TPreOrd.Subset.zero_subset y⟩
    exact False.elim (h2 hz.2)
  | succ x' ih =>
    intro y h1 h2
    match subset_succ_implies y x' ih h1 with
    | Or.inl hyx' => exact TPreOrd.Mem.mem_succ hyx'
    | Or.inr hx'y => exact False.elim (h2 (TPreOrd.Subset.succ_subset hx'y))
  | sup c f ih =>
    intro y h1 h2
    have h_ex : ∃ a, ¬ TPreOrd.Subset (f a) y := by
      apply Classical.byContradiction
      intro h_not
      apply h2
      exact TPreOrd.Subset.sup_subset fun a => Classical.byContradiction fun hnot => h_not ⟨a, hnot⟩
    let ⟨a, ha⟩ := h_ex
    have hy_fa : TPreOrd.Subset y (f a) := by
      match preord_total_order y (f a) with
      | Or.inl hsub => exact hsub
      | Or.inr hsub => exact False.elim (ha hsub)
    exact TPreOrd.Mem.mem_sup a (ih a y hy_fa ha)

theorem ordinal_total_order (x y : TOrdinal) : TOrdinal.Subset x y ∨ TOrdinal.Subset y x :=
  Quotient.inductionOn₂ x y fun a b => preord_total_order a b

theorem strict_subset_implies_mem_ord (x y : TOrdinal) : TOrdinal.Subset x y → ¬ TOrdinal.Subset y x → TOrdinal.Mem x y :=
  Quotient.inductionOn₂ x y fun a b h1 h2 => strict_subset_implies_mem b a h1 h2

end TarskiOrd
