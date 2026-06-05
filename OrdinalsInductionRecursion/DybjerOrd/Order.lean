import OrdinalsInductionRecursion.DybjerOrd.Ordinals

namespace DybjerOrd

-- ==========================================
-- Buen Orden (Well-Foundedness)
-- ==========================================

theorem acc_of_subset {y z : DPreOrd} (hz : Acc DMem z) (hsub : DSubset y z) : Acc DMem y :=
  Acc.intro y (fun _w hw => hz.inv (DMem_DSubset_trans hw hsub))

theorem preord_mem_acc (x : DPreOrd) : Acc DMem x :=
  match x with
  | .zero => Acc.intro _ (fun _ hy => nomatch hy)
  | .succ x' => 
    let acc_x' := preord_mem_acc x'
    Acc.intro _ (fun y hy => 
      match y, hy with
      | _, DMem.mem_succ hsub => acc_of_subset acc_x' hsub)
  | .sup _ f => 
    let acc_f := fun a => preord_mem_acc (f a)
    Acc.intro _ (fun y hy => 
      match y, hy with
      | _, DMem.mem_sup a hmem => (acc_f a).inv hmem)

theorem preord_mem_wf : WellFounded DMem :=
  ⟨preord_mem_acc⟩

theorem acc_lift {x : DPreOrd} (hx : Acc DMem x) : Acc DOrdinal.Mem (Quotient.mk Setoid x) :=
  hx.recOn fun _ _ IH =>
    Acc.intro _ fun y hy =>
      Quotient.inductionOn y (fun y' hy' => IH y' hy') hy

theorem ordinal_mem_wf : WellFounded DOrdinal.Mem :=
  ⟨fun a => Quotient.inductionOn a fun x => acc_lift (preord_mem_acc x)⟩

-- ==========================================
-- Orden Total (Trichotomy)
-- ==========================================

open Classical

theorem preord_total_order_and_lemma (x : DPreOrd) : 
  (∀ y, DSubset x y ∨ DSubset y x) ∧ 
  (∀ y, DSubset x y → ¬ DMem x y → DSubset y (.succ x)) := by
  induction x with
  | zero => 
    constructor
    · intro y; exact Or.inl (DSubset.zero_subset _)
    · intro y h1 h2
      induction y with
      | zero => exact DSubset.zero_subset _
      | succ y' _ => 
        have h_mem : DMem .zero (.succ y') := DMem.mem_succ (DSubset.zero_subset _)
        exact False.elim (h2 h_mem)
      | sup d g IHg =>
        exact DSubset.sup_subset fun a => IHg a (DSubset.zero_subset _) (fun h => h2 (DMem.mem_sup a h))
  | succ x' IHx =>
    have part1 : ∀ y, DSubset (.succ x') y ∨ DSubset y (.succ x') := by
      intro y
      if h : DMem x' y then
        exact Or.inl (DSubset.succ_subset h)
      else
        match IHx.1 y with
        | Or.inl hsub => exact Or.inr (IHx.2 y hsub h)
        | Or.inr hsub => exact Or.inr (DSubset_trans hsub (Dmem_implies_subset (DMem_self_succ x')))
    constructor
    · exact part1
    · intro y h1 h2
      induction y with
      | zero => exact DSubset.zero_subset _
      | succ y' _ =>
        match part1 y' with
        | Or.inl hsub => exact False.elim (h2 (DMem.mem_succ hsub))
        | Or.inr hsub => exact DSubset.succ_subset (DMem.mem_succ hsub)
      | sup d g IHg =>
        exact DSubset.sup_subset fun a =>
          match part1 (g a) with
          | Or.inl hsub => IHg a hsub (fun h => h2 (DMem.mem_sup a h))
          | Or.inr hsub => DSubset_trans hsub (Dmem_implies_subset (DMem_self_succ (.succ x')))
  | sup c f IHf =>
    have part1 : ∀ y, DSubset (.sup c f) y ∨ DSubset y (.sup c f) := by
      intro y
      if h : ∀ a, DSubset (f a) y then
        exact Or.inl (DSubset.sup_subset h)
      else
        have h_ex : ∃ a, ¬ DSubset (f a) y := by
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
        | Or.inr hsub => exact Or.inr (DSubset_trans hsub (DSubset_sup (DSubset_refl _) a rfl))
    constructor
    · exact part1
    · intro y h1 h2
      induction y with
      | zero => exact DSubset.zero_subset _
      | succ y' _ =>
        match part1 y' with
        | Or.inl hsub => exact False.elim (h2 (DMem.mem_succ hsub))
        | Or.inr hsub => exact DSubset.succ_subset (DMem.mem_succ hsub)
      | sup d g IHg =>
        exact DSubset.sup_subset fun a =>
          match part1 (g a) with
          | Or.inl hsub => IHg a hsub (fun h => h2 (DMem.mem_sup a h))
          | Or.inr hsub => DSubset_trans hsub (Dmem_implies_subset (DMem_self_succ (.sup c f)))

theorem mem_succ_iff_subset (x y : DPreOrd) : DMem x (.succ y) ↔ DSubset x y :=
  ⟨fun h => by cases h with | mem_succ hsub => exact hsub, fun h => DMem.mem_succ h⟩

theorem succ_subset_iff_mem (x y : DPreOrd) : DSubset (.succ x) y ↔ DMem x y :=
  ⟨fun h => by cases h with | succ_subset hmem => exact hmem, fun h => DSubset.succ_subset h⟩

theorem sup_subset_iff {A : Type} {c : UCodeFam A} {f : A → DPreOrd} {y : DPreOrd} : DSubset (.sup c f) y ↔ ∀ a, DSubset (f a) y :=
  ⟨fun h => by cases h with | sup_subset hall => exact hall, fun h => DSubset.sup_subset h⟩

theorem preord_total_order (x y : DPreOrd) : DSubset x y ∨ DSubset y x :=
  (preord_total_order_and_lemma x).1 y

theorem preord_subset_succ (x y : DPreOrd) : DSubset x y → ¬ DMem x y → DSubset y (.succ x) :=
  (preord_total_order_and_lemma x).2 y

theorem subset_succ_implies (y x : DPreOrd) (ih : ∀ z, DSubset z x → ¬ DSubset x z → DMem z x) : DSubset y (.succ x) → DSubset y x ∨ DMem x y := by
  induction y with
  | zero => 
    intro _
    exact Or.inl (DSubset.zero_subset x)
  | succ y' ih_y =>
    intro hz_succ
    have h_mem_y_succ : DMem y' (.succ x) := (succ_subset_iff_mem y' (.succ x)).1 hz_succ
    have h_sub : DSubset y' x := (mem_succ_iff_subset y' x).1 h_mem_y_succ
    if h_eq : DSubset x y' then
      exact Or.inr (DMem.mem_succ h_eq)
    else
      exact Or.inl (DSubset.succ_subset (ih y' h_sub h_eq))
  | sup d g ih_g =>
    intro hz_succ
    if h_ex : ∃ a, DMem x (g a) then
      let ⟨a, ha⟩ := h_ex
      exact Or.inr (DMem.mem_sup a ha)
    else
      have h_all : ∀ a, DSubset (g a) x := by
        intro a
        have h_sub_ga_succ : DSubset (g a) (.succ x) := (sup_subset_iff.1 hz_succ) a
        match ih_g a h_sub_ga_succ with
        | Or.inl hsub => exact hsub
        | Or.inr hmem => exact False.elim (h_ex ⟨a, hmem⟩)
      exact Or.inl (DSubset.sup_subset h_all)

theorem strict_subset_implies_mem (x : DPreOrd) : ∀ y, DSubset y x → ¬ DSubset x y → DMem y x := by
  induction x with
  | zero =>
    intro y h1 h2
    have hz : Equiv y .zero := ⟨h1, DSubset.zero_subset y⟩
    exact False.elim (h2 hz.2)
  | succ x' ih =>
    intro y h1 h2
    match subset_succ_implies y x' ih h1 with
    | Or.inl hyx' => exact DMem.mem_succ hyx'
    | Or.inr hx'y => exact False.elim (h2 (DSubset.succ_subset hx'y))
  | sup c f ih =>
    intro y h1 h2
    have h_ex : ∃ a, ¬ DSubset (f a) y := by
      apply Classical.byContradiction
      intro h_not
      apply h2
      exact DSubset.sup_subset fun a => Classical.byContradiction fun hnot => h_not ⟨a, hnot⟩
    let ⟨a, ha⟩ := h_ex
    have hy_fa : DSubset y (f a) := by
      match preord_total_order y (f a) with
      | Or.inl hsub => exact hsub
      | Or.inr hsub => exact False.elim (ha hsub)
    exact DMem.mem_sup a (ih a y hy_fa ha)

theorem ordinal_total_order (x y : DOrdinal) : DOrdinal.Subset x y ∨ DOrdinal.Subset y x :=
  Quotient.inductionOn₂ x y fun a b => preord_total_order a b

theorem strict_subset_implies_mem_ord (x y : DOrdinal) : DOrdinal.Subset x y → ¬ DOrdinal.Subset y x → DOrdinal.Mem x y :=
  Quotient.inductionOn₂ x y fun a b h1 h2 => strict_subset_implies_mem b a h1 h2

end DybjerOrd
