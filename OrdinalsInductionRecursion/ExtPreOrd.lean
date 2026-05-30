/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.PreOrd

namespace PreOrd

-- ==========================================
-- Lemas de Equivalencia para Relaciones
-- ==========================================

theorem Subset_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Subset x₁ y₁ = Subset x₂ y₂ :=
  propext ⟨fun h => Subset_trans (Subset_trans hx.right h) hy.left,
           fun h => Subset_trans (Subset_trans hx.left h) hy.right⟩

theorem Mem_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Mem x₁ y₁ = Mem x₂ y₂ :=
  propext ⟨fun h => Mem_Subset_trans (Subset_Mem_trans hx.right h) hy.left,
           fun h => Mem_Subset_trans (Subset_Mem_trans hx.left h) hy.right⟩


-- ==========================================
-- Intersección Parcial
-- ==========================================

def inter_succ_y (ih_x : PreOrd → PreOrd) : PreOrd → PreOrd
  | .zero => .zero
  | .succ y' => .succ (ih_x y')
  | .sup g => .sup (fun n => inter_succ_y ih_x (g n))

def inter (x : PreOrd) : PreOrd → PreOrd :=
  match x with
  | .zero => fun _ => .zero
  | .sup f => fun y => .sup (fun n => inter (f n) y)
  | .succ x' => inter_succ_y (inter x')

theorem zero_inter_subset (y : PreOrd) : Subset (inter zero y) zero :=
  .zero_subset _

theorem inter_zero_subset (x : PreOrd) : Subset (inter x zero) zero :=
  match x with
  | .zero => .zero_subset _
  | .succ _ => .zero_subset _
  | .sup f => .sup_subset fun n => inter_zero_subset (f n)

mutual
  theorem inter_mono_right_subset_succ (x' : PreOrd)
    (ih_subset : ∀ {y₁ y₂}, Subset y₁ y₂ → Subset (inter x' y₁) (inter x' y₂))
    {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (inter (succ x') y₁) (inter (succ x') y₂) :=
    match y₁, y₂, h with
    | _, _, .zero_subset _ => Subset_trans (inter_zero_subset _) (.zero_subset _)
    | _, _, .succ_subset hmem => inter_mono_right_mem_succ x' @ih_subset hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => inter_mono_right_subset_succ x' @ih_subset (hsub n)

  theorem inter_mono_right_mem_succ (x' : PreOrd)
    (ih_subset : ∀ {y₁ y₂}, Subset y₁ y₂ → Subset (inter x' y₁) (inter x' y₂))
    {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Subset (inter (succ x') (succ y₁)) (inter (succ x') y₂) :=
    match y₂, h with
    | _, .mem_succ hsub => .succ_subset (.mem_succ (ih_subset hsub))
    | _, .mem_sup n hmem =>
      Subset_trans (inter_mono_right_mem_succ x' @ih_subset hmem)
        (Subset_sup (f := fun _ => inter (succ x') _) (Subset_refl _) n rfl)
end

theorem inter_mono_right_subset (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (inter x y₁) (inter x y₂) :=
  match x with
  | .zero => Subset_trans (inter_zero_subset zero) (.zero_subset _)
  | .sup f => .sup_subset fun n => Subset_sup (f := fun k => inter (f k) y₂) (inter_mono_right_subset (f n) h) n rfl
  | .succ x' => inter_mono_right_subset_succ x' (fun h' => inter_mono_right_subset x' h') h

theorem inter_mono_right_mem (x : PreOrd) {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Subset (inter x (succ y₁)) (inter x y₂) :=
  match x with
  | .zero => .zero_subset _
  | .sup f => .sup_subset fun n => Subset_sup (f := fun k => inter (f k) y₂) (inter_mono_right_mem (f n) h) n rfl
  | .succ x' => inter_mono_right_mem_succ x' (fun h' => inter_mono_right_subset x' h') h

theorem inter_mono_left_mem_mem_succ {x₁ x₂' : PreOrd} (hsub : Subset x₁ x₂')
  (ih_subset : ∀ y, Subset (inter x₁ y) (inter x₂' y)) (y : PreOrd) :
  Subset (inter (succ x₁) y) (inter (succ x₂') y) :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih_subset y'))
  | .sup g => .sup_subset fun n => Subset_sup (f := fun k => inter (succ x₂') (g k)) (inter_mono_left_mem_mem_succ hsub ih_subset (g n)) n rfl

mutual
  theorem inter_mono_left_subset {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (inter x₁ y) (inter x₂ y) :=
    match x₁, x₂, h with
    | _, _, .zero_subset _ => Subset_trans (zero_inter_subset y) (.zero_subset _)
    | _, _, .succ_subset hmem => inter_mono_left_mem hmem y
    | _, _, .sup_subset hsub => .sup_subset fun n => inter_mono_left_subset (hsub n) y

  theorem inter_mono_left_mem {x₁ x₂ : PreOrd} (h : Mem x₁ x₂) (y : PreOrd) : Subset (inter (succ x₁) y) (inter x₂ y) :=
    match x₂, h with
    | .succ _, .mem_succ hsub => inter_mono_left_mem_mem_succ hsub (fun y => inter_mono_left_subset hsub y) y
    | .sup f, .mem_sup n hmem =>
      Subset_trans (inter_mono_left_mem hmem y) (Subset_sup (f := fun k => inter (f k) y) (Subset_refl _) n rfl)
end

theorem inter_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (inter x₁ y₁) (inter x₂ y₂) :=
  ⟨Subset_trans (inter_mono_left_subset hx.left y₁) (inter_mono_right_subset x₂ hy.left),
   Subset_trans (inter_mono_left_subset hx.right y₂) (inter_mono_right_subset x₁ hy.right)⟩


theorem inter_succ_y_subset {x' : PreOrd}
  (ih : ∀ y, Subset (inter x' y) x') (y : PreOrd) : Subset (inter_succ_y (inter x') y) (succ x') :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih y'))
  | .sup g => .sup_subset fun n => inter_succ_y_subset ih (g n)

theorem inter_subset_left (x y : PreOrd) : Subset (inter x y) x :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => inter_succ_y_subset (fun y => inter_subset_left x' y) y
  | .sup f => .sup_subset fun n => Subset_sup (inter_subset_left (f n) y) n rfl

theorem inter_succ_y_subset_right {x' y : PreOrd}
  (ih : ∀ y, Subset (inter x' y) y) : Subset (inter_succ_y (inter x') y) y :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih y'))
  | .sup g => .sup_subset fun n => Subset_sup (inter_succ_y_subset_right ih) n rfl

theorem inter_subset_right (x y : PreOrd) : Subset (inter x y) y :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => inter_succ_y_subset_right (fun y => inter_subset_right x' y)
  | .sup f => .sup_subset fun n => inter_subset_right (f n) y



theorem subset_inter_fixed {x y : PreOrd} (H_mem : ∀ z, Mem z x → Mem z y → Mem z (inter x y))
  {z : PreOrd} (hx : Subset z x) (hy : Subset z y) : Subset z (inter x y) :=
  match z, hx, hy with
  | .zero, _, _ => .zero_subset _
  | .succ z', .succ_subset hx_mem, .succ_subset hy_mem => .succ_subset (H_mem z' hx_mem hy_mem)
  | .sup f, .sup_subset hx_sub, .sup_subset hy_sub => .sup_subset fun n => subset_inter_fixed H_mem (hx_sub n) (hy_sub n)

theorem mem_inter_succ_y_fixed {x' y : PreOrd} (H_sub : ∀ z y', Subset z x' → Subset z y' → Subset z (inter x' y'))
  {z : PreOrd} (hx : Subset z x') (hy : Mem z y) : Mem z (inter_succ_y (inter x') y) :=
  match y, hy with
  | .succ y', .mem_succ hy_sub => .mem_succ (H_sub z y' hx hy_sub)
  | .sup g, .mem_sup n hmem => .mem_sup n (mem_inter_succ_y_fixed H_sub hx hmem)

def mem_succ_cases {x' z : PreOrd} (hx : Mem z (succ x')) {motive : Mem z (succ x') → Prop}
  (f : ∀ hx_sub, motive (.mem_succ hx_sub)) : motive hx :=
  match hx with
  | .mem_succ hx_sub => f hx_sub

def mem_sup_cases {F : ℕ₀ → PreOrd} {z : PreOrd} (hx : Mem z (sup F)) {motive : Mem z (sup F) → Prop}
  (g : ∀ n hx_mem, motive (.mem_sup n hx_mem)) : motive hx :=
  match hx with
  | .mem_sup n hx_mem => g n hx_mem

def mem_zero_cases {z : PreOrd} (hx : Mem z zero) {motive : Mem z zero → Prop} : motive hx :=
  nomatch hx

def InterProp (x : PreOrd) : Prop :=
  ∀ y, (∀ z, Subset z x → Subset z y → Subset z (inter x y)) ∧
       (∀ z, Mem z x → Mem z y → Mem z (inter x y))

theorem inter_prop (x : PreOrd) : InterProp x :=
  match x with
  | .zero => fun y =>
    ⟨fun z hx hy => subset_inter_fixed (fun z hx hy => mem_zero_cases (motive := fun _ => Mem z (inter zero y)) hx) hx hy,
     fun z hx hy => mem_zero_cases (motive := fun _ => Mem z (inter zero y)) hx⟩
  | .succ x' => fun y =>
    let ih_x' := inter_prop x'
    let mem_prop : ∀ z, Mem z (succ x') → Mem z y → Mem z (inter (succ x') y) :=
      fun z hx hy => mem_succ_cases (motive := fun _ => Mem z (inter (succ x') y)) hx
        (fun hx_sub => mem_inter_succ_y_fixed (fun z y' => (ih_x' y').1 z) hx_sub hy)
    ⟨fun z hx hy => subset_inter_fixed mem_prop hx hy, mem_prop⟩
  | .sup f => fun y =>
    let ih_f := fun n => inter_prop (f n)
    let mem_prop : ∀ z, Mem z (sup f) → Mem z y → Mem z (inter (sup f) y) :=
      fun z hx hy => mem_sup_cases (motive := fun _ => Mem z (inter (sup f) y)) hx
        (fun n hx_mem => Mem.mem_sup n ((ih_f n y).2 z hx_mem hy))
    ⟨fun z hx hy => subset_inter_fixed mem_prop hx hy, mem_prop⟩

theorem subset_inter {x y z : PreOrd} (hx : Subset z x) (hy : Subset z y) : Subset z (inter x y) :=
  (inter_prop x y).1 z hx hy

theorem mem_inter {x y z : PreOrd} (hx : Mem z x) (hy : Mem z y) : Mem z (inter x y) :=
  (inter_prop x y).2 z hx hy



-- ==========================================
-- Unión Binaria
-- ==========================================

def union (x y : PreOrd) : PreOrd :=
  sup (fun n => match n with
    | .zero => x
    | .succ _ => y)

theorem union_mono_left {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (union x₁ y) (union x₂ y) :=
  Subset.sup_subset fun n => match n with
    | .zero => Subset_trans h (Subset_sup (Subset_refl x₂) .zero rfl)
    | .succ m => Subset_sup (Subset_refl y) (.succ m) rfl

theorem union_mono_right (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (union x y₁) (union x y₂) :=
  Subset.sup_subset fun n => match n with
    | .zero => Subset_sup (Subset_refl x) .zero rfl
    | .succ m => Subset_trans h (Subset_sup (Subset_refl y₂) (.succ m) rfl)

theorem union_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (union x₁ y₁) (union x₂ y₂) :=
  ⟨Subset_trans (union_mono_left hx.left y₁) (union_mono_right x₂ hy.left),
   Subset_trans (union_mono_left hx.right y₂) (union_mono_right x₁ hy.right)⟩


theorem subset_union_left (x y : PreOrd) : Subset x (union x y) :=
  Subset_sup (Subset_refl _) .zero rfl

theorem subset_union_right (x y : PreOrd) : Subset y (union x y) :=
  Subset_sup (Subset_refl _) (.succ .zero) rfl

theorem union_subset {x y z : PreOrd} (hx : Subset x z) (hy : Subset y z) : Subset (union x y) z :=
  .sup_subset fun n => match n with
    | .zero => hx
    | .succ _ => hy


-- ==========================================
-- Unión e Intersección General
-- ==========================================

def sUnion : PreOrd → PreOrd
  | .zero => .zero
  | .succ x => x
  | .sup f => sup (fun n => sUnion (f n))

mutual
  theorem mem_subset {a b : PreOrd} (h : Mem a b) : Subset a b :=
    match b, h with
    | _, .mem_succ hsub => subset_succ_mono hsub
    | _, .mem_sup n hmem => Subset_sup (mem_subset hmem) n rfl

  theorem subset_succ_mono {a b : PreOrd} (h : Subset a b) : Subset a (succ b) :=
    match a, b, h with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem => .succ_subset (.mem_succ (mem_subset hmem))
    | _, _, .sup_subset hsub => .sup_subset fun n => subset_succ_mono (hsub n)
end

theorem sUnion_subset_self (x : PreOrd) : Subset (sUnion x) x :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => subset_succ_mono (Subset_refl x')
  | .sup f => .sup_subset fun n => Subset_sup (sUnion_subset_self (f n)) n rfl

theorem sUnion_mono_mem {x y : PreOrd} (h : Mem x y) : Subset (sUnion x) y :=
  Subset_trans (sUnion_subset_self x) (mem_subset h)

theorem mem_sUnion {a b : PreOrd} (h : Mem a b) : Subset a (sUnion b) :=
  match b, h with
  | _, .mem_succ hsub => hsub
  | _, .mem_sup n hmem => Subset_sup (mem_sUnion hmem) n rfl

theorem sUnion_mono_subset {x y : PreOrd} (h : Subset x y) : Subset (sUnion x) (sUnion y) :=
  match x, y, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => mem_sUnion hmem
  | _, _, .sup_subset hsub => .sup_subset fun n => sUnion_mono_subset (hsub n)

theorem sUnion_respects {x y : PreOrd} (h : Equiv x y) : Equiv (sUnion x) (sUnion y) :=
  ⟨sUnion_mono_subset h.left, sUnion_mono_subset h.right⟩

def sInter : PreOrd → PreOrd
  | _ => zero

theorem sInter_respects {x y : PreOrd} (_ : Equiv x y) : Equiv (sInter x) (sInter y) :=
  ⟨Subset_refl _, Subset_refl _⟩


open Classical

def TotalProp (x : PreOrd) : Prop :=
  ∀ y, (Subset x y ∨ Subset y x) ∧ (Mem x y ∨ Subset y x) ∧ (Mem y x ∨ Subset x y)

theorem total_prop (x : PreOrd) : TotalProp x :=
  match x with
  | .zero => fun y =>
    let rec tz (y : PreOrd) : (Subset zero y ∨ Subset y zero) ∧ (Mem zero y ∨ Subset y zero) ∧ (Mem y zero ∨ Subset zero y) :=
      match y with
      | .zero => ⟨Or.inl (.zero_subset _), Or.inr (.zero_subset _), Or.inr (.zero_subset _)⟩
      | .succ y' => ⟨Or.inl (.zero_subset _), Or.inl (.mem_succ (.zero_subset _)), Or.inr (.zero_subset _)⟩
      | .sup g =>
        ⟨Or.inl (.zero_subset _),
         if h : ∃ n, Mem zero (g n) then
           let ⟨n, hn⟩ := h
           Or.inl (.mem_sup n hn)
         else
           Or.inr (.sup_subset fun n =>
             match (tz (g n)).2.1 with
             | Or.inl hn => False.elim (h ⟨n, hn⟩)
             | Or.inr hs => hs
           ),
         Or.inr (.zero_subset _)⟩
    tz y
  | .succ x' => fun y =>
    let ih_x := total_prop x'
    let rec ts (y : PreOrd) : (Subset (succ x') y ∨ Subset y (succ x')) ∧ (Mem (succ x') y ∨ Subset y (succ x')) ∧ (Mem y (succ x') ∨ Subset (succ x') y) :=
      match y with
      | .zero => ⟨Or.inr (.zero_subset _), Or.inr (.zero_subset _), Or.inl (.mem_succ (.zero_subset _))⟩
      | .succ y' =>
        let p1 : Subset (succ x') (succ y') ∨ Subset (succ y') (succ x') :=
          match (ih_x (succ y')).2.1 with
          | Or.inl hm => Or.inl (.succ_subset hm)
          | Or.inr hs => Or.inr (subset_succ_mono hs)
        let p2 : Mem (succ x') (succ y') ∨ Subset (succ y') (succ x') :=
          match (ih_x y').2.1 with
          | Or.inl hm => Or.inl (.mem_succ (.succ_subset hm))
          | Or.inr hs => Or.inr (.succ_subset (.mem_succ hs))
        let p3 : Mem (succ y') (succ x') ∨ Subset (succ x') (succ y') :=
          match (ih_x y').2.2 with
          | Or.inl hm => Or.inl (.mem_succ (.succ_subset hm))
          | Or.inr hs => Or.inr (.succ_subset (.mem_succ hs))
        ⟨p1, p2, p3⟩
      | .sup g =>
        let ih_y_n := fun n => ts (g n)
        let p1 : Subset (succ x') (sup g) ∨ Subset (sup g) (succ x') :=
          if h : ∃ n, Mem x' (g n) then
            let ⟨n, hn⟩ := h
            Or.inl (.succ_subset (.mem_sup n hn))
          else
            Or.inr (.sup_subset fun n =>
              match (ih_x (g n)).2.1 with
              | Or.inl hm => False.elim (h ⟨n, hm⟩)
              | Or.inr hs => subset_succ_mono hs
            )
        let p2 : Mem (succ x') (sup g) ∨ Subset (sup g) (succ x') :=
          if h : ∃ n, Mem (succ x') (g n) then
            let ⟨n, hn⟩ := h
            Or.inl (.mem_sup n hn)
          else
            Or.inr (.sup_subset fun n =>
              match (ih_y_n n).2.1 with
              | Or.inl hm => False.elim (h ⟨n, hm⟩)
              | Or.inr hs => hs
            )
        let p3 : Mem (sup g) (succ x') ∨ Subset (succ x') (sup g) :=
          if h : ∃ n, ¬ Subset (g n) x' then
            let ⟨n, hn⟩ := h
            Or.inr (
              match (ih_x (g n)).2.1 with
              | Or.inl hm => .succ_subset (.mem_sup n hm)
              | Or.inr hs => False.elim (hn hs)
            )
          else
            Or.inl (.mem_succ (.sup_subset fun n => 
              if hn : Subset (g n) x' then hn else False.elim (h ⟨n, hn⟩)
            ))
        ⟨p1, p2, p3⟩
    ts y
  | .sup f => fun y =>
    let ih_f := fun n => total_prop (f n)
    let rec total_sup (y : PreOrd) : (Subset (sup f) y ∨ Subset y (sup f)) ∧ (Mem (sup f) y ∨ Subset y (sup f)) ∧ (Mem y (sup f) ∨ Subset (sup f) y) :=
      match y with
      | .zero => 
        let p1 : Subset (sup f) zero ∨ Subset zero (sup f) := Or.inr (.zero_subset _)
        let p2 : Mem (sup f) zero ∨ Subset zero (sup f) := Or.inr (.zero_subset _)
        let p3 : Mem zero (sup f) ∨ Subset (sup f) zero :=
          if h : ∃ n, Mem zero (f n) then
            let ⟨n, hn⟩ := h
            Or.inl (.mem_sup n hn)
          else
            Or.inr (.sup_subset fun n =>
              match (ih_f n zero).2.2 with
              | Or.inl hm => False.elim (h ⟨n, hm⟩)
              | Or.inr hs => hs
            )
        ⟨p1, p2, p3⟩
      | .succ y' =>
        let p1 : Subset (sup f) (succ y') ∨ Subset (succ y') (sup f) :=
          if h : ∃ n, ¬ Subset (f n) (succ y') then
            let ⟨n, hn⟩ := h
            Or.inr (
              match (ih_f n (succ y')).1 with
              | Or.inl hs => False.elim (hn hs)
              | Or.inr hs => Subset_trans hs (Subset_sup (Subset_refl _) n rfl)
            )
          else
            Or.inl (.sup_subset fun n => if hn : Subset (f n) (succ y') then hn else False.elim (h ⟨n, hn⟩))
        let p2 : Mem (sup f) (succ y') ∨ Subset (succ y') (sup f) :=
          if h : ∃ n, ¬ Subset (f n) y' then
            let ⟨n, hn⟩ := h
            Or.inr (
              match (ih_f n y').2.2 with
              | Or.inl hm => .succ_subset (.mem_sup n hm)
              | Or.inr hs => False.elim (hn hs)
            )
          else
            Or.inl (.mem_succ (.sup_subset fun n => if hn : Subset (f n) y' then hn else False.elim (h ⟨n, hn⟩)))
        let p3 : Mem (succ y') (sup f) ∨ Subset (sup f) (succ y') :=
          if h : ∃ n, Mem (succ y') (f n) then
            let ⟨n, hn⟩ := h
            Or.inl (.mem_sup n hn)
          else
            Or.inr (.sup_subset fun n => 
              match (ih_f n (succ y')).2.2 with
              | Or.inl hm => False.elim (h ⟨n, hm⟩)
              | Or.inr hs => hs
            )
        ⟨p1, p2, p3⟩
      | .sup g =>
        let ih_y_n := fun m => total_sup (g m)
        let p1 : Subset (sup f) (sup g) ∨ Subset (sup g) (sup f) :=
          if h : ∃ n, ¬ Subset (f n) (sup g) then
            let ⟨n, hn⟩ := h
            Or.inr (
              match (ih_f n (sup g)).1 with
              | Or.inl hs => False.elim (hn hs)
              | Or.inr hs => Subset_trans hs (Subset_sup (Subset_refl _) n rfl)
            )
          else
            Or.inl (.sup_subset fun n => if hn : Subset (f n) (sup g) then hn else False.elim (h ⟨n, hn⟩))
        let p2 : Mem (sup f) (sup g) ∨ Subset (sup g) (sup f) :=
          if h : ∃ m, Mem (sup f) (g m) then
            let ⟨m, hm⟩ := h
            Or.inl (.mem_sup m hm)
          else
            Or.inr (.sup_subset fun m =>
              match (ih_y_n m).2.1 with
              | Or.inl hm => False.elim (h ⟨m, hm⟩)
              | Or.inr hs => hs
            )
        let p3 : Mem (sup g) (sup f) ∨ Subset (sup f) (sup g) :=
          if h : ∃ n, Mem (sup g) (f n) then
            let ⟨n, hn⟩ := h
            Or.inl (.mem_sup n hn)
          else
            Or.inr (.sup_subset fun n =>
              match (ih_f n (sup g)).2.2 with
              | Or.inl hm => False.elim (h ⟨n, hm⟩)
              | Or.inr hs => hs
            )
        ⟨p1, p2, p3⟩
    total_sup y

theorem le_total (x y : PreOrd) : Subset x y ∨ Subset y x :=
  (total_prop x y).1

end PreOrd
