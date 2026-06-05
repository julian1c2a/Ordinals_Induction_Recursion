import OrdinalsInductionRecursion.DybjerOrd.Lattice
import OrdinalsInductionRecursion.DybjerOrd.Arith

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Definición de Equipotencia
-- ==========================================

/-- Una biyección genérica entre dos tipos. -/
structure Bijection (α β : Type 1) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b

/-- El tipo de los elementos (ordinales estrictamente menores) de un ordinal. -/
def Elements (x : DOrdinal) : Type 1 := { y : DOrdinal // DOrdinal.Mem y x }

/-- Dos ordinales son equipotentes si existe una biyección entre sus tipos de elementos. -/
def Equipotent (x y : DOrdinal) : Prop := Nonempty (Bijection (Elements x) (Elements y))

-- ==========================================
-- Propiedades de Equipotencia
-- ==========================================

theorem Equipotent_refl (x : DOrdinal) : Equipotent x x :=
  ⟨{ toFun := id, invFun := id, left_inv := fun _ => rfl, right_inv := fun _ => rfl }⟩

theorem Equipotent_symm {x y : DOrdinal} (h : Equipotent x y) : Equipotent y x :=
  h.elim fun e => ⟨{ toFun := e.invFun, invFun := e.toFun, left_inv := e.right_inv, right_inv := e.left_inv }⟩

theorem Equipotent_trans {x y z : DOrdinal} (h1 : Equipotent x y) (h2 : Equipotent y z) : Equipotent x z :=
  h1.elim fun e1 => h2.elim fun e2 => 
    ⟨{ toFun := fun a => e2.toFun (e1.toFun a),
       invFun := fun c => e1.invFun (e2.invFun c),
       left_inv := fun a => by simp [e1.left_inv, e2.left_inv],
       right_inv := fun c => by simp [e1.right_inv, e2.right_inv] }⟩

-- ==========================================
-- Definición de Cardinal
-- ==========================================

/-- Un ordinal es un cardinal si ningún ordinal estrictamente menor es equipotente a él. -/
def IsCardinal (x : DOrdinal) : Prop := ∀ y, DOrdinal.Mem y x → ¬ Equipotent y x

/-- El subtipo empaquetado para Cardinales. -/
def DCardinal : Type 1 := { x : DOrdinal // IsCardinal x }

-- ==========================================
-- Primeros Cardinales
-- ==========================================

theorem zero_le (y : DOrdinal) : (Quotient.mk Setoid .zero : DOrdinal) ≤ y :=
  Quotient.inductionOn y fun a => DSubset.zero_subset a

theorem not_mem_zero (y : DOrdinal) : ¬ DOrdinal.Mem y (Quotient.mk Setoid .zero) :=
  Quotient.inductionOn y fun a h => by cases h

theorem zero_is_cardinal : IsCardinal (Quotient.mk Setoid .zero) := by
  intro y hy
  exact False.elim (not_mem_zero y hy)

def card_zero : DCardinal := ⟨Quotient.mk Setoid .zero, zero_is_cardinal⟩

-- ==========================================
-- Teorema y Función de Hartogs
-- ==========================================

/-- Una inyección genérica entre dos tipos. -/
structure Injection (α β : Type 1) where
  toFun : α → β
  inj' : ∀ a b, toFun a = toFun b → a = b

/-- Un ordinal x se inyecta en y si existe una inyección entre sus tipos de elementos. -/
def InjectsInto (x y : DOrdinal) : Prop := Nonempty (Injection (Elements x) (Elements y))

theorem Mem_Subset_trans {x y z : DOrdinal} : DOrdinal.Mem x y → DOrdinal.Subset y z → DOrdinal.Mem x z :=
  Quotient.inductionOn₃ x y z fun _ _ _ hab hbc => DMem_DSubset_trans hab hbc

/-- Si x ⊆ y, la inclusión natural nos da una inyección de los elementos de x en y. -/
theorem Subset_implies_InjectsInto {x y : DOrdinal} (h : DOrdinal.Subset x y) : InjectsInto x y :=
  ⟨{ toFun := fun a => ⟨a.val, Mem_Subset_trans a.property h⟩,
     inj' := fun ⟨aval, aprop⟩ ⟨bval, bprop⟩ heq => by
       have hval : aval = bval := by injection heq
       exact Subtype.ext hval }⟩

/-- El Teorema de Hartogs axiomatizado. 
  Garantiza que para todo ordinal x, existe algún ordinal γ que no se puede inyectar en x. -/
axiom hartogs_exists (x : DOrdinal) : ∃ γ, ¬ InjectsInto γ x

theorem wf_has_min {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r) (p : α → Prop) (h : ∃ x, p x) : ∃ m, p m ∧ ∀ y, p y → ¬ r y m :=
  Classical.byContradiction fun h_contra =>
    have h_all : ∀ x, ¬ p x := fun x =>
      @WellFounded.induction α r hwf (fun z => ¬ p z) x (fun x' ih hpx =>
        have h_step : ∃ y, p y ∧ r y x' :=
          Classical.byContradiction fun hn =>
            h_contra ⟨x', hpx, fun y hpy hr => hn ⟨y, hpy, hr⟩⟩
        Exists.elim h_step fun y hy =>
          ih y hy.right hy.left)
    Exists.elim h fun x hpx => h_all x hpx

noncomputable def wf_min {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r) (p : α → Prop) (h : ∃ x, p x) : α :=
  Classical.choose (wf_has_min hwf p h)

theorem wf_min_mem {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r) (p : α → Prop) (h : ∃ x, p x) : p (wf_min hwf p h) :=
  (Classical.choose_spec (wf_has_min hwf p h)).left

theorem not_lt_wf_min {α : Sort u} {r : α → α → Prop} (hwf : WellFounded r) (p : α → Prop) (h : ∃ x, p x) : ∀ y, p y → ¬ r y (wf_min hwf p h) :=
  (Classical.choose_spec (wf_has_min hwf p h)).right

/-- La función de Hartogs devuelve el menor ordinal que no se inyecta en x. -/
noncomputable def hartogs (x : DOrdinal) : DOrdinal :=
  wf_min ordinal_mem_wf (fun γ => ¬ InjectsInto γ x) (hartogs_exists x)

/-- Propiedad fundamental de la minimización: hartogs x no se inyecta en x. -/
theorem hartogs_not_injects (x : DOrdinal) : ¬ InjectsInto (hartogs x) x :=
  wf_min_mem ordinal_mem_wf (fun γ => ¬ InjectsInto γ x) (hartogs_exists x)

/-- Si y ∈ hartogs x, entonces y sí se inyecta en x (por minimalidad). -/
theorem mem_hartogs_injects {x y : DOrdinal} (h : DOrdinal.Mem y (hartogs x)) : InjectsInto y x :=
  Classical.byContradiction fun hn =>
    not_lt_wf_min ordinal_mem_wf (fun γ => ¬ InjectsInto γ x) (hartogs_exists x) y hn h

theorem InjectsInto_trans {x y z : DOrdinal} (h1 : InjectsInto x y) (h2 : InjectsInto y z) : InjectsInto x z :=
  h1.elim fun i1 => h2.elim fun i2 =>
    ⟨{ toFun := fun a => i2.toFun (i1.toFun a),
       inj' := fun a b eq => i1.inj' a b (i2.inj' _ _ eq) }⟩

theorem Equipotent_implies_InjectsInto_right {x y : DOrdinal} (h : Equipotent x y) : InjectsInto y x :=
  h.elim fun e => ⟨{ toFun := e.invFun, inj' := fun a b eq => Eq.trans (Eq.symm (e.right_inv a)) (Eq.trans (congrArg e.toFun eq) (e.right_inv b)) }⟩

theorem hartogs_is_cardinal (x : DOrdinal) : IsCardinal (hartogs x) := by
  intro y hy heq
  have h_inj_hartogs_y := Equipotent_implies_InjectsInto_right heq
  have h_inj_y_x := mem_hartogs_injects hy
  have h_inj_hartogs_x := InjectsInto_trans h_inj_hartogs_y h_inj_y_x
  exact hartogs_not_injects x h_inj_hartogs_x

theorem lt_hartogs (x : DOrdinal) : DOrdinal.Mem x (hartogs x) := by
  have total := DybjerOrd.ordinal_total_order x (hartogs x)
  match total with
  | Or.inl hsub =>
    have h_not_sub : ¬ DOrdinal.Subset (hartogs x) x := by
      intro h_sub_inv
      have h_inj : InjectsInto (hartogs x) x := Subset_implies_InjectsInto h_sub_inv
      exact hartogs_not_injects x h_inj
    exact strict_subset_implies_mem_ord x (hartogs x) hsub h_not_sub
  | Or.inr hsub =>
    have h_inj : InjectsInto (hartogs x) x := Subset_implies_InjectsInto hsub
    exact False.elim (hartogs_not_injects x h_inj)

theorem hartogs_monotone {x y : DOrdinal} (h : DOrdinal.Subset x y) : DOrdinal.Subset (hartogs x) (hartogs y) := by
  have total := DybjerOrd.ordinal_total_order (hartogs x) (hartogs y)
  match total with
  | Or.inl hsub => exact hsub
  | Or.inr hsub =>
    have h_not_sub_cases : DOrdinal.Subset (hartogs x) (hartogs y) ∨ ¬ DOrdinal.Subset (hartogs x) (hartogs y) := Classical.em _
    match h_not_sub_cases with
    | Or.inl h_eq => exact h_eq
    | Or.inr h_lt =>
      have h_mem : DOrdinal.Mem (hartogs y) (hartogs x) := strict_subset_implies_mem_ord (hartogs y) (hartogs x) hsub h_lt
      have h_inj : InjectsInto (hartogs y) x := mem_hartogs_injects h_mem
      have h_x_inj_y : InjectsInto x y := Subset_implies_InjectsInto h
      have h_inj_y : InjectsInto (hartogs y) y := InjectsInto_trans h_inj h_x_inj_y
      exact False.elim (hartogs_not_injects y h_inj_y)

/-- La cardinalidad de un ordinal x es el menor ordinal equipotente a x. -/
noncomputable def card (x : DOrdinal) : DOrdinal :=
  wf_min ordinal_mem_wf (fun y => Equipotent y x) ⟨x, Equipotent_refl x⟩

theorem card_is_equipotent (x : DOrdinal) : Equipotent (card x) x :=
  wf_min_mem ordinal_mem_wf (fun y => Equipotent y x) ⟨x, Equipotent_refl x⟩

theorem card_is_cardinal (x : DOrdinal) : IsCardinal (card x) := by
  intro y hy heq
  have heq_x : Equipotent y x := Equipotent_trans heq (card_is_equipotent x)
  have h_min := not_lt_wf_min ordinal_mem_wf (fun z => Equipotent z x) ⟨x, Equipotent_refl x⟩ y heq_x
  exact h_min hy

/-- Promueve la cardinalidad a un subtipo empaquetado. -/
noncomputable def DCard (x : DOrdinal) : DCardinal :=
  ⟨card x, card_is_cardinal x⟩

/-- Suma cardinal de dos ordinales. -/
noncomputable def cardAdd (x y : DOrdinal) : DOrdinal :=
  card (x + y)

/-- Producto cardinal de dos ordinales. -/
noncomputable def cardMul (x y : DOrdinal) : DOrdinal :=
  card (x * y)

end DybjerOrd
