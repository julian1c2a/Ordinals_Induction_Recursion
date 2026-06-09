/-
Copyright (c) 2025. All rights reserved.
Author: Julián Calderón Almendros
License: MIT

  MK⁺ — Morse-Kelley Set Theory + Class Axiom Scheme of Choice
  =============================================================

  Parallel development to ZfcSetTheory (ZFC), but grounded on a
  two-sorted ontology:

    · Sets    — collections that *belong to* some class.
    · Classes — any definable collection (sets are a subclass).

  Key differences from ZFC / ZfcSetTheory:
    1. Proper classes are first-class objects (not just informal talk).
    2. Comprehension schema (A7) allows formulas quantifying over classes,
       not just over sets — making MK strictly stronger than ZFC.
    3. Global Choice is included as A9 in the base MK axioms,
       following Kelley (1955). This is already stronger than AC in ZFC.
    4. MK⁺ = MK (with Global Choice) + Class Axiom Scheme of Choice (CAC).
       CAC is strictly stronger than Global Choice over MK.

  Lean encoding strategy:
    · A single Lean `Type` called `Class` for the universe of discourse.
    · `Mem : Class → Class → Prop` as the primitive membership relation.
    · `IsSet : Class → Prop` defined from membership (see §1).
    · Ordered pairs ⟪x, y⟫ are a *defined* notion (Kuratowski or Morse).
    · All axioms are stated as `axiom` declarations — left without unresolved proofs
      by design; concrete proofs will live in separate modules.
-/

import OrdinalsInductionRecursion.MKplusCAC.Prelim
import OrdinalsInductionRecursion.UnivSets.Axioms

namespace MKplusCAC

open Classical
open UnivSets

/-! ─────────────────────────────────────────────────────────────────────────
    §0 · Primitive Sorts and Relations (Constructive Base)
    ─────────────────────────────────────────────────────────────────────────
-/

-- The universe of all classes, defined constructively over Aczel's Extensional Universe.
def Class := USet → Prop

-- Primitive membership: A is a member of B if A is a set and its corresponding set satisfies B.
-- Since in this model sets are elements of USet, we can just map USet directly.
def toClass (d : USet) : Class := fun x => x ∈ d

def Mem (A B : Class) : Prop := ∃ d : USet, A = toClass d ∧ B d

-- Preferred infix notation for membership.
local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y


/-! ─────────────────────────────────────────────────────────────────────────
    §1 · Defined Notions (sin axiomas)
    ─────────────────────────────────────────────────────────────────────────

  These are purely definitional; they carry no axiomatic content.
-/

-- A class X is a *set* iff it is a member of some class Y.
def IsSet (X : Class) : Prop := ∃ Y : Class, X ∈ᴹ Y

-- Theorem linking MK set-hood to Aczel universes
theorem isSet_iff_exists_uset (X : Class) : IsSet X ↔ ∃ d : USet, X = toClass d := by
  constructor
  · rintro ⟨Y, hY⟩
    obtain ⟨d, hd1, _⟩ := hY
    exact ⟨d, hd1⟩
  · rintro ⟨d, hd⟩
    let Y : Class := fun x => x = d
    exact ⟨Y, ⟨d, hd, rfl⟩⟩

theorem toClass_inj {d1 d2 : USet} : toClass d1 = toClass d2 ↔ d1 = d2 := by
  constructor
  · intro h
    have h1 : ∀ x, x ∈ d1 ↔ x ∈ d2 := fun x => by
      have h2 : toClass d1 x ↔ toClass d2 x := by rw [h]
      exact h2
    apply USet.ext
    · rw [UnivSets.uset_subset_iff]
      intro x hx; exact (h1 x).mp hx
    · rw [UnivSets.uset_subset_iff]
      intro x hx; exact (h1 x).mpr hx
  · rintro rfl
    rfl

theorem mem_toClass_iff {d : USet} {X : Class} : toClass d ∈ᴹ X ↔ X d := by
  constructor
  · rintro ⟨d', hd_eq, hd'⟩
    have h_eq : d = d' := toClass_inj.mp hd_eq
    subst h_eq
    exact hd'
  · intro hd
    exact ⟨d, rfl, hd⟩

-- X is a subclass of Y (class inclusion).
def SubClass (X Y : Class) : Prop := ∀ u : Class, (u ∈ᴹ X) → (u ∈ᴹ Y)
local infix:50 " ⊆ᴹ " => SubClass

-- Todo miembro de una clase es un set.
theorem isSet_of_mem {u X : Class} (h : u ∈ᴹ X) : IsSet u := ⟨X, h⟩


/-! ─────────────────────────────────────────────────────────────────────────
    §2 · Axioms of Morse-Kelley Set Theory (MK)
    ─────────────────────────────────────────────────────────────────────────
-/

-- ── A1. Extensionality ────────────────────────────────────────────────────
theorem MK_Ext :
  ∀ X Y : Class,
    (∀ u : Class, IsSet u → (u ∈ᴹ X ↔ u ∈ᴹ Y)) → X = Y := by
  intro X Y h
  apply funext
  intro d
  have hu : IsSet (toClass d) := (isSet_iff_exists_uset (toClass d)).mpr ⟨d, rfl⟩
  have h_iff := h (toClass d) hu
  rw [mem_toClass_iff, mem_toClass_iff] at h_iff
  exact propext h_iff

-- ── A2. Foundation (Regularity) ───────────────────────────────────────────
-- Every non-empty class has an ∈ᴹ-minimal member.
-- Equivalently: no class is a member of itself, and ∈ᴹ is well-founded on sets.
theorem MK_Found :
  ∀ X : Class, (∃ u : Class, u ∈ᴹ X) →
    ∃ u : Class, u ∈ᴹ X ∧ ¬ ∃ v : Class, v ∈ᴹ u ∧ v ∈ᴹ X := by
  intro X hX
  obtain ⟨u, hu⟩ := hX
  have hu_set : IsSet u := isSet_of_mem hu
  rw [isSet_iff_exists_uset] at hu_set
  obtain ⟨du, rfl⟩ := hu_set
  let S := fun (d : USet) => toClass d ∈ᴹ X
  have hS_nonempty : ∃ d, S d := ⟨du, hu⟩
  have ⟨m, hm_mem, hm_min⟩ := UnivSets.wf_has_min UnivSets.uset_mem_wf S hS_nonempty
  exact ⟨toClass m, hm_mem, by
    rintro ⟨v, hv_mem_m, hv_mem_X⟩
    have hv_set : IsSet v := isSet_of_mem hv_mem_m
    rw [isSet_iff_exists_uset] at hv_set
    obtain ⟨dv, rfl⟩ := hv_set
    have h_dv_m : dv ∈ m := by
      rw [mem_toClass_iff] at hv_mem_m
      exact hv_mem_m
    have contra := hm_min dv h_dv_m hv_mem_X
    contradiction⟩


-- ── A3. Pairing ───────────────────────────────────────────────────────────
-- For any two sets x, y their unordered pair {x, y} is a set.
theorem MK_Pair :
  ∀ x y : Class, IsSet x → IsSet y →
    ∃ z : Class, IsSet z ∧ ∀ u : Class, (u ∈ᴹ z) ↔ ((u = x) ∨ (u = y)) := by
  intro x y hx hy
  rw [isSet_iff_exists_uset] at hx hy
  obtain ⟨dx, rfl⟩ := hx
  obtain ⟨dy, rfl⟩ := hy
  let z : Class := toClass (UnivSets.pair dx dy)
  have hz1 : IsSet z := by
    rw [isSet_iff_exists_uset]
    exact ⟨UnivSets.pair dx dy, rfl⟩
  have hz2 : ∀ u : Class, (u ∈ᴹ z) ↔ ((u = toClass dx) ∨ (u = toClass dy)) := by
    intro u
    constructor
    · intro h
      obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := h
      change d_u ∈ UnivSets.pair dx dy at hd_u_mem
      rw [UnivSets.mem_pair_iff] at hd_u_mem
      cases hd_u_mem with
      | inl h1 => exact Or.inl (by rw [hd_u_eq, h1])
      | inr h2 => exact Or.inr (by rw [hd_u_eq, h2])
    · rintro (h1 | h2)
      · rw [h1]
        exact ⟨dx, rfl, by change dx ∈ UnivSets.pair dx dy; rw [UnivSets.mem_pair_iff]; exact Or.inl rfl⟩
      · rw [h2]
        exact ⟨dy, rfl, by change dy ∈ UnivSets.pair dx dy; rw [UnivSets.mem_pair_iff]; exact Or.inr rfl⟩
  exact ⟨z, hz1, hz2⟩

/-! ─────────────────────────────────────────────────────────────────────────
    §1b · Pares y singletons (requieren A3)
    ─────────────────────────────────────────────────────────────────────────
-/

-- Par no ordenado {x, y}: testigo de A3.
noncomputable def uPairCore (x y : Class) (hx : IsSet x) (hy : IsSet y) : Class :=
  Classical.choose (MK_Pair x y hx hy)

theorem isSet_uPairCore {x y : Class} (hx : IsSet x) (hy : IsSet y) :
    IsSet (uPairCore x y hx hy) :=
  (Classical.choose_spec (MK_Pair x y hx hy)).1

theorem mem_uPairCore_iff {x y : Class} (hx : IsSet x) (hy : IsSet y) (u : Class) :
    (u ∈ᴹ uPairCore x y hx hy) ↔ (u = x ∨ u = y) :=
  (Classical.choose_spec (MK_Pair x y hx hy)).2 u

-- Singleton {x} := {x, x}.
noncomputable def singCore (x : Class) (hx : IsSet x) : Class := uPairCore x x hx hx

theorem isSet_singCore {x : Class} (hx : IsSet x) : IsSet (singCore x hx) :=
  isSet_uPairCore hx hx

theorem mem_singCore_iff {x : Class} (hx : IsSet x) (u : Class) :
    (u ∈ᴹ singCore x hx) ↔ (u = x) := by
  simp [singCore, mem_uPairCore_iff hx hx]

-- Singleton es inyectivo.
theorem singCore_inj {x x' : Class} (hx : IsSet x) (hx' : IsSet x')
    (h : singCore x hx = singCore x' hx') : x = x' :=
  (mem_singCore_iff hx' x).mp (h ▸ (mem_singCore_iff hx x).mpr rfl)

-- Igualdad de pares no ordenados implica igualdad de componentes (en algún orden).
theorem uPairCore_cases {x y x' y' : Class} (hx : IsSet x) (hy : IsSet y)
    (hx' : IsSet x') (hy' : IsSet y')
    (h : uPairCore x y hx hy = uPairCore x' y' hx' hy') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  -- Extraemos presencia de x e y en el par derecho
  have hx_in := (mem_uPairCore_iff hx' hy' x).mp (h ▸ (mem_uPairCore_iff hx hy x).mpr (Or.inl rfl))
  have hy_in := (mem_uPairCore_iff hx' hy' y).mp (h ▸ (mem_uPairCore_iff hx hy y).mpr (Or.inr rfl))
  rcases hx_in with hxx' | hxy'
  · -- x = x'
    rcases hy_in with hyx' | hyy'
    · -- y = x'; determinamos y' desde el par izquierdo
      have hy'_in := (mem_uPairCore_iff hx hy y').mp
        (h.symm ▸ (mem_uPairCore_iff hx' hy' y').mpr (Or.inr rfl))
      rcases hy'_in with hy'x | hy'y
      · exact Or.inl ⟨hxx', hyx'.trans (hxx'.symm.trans hy'x.symm)⟩
      · exact Or.inl ⟨hxx', hy'y.symm⟩
    · exact Or.inl ⟨hxx', hyy'⟩
  · -- x = y'
    rcases hy_in with hyx' | hyy'
    · exact Or.inr ⟨hxy', hyx'⟩
    · -- x = y', y = y'; determinamos x' desde el par izquierdo
      have hx'_in := (mem_uPairCore_iff hx hy x').mp
        (h.symm ▸ (mem_uPairCore_iff hx' hy' x').mpr (Or.inl rfl))
      rcases hx'_in with hx'x | hx'y
      · exact Or.inl ⟨hx'x.symm, hyy'⟩
      · exact Or.inr ⟨hxy', hx'y.symm⟩

-- Par de Kuratowski: ⟪x, y⟫ := {{x}, {x, y}}.
noncomputable def opairCore (x y : Class) (hx : IsSet x) (hy : IsSet y) : Class :=
  uPairCore (singCore x hx) (uPairCore x y hx hy) (isSet_singCore hx) (isSet_uPairCore hx hy)

-- Inyectividad del par de Kuratowski.
theorem opairCore_inj {x y x' y' : Class} (hx : IsSet x) (hy : IsSet y)
    (hx' : IsSet x') (hy' : IsSet y')
    (h : opairCore x y hx hy = opairCore x' y' hx' hy') : x = x' ∧ y = y' := by
  rcases uPairCore_cases (isSet_singCore hx) (isSet_uPairCore hx hy)
                     (isSet_singCore hx') (isSet_uPairCore hx' hy') h with
    ⟨hSS', hPP'⟩ | ⟨hSP', hPS'⟩
  · -- singCore x = singCore x'  ∧  uPairCore x y = uPairCore x' y'
    have hxx' := singCore_inj hx hx' hSS'
    rcases uPairCore_cases hx hy hx' hy' hPP' with ⟨_, hyy'⟩ | ⟨hxy', hyx'⟩
    · exact ⟨hxx', hyy'⟩
    · -- x = y', y = x'; con x = x': y = x' = x = y'
      exact ⟨hxx', hyx'.trans (hxx'.symm.trans hxy')⟩
  · -- singCore x = uPairCore x' y'  ∧  uPairCore x y = singCore x'
    have hx'x : x' = x := by
      have h1 : x' ∈ᴹ uPairCore x' y' hx' hy' := (mem_uPairCore_iff hx' hy' x').mpr (Or.inl rfl)
      rw [← hSP'] at h1; exact (mem_singCore_iff hx x').mp h1
    have hy'x : y' = x := by
      have h1 : y' ∈ᴹ uPairCore x' y' hx' hy' := (mem_uPairCore_iff hx' hy' y').mpr (Or.inr rfl)
      rw [← hSP'] at h1; exact (mem_singCore_iff hx y').mp h1
    have hyx' : y = x' := by
      have h1 : y ∈ᴹ uPairCore x y hx hy := (mem_uPairCore_iff hx hy y).mpr (Or.inr rfl)
      rw [hPS'] at h1; exact (mem_singCore_iff hx' y).mp h1
    -- x = x' y y = y' (via y = x' = x = y')
    exact ⟨hx'x.symm, hyx'.trans (hx'x.trans hy'x.symm)⟩

-- ── A4. Union ─────────────────────────────────────────────────────────────
-- The union ⋃x of a set x is a set.
theorem MK_Union :
  ∀ x : Class, IsSet x →
    ∃ z : Class, IsSet z ∧
      ∀ u : Class, u ∈ᴹ z ↔ ∃ v : Class, u ∈ᴹ v ∧ v ∈ᴹ x := by
  intro x hx
  rw [isSet_iff_exists_uset] at hx
  obtain ⟨dx, rfl⟩ := hx
  let z : Class := toClass (UnivSets.union dx)
  let z : Class := toClass (UnivSets.union dx)
  have hz1 : IsSet z := by
    rw [isSet_iff_exists_uset]
    exact ⟨UnivSets.union dx, rfl⟩
  have hz2 : ∀ u : Class, u ∈ᴹ z ↔ ∃ v, u ∈ᴹ v ∧ v ∈ᴹ toClass dx := by
    intro u
    constructor
    · intro h
      obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := h
      change d_u ∈ UnivSets.union dx at hd_u_mem
      rw [UnivSets.mem_union_iff] at hd_u_mem
      obtain ⟨dv, hd_u_in_dv, hdv_in_dx⟩ := hd_u_mem
      exact ⟨toClass dv, by
        constructor
        · exact ⟨d_u, hd_u_eq, hd_u_in_dv⟩
        · exact ⟨dv, rfl, hdv_in_dx⟩⟩
    · intro hu
      obtain ⟨V, huV, hVx⟩ := hu
      obtain ⟨d_V, hd_V_eq, hd_V_mem⟩ := hVx
      have hu_in_d_V : u ∈ᴹ toClass d_V := by rw [← hd_V_eq]; exact huV
      obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := hu_in_d_V
      exact ⟨d_u, hd_u_eq, by
        change d_u ∈ UnivSets.union dx
        rw [UnivSets.mem_union_iff]
        exact ⟨d_V, hd_u_mem, hd_V_mem⟩⟩
  exact ⟨z, hz1, hz2⟩



-- ── A5. Power Set ─────────────────────────────────────────────────────────
-- The power class 𝒫(x) = {u | u ⊆ x} of a set x is a set.
theorem MK_Pow :
  ∀ x : Class, IsSet x →
    ∃ z : Class, IsSet z ∧
      ∀ u : Class, u ∈ᴹ z ↔ IsSet u ∧ ∀ v : Class, v ∈ᴹ u → v ∈ᴹ x := by
  intro x hx
  rw [isSet_iff_exists_uset] at hx
  obtain ⟨dx, rfl⟩ := hx
  let z : Class := toClass (UnivSets.powerset dx)
  have hz1 : IsSet z := by
    rw [isSet_iff_exists_uset]
    exact ⟨UnivSets.powerset dx, rfl⟩
  have hz2 : ∀ u : Class, u ∈ᴹ z ↔ IsSet u ∧ ∀ v : Class, v ∈ᴹ u → v ∈ᴹ (toClass dx) := by
    intro u
    constructor
    · intro hu
      obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := hu
      change d_u ∈ UnivSets.powerset dx at hd_u_mem
      rw [UnivSets.mem_powerset_iff] at hd_u_mem
      refine ⟨(isSet_iff_exists_uset u).mpr ⟨d_u, hd_u_eq⟩, ?_⟩
      intro v hv
      have hv_in_d_u : v ∈ᴹ toClass d_u := by rw [← hd_u_eq]; exact hv
      obtain ⟨d_v, hd_v_eq, hd_v_mem⟩ := hv_in_d_u
      exact ⟨d_v, hd_v_eq, by
        change d_v ∈ dx
        have h_sub : ∀ z, z ∈ d_u → z ∈ dx := UnivSets.uset_subset_iff.mp hd_u_mem
        exact h_sub d_v hd_v_mem⟩
    · rintro ⟨hu_set, hu_sub⟩
      have hd_u_ex := (isSet_iff_exists_uset u).mp hu_set
      obtain ⟨d_u, hd_u_eq⟩ := hd_u_ex
      refine ⟨d_u, hd_u_eq, ?_⟩
      change d_u ∈ UnivSets.powerset dx
      rw [UnivSets.mem_powerset_iff]
      rw [UnivSets.uset_subset_iff]
      intro d_v hd_v_mem
      have hd_v_in_u : toClass d_v ∈ᴹ u := by
        rw [hd_u_eq]
        exact ⟨d_v, rfl, hd_v_mem⟩
      have hd_v_in_x := hu_sub (toClass d_v) hd_v_in_u
      obtain ⟨d_v', hd_v_eq', hd_v_mem'⟩ := hd_v_in_x
      have hd_v_eq_d_v' : d_v = d_v' := toClass_inj.mp hd_v_eq'
      rw [hd_v_eq_d_v']
      exact hd_v_mem'
  exact ⟨z, hz1, hz2⟩

-- ── A6. Infinity ──────────────────────────────────────────────────────────
-- There exists an inductive set: one containing ∅ and closed under
-- the von Neumann successor s(x) = x ∪ {x}.
-- (∅ and s are defined via A3 + A4 + A7; stated here informally.)
theorem MK_Inf :
  ∃ x : Class, IsSet x ∧
    -- ∅ ∈ x:
    (∃ e : Class, IsSet e ∧ (∀ u : Class, u ∉ᴹ e) ∧ e ∈ᴹ x) ∧
    -- ∀ y ∈ x, s(y) = y ∪ {y} ∈ x:
    (∀ y : Class, y ∈ᴹ x →
      ∃ s : Class, IsSet s ∧ s ∈ᴹ x ∧
        ∀ u : Class, u ∈ᴹ s ↔ u ∈ᴹ y ∨ u = y) := by
  refine ⟨toClass UnivSets.omega, (isSet_iff_exists_uset _).mpr ⟨UnivSets.omega, rfl⟩, ?_⟩
  constructor
  · refine ⟨toClass UnivSets.empty, (isSet_iff_exists_uset _).mpr ⟨UnivSets.empty, rfl⟩, ?_, ?_⟩
    · intro u hu
      obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := hu
      exact UnivSets.not_mem_empty d_u hd_u_mem
    · exact ⟨UnivSets.empty, rfl, UnivSets.empty_mem_omega⟩
  · intro y hy
    obtain ⟨d_y, hd_y_eq, hd_y_mem⟩ := hy
    refine ⟨toClass (UnivSets.insert d_y d_y), (isSet_iff_exists_uset _).mpr ⟨UnivSets.insert d_y d_y, rfl⟩, ?_, ?_⟩
    · exact ⟨UnivSets.insert d_y d_y, rfl, UnivSets.insert_mem_omega hd_y_mem⟩
    · intro u
      constructor
      · intro hu
        obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := hu
        have h_or := (UnivSets.mem_insert_iff d_u d_y d_y).mp hd_u_mem
        cases h_or with
        | inl h_eq =>
          right
          rw [hd_u_eq, hd_y_eq]
          exact toClass_inj.mpr h_eq
        | inr h_mem =>
          left
          rw [hd_y_eq]
          exact ⟨d_u, hd_u_eq, h_mem⟩
      · intro hu
        rw [hd_y_eq] at hu
        cases hu with
        | inl h_mem =>
          obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := h_mem
          refine ⟨d_u, hd_u_eq, (UnivSets.mem_insert_iff d_u d_y d_y).mpr (Or.inr hd_u_mem)⟩
        | inr h_eq =>
          refine ⟨d_y, h_eq, (UnivSets.mem_insert_iff d_y d_y d_y).mpr (Or.inl rfl)⟩

/-! ─────────────────────────────────────────────────────────────────────────
    §1c · Par ordenado total + IsClassFun (requieren MK_Inf)
    ─────────────────────────────────────────────────────────────────────────
-/

-- Class es no-vacía: MK_Inf garantiza al menos un set.
noncomputable instance : Nonempty Class :=
  let ⟨x, _, _⟩ := MK_Inf; ⟨x⟩

-- Par ordenado total: igual a opairCore cuando x, y son sets;
-- valor arbitrario (junk) en caso contrario.
noncomputable def opair (x y : Class) : Class :=
  if hx : IsSet x then
    if hy : IsSet y then opairCore x y hx hy
    else Classical.choice inferInstance
  else Classical.choice inferInstance

-- Lema de reducción: bajo IsSet, opair coincide con opairCore.
theorem opair_eq_opairCore {x y : Class} (hx : IsSet x) (hy : IsSet y) :
    opair x y = opairCore x y hx hy := by
  simp [opair, hx, hy]

local notation "⟪" x ", " y "⟫" => opair x y

-- El par ordenado de dos sets es un set.
theorem isSet_opair {x y : Class} (hx : IsSet x) (hy : IsSet y) :
    IsSet (⟪x, y⟫) := by
  rw [opair_eq_opairCore hx hy]
  exact isSet_uPairCore (isSet_singCore hx) (isSet_uPairCore hx hy)

-- Inyectividad del par ordenado total (corolario de opairCore_inj).
theorem opair_inj {x y x' y' : Class} (hx : IsSet x) (hy : IsSet y)
    (hx' : IsSet x') (hy' : IsSet y')
    (h : ⟪x, y⟫ = ⟪x', y'⟫) : x = x' ∧ y = y' := by
  rw [opair_eq_opairCore hx hy, opair_eq_opairCore hx' hy'] at h
  exact opairCore_inj hx hy hx' hy' h

-- F es una clase-función (cada componente izquierda tiene exactamente una derecha).
def IsClassFun (F : Class) : Prop :=
  ∀ x y z : Class, IsSet x → IsSet y → IsSet z →
    ⟪x, y⟫ ∈ᴹ F → ⟪x, z⟫ ∈ᴹ F → y = z

-- ── A7. Class Comprehension Schema (MK-Comp) ──────────────────────────────
-- The hallmark of MK over NBG:
--   For *any* Lean Prop φ (including those quantifying over classes),
--   the collection {u : Set | φ u} exists as a class.
--
-- In NBG the schema is restricted to *predicative* formulas (no class
-- quantifiers); in MK the schema is *impredicative* (full second-order).
--
theorem MK_Comp :
  ∀ (φ : Class → Prop),
    ∃ Z : Class, ∀ u : Class, u ∈ᴹ Z ↔ IsSet u ∧ φ u := by
  intro φ
  let Z : Class := fun d => φ (toClass d)
  have hZ : ∀ u : Class, u ∈ᴹ Z ↔ IsSet u ∧ φ u := by
    intro u
    constructor
    · intro hu
      obtain ⟨d_u, hd_eq, hd_Z⟩ := hu
      have hu_set : IsSet u := by
        rw [isSet_iff_exists_uset]
        exact ⟨d_u, hd_eq⟩
      have hu_phi : φ u := by
        rw [hd_eq]
        exact hd_Z
      exact ⟨hu_set, hu_phi⟩
    · rintro ⟨hu_set, h_phi⟩
      rw [isSet_iff_exists_uset] at hu_set
      obtain ⟨d_u, rfl⟩ := hu_set
      exact ⟨d_u, rfl, h_phi⟩
  exact ⟨Z, hZ⟩

-- ── §1e · Comprensión de clase — classComp ────────────────────────────────

-- Abstracción total sobre MK_Comp: la clase de todos los sets que cumplen φ.
noncomputable def classComp (φ : Class → Prop) : Class :=
  Classical.choose (MK_Comp φ)

-- Caracterización de la membresía.
theorem classComp_mem (φ : Class → Prop) (u : Class) :
    u ∈ᴹ classComp φ ↔ IsSet u ∧ φ u :=
  Classical.choose_spec (MK_Comp φ) u

-- Notación libre: {| x | φ x |}  — todos los sets que satisfacen φ.
macro "{|" x:ident " | " p:term " |}" : term =>
  `(classComp (fun $x => $p))

-- Notación acotada: {| x ∈ᴹ X | φ x |}  — los sets de X que satisfacen φ.
macro "{|" x:ident " ∈ᴹ " X:term " | " p:term " |}" : term =>
  `(classComp (fun $x => $x ∈ᴹ $X ∧ $p))

-- ── §1d · Unión de clase ──────────────────────────────────────────────────

-- ⋃ᴹ X := {u | ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X}
-- Existe siempre como clase; es set cuando X es set (MK_Union).
noncomputable def sUnion (X : Class) : Class :=
  {| u | ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X |}

local prefix:110 "⋃ᴹ " => sUnion

-- Caracterización de la membresía en ⋃ᴹ X.
theorem mem_sUnion_iff (X u : Class) :
    u ∈ᴹ ⋃ᴹ X ↔ IsSet u ∧ ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X :=
  classComp_mem _ u

-- Versión simplificada: cuando u ya es set, IsSet u es automático.
theorem mem_sUnion_iff' {X u : Class} (hu : IsSet u) :
    u ∈ᴹ ⋃ᴹ X ↔ ∃ v, u ∈ᴹ v ∧ v ∈ᴹ X := by
  rw [mem_sUnion_iff]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- La unión de un set es un set (consecuencia de MK_Union).
theorem isSet_sUnion {X : Class} (hX : IsSet X) : IsSet (⋃ᴹ X) := by
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Union X hX
  suffices h : ⋃ᴹ X = z by rw [h]; exact hz_set
  apply MK_Ext
  intro u hu
  rw [mem_sUnion_iff]
  constructor
  · rintro ⟨_, v, huv, hvX⟩
    exact (hz_mem u).mpr ⟨v, huv, hvX⟩
  · intro huz
    obtain ⟨v, huv, hvX⟩ := (hz_mem u).mp huz
    exact ⟨hu, v, huv, hvX⟩

-- ── A8. Substitution (Replacement) ───────────────────────────────────────
-- The image of a set under a class-function is a set.
noncomputable def sepP (φ : Class → Prop) (t : UnivSets.Tree) : Prop :=
  φ (toClass (Quotient.mk UnivSets.Tree.Setoid t))

theorem sepP_respects (φ : Class → Prop) (x y : UnivSets.Tree) (hxy : UnivSets.Tree.Equiv x y) :
  sepP φ x ↔ sepP φ y := by
  unfold sepP
  have heq : Quotient.mk UnivSets.Tree.Setoid x = Quotient.mk UnivSets.Tree.Setoid y := Quotient.sound hxy
  rw [heq]

theorem isSet_sep {X : Class} (hX : IsSet X) (φ : Class → Prop) :
    IsSet (classComp (fun x => Mem x X ∧ φ x)) := by
  obtain ⟨d_X, hd_X_eq⟩ := (isSet_iff_exists_uset X).mp hX
  let P := sepP φ
  haveI : ∀ x, Decidable (P x) := fun x => Classical.propDecidable (P x)
  let hP := sepP_respects φ
  let z_uset := UnivSets.sep P hP d_X
  refine (isSet_iff_exists_uset _).mpr ⟨z_uset, ?_⟩
  apply MK_Ext
  intro u hu
  rw [classComp_mem]
  constructor
  · rintro ⟨hu_set, huX, hφu⟩
    have huX_d_X : Mem u (toClass d_X) := by rwa [← hd_X_eq]
    obtain ⟨d_u, hd_u_eq, hd_u_mem⟩ := huX_d_X
    have h_mem_sep : d_u ∈ UnivSets.sep P hP d_X := by
      apply (UnivSets.mem_sep_iff P hP d_X d_u).mpr
      constructor
      · exact hd_u_mem
      · unfold UnivSets.sepUSetP
        have hd_lift : Quotient.lift P (fun a b hab => propext (hP a b hab)) d_u = P (UnivSets.USet.out d_u) := by
          have h_eq : d_u = Quotient.mk _ d_u.out := (UnivSets.USet.out_eq d_u).symm
          calc Quotient.lift P (fun a b hab => propext (hP a b hab)) d_u
            _ = Quotient.lift P (fun a b hab => propext (hP a b hab)) (Quotient.mk _ d_u.out) := congrArg _ h_eq
            _ = P d_u.out := rfl
        rw [hd_lift]
        unfold P sepP
        have hz_mk : Quotient.mk UnivSets.Tree.Setoid (UnivSets.USet.out d_u) = d_u := UnivSets.USet.out_eq d_u
        rw [hz_mk]
        rw [← hd_u_eq]
        exact hφu
    exact ⟨d_u, hd_u_eq, h_mem_sep⟩
  · intro hz
    obtain ⟨d_z, hd_z_eq, hz_sep⟩ := hz
    have hz_sep_iff := (UnivSets.mem_sep_iff P hP d_X d_z).mp hz_sep
    have hu_set : IsSet u := (isSet_iff_exists_uset u).mpr ⟨d_z, hd_z_eq⟩
    refine ⟨hu_set, ?_, ?_⟩
    · rw [hd_X_eq]
      exact ⟨d_z, hd_z_eq, hz_sep_iff.left⟩
    · have h_prop := hz_sep_iff.right
      unfold UnivSets.sepUSetP at h_prop
      have hz_mk : Quotient.mk UnivSets.Tree.Setoid (UnivSets.USet.out d_z) = d_z := UnivSets.USet.out_eq d_z
      have hd_lift : Quotient.lift P (fun a b hab => propext (hP a b hab)) d_z = P (UnivSets.USet.out d_z) := by
        have h_eq : d_z = Quotient.mk _ d_z.out := (UnivSets.USet.out_eq d_z).symm
        calc Quotient.lift P (fun a b hab => propext (hP a b hab)) d_z
          _ = Quotient.lift P (fun a b hab => propext (hP a b hab)) (Quotient.mk _ d_z.out) := congrArg _ h_eq
          _ = P d_z.out := rfl
      rw [hd_lift] at h_prop
      unfold P sepP at h_prop
      rw [hz_mk] at h_prop
      rw [← hd_z_eq] at h_prop
      exact h_prop

noncomputable def extractUSetFun (F : Class) (u : UnivSets.USet) : UnivSets.USet :=
  if h : ∃ v : UnivSets.USet, Mem (opair (toClass u) (toClass v)) F then
    Classical.choose h
  else
    UnivSets.empty

noncomputable def extractTreeFun (F : Class) (t : UnivSets.Tree) : UnivSets.Tree :=
  UnivSets.USet.out (extractUSetFun F (Quotient.mk UnivSets.Tree.Setoid t))

theorem extractTreeFun_respects (F : Class) :
  ∀ x y, UnivSets.Tree.Equiv x y → UnivSets.Tree.Equiv (extractTreeFun F x) (extractTreeFun F y) := by
  intro x y hxy
  have heq : Quotient.mk UnivSets.Tree.Setoid x = Quotient.mk UnivSets.Tree.Setoid y := Quotient.sound hxy
  unfold extractTreeFun
  rw [heq]
  apply UnivSets.Tree.Equiv_refl

theorem extractTreeFun_eq (F : Class) (u : UnivSets.USet) :
  Quotient.mk UnivSets.Tree.Setoid (extractTreeFun F (UnivSets.USet.out u)) = extractUSetFun F u := by
  unfold extractTreeFun
  have h_mk_out : Quotient.mk UnivSets.Tree.Setoid (UnivSets.USet.out u) = u := UnivSets.USet.out_eq u
  rw [h_mk_out]
  exact UnivSets.USet.out_eq (extractUSetFun F u)

theorem liftFun_extractTreeFun_eq (F : Class) (u : UnivSets.USet) :
  UnivSets.liftFun (extractTreeFun F) (extractTreeFun_respects F) u = extractUSetFun F u := by
  have h_eq : u = Quotient.mk _ u.out := (UnivSets.USet.out_eq u).symm
  calc UnivSets.liftFun (extractTreeFun F) (extractTreeFun_respects F) u
    _ = UnivSets.liftFun (extractTreeFun F) (extractTreeFun_respects F) (Quotient.mk _ u.out) := congrArg _ h_eq
    _ = Quotient.mk _ (extractTreeFun F u.out) := rfl
    _ = extractUSetFun F u := extractTreeFun_eq F u

/-- A7. Axiom of Replacement (MK) -/
theorem MK_Repl :
  ∀ (F x : Class), IsSet x → IsClassFun F →
    ∃ z : Class, IsSet z ∧
      ∀ v : Class, Mem v z ↔ IsSet v ∧ ∃ u : Class, Mem u x ∧ Mem (opair u v) F := by
  intro F x hx hF
  let dom_x := classComp (fun u => Mem u x ∧ ∃ v : Class, IsSet v ∧ Mem (opair u v) F)
  have h_dom_set : IsSet dom_x := isSet_sep hx (fun u => ∃ v : Class, IsSet v ∧ Mem (opair u v) F)
  obtain ⟨d_dom, hd_dom_eq⟩ := (isSet_iff_exists_uset dom_x).mp h_dom_set
  let f := extractTreeFun F
  let hf := extractTreeFun_respects F
  let z_uset := UnivSets.repl f hf d_dom
  refine ⟨toClass z_uset, (isSet_iff_exists_uset _).mpr ⟨z_uset, rfl⟩, ?_⟩
  intro v
  constructor
  · intro hv
    obtain ⟨d_v, hd_v_eq, hd_v_mem⟩ := hv
    have h_mem := (UnivSets.mem_repl_iff f hf d_dom d_v).mp hd_v_mem
    obtain ⟨d_u, hd_u_mem, hd_v_eq_lift⟩ := h_mem
    rw [liftFun_extractTreeFun_eq F d_u] at hd_v_eq_lift
    have h_du_in_dom : Mem (toClass d_u) dom_x := by
      have h1 : dom_x d_u := by rw [hd_dom_eq]; exact hd_u_mem
      exact ⟨d_u, rfl, h1⟩
    have h_du_in_dom_unfold : Mem (toClass d_u) x ∧ ∃ v : Class, IsSet v ∧ Mem (opair (toClass d_u) v) F := by
      have h := (classComp_mem (fun u => Mem u x ∧ ∃ v : Class, IsSet v ∧ Mem (opair u v) F) (toClass d_u)).mp h_du_in_dom
      exact h.2
    obtain ⟨h_du_in_x, h_ex_v⟩ := h_du_in_dom_unfold
    obtain ⟨v_ex, hv_set, hv_in_F⟩ := h_ex_v
    obtain ⟨d_v_ex, hd_v_ex_eq⟩ := (isSet_iff_exists_uset v_ex).mp hv_set
    rw [hd_v_ex_eq] at hv_in_F
    have hex_uset : ∃ v' : UnivSets.USet, Mem (opair (toClass d_u) (toClass v')) F := ⟨d_v_ex, hv_in_F⟩
    have h_choose_spec := Classical.choose_spec hex_uset
    unfold extractUSetFun at hd_v_eq_lift
    simp only [hex_uset, dif_pos] at hd_v_eq_lift
    have h_d_v_is_choose : d_v = Classical.choose hex_uset := hd_v_eq_lift
    have hv_is_set : IsSet v := (isSet_iff_exists_uset v).mpr ⟨d_v, hd_v_eq⟩
    rw [h_d_v_is_choose] at hd_v_eq
    refine ⟨hv_is_set, toClass d_u, h_du_in_x, ?_⟩
    rw [hd_v_eq]
    exact h_choose_spec
  · rintro ⟨hv_set, u, hu_in_x, huv_in_F⟩
    obtain ⟨d_u, hd_u_eq⟩ := (isSet_iff_exists_uset u).mp (isSet_of_mem hu_in_x)
    obtain ⟨d_v, hd_v_eq⟩ := (isSet_iff_exists_uset v).mp hv_set
    have h_du_in_dom : Mem u dom_x := by
      apply (classComp_mem (fun u => Mem u x ∧ ∃ v : Class, IsSet v ∧ Mem (opair u v) F) u).mpr
      exact ⟨isSet_of_mem hu_in_x, hu_in_x, v, hv_set, huv_in_F⟩
    have h_du_mem_d_dom : d_u ∈ d_dom := by
      rw [hd_dom_eq] at h_du_in_dom
      obtain ⟨d_u', hd_u'_eq, hd_u'_mem⟩ := h_du_in_dom
      have h_eq : d_u = d_u' := toClass_inj.mp (hd_u_eq.symm.trans hd_u'_eq)
      rw [h_eq]
      exact hd_u'_mem
    have h_v_eq_extract : d_v = extractUSetFun F d_u := by
      unfold extractUSetFun
      have hex_uset : ∃ v' : UnivSets.USet, Mem (opair (toClass d_u) (toClass v')) F := by
        refine ⟨d_v, ?_⟩
        rw [← hd_u_eq, ← hd_v_eq]
        exact huv_in_F
      simp only [hex_uset, dif_pos]
      have h_choose := Classical.choose_spec hex_uset
      have h_opair_in_F : Mem (opair u (toClass (Classical.choose hex_uset))) F := by
        rw [hd_u_eq]
        exact h_choose
      have hu_is_set : IsSet u := (isSet_iff_exists_uset u).mpr ⟨d_u, hd_u_eq⟩
      have h_choose_set : IsSet (toClass (Classical.choose hex_uset)) := (isSet_iff_exists_uset _).mpr ⟨_, rfl⟩
      have hv_is_set : IsSet v := (isSet_iff_exists_uset v).mpr ⟨d_v, hd_v_eq⟩
      have h_eq := hF u (toClass (Classical.choose hex_uset)) v hu_is_set h_choose_set hv_is_set h_opair_in_F huv_in_F
      have h_eq_v : toClass (Classical.choose hex_uset) = toClass d_v := h_eq.trans hd_v_eq
      exact toClass_inj.mp h_eq_v.symm
    have h_repl : UnivSets.liftFun f hf d_u ∈ UnivSets.repl f hf d_dom := (UnivSets.mem_repl_iff f hf d_dom (UnivSets.liftFun f hf d_u)).mpr ⟨d_u, h_du_mem_d_dom, rfl⟩
    rw [liftFun_extractTreeFun_eq F d_u] at h_repl
    rw [← h_v_eq_extract] at h_repl
    exact ⟨d_v, hd_v_eq, h_repl⟩

-- ── §1f · Operaciones binarias de clase ──────────────────────────────────

-- ─ Unión binaria ──────────────────────────────────────────────────────────
noncomputable def union (A B : Class) : Class := {| x | x ∈ᴹ A ∨ x ∈ᴹ B |}

local infix:65 " ∪ᴹ " => union

theorem mem_union_iff (A B u : Class) :
    u ∈ᴹ A ∪ᴹ B ↔ IsSet u ∧ (u ∈ᴹ A ∨ u ∈ᴹ B) :=
  classComp_mem _ u

theorem mem_union_iff' {A B u : Class} (hu : IsSet u) :
    u ∈ᴹ A ∪ᴹ B ↔ u ∈ᴹ A ∨ u ∈ᴹ B := by
  rw [mem_union_iff]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- A ∪ B es set cuando A y B son sets.
theorem isSet_union {A B : Class} (hA : IsSet A) (hB : IsSet B) :
    IsSet (A ∪ᴹ B) := by
  suffices h : A ∪ᴹ B = ⋃ᴹ (uPairCore A B hA hB) by
    rw [h]; exact isSet_sUnion (isSet_uPairCore hA hB)
  apply MK_Ext
  intro u hu
  rw [mem_union_iff' hu, mem_sUnion_iff' hu]
  constructor
  · rintro (huA | huB)
    · exact ⟨A, huA, (mem_uPairCore_iff hA hB A).mpr (Or.inl rfl)⟩
    · exact ⟨B, huB, (mem_uPairCore_iff hA hB B).mpr (Or.inr rfl)⟩
  · rintro ⟨v, huv, hvAB⟩
    rcases (mem_uPairCore_iff hA hB v).mp hvAB with rfl | rfl
    · exact Or.inl huv
    · exact Or.inr huv

-- ─ Intersección binaria ───────────────────────────────────────────────────
noncomputable def inter (A B : Class) : Class := {| x | x ∈ᴹ A ∧ x ∈ᴹ B |}

local infix:70 " ∩ᴹ " => inter

theorem mem_inter_iff (A B u : Class) :
    u ∈ᴹ A ∩ᴹ B ↔ IsSet u ∧ u ∈ᴹ A ∧ u ∈ᴹ B :=
  classComp_mem _ u

theorem mem_inter_iff' {A B u : Class} (hu : IsSet u) :
    u ∈ᴹ A ∩ᴹ B ↔ u ∈ᴹ A ∧ u ∈ᴹ B := by
  rw [mem_inter_iff]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- A ∩ B es set cuando A es set (subclase de A, por isSet_sep).
theorem isSet_inter_left {A B : Class} (hA : IsSet A) : IsSet (A ∩ᴹ B) :=
  isSet_sep hA (fun x => x ∈ᴹ B)

-- Simétrico: A ∩ B es set cuando B es set.
theorem isSet_inter_right {A B : Class} (hB : IsSet B) : IsSet (A ∩ᴹ B) := by
  suffices h : A ∩ᴹ B = B ∩ᴹ A by
    rw [h]; exact isSet_inter_left hB
  apply MK_Ext; intro u hu
  simp [mem_inter_iff' hu, And.comm]

-- ─ Diferencia de clases ───────────────────────────────────────────────────
noncomputable def sdiff (A B : Class) : Class := {| x | x ∈ᴹ A ∧ x ∉ᴹ B |}

local infix:70 " ∖ᴹ " => sdiff

theorem mem_sdiff_iff (A B u : Class) :
    u ∈ᴹ A ∖ᴹ B ↔ IsSet u ∧ u ∈ᴹ A ∧ u ∉ᴹ B :=
  classComp_mem _ u

theorem mem_sdiff_iff' {A B u : Class} (hu : IsSet u) :
    u ∈ᴹ A ∖ᴹ B ↔ u ∈ᴹ A ∧ u ∉ᴹ B := by
  rw [mem_sdiff_iff]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩

-- A \ B es set cuando A es set.
theorem isSet_sdiff {A B : Class} (hA : IsSet A) : IsSet (A ∖ᴹ B) :=
  isSet_sep hA (fun x => x ∉ᴹ B)

-- ─ Diferencia simétrica ───────────────────────────────────────────────────
noncomputable def symmDiff (A B : Class) : Class := (A ∖ᴹ B) ∪ᴹ (B ∖ᴹ A)

local infix:65 " △ᴹ " => symmDiff

-- A △ B es set cuando A y B son sets.
theorem isSet_symmDiff {A B : Class} (hA : IsSet A) (hB : IsSet B) :
    IsSet (A △ᴹ B) :=
  isSet_union (isSet_sdiff hA) (isSet_sdiff hB)

-- ─ Complemento de clase ───────────────────────────────────────────────────
-- ∁ᴹ A := {x : Set | x ∉ A}
-- Es siempre una clase propia (salvo casos triviales).
-- En particular: ∁ᴹ ∅ = V (la clase universal), que no es set.
noncomputable def compl (A : Class) : Class := {| x | x ∉ᴹ A |}

local prefix:110 "∁ᴹ " => compl

theorem mem_compl_iff (A u : Class) :
    u ∈ᴹ ∁ᴹ A ↔ IsSet u ∧ u ∉ᴹ A :=
  classComp_mem _ u

-- ── §1g · Conjuntos finitos por enumeración ──────────────────────────────

-- Singleton total: sing x = {x} si IsSet x; valor basura en caso contrario.
noncomputable def sing (x : Class) : Class :=
  if hx : IsSet x then singCore x hx else Classical.choice inferInstance

theorem sing_eq_singCore {x : Class} (hx : IsSet x) : sing x = singCore x hx :=
  dif_pos hx

theorem sing_isSet {x : Class} (hx : IsSet x) : IsSet (sing x) := by
  rw [sing_eq_singCore hx]; exact isSet_singCore hx

theorem sing_mem {x u : Class} (hx : IsSet x) : u ∈ᴹ sing x ↔ u = x := by
  rw [sing_eq_singCore hx]; exact mem_singCore_iff hx u

-- Notación de enumeración finita: {| x₁, x₂, ..., xₙ |}
-- Separador ","  (distinto del separador "|" de la comprensión {| x | φ |}).
--   {| x |}              = sing x
--   {| x, y, ... |}      = sing x ∪ᴹ {| y, ... |}
syntax "{|" term,+ "|}" : term
macro_rules
  | `({| $x |})        => `(sing $x)
  | `({| $x, $xs,* |}) => `(sing $x ∪ᴹ {| $xs,* |})

-- isSet: {| x₁, ..., xₙ |} es set ⟺ cada xᵢ es set.
-- Construcción composicional:
--   n = 1 : sing_isSet hx
--   n ≥ 2 : isSet_union (sing_isSet hx₁) (isSet_union (sing_isSet hx₂) ...)
-- Caso base (azúcar para n = 1):
theorem finiteset_isSet₁ {x : Class} (hx : IsSet x) :
    IsSet {| x |} :=
  sing_isSet hx

-- ── §1h · Clases derivadas esenciales ────────────────────────────────────

-- ─ Clase vacía ────────────────────────────────────────────────────────────
noncomputable def empty : Class := classComp (fun _ => False)

local notation "∅ᴹ" => empty

theorem not_mem_empty (u : Class) : u ∉ᴹ ∅ᴹ :=
  fun h => ((classComp_mem _ u).mp h).2

-- ∅ᴹ es set: coincide con el vacío garantizado por MK_Inf.
theorem isSet_empty : IsSet ∅ᴹ := by
  obtain ⟨_, _, ⟨e, he_set, he_empty, _⟩, _⟩ := MK_Inf
  suffices h : ∅ᴹ = e by rw [h]; exact he_set
  apply MK_Ext; intro u _
  exact ⟨fun h => (not_mem_empty u h).elim, fun h => (he_empty u h).elim⟩

-- ─ Clase universal ────────────────────────────────────────────────────────
-- 𝐕ᴹ := {x : Set | True} — contiene exactamente todos los sets.
-- Es clase propia: si fuera set, se contendría a sí misma (contradice Foundation).
noncomputable def univ : Class := classComp (fun _ => True)

local notation "𝐕ᴹ" => univ

theorem mem_univ_iff (u : Class) : u ∈ᴹ 𝐕ᴹ ↔ IsSet u :=
  ⟨fun h => ((classComp_mem _ u).mp h).1,
   fun h => (classComp_mem _ u).mpr ⟨h, trivial⟩⟩

-- ─ Clase potencia ─────────────────────────────────────────────────────────
noncomputable def powerset (X : Class) : Class := {| u | u ⊆ᴹ X |}

local prefix:110 "𝒫ᴹ " => powerset

theorem mem_powerset_iff (X u : Class) :
    u ∈ᴹ 𝒫ᴹ X ↔ IsSet u ∧ u ⊆ᴹ X :=
  classComp_mem _ u

-- 𝒫ᴹ X es set cuando X es set (consecuencia de MK_Pow).
theorem isSet_powerset {X : Class} (hX : IsSet X) : IsSet (𝒫ᴹ X) := by
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Pow X hX
  suffices h : 𝒫ᴹ X = z by rw [h]; exact hz_set
  apply MK_Ext; intro u _
  rw [mem_powerset_iff, hz_mem]
  exact Iff.rfl

-- ─ Dominio de una clase ───────────────────────────────────────────────────
noncomputable def dom (F : Class) : Class := {| x | ∃ y, ⟪x, y⟫ ∈ᴹ F |}

theorem mem_dom_iff (F x : Class) :
    x ∈ᴹ dom F ↔ IsSet x ∧ ∃ y, ⟪x, y⟫ ∈ᴹ F :=
  classComp_mem _ x

-- ─ Imagen de un conjunto bajo una clase ──────────────────────────────────
noncomputable def image (F x : Class) : Class :=
  {| y | ∃ u, u ∈ᴹ x ∧ ⟪u, y⟫ ∈ᴹ F |}

theorem mem_image_iff (F x v : Class) :
    v ∈ᴹ image F x ↔ IsSet v ∧ ∃ u, u ∈ᴹ x ∧ ⟪u, v⟫ ∈ᴹ F :=
  classComp_mem _ v

-- image F x es set cuando x es set e IsClassFun F (consecuencia de MK_Repl).
theorem isSet_image {F x : Class} (hx : IsSet x) (hF : IsClassFun F) :
    IsSet (image F x) := by
  obtain ⟨z, hz_set, hz_mem⟩ := MK_Repl F x hx hF
  suffices h : image F x = z by rw [h]; exact hz_set
  apply MK_Ext; intro v hv
  rw [mem_image_iff, hz_mem]

-- ── §1i · Álgebra booleana de clases ─────────────────────────────────────

-- ─ Helpers de membresía ───────────────────────────────────────────────────

-- ∅ᴹ tiene membresía equivalente a False.
theorem mem_empty_iff (u : Class) : u ∈ᴹ ∅ᴹ ↔ False :=
  ⟨not_mem_empty u, False.elim⟩

-- Complemento simplificado: IsSet u ya disponible.
theorem mem_compl_iff' {A u : Class} (hu : IsSet u) :
    u ∈ᴹ ∁ᴹ A ↔ u ∉ᴹ A :=
  ⟨fun h => ((mem_compl_iff A u).mp h).2,
   fun h => (mem_compl_iff A u).mpr ⟨hu, h⟩⟩

-- IsSet X ↔ X ∈ᴹ 𝐕ᴹ.
theorem isSet_iff_mem_univ {X : Class} : IsSet X ↔ X ∈ᴹ 𝐕ᴹ :=
  (mem_univ_iff X).symm

-- ─ SubClass ───────────────────────────────────────────────────────────────

theorem subset_refl (A : Class) : A ⊆ᴹ A :=
  fun _ h => h

theorem subset_trans {A B C : Class} (h1 : A ⊆ᴹ B) (h2 : B ⊆ᴹ C) : A ⊆ᴹ C :=
  fun u h => h2 u (h1 u h)

theorem subset_antisymm {A B : Class} (h1 : A ⊆ᴹ B) (h2 : B ⊆ᴹ A) : A = B :=
  MK_Ext A B fun u _ => ⟨h1 u, h2 u⟩

theorem empty_subset (A : Class) : ∅ᴹ ⊆ᴹ A :=
  fun u h => (not_mem_empty u h).elim

theorem subset_univ (A : Class) : A ⊆ᴹ 𝐕ᴹ :=
  fun u h => (mem_univ_iff u).mpr (isSet_of_mem h)

theorem subset_union_left (A B : Class) : A ⊆ᴹ A ∪ᴹ B :=
  fun _ h => (mem_union_iff' (isSet_of_mem h)).mpr (Or.inl h)

theorem subset_union_right (A B : Class) : B ⊆ᴹ A ∪ᴹ B :=
  fun _ h => (mem_union_iff' (isSet_of_mem h)).mpr (Or.inr h)

theorem inter_subset_left (A B : Class) : A ∩ᴹ B ⊆ᴹ A :=
  fun _ h => ((mem_inter_iff' (isSet_of_mem h)).mp h).1

theorem inter_subset_right (A B : Class) : A ∩ᴹ B ⊆ᴹ B :=
  fun _ h => ((mem_inter_iff' (isSet_of_mem h)).mp h).2

-- ─ Unión binaria — álgebra ────────────────────────────────────────────────

theorem union_comm (A B : Class) : A ∪ᴹ B = B ∪ᴹ A := by
  apply MK_Ext; intro u hu
  simp only [mem_union_iff' hu]; exact Or.comm

theorem union_assoc (A B C : Class) : (A ∪ᴹ B) ∪ᴹ C = A ∪ᴹ (B ∪ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [mem_union_iff' hu]; exact or_assoc

theorem union_self (A : Class) : A ∪ᴹ A = A := by
  apply MK_Ext; intro u hu
  simp only [mem_union_iff' hu]; exact or_self_iff

theorem union_empty (A : Class) : A ∪ᴹ ∅ᴹ = A := by
  apply MK_Ext; intro u hu
  simp [mem_union_iff' hu, mem_empty_iff]

theorem empty_union (A : Class) : ∅ᴹ ∪ᴹ A = A := by
  rw [union_comm]; exact union_empty A

theorem union_univ (A : Class) : A ∪ᴹ 𝐕ᴹ = 𝐕ᴹ := by
  apply MK_Ext; intro u hu
  simp only [mem_union_iff' hu, mem_univ_iff]
  exact ⟨fun h => h.elim isSet_of_mem id, Or.inr⟩

theorem univ_union (A : Class) : 𝐕ᴹ ∪ᴹ A = 𝐕ᴹ := by
  rw [union_comm]; exact union_univ A

-- ─ Intersección binaria — álgebra ─────────────────────────────────────────

theorem inter_comm (A B : Class) : A ∩ᴹ B = B ∩ᴹ A := by
  apply MK_Ext; intro u hu
  simp only [mem_inter_iff' hu]; exact And.comm

theorem inter_assoc (A B C : Class) : (A ∩ᴹ B) ∩ᴹ C = A ∩ᴹ (B ∩ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [mem_inter_iff' hu]; exact and_assoc

theorem inter_self (A : Class) : A ∩ᴹ A = A := by
  apply MK_Ext; intro u hu
  simp only [mem_inter_iff' hu]; exact and_self_iff

theorem inter_empty (A : Class) : A ∩ᴹ ∅ᴹ = ∅ᴹ := by
  apply MK_Ext; intro u hu
  simp [mem_inter_iff' hu, mem_empty_iff]

theorem empty_inter (A : Class) : ∅ᴹ ∩ᴹ A = ∅ᴹ := by
  rw [inter_comm]; exact inter_empty A

theorem inter_univ (A : Class) : A ∩ᴹ 𝐕ᴹ = A := by
  apply MK_Ext; intro u hu
  simp only [mem_inter_iff' hu, mem_univ_iff]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, isSet_of_mem h⟩⟩

theorem univ_inter (A : Class) : 𝐕ᴹ ∩ᴹ A = A := by
  rw [inter_comm]; exact inter_univ A

-- ─ Distributividad ────────────────────────────────────────────────────────

theorem union_inter_distrib_left (A B C : Class) :
    A ∪ᴹ (B ∩ᴹ C) = (A ∪ᴹ B) ∩ᴹ (A ∪ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [mem_union_iff' hu, mem_inter_iff' hu]
  exact ⟨fun h => h.elim (fun ha => ⟨Or.inl ha, Or.inl ha⟩)
                          (fun ⟨hb, hc⟩ => ⟨Or.inr hb, Or.inr hc⟩),
         fun ⟨h1, h2⟩ => h1.elim Or.inl (fun hb => h2.elim Or.inl
                          (fun hc => Or.inr ⟨hb, hc⟩))⟩

theorem inter_union_distrib_left (A B C : Class) :
    A ∩ᴹ (B ∪ᴹ C) = (A ∩ᴹ B) ∪ᴹ (A ∩ᴹ C) := by
  apply MK_Ext; intro u hu
  simp only [mem_inter_iff' hu, mem_union_iff' hu]
  exact ⟨fun ⟨ha, h⟩ => h.elim (fun hb => Or.inl ⟨ha, hb⟩)
                                 (fun hc => Or.inr ⟨ha, hc⟩),
         fun h => h.elim (fun ⟨ha, hb⟩ => ⟨ha, Or.inl hb⟩)
                          (fun ⟨ha, hc⟩ => ⟨ha, Or.inr hc⟩)⟩

-- ─ Complemento ────────────────────────────────────────────────────────────

theorem compl_compl (A : Class) : ∁ᴹ (∁ᴹ A) = A := by
  apply MK_Ext; intro u hu
  rw [mem_compl_iff' hu, mem_compl_iff' hu]
  exact ⟨Classical.byContradiction, fun ha hna => hna ha⟩

theorem union_compl_self (A : Class) : A ∪ᴹ ∁ᴹ A = 𝐕ᴹ := by
  apply MK_Ext; intro u hu
  simp only [mem_union_iff' hu, mem_compl_iff' hu, mem_univ_iff]
  exact ⟨fun _ => hu, fun _ => Classical.em (u ∈ᴹ A)⟩

theorem inter_compl_self (A : Class) : A ∩ᴹ ∁ᴹ A = ∅ᴹ := by
  apply MK_Ext; intro u hu
  simp only [mem_inter_iff' hu, mem_compl_iff' hu, mem_empty_iff]
  exact ⟨fun ⟨h, hn⟩ => hn h, False.elim⟩

-- ─ Leyes de De Morgan ─────────────────────────────────────────────────────

theorem compl_union (A B : Class) : ∁ᴹ (A ∪ᴹ B) = ∁ᴹ A ∩ᴹ ∁ᴹ B := by
  apply MK_Ext; intro u hu
  simp only [mem_compl_iff' hu, mem_union_iff' hu, mem_inter_iff' hu]
  exact ⟨fun h => ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr hb)⟩,
         fun ⟨ha, hb⟩ h => h.elim ha hb⟩

theorem compl_inter (A B : Class) : ∁ᴹ (A ∩ᴹ B) = ∁ᴹ A ∪ᴹ ∁ᴹ B := by
  apply MK_Ext; intro u hu
  simp only [mem_compl_iff' hu, mem_inter_iff' hu, mem_union_iff' hu]
  exact ⟨fun h => Classical.byContradiction (fun hn =>
           h ⟨Classical.byContradiction (fun ha => hn (Or.inl ha)),
              Classical.byContradiction (fun hb => hn (Or.inr hb))⟩),
         fun h ⟨ha, hb⟩ => h.elim (· ha) (· hb)⟩

-- ─ Diferencia = intersección con complemento ──────────────────────────────

theorem sdiff_eq_inter_compl (A B : Class) : A ∖ᴹ B = A ∩ᴹ ∁ᴹ B := by
  apply MK_Ext; intro u hu
  rw [mem_sdiff_iff' hu, mem_inter_iff' hu, mem_compl_iff' hu]

-- ── A9. Global Choice ─────────────────────────────────────────────────────
-- There exists a class C that selects an element from every non-empty set.
-- This is Kelley's (1955) original ninth axiom, included here as part of
-- the base MK system. It is stronger than AC (which only gives a set-function
-- for set-indexed families) because C is a proper class that works uniformly
-- over ALL sets simultaneously.
--
-- Three equivalent formulations (all provably equivalent over A1–A8):
--
--   (a) Class selector form:
-- axiom MK_GlobalChoice :
--   ∃ C : Class,
--     ∀ x : Class, IsSet x → (∃ u : Class, u ∈ᴹ x) →
--       ∃ u : Class, u ∈ᴹ x ∧ ⟪x, u⟫ ∈ᴹ C
--
--   (b) Class well-order form:
-- axiom MK_WO :
--   ∃ W : Class,
--     (∀ x y : Class, IsSet x → IsSet y → x ≠ y →
--       ⟪x, y⟫ ∈ᴹ W ∨ ⟪y, x⟫ ∈ᴹ W) ∧
--     (∀ x y : Class, ⟪x, y⟫ ∈ᴹ W → ¬ ⟪y, x⟫ ∈ᴹ W) ∧
--     (∀ X : Class, (∃ u : Class, IsSet u ∧ u ∈ᴹ X) →
--       ∃ m : Class, IsSet m ∧ m ∈ᴹ X ∧
--         ∀ u : Class, IsSet u → u ∈ᴹ X → ¬ ⟪u, m⟫ ∈ᴹ W)
--
--   (c) Zermelo form (every set can be well-ordered by some set-relation):
--       follows from (b) by restriction.
--
-- We adopt formulation (a) as the official axiom; (b) and (c) will be
-- derived theorems.
noncomputable def choose_elem (x : Class) : Class :=
  if h : ∃ u : Class, u ∈ᴹ x then Classical.choose h else ∅ᴹ

theorem choose_elem_mem (x : Class) (h : ∃ u : Class, u ∈ᴹ x) : choose_elem x ∈ᴹ x := by
  unfold choose_elem
  simp only [h, dif_pos]
  exact Classical.choose_spec h

noncomputable def GlobalChoiceClass : Class :=
  classComp (fun p => ∃ x : Class, IsSet x ∧ p = opair x (choose_elem x))

theorem MK_GlobalChoice :
  ∃ C : Class,
    ∀ x : Class, IsSet x → (∃ u : Class, u ∈ᴹ x) →
      ∃ u : Class, u ∈ᴹ x ∧ ⟪x, u⟫ ∈ᴹ C := by
  refine ⟨GlobalChoiceClass, ?_⟩
  intro x hx h_ex
  let u := choose_elem x
  have hu_mem : u ∈ᴹ x := choose_elem_mem x h_ex
  refine ⟨u, hu_mem, ?_⟩
  apply (classComp_mem _ _).mpr
  have h_opair_set : IsSet ⟪x, u⟫ := isSet_opair hx (isSet_of_mem hu_mem)
  exact ⟨h_opair_set, x, hx, rfl⟩


/-! ─────────────────────────────────────────────────────────────────────────
    §3 · MK⁺ — Class Axiom Scheme of Choice (CAC)
    ─────────────────────────────────────────────────────────────────────────

  MK (with A1–A9 above) already has Global Choice as a single axiom.
  What MK⁺ adds is the *scheme* of class choice: for any *definable*
  class-relation R that is total on sets, a class-function selector exists.

  The difference:
    · A9 (Global Choice) gives one fixed class C that chooses from all sets.
    · CAC (MK⁺) gives, for each total class-relation R, a class-function
      F ⊆ R. This is strictly stronger because R can depend on parameters
      ranging over classes, yielding choices that A9 alone cannot provide.

  Reference: Felgner (1971) "Models of ZF-Set Theory", §IV;
             Lévy (1976) "The Role of Classes in Set Theory".
-/

-- ── MK⁺. Class Axiom Scheme of Choice (CAC) ──────────────────────────────
-- For any class-relation R that is total on sets (every set has an R-image),
-- there exists a class-function F ⊆ R with the same domain on sets.
--
-- In Lean a single `axiom` with universally quantified R captures the
-- whole scheme (one Lean Prop = one formula, so ∀ R already ranges over
-- all definable class-relations).
--
noncomputable def choose_R_elem (R x : Class) : Class :=
  if h : ∃ y : Class, IsSet y ∧ ⟪x, y⟫ ∈ᴹ R then Classical.choose h else ∅ᴹ

theorem choose_R_elem_mem (R x : Class) (h : ∃ y : Class, IsSet y ∧ ⟪x, y⟫ ∈ᴹ R) : IsSet (choose_R_elem R x) ∧ ⟪x, choose_R_elem R x⟫ ∈ᴹ R := by
  unfold choose_R_elem
  simp only [h, dif_pos]
  exact Classical.choose_spec h

theorem MK_CAC :
  ∀ (R : Class),
    (∀ x : Class, IsSet x → ∃ y : Class, IsSet y ∧ ⟪x, y⟫ ∈ᴹ R) →
    ∃ F : Class,
      (∀ x y z : Class, IsSet x → IsSet y → IsSet z → ⟪x, y⟫ ∈ᴹ F → ⟪x, z⟫ ∈ᴹ F → y = z) ∧
      (∀ x : Class, IsSet x → ∃ y : Class, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) ∧
      (∀ x y : Class, IsSet x → IsSet y → ⟪x, y⟫ ∈ᴹ F → ⟪x, y⟫ ∈ᴹ R) := by
  intro R hR
  let F := classComp (fun p => ∃ x y : Class, IsSet x ∧ IsSet y ∧ p = opair x y ∧ y = choose_R_elem R x)
  refine ⟨F, ?_, ?_, ?_⟩
  · intro x y z hx hy hz hxy_F hxz_F
    have hxy_iff := (classComp_mem _ (opair x y)).mp hxy_F
    have hxz_iff := (classComp_mem _ (opair x z)).mp hxz_F
    obtain ⟨x1, y1, hx1, hy1, eq1, hy1_eq⟩ := hxy_iff.2
    obtain ⟨x2, y2, hx2, hy2, eq2, hy2_eq⟩ := hxz_iff.2
    have heq1 := opair_inj hx hy hx1 hy1 eq1
    have heq2 := opair_inj hx hz hx2 hy2 eq2
    have hx1_eq : x1 = x := heq1.1.symm
    have hx2_eq : x2 = x := heq2.1.symm
    have hy1_eq_y : y1 = y := heq1.2.symm
    have hy2_eq_z : y2 = z := heq2.2.symm
    rw [← hy1_eq_y, hy1_eq, hx1_eq]
    rw [← hy2_eq_z, hy2_eq, hx2_eq]
  · intro x hx
    have h_ex := hR x hx
    have h_mem := choose_R_elem_mem R x h_ex
    refine ⟨choose_R_elem R x, h_mem.1, ?_⟩
    apply (classComp_mem _ _).mpr
    exact ⟨isSet_opair hx h_mem.1, x, choose_R_elem R x, hx, h_mem.1, rfl, rfl⟩
  · intro x y hx hy hy_F
    have hxy_iff := (classComp_mem _ _).mp hy_F
    obtain ⟨x1, y1, hx1, hy1, eq1, hy1_eq⟩ := hxy_iff.2
    have heq := opair_inj hx hy hx1 hy1 eq1
    have hx_eq : x = x1 := heq.1
    have hy_eq : y = y1 := heq.2
    rw [hx_eq, hy_eq, hy1_eq]
    have h_ex := hR x1 hx1
    exact (choose_R_elem_mem R x1 h_ex).2


/-! ─────────────────────────────────────────────────────────────────────────
    §4 · ∃¹ en el contexto de clases
    ─────────────────────────────────────────────────────────────────────────

  Usamos ∃¹ (notación preferida de Prelim) en lugar de ∃!.
  Ambas expanden a ExistsUnique; ∃¹ evita colisiones con el ∃! de Lean.

  En el contexto MK, ∃¹ x, φ x significa:
    existe exactamente una *clase* X (o set, según contexto) que cumple φ.

  Usos típicos:
    · Unicidad de la clase vacía: ∃¹ E : Class, ∀ u, u ∉ᴹ E
    · Unicidad del segundo componente: ∃¹ y, ⟪x, y⟫ ∈ᴹ F
    · Relaciones funcionales: IsClassFun F → ∀ x, IsSet x → ∃¹ y, ⟪x, y⟫ ∈ᴹ F
-/

theorem empty_unique :
    ∃¹ E : Class, (∀ u : Class, u ∉ᴹ E) ∧ IsSet E := by
  -- Existencia: MK_Inf garantiza un set vacío e.
  obtain ⟨_, _, ⟨e, he_set, he_empty, _⟩, _⟩ := MK_Inf
  refine ExistsUnique.intro e ⟨he_empty, he_set⟩ ?_
  -- Unicidad: cualquier E' vacío coincide con e por MK_Ext.
  intro E' ⟨hE', _⟩
  apply MK_Ext
  intro u _
  exact ⟨fun h => absurd h (hE' u), fun h => absurd h (he_empty u)⟩

theorem unique_image (F x : Class) (hF : IsClassFun F) (hx : IsSet x)
    (hu : ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) : ∃¹ y : Class, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F := by
  obtain ⟨y, hy_set, hy⟩ := hu
  refine ExistsUnique.intro y ⟨hy_set, hy⟩ ?_
  intro z ⟨hz_set, hz⟩
  exact (hF x y z hx hy_set hz_set hy hz).symm


end MKplusCAC
