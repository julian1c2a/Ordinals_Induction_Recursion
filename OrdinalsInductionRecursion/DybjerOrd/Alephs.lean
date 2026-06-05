import OrdinalsInductionRecursion.DybjerOrd.Transfinite
import OrdinalsInductionRecursion.DybjerOrd.Universes

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- FASE 1: Operaciones de Extracción (Setup)
-- ==========================================

/-- Función de extracción que nos da un representante DPreOrd de un DOrdinal arbitrario.
Usa Elección Clásica ya que DOrdinal es un cociente. -/
noncomputable def out (x : DOrdinal) : DPreOrd :=
  Classical.choose (Quotient.exists_rep x)

/-- Versión puramente estructural (en DPreOrd) de la función de Hartogs, 
usando la extracción sobre el Hartogs ordinal. -/
noncomputable def hartogs_pre (x : DPreOrd) : DPreOrd :=
  out (hartogs (Quotient.mk Setoid x))

-- ==========================================
-- FASE 2: La Recursión Estructural (aleph_pre)
-- ==========================================

/-- 
Aleph Computacional: Recursión directa sobre los árboles sintácticos.
-/
noncomputable def aleph_pre : DPreOrd → DPreOrd
  | .zero => omega_pre
  | .succ x' => hartogs_pre (aleph_pre x')
  | .sup c f => .sup (.sum c .unit) (fun a => match a with
    | Sum.inl b => aleph_pre (f b)
    | Sum.inr _ => omega_pre)

-- ==========================================
-- FASE 4: La Ruta Lógica para Probar el Respeto
-- ==========================================

theorem out_eq (x : DOrdinal) : Quotient.mk Setoid (out x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

theorem mk_hartogs_pre (y : DPreOrd) : (Quotient.mk Setoid (hartogs_pre y) : DOrdinal) = hartogs (Quotient.mk Setoid y) :=
  out_eq (hartogs (Quotient.mk Setoid y))

theorem mem_hartogs_pre (y : DPreOrd) : DMem y (hartogs_pre y) := by
  have h := lt_hartogs (Quotient.mk Setoid y)
  have heq : hartogs (Quotient.mk Setoid y) = Quotient.mk Setoid (hartogs_pre y) := (mk_hartogs_pre y).symm
  rw [heq] at h
  exact h

/-- Lema Crítico: Si A ⊆ B, entonces A ∈ hartogs(B). 
Esto es cierto porque hartogs(B) es estrictamente mayor que cualquier subconjunto de B. -/
theorem Subset_implies_Mem_hartogs_pre {x y : DPreOrd} (h : DSubset x y) : DMem x (hartogs_pre y) :=
  DSubset_DMem_trans h (mem_hartogs_pre y)

-- Theorem stating that omega_pre is a subset of any aleph
theorem omega_subset_aleph (y : DPreOrd) : DSubset omega_pre (aleph_pre y) := by
  induction y with
  | zero => exact DSubset_refl omega_pre
  | succ y' ih =>
    have h2 : DSubset (aleph_pre y') (hartogs_pre (aleph_pre y')) := Dmem_implies_subset (mem_hartogs_pre _)
    exact DSubset_trans ih h2
  | sup c f ih =>
    have hs := @DSubset_sup omega_pre omega_pre _ (.sum c .unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (DSubset_refl _) (Sum.inr ()) rfl
    unfold aleph_pre
    exact hs

/-- Monotonía Estricta: Aleph preserva subconjuntos y pertenencia mutuamente. -/
theorem hartogs_pre_monotone {x y : DPreOrd} (h : DSubset x y) : DSubset (hartogs_pre x) (hartogs_pre y) := by
  have h_sub_ord : DOrdinal.Subset (Quotient.mk Setoid x) (Quotient.mk Setoid y) := h
  have h_hartogs_ord_sub := DybjerOrd.hartogs_monotone h_sub_ord
  have heqx : hartogs (Quotient.mk Setoid x) = Quotient.mk Setoid (hartogs_pre x) := (mk_hartogs_pre x).symm
  have heqy : hartogs (Quotient.mk Setoid y) = Quotient.mk Setoid (hartogs_pre y) := (mk_hartogs_pre y).symm
  rw [heqx, heqy] at h_hartogs_ord_sub
  exact h_hartogs_ord_sub

theorem aleph_pre_sup {A : Type} (c : UCodeFam A) (f : A → DPreOrd) : aleph_pre (.sup c f) = .sup (.sum c .unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) := by
  conv =>
    lhs
    unfold aleph_pre

def aleph_all (x : DPreOrd) :
  (∀ {y}, DSubset x y → DSubset (aleph_pre x) (aleph_pre y)) ∧
  (∀ {y}, DMem x y → DMem (aleph_pre x) (aleph_pre y)) ∧
  (∀ {y}, DMem x y → DSubset (hartogs_pre (aleph_pre x)) (aleph_pre y)) :=
  let sub_sub : ∀ {y}, DSubset x y → DSubset (aleph_pre x) (aleph_pre y) :=
    match x with
    | .zero => fun _ => omega_subset_aleph _
    | .succ x' => fun h =>
      match h with
      | @DSubset.succ_subset _ _ hmem => (aleph_all x').2.2 hmem
    | .sup c f => fun h =>
      match h with
      | @DSubset.sup_subset A c f _ hsub =>
        have h_all : ∀ a : A ⊕ PUnit, DSubset (match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (aleph_pre _) := fun a =>
          match a with
          | Sum.inl b => (aleph_all (f b)).1 (hsub b)
          | Sum.inr _ => omega_subset_aleph _
        have hs := @DSubset.sup_subset (A ⊕ PUnit) (.sum c .unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (aleph_pre _) h_all
        by { rw [aleph_pre_sup]; exact hs }

  let rec mem_mem {y} (h : DMem x y) : DMem (aleph_pre x) (aleph_pre y) :=
    match y, h with
    | .succ y', DMem.mem_succ hsub =>
      Subset_implies_Mem_hartogs_pre (sub_sub hsub)
    | .sup c f, DMem.mem_sup a hmem =>
      have h_mem_a := mem_mem hmem
      have hs := @DMem.mem_sup _ (.sum c .unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (aleph_pre x) (Sum.inl a) h_mem_a
      by { rw [aleph_pre_sup]; exact hs }

  let rec mem_hartogs {y} (h : DMem x y) : DSubset (hartogs_pre (aleph_pre x)) (aleph_pre y) :=
    match y, h with
    | .succ y', DMem.mem_succ hsub =>
      hartogs_pre_monotone (sub_sub hsub)
    | .sup c f, DMem.mem_sup a hmem =>
      have h1 := mem_hartogs hmem
      have hs := @DSubset_sup (aleph_pre (f a)) (aleph_pre (f a)) _ (.sum c .unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (DSubset_refl _) (Sum.inl a) rfl
      have h2 : DSubset (aleph_pre (f a)) (aleph_pre (.sup c f)) := by { rw [aleph_pre_sup]; exact hs }
      DSubset_trans h1 h2

  ⟨sub_sub, mem_mem, mem_hartogs⟩

theorem aleph_subset_and_mem (x y : DPreOrd) :
  (DSubset x y → DSubset (aleph_pre x) (aleph_pre y)) ∧
  (DMem x y → DMem (aleph_pre x) (aleph_pre y)) :=
  ⟨(aleph_all x).1, (aleph_all x).2.1⟩

/-- El isomorfismo extensional es preservado porque la función es monótona. -/
theorem aleph_respects_Equiv {x y : DPreOrd} (h : Equiv x y) : Equiv (aleph_pre x) (aleph_pre y) :=
  ⟨(aleph_subset_and_mem x y).1 h.1, (aleph_subset_and_mem y x).1 h.2⟩

-- ==========================================
-- FASE 3: Elevación al Universo de Ordinales (Quotient Lift)
-- ==========================================

/-- 
La Jerarquía de Alephs ($\aleph_\alpha$) pura, construida SIN axioma de reemplazo,
soportada enteramente en la estructura sintáctica de UCodeFam.
-/
noncomputable def aleph (x : DOrdinal) : DOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk Setoid (aleph_pre a) : DOrdinal))
    (fun _ _ h => Quotient.sound (aleph_respects_Equiv h))

-- Propiedades básicas
theorem aleph_zero : aleph zeroOrd = omega := rfl

theorem aleph_succ (a : DOrdinal) : aleph (succOrd a) = hartogs (aleph a) := by
  revert a
  exact Quotient.ind (fun x => mk_hartogs_pre (aleph_pre x))

theorem omega_le_aleph (a : DOrdinal) : omega ≤ aleph a := by
  revert a
  exact Quotient.ind (fun x => omega_subset_aleph x)

end DybjerOrd
