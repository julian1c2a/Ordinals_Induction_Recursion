import OrdinalsInductionRecursion.TarskiOrd.Transfinite

namespace TarskiOrd
open TPreOrd
open Classical

-- ==========================================
-- FASE 1: Operaciones de Extracción (Setup)
-- ==========================================

/-- Función de extracción que nos da un representante TPreOrd de un TOrdinal arbitrario.
Usa Elección Clásica ya que TOrdinal es un cociente. -/
noncomputable def out (x : TOrdinal) : TPreOrd :=
  Classical.choose (Quotient.exists_rep x)

/-- Versión puramente estructural (en TPreOrd) de la función de Hartogs, 
usando la extracción sobre el Hartogs ordinal. -/
noncomputable def hartogs_pre (x : TPreOrd) : TPreOrd :=
  out (hartogs (Quotient.mk TPreOrd.Setoid x))

-- ==========================================
-- FASE 2: La Recursión Estructural (aleph_pre)
-- ==========================================

/-- 
Aleph Computacional: Recursión directa sobre los árboles sintácticos.
El caso límite es nativo ya que el supremum estructural avanza por sí solo.
-/
noncomputable def aleph_pre : TPreOrd → TPreOrd
  | .zero => omega_pre
  | .succ x' => hartogs_pre (aleph_pre x')
  | .sup c f => sup (.sum c .unit) (fun a => match a with
    | Sum.inl b => aleph_pre (f b)
    | Sum.inr _ => omega_pre)

-- ==========================================
-- FASE 4: La Ruta Lógica para Probar el Respeto
-- ==========================================

theorem out_eq (x : TOrdinal) : Quotient.mk TPreOrd.Setoid (out x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

theorem mk_hartogs_pre (y : TPreOrd) : (Quotient.mk TPreOrd.Setoid (hartogs_pre y) : TOrdinal) = hartogs (Quotient.mk TPreOrd.Setoid y) :=
  out_eq (hartogs (Quotient.mk TPreOrd.Setoid y))

theorem mem_hartogs_pre (y : TPreOrd) : TPreOrd.Mem y (hartogs_pre y) := by
  have h := lt_hartogs (Quotient.mk TPreOrd.Setoid y)
  have heq : hartogs (Quotient.mk TPreOrd.Setoid y) = Quotient.mk TPreOrd.Setoid (hartogs_pre y) := (mk_hartogs_pre y).symm
  rw [heq] at h
  exact h

/-- Lema Crítico: Si A ⊆ B, entonces A ∈ hartogs(B). 
Esto es cierto porque hartogs(B) es estrictamente mayor que cualquier subconjunto de B. -/
theorem Subset_implies_Mem_hartogs_pre {x y : TPreOrd} (h : TPreOrd.Subset x y) : TPreOrd.Mem x (hartogs_pre y) :=
  TPreOrd.Subset_Mem_trans h (mem_hartogs_pre y)

-- Theorem stating that omega_pre is a subset of any aleph
theorem omega_subset_aleph (y : TPreOrd) : TPreOrd.Subset omega_pre (aleph_pre y) := by
  induction y with
  | zero => exact TPreOrd.Subset_refl omega_pre
  | succ y' ih =>
    have h2 : TPreOrd.Subset (aleph_pre y') (hartogs_pre (aleph_pre y')) := TPreOrd.mem_implies_subset (mem_hartogs_pre _)
    exact TPreOrd.Subset_trans ih h2
  | sup c f ih =>
    have hs := @TPreOrd.Subset_sup omega_pre omega_pre (UCode.sum c UCode.unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (TPreOrd.Subset_refl _) (Sum.inr ()) rfl
    unfold aleph_pre
    exact hs

/-- Monotonía Estricta: Aleph preserva subconjuntos y pertenencia mutuamente. -/
theorem hartogs_pre_monotone {x y : TPreOrd} (h : TPreOrd.Subset x y) : TPreOrd.Subset (hartogs_pre x) (hartogs_pre y) := by
  have h_sub_ord : TOrdinal.Subset (Quotient.mk TPreOrd.Setoid x) (Quotient.mk TPreOrd.Setoid y) := h
  have h_hartogs_ord_sub := hartogs_monotone h_sub_ord
  have heqx : hartogs (Quotient.mk TPreOrd.Setoid x) = Quotient.mk TPreOrd.Setoid (hartogs_pre x) := (mk_hartogs_pre x).symm
  have heqy : hartogs (Quotient.mk TPreOrd.Setoid y) = Quotient.mk TPreOrd.Setoid (hartogs_pre y) := (mk_hartogs_pre y).symm
  rw [heqx, heqy] at h_hartogs_ord_sub
  exact h_hartogs_ord_sub

theorem aleph_pre_sup (c f) : aleph_pre (TPreOrd.sup c f) = TPreOrd.sup (UCode.sum c UCode.unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) := by
  conv =>
    lhs
    unfold aleph_pre

def aleph_all (x : TPreOrd) :
  (∀ {y}, TPreOrd.Subset x y → TPreOrd.Subset (aleph_pre x) (aleph_pre y)) ∧
  (∀ {y}, TPreOrd.Mem x y → TPreOrd.Mem (aleph_pre x) (aleph_pre y)) ∧
  (∀ {y}, TPreOrd.Mem x y → TPreOrd.Subset (hartogs_pre (aleph_pre x)) (aleph_pre y)) :=
  let sub_sub : ∀ {y}, TPreOrd.Subset x y → TPreOrd.Subset (aleph_pre x) (aleph_pre y) :=
    match x with
    | .zero => fun _ => omega_subset_aleph _
    | .succ x' => fun h =>
      match h with
      | @TPreOrd.Subset.succ_subset _ _ hmem => (aleph_all x').2.2 hmem
    | .sup c f => fun h =>
      match h with
      | @TPreOrd.Subset.sup_subset _ _ _ hsub =>
        have h_all : ∀ a : El (UCode.sum c UCode.unit), TPreOrd.Subset (match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (aleph_pre _) := fun a =>
          match a with
          | Sum.inl b => (aleph_all (f b)).1 (hsub b)
          | Sum.inr _ => omega_subset_aleph _
        have hs := @TPreOrd.Subset.sup_subset (UCode.sum c UCode.unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (aleph_pre _) h_all
        by { rw [aleph_pre_sup]; exact hs }

  let rec mem_mem {y} (h : TPreOrd.Mem x y) : TPreOrd.Mem (aleph_pre x) (aleph_pre y) :=
    match y, h with
    | .succ y', TPreOrd.Mem.mem_succ hsub =>
      Subset_implies_Mem_hartogs_pre (sub_sub hsub)
    | .sup c f, TPreOrd.Mem.mem_sup a hmem =>
      have h_mem_a := mem_mem hmem
      have hs := @TPreOrd.Mem.mem_sup (UCode.sum c UCode.unit) (aleph_pre x) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (Sum.inl a) h_mem_a
      by { rw [aleph_pre_sup]; exact hs }

  let rec mem_hartogs {y} (h : TPreOrd.Mem x y) : TPreOrd.Subset (hartogs_pre (aleph_pre x)) (aleph_pre y) :=
    match y, h with
    | .succ y', TPreOrd.Mem.mem_succ hsub =>
      hartogs_pre_monotone (sub_sub hsub)
    | .sup c f, TPreOrd.Mem.mem_sup a hmem =>
      have h1 := mem_hartogs hmem
      have hs := @TPreOrd.Subset_sup (aleph_pre (f a)) (aleph_pre (f a)) (UCode.sum c UCode.unit) (fun a => match a with | Sum.inl b => aleph_pre (f b) | Sum.inr _ => omega_pre) (TPreOrd.Subset_refl _) (Sum.inl a) rfl
      have h2 : TPreOrd.Subset (aleph_pre (f a)) (aleph_pre (TPreOrd.sup c f)) := by { rw [aleph_pre_sup]; exact hs }
      TPreOrd.Subset_trans h1 h2

  ⟨sub_sub, mem_mem, mem_hartogs⟩

theorem aleph_subset_and_mem (x y : TPreOrd) :
  (TPreOrd.Subset x y → TPreOrd.Subset (aleph_pre x) (aleph_pre y)) ∧
  (TPreOrd.Mem x y → TPreOrd.Mem (aleph_pre x) (aleph_pre y)) :=
  ⟨(aleph_all x).1, (aleph_all x).2.1⟩

/-- El isomorfismo extensional es preservado porque la función es monótona. -/
theorem aleph_respects_Equiv {x y : TPreOrd} (h : Equiv x y) : Equiv (aleph_pre x) (aleph_pre y) :=
  ⟨(aleph_subset_and_mem x y).1 h.1, (aleph_subset_and_mem y x).1 h.2⟩

-- ==========================================
-- FASE 3: Elevación al Universo de Ordinales (Quotient Lift)
-- ==========================================

/-- 
La Jerarquía de Alephs ($\aleph_\alpha$) pura, construida SIN axioma de reemplazo,
soportada enteramente en la estructura sintáctica de UCode.
-/
noncomputable def aleph (x : TOrdinal) : TOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk TPreOrd.Setoid (aleph_pre a) : TOrdinal))
    (fun _ _ h => Quotient.sound (aleph_respects_Equiv h))

-- Propiedades básicas
theorem aleph_zero : aleph zeroOrd = omega := rfl

theorem aleph_succ (a : TOrdinal) : aleph (succOrd a) = hartogs (aleph a) := by
  revert a
  exact Quotient.ind (fun x => mk_hartogs_pre (aleph_pre x))

theorem omega_le_aleph (a : TOrdinal) : omega ≤ aleph a := by
  revert a
  exact Quotient.ind (fun x => omega_subset_aleph x)

end TarskiOrd
