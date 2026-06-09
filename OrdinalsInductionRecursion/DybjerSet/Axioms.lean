import OrdinalsInductionRecursion.DybjerSet.Tree

namespace DybjerSet

open Tree

-- ══════════════════════════════════════════════════════════════════
-- § 1. Conjunto Vacío
-- ══════════════════════════════════════════════════════════════════

def empty : DSet := Quotient.mk DybjerSet.Tree.Setoid .zero

theorem not_mem_empty (x : DSet) : ¬ (x ∈ empty) := by
  induction x using Quotient.ind
  rename_i a
  intro h
  have h' : DybjerSet.Tree.Mem a .zero := h
  cases h'

-- ══════════════════════════════════════════════════════════════════
-- § 2. Adjunción (Inserción de un elemento)
-- ══════════════════════════════════════════════════════════════════

open DybjerOrd

def insertTree (a b : Tree) : Tree :=
  match b with
  | .zero => .succ a
  | .succ c => .sup (.sum .unit .unit) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr _ => c
  | .sup c f => .sup (.sum .unit c) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr y => f y

-- Extensionalidad ya probada en DSet.ext

axiom insert_respects (a a' b b' : Tree) (ha : Equiv a a') (hb : Equiv b b') : Equiv (insertTree a b) (insertTree a' b')

def insert (a b : DSet) : DSet :=
  Quotient.lift₂ (fun x y => (Quotient.mk Tree.Setoid (insertTree x y) : DSet))
    (fun _ _ _ _ hx hy => Quotient.sound (insert_respects _ _ _ _ hx hy)) a b

-- ══════════════════════════════════════════════════════════════════
-- § 3. Singleton y Par No Ordenado
-- ══════════════════════════════════════════════════════════════════

def singleton (a : DSet) : DSet := insert a empty

def pair (a b : DSet) : DSet := insert a (singleton b)

theorem mem_insertTree_iff {c a b : Tree} : Mem c (insertTree a b) ↔ Equiv c a ∨ Mem c b := by
  cases b
  case zero =>
    constructor
    · intro h
      cases h
      rename_i h1 h2
      left
      exact ⟨h1, h2⟩
    · intro h
      cases h
      case inl heq =>
        exact mem_succ_equiv heq
      case inr hmem =>
        cases hmem
  case succ d =>
    constructor
    · intro h
      cases h
      rename_i i h1 h2
      cases i
      case inl _ =>
        left
        exact ⟨h1, h2⟩
      case inr _ =>
        right
        exact mem_succ_equiv ⟨h1, h2⟩
    · intro h
      cases h
      case inl heq =>
        exact mem_sup_equiv (Sum.inl ()) heq
      case inr hmem =>
        cases hmem
        rename_i hd1 hd2
        exact mem_sup_equiv (Sum.inr ()) ⟨hd1, hd2⟩
  case sup A fam f =>
    constructor
    · intro h
      cases h
      rename_i i h1 h2
      cases i
      case inl _ =>
        left
        exact ⟨h1, h2⟩
      case inr j =>
        right
        exact mem_sup_equiv j ⟨h1, h2⟩
    · intro h
      cases h
      case inl heq =>
        exact mem_sup_equiv (Sum.inl ()) heq
      case inr hmem =>
        cases hmem
        rename_i j hd1 hd2
        exact mem_sup_equiv (Sum.inr j) ⟨hd1, hd2⟩

theorem mem_insert_iff {c a b : DSet} : c ∈ insert a b ↔ c = a ∨ c ∈ b := by
  induction c using Quotient.ind
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i t_c t_a t_b
  change Tree.Mem t_c (insertTree t_a t_b) ↔ Quotient.mk Tree.Setoid t_c = Quotient.mk Tree.Setoid t_a ∨ Tree.Mem t_c t_b
  rw [mem_insertTree_iff]
  apply Iff.intro
  · rintro (h1 | h2)
    · left; exact Quotient.sound h1
    · right; exact h2
  · rintro (h1 | h2)
    · left; exact Quotient.exact h1
    · right; exact h2

theorem mem_singleton_iff {c a : DSet} : c ∈ singleton a ↔ c = a := by
  change c ∈ insert a empty ↔ c = a
  rw [mem_insert_iff]
  apply Iff.intro
  · rintro (h1 | h2)
    · exact h1
    · exfalso; exact not_mem_empty c h2
  · intro h; left; exact h

theorem mem_pair_iff {c a b : DSet} : c ∈ pair a b ↔ c = a ∨ c = b := by
  change c ∈ insert a (singleton b) ↔ c = a ∨ c = b
  rw [mem_insert_iff, mem_singleton_iff]

-- ══════════════════════════════════════════════════════════════════
-- § 4. Axioma del Infinito (Conjunto ω)
-- ══════════════════════════════════════════════════════════════════

/-- Árbol de Von Neumann para un número natural n -/
def natTree : Nat → Tree
  | 0 => .zero
  | n + 1 => insertTree (natTree n) (natTree n)

/-- El conjunto infinito omega (ω) que recopila todos los naturales -/
def omegaTree : Tree := .sup .nat (fun n => natTree n)

def omegaSet : DSet := Quotient.mk Tree.Setoid omegaTree

-- ══════════════════════════════════════════════════════════════════
-- § 5. Funciones Auxiliares para Estandarización de Árboles
-- ══════════════════════════════════════════════════════════════════

def indexType (t : Tree) : Type :=
  match t with
  | .zero => PEmpty
  | .succ _ => Unit
  | @Tree.sup A _ _ => A

def indexCode (t : Tree) : UCodeFam (indexType t) :=
  match t with
  | .zero => UCodeFam.empty
  | .succ _ => UCodeFam.unit
  | @Tree.sup _ c _ => c

def indexFun (t : Tree) : indexType t → Tree :=
  match t with
  | .zero => fun a => PEmpty.elim a
  | .succ x => fun _ => x
  | @Tree.sup _ _ f => f

-- ══════════════════════════════════════════════════════════════════
-- § 6. Axioma de la Unión (⋃ A)
-- ══════════════════════════════════════════════════════════════════

/-- Construye la unión universal de todos los elementos de un árbol -/
def unionTree (t : Tree) : Tree :=
  .sup (UCodeFam.sigma (indexCode t) (fun i => indexCode (indexFun t i)))
       (fun p => indexFun (indexFun t p.1) p.2)

axiom union_respects (a b : Tree) (h : Equiv a b) : Equiv (unionTree a) (unionTree b)

def sUnion (x : DSet) : DSet :=
  Quotient.lift (fun t => Quotient.mk Tree.Setoid (unionTree t))
    (fun _ _ h => Quotient.sound (union_respects _ _ h)) x

theorem mem_iff_exists_index {x y : Tree} : Mem x y ↔ ∃ i : indexType y, Equiv x (indexFun y i) := by
  cases y
  case zero =>
    constructor
    · intro h
      cases h
    · intro h
      obtain ⟨i, _⟩ := h
      cases i
  case succ d =>
    constructor
    · intro h
      cases h
      rename_i h1 h2
      exact ⟨(), h1, h2⟩
    · intro h
      obtain ⟨i, heq⟩ := h
      exact mem_succ_equiv heq
  case sup A c f =>
    constructor
    · intro h
      cases h
      rename_i a h1 h2
      exact ⟨a, h1, h2⟩
    · intro h
      obtain ⟨a, heq⟩ := h
      exact mem_sup_equiv a heq

theorem mem_unionTree_iff {c t : Tree} : Mem c (unionTree t) ↔ ∃ v, Mem c v ∧ Mem v t := by
  unfold unionTree
  rw [mem_iff_exists_index]
  constructor
  · rintro ⟨p, heq⟩
    have hv_t : Mem (indexFun t p.1) t := (mem_iff_exists_index).mpr ⟨p.1, Equiv_refl _⟩
    have hc_v : Mem c (indexFun t p.1) := (mem_iff_exists_index).mpr ⟨p.2, heq⟩
    exact ⟨indexFun t p.1, hc_v, hv_t⟩
  · rintro ⟨v, hc_v, hv_t⟩
    obtain ⟨i, heq_v⟩ := mem_iff_exists_index.mp hv_t
    have hc_f_i : Mem c (indexFun t i) := Mem_Subset_trans hc_v heq_v.left
    obtain ⟨j, heq_c⟩ := mem_iff_exists_index.mp hc_f_i
    exact ⟨⟨i, j⟩, heq_c⟩

theorem mem_sUnion_iff {c x : DSet} : c ∈ sUnion x ↔ ∃ v, c ∈ v ∧ v ∈ x := by
  induction c using Quotient.ind
  induction x using Quotient.ind
  rename_i t_c t_x
  change Tree.Mem t_c (unionTree t_x) ↔ ∃ v : DSet, Quotient.mk Tree.Setoid t_c ∈ v ∧ v ∈ Quotient.mk Tree.Setoid t_x
  rw [mem_unionTree_iff]
  constructor
  · rintro ⟨v, hc_v, hv_tx⟩
    exact ⟨Quotient.mk Tree.Setoid v, hc_v, hv_tx⟩
  · rintro ⟨v_set, hc_vset, hvset_x⟩
    induction v_set using Quotient.ind
    rename_i v
    exact ⟨v, hc_vset, hvset_x⟩

-- ══════════════════════════════════════════════════════════════════
-- § 7. Axioma del Conjunto Potencia (𝒫(A))
-- ══════════════════════════════════════════════════════════════════

def FilterType (b : Bool) : Type :=
  match b with
  | true => PUnit
  | false => PEmpty

def filterCode (b : Bool) : UCodeFam (FilterType b) :=
  match b with
  | true => UCodeFam.unit
  | false => UCodeFam.empty

/-- Construye un subconjunto de `t` filtrando las ramas según `g` -/
def filterTree (t : Tree) (g : indexType t → Bool) : Tree :=
  .sup (UCodeFam.sigma (indexCode t) (fun i => filterCode (g i)))
       (fun p => indexFun t p.1)

/-- El Conjunto Potencia de `t`, indexado por todas las funciones booleanas sobre las ramas de `t` -/
def powersetTree (t : Tree) : Tree :=
  .sup (UCodeFam.pi (indexCode t) (fun _ => UCodeFam.bool))
       (fun g => filterTree t g)

axiom powerset_respects (a b : Tree) (h : Equiv a b) : Equiv (powersetTree a) (powersetTree b)

def powerset (x : DSet) : DSet :=
  Quotient.lift (fun t => Quotient.mk Tree.Setoid (powersetTree t))
    (fun _ _ h => Quotient.sound (powerset_respects _ _ h)) x

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem mem_filterTree_iff {c t : Tree} {g : indexType t → Bool} : Mem c (filterTree t g) ↔ ∃ i : indexType t, g i = true ∧ Equiv c (indexFun t i) := by
  unfold filterTree
  rw [mem_iff_exists_index]
  constructor
  · rintro ⟨p, heq⟩
    have hp2 : g p.1 = true := by
      cases hg : g p.1
      case false =>
        have hp2' : FilterType false := hg ▸ p.2
        cases hp2'
      case true => rfl
    exact ⟨p.1, hp2, heq⟩
  · rintro ⟨i, hgi, heq⟩
    have hp2 : FilterType (g i) := by
      rw [hgi]
      exact ⟨⟩
    exact ⟨⟨i, hp2⟩, heq⟩

theorem Subset_iff_forall_Mem {x y : Tree} : Tree.Subset x y ↔ ∀ u, Mem u x → Mem u y := by
  constructor
  · intro h u hu
    exact Mem_Subset_trans hu h
  · intro h
    cases x
    case zero => exact Tree.Subset.zero_subset y
    case succ a =>
      have ha : Mem a (Tree.succ a) := mem_succ_equiv (Equiv_refl a)
      exact Tree.Subset.succ_subset (h a ha)
    case sup A c f =>
      apply Tree.Subset.sup_subset
      intro a
      have ha : Mem (f a) (Tree.sup c f) := mem_sup_equiv a (Equiv_refl (f a))
      exact h (f a) ha

theorem mem_powersetTree_iff {c t : Tree} : Mem c (powersetTree t) ↔ Tree.Subset c t := by
  unfold powersetTree
  rw [mem_iff_exists_index]
  constructor
  · rintro ⟨g, heq⟩
    apply Subset_iff_forall_Mem.mpr
    intro x hx
    have hx_filter : Mem x (filterTree t g) := Mem_Subset_trans hx heq.left
    obtain ⟨i, _, hx_eq⟩ := mem_filterTree_iff.mp hx_filter
    have ht : Mem (indexFun t i) t := (mem_iff_exists_index).mpr ⟨i, Equiv_refl _⟩
    exact Equiv_Mem_trans hx_eq ht
  · intro hsub
    let g : indexType t → Bool := fun i =>
      if Mem (indexFun t i) c then true else false
    refine ⟨g, ?_⟩
    constructor
    · apply Subset_iff_forall_Mem.mpr
      intro x hx
      have hxt : Mem x t := Subset_iff_forall_Mem.mp hsub x hx
      obtain ⟨i, hx_eq⟩ := mem_iff_exists_index.mp hxt
      have h_mem_c : Mem (indexFun t i) c := Equiv_Mem_trans (Equiv_symm hx_eq) hx
      have hgi : g i = true := by
        change (if Mem (indexFun t i) c then true else false) = true
        rw [if_pos h_mem_c]
      apply mem_filterTree_iff.mpr
      exact ⟨i, hgi, hx_eq⟩
    · apply Subset_iff_forall_Mem.mpr
      intro x hx
      obtain ⟨i, hgi, hx_eq⟩ := mem_filterTree_iff.mp hx
      have h_mem_c : Mem (indexFun t i) c := by
        change (if Mem (indexFun t i) c then true else false) = true at hgi
        split at hgi
        · assumption
        · contradiction
      exact Equiv_Mem_trans hx_eq h_mem_c

theorem mem_powerset_iff {c t : DSet} : c ∈ powerset t ↔ c ⊆ t := by
  induction c using Quotient.ind
  induction t using Quotient.ind
  rename_i t_c t_t
  change Tree.Mem t_c (powersetTree t_t) ↔ Tree.Subset t_c t_t
  exact mem_powersetTree_iff

theorem subset_iff_forall_mem {c t : DSet} : c ⊆ t ↔ ∀ u, u ∈ c → u ∈ t := by
  induction c using Quotient.ind
  induction t using Quotient.ind
  rename_i t_c t_t
  change Tree.Subset t_c t_t ↔ ∀ u : DSet, u ∈ Quotient.mk Tree.Setoid t_c → u ∈ Quotient.mk Tree.Setoid t_t
  rw [Subset_iff_forall_Mem]
  constructor
  · intro h u hu
    induction u using Quotient.ind
    rename_i t_u
    exact h t_u hu
  · intro h u hu
    exact h (Quotient.mk Tree.Setoid u) hu

end

-- ══════════════════════════════════════════════════════════════════
-- § 8. Axioma de Reemplazo
-- ══════════════════════════════════════════════════════════════════

/-- Aplica una función a todas las ramas de un árbol (Esquema de Reemplazo) -/
def mapTree (t : Tree) (F : indexType t → Tree) : Tree :=
  .sup (indexCode t) F

axiom map_respects (a b : Tree) (h : Equiv a b) 
  (F : indexType a → Tree) (G : indexType b → Tree) 
  (hF : ∀ i j, Equiv (indexFun a i) (indexFun b j) → Equiv (F i) (G j)) : 
  Equiv (mapTree a F) (mapTree b G)

-- ══════════════════════════════════════════════════════════════════
-- § 9. Axioma de Separación
-- ══════════════════════════════════════════════════════════════════

/-- Separación Acotada: filtra un árbol dada una propiedad booleana decidible -/
def sepTree (t : Tree) (g : indexType t → Bool) : Tree :=
  filterTree t g

axiom sep_respects (a b : Tree) (h : Equiv a b) (g : indexType a → Bool) (g' : indexType b → Bool)
  (hg : ∀ i j, Equiv (indexFun a i) (indexFun b j) → g i = g' j) : Equiv (sepTree a g) (sepTree b g')

end DybjerSet
