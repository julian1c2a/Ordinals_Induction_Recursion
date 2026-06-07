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
