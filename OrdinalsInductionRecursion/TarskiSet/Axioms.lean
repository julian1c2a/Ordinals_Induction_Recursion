import OrdinalsInductionRecursion.TarskiSet.Tree

namespace TarskiSet

open Tree

-- ══════════════════════════════════════════════════════════════════
-- § 1. Conjunto Vacío
-- ══════════════════════════════════════════════════════════════════

def empty : TSet := Quotient.mk TarskiSet.Tree.Setoid .zero

theorem not_mem_empty (x : TSet) : ¬ (x ∈ empty) := by
  induction x using Quotient.ind
  rename_i a
  intro h
  have h' : TarskiSet.Tree.Mem a .zero := h
  cases h'

-- ══════════════════════════════════════════════════════════════════
-- § 2. Adjunción (Inserción de un elemento)
-- ══════════════════════════════════════════════════════════════════

open TarskiOrd

def insertTree (a b : Tree) : Tree :=
  match b with
  | .zero => .succ a
  | .succ c => .sup (.sum .unit .unit) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr _ => c
  | .sup c f => .sup (.sum .unit c) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr y => f y

axiom insert_respects (a a' b b' : Tree) (ha : Equiv a a') (hb : Equiv b b') : Equiv (insertTree a b) (insertTree a' b')

def insert (a b : TSet) : TSet :=
  Quotient.lift₂ (fun x y => (Quotient.mk Setoid (insertTree x y) : TSet))
    (fun _ _ _ _ hx hy => Quotient.sound (insert_respects _ _ _ _ hx hy)) a b

-- ══════════════════════════════════════════════════════════════════
-- § 3. Singleton y Par No Ordenado
-- ══════════════════════════════════════════════════════════════════

def singleton (a : TSet) : TSet := insert a empty

def pair (a b : TSet) : TSet := insert a (singleton b)

-- ══════════════════════════════════════════════════════════════════
-- § 4. Axioma del Infinito (Conjunto ω)
-- ══════════════════════════════════════════════════════════════════

/-- Árbol de Von Neumann para un número natural n -/
def natTree : Nat → Tree
  | 0 => .zero
  | n + 1 => insertTree (natTree n) (natTree n)

/-- El conjunto infinito omega (ω) que recopila todos los naturales -/
def omegaTree : Tree := .sup .nat (fun n => natTree n)

def omegaSet : TSet := Quotient.mk Setoid omegaTree

-- ══════════════════════════════════════════════════════════════════
-- § 5. La Barrera Estructural de TarskiSet (Unión y Potencia)
-- ══════════════════════════════════════════════════════════════════

/-
Nota Arquitectónica:
Hasta aquí llega el poder del Universo de Tarski para emular ZFC puro.

- **Axioma de la Unión (⋃ A):** Dado A = .sup c f, cada elemento f(a) es a su vez un árbol 
  indexado por un código c_a. Para agrupar todos los elementos de todos los f(a) en un solo árbol, 
  necesitamos un constructor de índice que agrupe c y todos los c_a.
  Ese constructor es la Suma Dependiente (`sigma`). Como `UCode` no tiene `sigma`, 
  la Unión NO puede definirse genéricamente.

- **Axioma del Conjunto Potencia (𝒫(A)):** Para extraer subconjuntos genéricos, necesitamos 
  funciones de decisión y filtrado sobre los subárboles. Sin tipos dependientes (`pi`/`sigma`), 
  no podemos derivar dinámicamente el tipo de ramas filtradas.

**Conclusión:** `TarskiSet` es insuficientemente expresivo para construir el conjunto de partes 
y la unión universal. Esta barrera matemática nos obliga a abandonar Tarski y trasplantar 
nuestra Teoría de Conjuntos hacia `DybjerSet`, donde el universo `UCodeFam` posee 
`sigma` y `pi`, abriendo la puerta a ZFC completo y los Grandes Cardinales.
-/

end TarskiSet
