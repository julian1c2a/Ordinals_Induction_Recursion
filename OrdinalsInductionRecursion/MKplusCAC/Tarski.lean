import OrdinalsInductionRecursion.MKplusCAC.MKplusCACAxioms

namespace MKplusCAC

open Classical

local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y

/--
  Un Universo de Grothendieck es una clase U que es transitiva y cerrada bajo
  operaciones conjuntistas (pares, potencias, uniones y reemplazo).
  Como estamos en MK, representamos U como una Clase.
-/
def IsTransitive (U : Class) : Prop :=
  ∀ x : Class, x ∈ᴹ U → ∀ y : Class, y ∈ᴹ x → y ∈ᴹ U

def IsGrothendieckUniverse (U : Class) : Prop :=
  IsSet U ∧
  IsTransitive U ∧
  -- Contiene a los pares
  (∀ x y : Class, x ∈ᴹ U → y ∈ᴹ U → ∃ p : Class, IsSet p ∧ p ∈ᴹ U ∧ ∀ u : Class, u ∈ᴹ p ↔ (u = x ∨ u = y)) ∧
  -- Cerrado bajo Unión
  (∀ x : Class, x ∈ᴹ U → ∃ s : Class, IsSet s ∧ s ∈ᴹ U ∧ ∀ u : Class, u ∈ᴹ s ↔ ∃ v : Class, u ∈ᴹ v ∧ v ∈ᴹ x) ∧
  -- Cerrado bajo Partes
  (∀ x : Class, x ∈ᴹ U → ∃ p : Class, IsSet p ∧ p ∈ᴹ U ∧ ∀ u : Class, u ∈ᴹ p ↔ IsSet u ∧ ∀ v : Class, v ∈ᴹ u → v ∈ᴹ x) ∧
  -- Contiene el conjunto infinito (el garantizado por MK_Inf)
  (∃ w : Class, w ∈ᴹ U ∧ 
    (∃ e : Class, IsSet e ∧ (∀ u : Class, u ∉ᴹ e) ∧ e ∈ᴹ w) ∧
    (∀ y : Class, y ∈ᴹ w → ∃ s : Class, IsSet s ∧ s ∈ᴹ w ∧ ∀ u : Class, u ∈ᴹ s ↔ u ∈ᴹ y ∨ u = y))

/--
  AXIOMA DE TARSKI:
  Todo conjunto está contenido en un Universo de Grothendieck.
  Este axioma añade la fuerza equivalente a tener una clase propia de cardinales
  fuertemente inaccesibles.
-/
axiom MK_Tarski :
  ∀ x : Class, IsSet x →
    ∃ U : Class, IsGrothendieckUniverse U ∧ x ∈ᴹ U

end MKplusCAC
