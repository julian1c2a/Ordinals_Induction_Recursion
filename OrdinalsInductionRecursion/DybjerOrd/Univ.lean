/-
  Módulo: Univ
  Descripción: Definición del Universo Sintáctico usando el Truco de Peter Dybjer
  (Familias Inductivas Indexadas) para lograr Inducción-Recursión en Lean 4.
-/

import OrdinalsInductionRecursion.TarskiOrd.UCode

namespace DybjerOrd

/-- 
  UCodeFam : Type → Type 1
  Familia inductiva indexada que codifica tanto el código de construcción
  como su decodificación (el tipo que representa) en el propio índice.
  Esto nos permite tener tipos Pi y Sigma verdaderos sin violar la recursión estricta.
-/
inductive UCodeFam : Type → Type 1
  -- Tipos básicos
  | empty : UCodeFam PEmpty
  | unit : UCodeFam PUnit
  | bool : UCodeFam Bool
  | nat  : UCodeFam Nat
  | tarski : UCodeFam TarskiOrd.UCode

  -- Constructores de tipos (Cierre bajo operaciones)
  | sum   {A B : Type} (a : UCodeFam A) (b : UCodeFam B) : UCodeFam (A ⊕ B)
  | prod  {A B : Type} (a : UCodeFam A) (b : UCodeFam B) : UCodeFam (A × B)
  
  -- Tipos Dependientes (La magia del truco de Dybjer)
  | sigma {A : Type} {B : A → Type} (a : UCodeFam A) (b : (x : A) → UCodeFam (B x)) : UCodeFam (Σ x, B x)
  | pi    {A : Type} {B : A → Type} (a : UCodeFam A) (b : (x : A) → UCodeFam (B x)) : UCodeFam ((x : A) → B x)

/-- 
  Para conveniencia, empaquetamos el código junto con el tipo que decodifica.
  Esto es equivalente a nuestro antiguo `UCode`, pero ahora lleva su tipo `El` de forma nativa.
-/
def UCode : Type 1 := Σ A : Type, UCodeFam A

/-- Función extractora del tipo decodificado (antiguo `El`) -/
def El (c : UCode) : Type := c.1

end DybjerOrd
