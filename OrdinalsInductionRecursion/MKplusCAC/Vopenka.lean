import OrdinalsInductionRecursion.MKplusCAC.Functions

namespace MKplusCAC

open Classical

local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y
local infix:50 " ⊆ᴹ " => SubClass
local notation "⟪" x ", " y "⟫" => opair x y
local infix:70 " ∩ᴹ " => inter
local infix:65 " ∪ᴹ " => union
local notation "𝐕ᴹ" => univ
local notation "∅ᴹ" => empty
local postfix:max "⁻¹" => inv
local infixl:80 " ↾ᴹ " => restrict

/--
  Una estructura relacional sobre el universo de conjuntos de Morse-Kelley.
  Se representa como un par (domain, R) donde domain es un Set y R es una relación (Set).
-/
structure MKRelationalStructure where
  domain : Class
  h_domain : IsSet domain
  rel : Class
  h_rel : IsSet rel
  -- R es una relación sobre el dominio
  h_rel_sub : ∀ p : Class, p ∈ᴹ rel → ∃ x y : Class, x ∈ᴹ domain ∧ y ∈ᴹ domain ∧ p = ⟪x, y⟫

/--
  Inmersión Estructural entre A y B.
  Es una clase-función (que es un Set) f: dom(A) → dom(B) tal que
  x R_A y ↔ f(x) R_B f(y).
-/
def IsMKStructureEmbedding (A B : MKRelationalStructure) (f : Class) : Prop :=
  IsSet f ∧ 
  IsClassFun f ∧
  (dom f = A.domain) ∧
  (rng (f ↾ᴹ A.domain) ⊆ᴹ B.domain) ∧
  -- f es inyectiva
  (∀ x y z : Class, x ∈ᴹ A.domain → y ∈ᴹ A.domain → ⟪x, z⟫ ∈ᴹ f → ⟪y, z⟫ ∈ᴹ f → x = y) ∧
  -- preserva la relación
  (∀ x y fx fy : Class, x ∈ᴹ A.domain → y ∈ᴹ A.domain →
    ⟪x, fx⟫ ∈ᴹ f → ⟪y, fy⟫ ∈ᴹ f →
    (⟪x, y⟫ ∈ᴹ A.rel ↔ ⟪fx, fy⟫ ∈ᴹ B.rel))

/--
  Una Clase Propia de Estructuras.
  En MK, las clases propias son sencillamente Clases (objetos de primer orden)
  que no son conjuntos (`¬ IsSet C`).
-/
def IsProperClassOfStructures (C : Class) : Prop :=
  (¬ IsSet C) ∧
  -- Todos los elementos de C codifican una estructura relacional.
  -- Para simplificar axiomatización, asumimos que todos los elementos de C
  -- corresponden a un par (domain, rel).
  (∀ s : Class, s ∈ᴹ C → ∃ A : MKRelationalStructure, s = ⟪A.domain, A.rel⟫)

/--
  EL PRINCIPIO DE VOPĚNKA (en Morse-Kelley)
  Toda clase propia de estructuras relacionales admite una inmersión elemental
  entre dos de sus miembros.
-/
axiom MK_Vopenka :
  ∀ C : Class, IsProperClassOfStructures C →
    ∃ A B : MKRelationalStructure,
      ⟪A.domain, A.rel⟫ ∈ᴹ C ∧ 
      ⟪B.domain, B.rel⟫ ∈ᴹ C ∧ 
      -- Estructuras distintas
      ⟪A.domain, A.rel⟫ ≠ ⟪B.domain, B.rel⟫ ∧
      ∃ f : Class, IsMKStructureEmbedding A B f

end MKplusCAC
