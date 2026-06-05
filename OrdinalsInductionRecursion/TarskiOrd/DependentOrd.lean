import OrdinalsInductionRecursion.TarskiOrd.Univ

/-
  Módulo: DependentOrd
  Descripción: Definición de Pre-Ordinales de Tarski usando la familia inductiva indexada (UCodeFam).
  Esto dota al sistema de Reemplazo (Tipos Dependientes Nativos).
-/

namespace TarskiOrd

/--
  Pre-Ordinales Dependientes (DPreOrd)
  En lugar de usar `sup c f` donde `c : UCode` y `f : El c → TPreOrd`,
  ahora pasamos explícitamente el tipo de indexación `A : Type`, 
  y la demostración de que dicho tipo pertenece al universo sintáctico (`c : UCodeFam A`).
-/
inductive DPreOrd : Type 1
  | zero : DPreOrd
  | succ (x : DPreOrd) : DPreOrd
  | sup  {A : Type} (c : UCodeFam A) (f : A → DPreOrd) : DPreOrd

mutual
/-- Relación de subconjunto (≤) para los DPreOrd -/
inductive DSubset : DPreOrd → DPreOrd → Prop where
  | zero_subset (y : DPreOrd) : DSubset .zero y
  | succ_subset {x y : DPreOrd} : DMem x y → DSubset (.succ x) y
  | sup_subset  {A : Type} {c : UCodeFam A} {f : A → DPreOrd} {y : DPreOrd} : 
      (∀ a : A, DSubset (f a) y) → DSubset (.sup c f) y

/-- Relación de pertenencia (<) para los DPreOrd -/
inductive DMem : DPreOrd → DPreOrd → Prop where
  | mem_succ {x y : DPreOrd} : DSubset x y → DMem x (.succ y)
  | mem_sup  {A : Type} {c : UCodeFam A} {f : A → DPreOrd} {x : DPreOrd} (a : A) : 
      DMem x (f a) → DMem x (.sup c f)
end

end TarskiOrd
