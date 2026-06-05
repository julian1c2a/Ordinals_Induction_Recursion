import OrdinalsInductionRecursion.DybjerOrd.Univ

/-
  Módulo: DependentOrd
  Descripción: Definición de Pre-Ordinales de Tarski usando la familia inductiva indexada (UCodeFam).
  Esto dota al sistema de Reemplazo (Tipos Dependientes Nativos).
-/

namespace DybjerOrd

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

instance : Membership DPreOrd DPreOrd := ⟨DMem⟩
instance : HasSubset DPreOrd := ⟨DSubset⟩

/-- Igualdad extensional (equivalencia) de pre-ordinales -/
def Equiv (x y : DPreOrd) : Prop := DSubset x y ∧ DSubset y x

-- ==========================================
-- Lemas de Equivalencia (Setoid)
-- ==========================================

theorem DSubset_sup {y z : DPreOrd} {A : Type} {c : UCodeFam A} {f : A → DPreOrd}
  (h : DSubset y z) (a : A) (hz : z = f a) :
    DSubset y (.sup c f)
      :=
  match y, z, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => .succ_subset (DMem.mem_sup a (hz ▸ hmem))
  | _, _, .sup_subset hsub => .sup_subset fun k => DSubset_sup (hsub k) a hz

theorem DSubset_refl
  (x : DPreOrd) :
    DSubset x x
      :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => .succ_subset (.mem_succ (DSubset_refl x'))
  | .sup _c f => .sup_subset fun a => DSubset_sup (DSubset_refl (f a)) a rfl

theorem DMem_self_succ
  (x : DPreOrd) :
    DMem x (.succ x)
      :=
  .mem_succ (DSubset_refl x)

def trans_all
  (x : DPreOrd) :
    (∀ {y z}, DSubset x y → DSubset y z → DSubset x z) ∧
    (∀ {y z}, DMem x y → DSubset y z → DMem x z) ∧
    (∀ {y z}, DSubset x y → DMem y z → DMem x z)
      :=
  let sub_sub : ∀ {y z}, DSubset x y → DSubset y z → DSubset x z :=
    match x with
    | .zero => fun _ _ => .zero_subset _
    | .succ x' => fun h1 h2 =>
      match h1 with
      | @DSubset.succ_subset _ _ hmem1 => .succ_subset ((trans_all x').2.1 hmem1 h2)
    | .sup _c f => fun h1 h2 =>
      match h1 with
      | @DSubset.sup_subset _ _ _ _ hsub1 => .sup_subset fun a => (trans_all (f a)).1 (hsub1 a) h2

  let rec sub_mem {y z} (h1 : DSubset x y) (h2 : DMem y z) : DMem x z :=
    match y, z, h2 with
    | _, _, .mem_succ hsub2 => .mem_succ (sub_sub h1 hsub2)
    | _, _, .mem_sup a hmem2 => .mem_sup a (sub_mem h1 hmem2)

  let rec mem_sub {y z} (h1 : DMem x y) (h2 : DSubset y z) : DMem x z :=
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, @DSubset.succ_subset y' _ hmem2 =>
      match h1 with
      | @DMem.mem_succ _ _ hsub1 => sub_mem hsub1 hmem2
    | _, _, @DSubset.sup_subset _ _ _ _ hsub2 =>
      match h1 with
      | @DMem.mem_sup _ _ _ _ a hmem1 => mem_sub hmem1 (hsub2 a)

  ⟨sub_sub, mem_sub, sub_mem⟩

theorem DSubset_trans {x y z : DPreOrd} (h1 : DSubset x y) (h2 : DSubset y z) : DSubset x z :=
  (trans_all x).1 h1 h2

theorem DMem_DSubset_trans {x y z : DPreOrd} (h1 : DMem x y) (h2 : DSubset y z) : DMem x z :=
  (trans_all x).2.1 h1 h2

theorem DSubset_DMem_trans {x y z : DPreOrd} (h1 : DSubset x y) (h2 : DMem y z) : DMem x z :=
  (trans_all x).2.2 h1 h2

def trans_y (y : DPreOrd) :
  (DSubset y (.succ y)) ∧
  (∀ {x}, DMem x y → DSubset x y) :=
  match y with
  | .zero =>
    ⟨DSubset.zero_subset _, fun h => nomatch h⟩
  | .succ a =>
    let ih := trans_y a
    let self_succ := DSubset.succ_subset (DMem.mem_succ ih.1)
    let rec sub_succ_a {x} (h : DSubset x a) : DSubset x (.succ a) :=
      match x, h with
      | _, DSubset.zero_subset _ => DSubset.zero_subset _
      | _, @DSubset.succ_subset z _ hmem =>
        DSubset.succ_subset (DMem.mem_succ (ih.2 hmem))
      | _, @DSubset.sup_subset _ _ _ _ hsub =>
        DSubset.sup_subset fun j => sub_succ_a (hsub j)
    let mem_sub := fun {x} (h : DMem x (.succ a)) =>
      match x, h with
      | _, DMem.mem_succ hsub => sub_succ_a hsub
    ⟨self_succ, mem_sub⟩
  | .sup c f =>
    let ih := fun i => trans_y (f i)
    let mem_sub := fun {x} (h : DMem x (.sup c f)) =>
      match x, h with
      | _, DMem.mem_sup i hmem => DSubset_sup ((ih i).2 hmem) i rfl
    let rec sub_succ_sup {x} (h : DSubset x (.sup c f)) : DSubset x (.succ (.sup c f)) :=
      match x, h with
      | _, DSubset.zero_subset _ => DSubset.zero_subset _
      | _, @DSubset.succ_subset z _ hmem =>
        DSubset.succ_subset (DMem.mem_succ (mem_sub hmem))
      | _, @DSubset.sup_subset _ _ _ _ hsub =>
        DSubset.sup_subset fun j => sub_succ_sup (hsub j)
    let self_succ := DSubset.sup_subset fun i => sub_succ_sup (DSubset_sup (DSubset_refl _) i rfl)
    ⟨self_succ, mem_sub⟩

theorem Dmem_implies_subset {x y : DPreOrd} (h : DMem x y) : DSubset x y :=
  (trans_y y).2 h

theorem Equiv_refl (x : DPreOrd) : Equiv x x :=
  ⟨DSubset_refl x, DSubset_refl x⟩

theorem Equiv_symm {x y : DPreOrd} (h : Equiv x y) : Equiv y x :=
  ⟨h.right, h.left⟩

theorem Equiv_trans {x y z : DPreOrd} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  ⟨DSubset_trans h1.left h2.left, DSubset_trans h2.right h1.right⟩

instance Setoid : Setoid DPreOrd where
  r := Equiv
  iseqv := {
    refl := Equiv_refl
    symm := Equiv_symm
    trans := Equiv_trans
  }

end DybjerOrd
