universe u

inductive PreOrd : Type (u+1) where
  | zero : PreOrd
  | succ : PreOrd → PreOrd
  | sup  : {α : Type u} → (α → PreOrd) → PreOrd

namespace PreOrd

mutual
  inductive Subset : PreOrd.{u} → PreOrd.{u} → Prop where
    | zero_subset (y : PreOrd) : Subset .zero y
    | succ_subset {x y : PreOrd} : Mem x y → Subset (.succ x) y
    | sup_subset {α : Type u} {f : α → PreOrd} {y : PreOrd} : (∀ a, Subset (f a) y) → Subset (.sup f) y

  inductive Mem : PreOrd.{u} → PreOrd.{u} → Prop where
    | mem_succ {x y : PreOrd} : Subset x y → Mem x (.succ y)
    | mem_sup {α : Type u} {f : α → PreOrd} {x : PreOrd} (a : α) : Mem x (f a) → Mem x (.sup f)
end

def union (a b : PreOrd.{u}) : PreOrd.{u} :=
  .sup (α := ULift.{u, 0} Bool) (fun x => match x.down with
    | true => a
    | false => b)

def add (a b : PreOrd.{u}) : PreOrd.{u} :=
  match b with
  | .zero => a
  | .succ b' => .succ (add a b')
def union (a b : PreOrd.{u}) : PreOrd.{u} :=
  .sup (α := ULift.{u, 0} Bool) (fun x => match x.down with
    | true => a
    | false => b)

theorem subset_union_left (x y : PreOrd.{u}) : Subset x (union x y) :=
  Subset_sup (Subset_refl x) ⟨true⟩ rfl

theorem subset_union_right (x y : PreOrd.{u}) : Subset y (union x y) :=
  Subset_sup (Subset_refl y) ⟨false⟩ rfl

theorem union_subset {x y z : PreOrd.{u}} (hx : Subset x z) (hy : Subset y z) : Subset (union x y) z :=
  Subset.sup_subset fun a => match a.down with
    | true => hx
    | false => hy

def add (a b : PreOrd.{u}) : PreOrd.{u} :=
  match b with
  | .zero => a
  | .succ b' => .succ (add a b')
  | .sup f => union a (.sup (fun k => add a (f k)))

theorem add_mono_left {a1 a2 : PreOrd.{u}} (h : Subset a1 a2) (b : PreOrd.{u}) : Subset (add a1 b) (add a2 b) := by
  induction b with
  | zero => exact h
  | succ b' ih => exact Subset.succ_subset (Mem.mem_succ ih)
  | sup f ih =>
    exact union_subset
      (Subset_trans h (subset_union_left _ _))
      (Subset_trans (Subset.sup_subset fun n => Subset_sup (ih n) n rfl) (subset_union_right _ _))

theorem le_add_right (a b : PreOrd.{u}) : Subset a (add a b) := by
  induction b with
  | zero => exact Subset_refl a
  | succ b' ih => exact mem_subset (Subset_Mem_trans ih (Mem_self_succ _))
  | sup f ih => exact subset_union_left _ _

mutual
  def add_mono_right_sub (a : PreOrd.{u}) {b1 b2 : PreOrd.{u}} (h : Subset b1 b2) : Subset (add a b1) (add a b2) :=
    match b1, b2, h with
    | _, b, .zero_subset _ => le_add_right a b
    | _, _, .succ_subset hmem => .succ_subset (add_mono_right_mem a hmem)
    | _, b, .sup_subset hsub => union_subset (le_add_right a b) (Subset.sup_subset fun n => add_mono_right_sub a (hsub n))

  def add_mono_right_mem (a : PreOrd.{u}) {b1 b2 : PreOrd.{u}} (h : Mem b1 b2) : Mem (add a b1) (add a b2) :=
    match b1, b2, h with
    | _, _, .mem_succ hsub => .mem_succ (add_mono_right_sub a hsub)
    | _, _, .mem_sup n hmem => .mem_sup ⟨false⟩ (.mem_sup n (add_mono_right_mem a hmem))
end

end PreOrd
