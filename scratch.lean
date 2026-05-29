import Peano

open Peano

inductive PreOrd : Type where
  | zero : PreOrd
  | succ : PreOrd → PreOrd
  | sup  : (ℕ₀ → PreOrd) → PreOrd

namespace PreOrd

mutual
  inductive Subset : PreOrd → PreOrd → Prop where
    | zero_subset (y : PreOrd) : Subset zero y
    | succ_subset {x y : PreOrd} : Mem x y → Subset (succ x) y
    | sup_subset {f : ℕ₀ → PreOrd} {y : PreOrd} : (∀ n, Subset (f n) y) → Subset (sup f) y

  inductive Mem : PreOrd → PreOrd → Prop where
    | mem_succ {x y : PreOrd} : Subset x y → Mem x (succ y)
    | mem_sup {x : PreOrd} {f : ℕ₀ → PreOrd} (n : ℕ₀) : Mem x (f n) → Mem x (sup f)
end

theorem Subset_sup {y z : PreOrd} (h : Subset y z) {f : ℕ₀ → PreOrd} (n : ℕ₀) (hz : z = f n) : Subset y (sup f) :=
  match y, z, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => .succ_subset (Mem.mem_sup n (hz ▸ hmem))
  | _, _, .sup_subset hsub => .sup_subset fun k => Subset_sup (hsub k) n hz

mutual
  theorem Subset_refl (x : PreOrd) : Subset x x :=
    match x with
    | .zero => .zero_subset _
    | .succ x' => .succ_subset (Mem_self_succ x')
    | .sup f => .sup_subset fun n => Subset_sup (Subset_refl (f n)) n rfl

  theorem Mem_self_succ (x : PreOrd) : Mem x (succ x) :=
    .mem_succ (Subset_refl x)
end

mutual
  theorem Subset_trans {x y z : PreOrd} (h1 : Subset x y) (h2 : Subset y z) : Subset x z :=
    match x, y, h1 with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem1 => .succ_subset (Mem_Subset_trans hmem1 h2)
    | _, _, .sup_subset hsub1 => .sup_subset fun n => Subset_trans (hsub1 n) h2

  theorem Mem_Subset_trans {x y z : PreOrd} (h1 : Mem x y) (h2 : Subset y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, .succ_subset hmem2 =>
      match x, y, h1 with
      | _, _, .mem_succ hsub1 => Subset_Mem_trans hsub1 hmem2
    | _, _, .sup_subset hsub2 =>
      match x, y, h1 with
      | _, _, .mem_sup n hmem1 => Mem_Subset_trans hmem1 (hsub2 n)

  theorem Subset_Mem_trans {x y z : PreOrd} (h1 : Subset x y) (h2 : Mem y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .mem_succ hsub2 => .mem_succ (Subset_trans h1 hsub2)
    | _, _, .mem_sup n hmem2 => .mem_sup n (Subset_Mem_trans h1 hmem2)
end

def add (x : PreOrd) : PreOrd → PreOrd
  | zero   => x
  | succ y => succ (add x y)
  | sup f  => sup (fun n => add x (f n))

axiom Subset_add {x₁ x₂ y₁ y₂ : PreOrd} (hx : Subset x₁ x₂) (hy : Subset y₁ y₂) : Subset (add x₁ y₁) (add x₂ y₂)

def mul (x : PreOrd) : PreOrd → PreOrd
  | zero   => zero
  | succ y => add (mul x y) x
  | sup f  => sup (fun n => mul x (f n))

theorem mul_mono_left_subset {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (mul x₁ y) (mul x₂ y) :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => Subset_add (mul_mono_left_subset h y') h
  | .sup f => .sup_subset fun n => mul_mono_left_subset h (f n)

mutual
  theorem mul_mono_right_subset (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (mul x y₁) (mul x y₂) :=
    match y₁, y₂, h with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem => mul_mono_right_mem x hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => mul_mono_right_subset x (hsub n)

  theorem mul_mono_right_mem (x : PreOrd) {a b : PreOrd} (h : Mem a b) : Subset (add (mul x a) x) (mul x b) :=
    match b, h with
    | _, .mem_succ hsub => Subset_add (mul_mono_right_subset x hsub) (Subset_refl x)
    | _, .mem_sup n hmem => Subset_sup (mul_mono_right_mem x hmem) n rfl
end

end PreOrd
