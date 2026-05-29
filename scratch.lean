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

def add (x : PreOrd) : PreOrd → PreOrd
  | zero   => x
  | succ y => succ (add x y)
  | sup f  => sup (fun n => add x (f n))

def mul (x : PreOrd) : PreOrd → PreOrd
  | zero   => zero
  | succ y => add (mul x y) x
  | sup f  => sup (fun n => mul x (f n))

def pow (x : PreOrd) : PreOrd → PreOrd
  | zero   => succ zero
  | succ y => mul (pow x y) x
  | sup f  => sup (fun n => pow x (f n))

-- The counterexample:
-- Subset zero (succ zero) is true.
-- If pow were monotonic on the right:
-- pow zero zero = succ zero
-- pow zero (succ zero) = mul (succ zero) zero = zero
-- Monotonicity would imply: Subset (succ zero) zero.
-- But Subset (succ zero) zero is FALSE!

theorem counterexample (h : Subset (pow zero zero) (pow zero (succ zero))) : False := by
  -- pow zero zero = succ zero
  -- pow zero (succ zero) = zero
  -- h : Subset (succ zero) zero
  -- The only way to prove Subset (succ x) y is `succ_subset`, which requires `y` to be matched.
  -- But y is `zero`. `succ_subset` matches `Subset (succ x) y`. But wait.
  -- The constructor `zero_subset` is for `Subset zero y`.
  -- The constructor `succ_subset` is for `Subset (succ x) y`.
  -- But in `succ_subset`, `y` can be anything!
  -- Wait, `succ_subset {x y} : Mem x y → Subset (succ x) y`.
  -- So we need `Mem zero zero`.
  -- The constructors for `Mem` are `mem_succ` and `mem_sup`. Neither matches `zero`.
  -- So `Mem zero zero` is uninhabited. Thus `Subset (succ zero) zero` is uninhabited.
  sorry

end PreOrd
