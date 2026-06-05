import OrdinalsInductionRecursion.TarskiOrd.Ordinals

namespace TarskiOrd

open TPreOrd

/-- Suma constructiva de pre-ordinales de Tarski. -/
def add (x y : TPreOrd) : TPreOrd :=
  match y with
  | .zero => x
  | .succ y' => succ (add x y')
  | .sup c f => sup c (fun a => add x (f a))

def c_inhabited (c : UCode) : El c :=
  match c with
  | .unit => ()
  | .nat => (0 : Nat)
  | .sum a _b => Sum.inl (c_inhabited a)
  | .arrow _a b => fun _ => c_inhabited b
  | .univ _n => .unit

theorem x_Subset_add (x y : TPreOrd) : TPreOrd.Subset x (add x y) :=
  match y with
  | .zero => Subset_refl x
  | .succ y' => mem_implies_subset (TPreOrd.Mem.mem_succ (x_Subset_add x y'))
  | .sup c f => Subset_sup (x_Subset_add x (f (c_inhabited c))) (c_inhabited c) rfl

mutual
  theorem add_Subset_right (x : TPreOrd) {y₁ y₂ : TPreOrd} (h : TPreOrd.Subset y₁ y₂) : TPreOrd.Subset (add x y₁) (add x y₂) :=
    match y₁, y₂, h with
    | _, _, TPreOrd.Subset.zero_subset _ => x_Subset_add x _
    | _, _, TPreOrd.Subset.succ_subset hmem => TPreOrd.Subset.succ_subset (add_Mem_right x hmem)
    | _, _, TPreOrd.Subset.sup_subset hsub => TPreOrd.Subset.sup_subset fun a => add_Subset_right x (hsub a)

  theorem add_Mem_right (x : TPreOrd) {y₁ y₂ : TPreOrd} (h : TPreOrd.Mem y₁ y₂) : TPreOrd.Mem (add x y₁) (add x y₂) :=
    match y₁, y₂, h with
    | _, _, TPreOrd.Mem.mem_succ hsub => TPreOrd.Mem.mem_succ (add_Subset_right x hsub)
    | _, _, TPreOrd.Mem.mem_sup a hmem => TPreOrd.Mem.mem_sup a (add_Mem_right x hmem)
end

mutual
  theorem add_Subset_left {x₁ x₂ : TPreOrd} (y : TPreOrd) (h : TPreOrd.Subset x₁ x₂) : TPreOrd.Subset (add x₁ y) (add x₂ y) :=
    match y with
    | .zero => h
    | .succ y' => TPreOrd.Subset.succ_subset (TPreOrd.Mem.mem_succ (add_Subset_left y' h))
    | .sup c f => TPreOrd.Subset.sup_subset fun a => Subset_sup (add_Subset_left (f a) h) a rfl
end

theorem add_respects_Equiv {x₁ x₂ y₁ y₂ : TPreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (add x₁ y₁) (add x₂ y₂) :=
  ⟨Subset_trans (add_Subset_left y₁ hx.left) (add_Subset_right x₂ hy.left),
   Subset_trans (add_Subset_left y₂ hx.right) (add_Subset_right x₁ hy.right)⟩

/-- Multiplicación constructiva de pre-ordinales de Tarski. -/
def mul (x y : TPreOrd) : TPreOrd :=
  match y with
  | .zero => zero
  | .succ y' => add (mul x y') x
  | .sup c f => sup c (fun a => mul x (f a))

mutual
  theorem mul_Subset_right (x : TPreOrd) {y₁ y₂ : TPreOrd} (h : TPreOrd.Subset y₁ y₂) : TPreOrd.Subset (mul x y₁) (mul x y₂) :=
    match y₁, y₂, h with
    | _, _, TPreOrd.Subset.zero_subset _ => TPreOrd.Subset.zero_subset _
    | _, _, TPreOrd.Subset.succ_subset hmem => mul_Mem_Subset_right x hmem
    | _, _, TPreOrd.Subset.sup_subset hsub => TPreOrd.Subset.sup_subset fun a => mul_Subset_right x (hsub a)

  theorem mul_Mem_Subset_right (x : TPreOrd) {y₁ y₂ : TPreOrd} (h : TPreOrd.Mem y₁ y₂) : TPreOrd.Subset (add (mul x y₁) x) (mul x y₂) :=
    match y₁, y₂, h with
    | _, _, TPreOrd.Mem.mem_succ hsub => add_Subset_left x (mul_Subset_right x hsub)
    | _, _, TPreOrd.Mem.mem_sup a hmem => Subset_sup (mul_Mem_Subset_right x hmem) a rfl
end

mutual
  theorem mul_Subset_left {x₁ x₂ : TPreOrd} (y : TPreOrd) (h : TPreOrd.Subset x₁ x₂) : TPreOrd.Subset (mul x₁ y) (mul x₂ y) :=
    match y with
    | .zero => TPreOrd.Subset.zero_subset _
    | .succ y' => 
        -- mul x₁ (succ y') = add (mul x₁ y') x₁
        -- mul x₂ (succ y') = add (mul x₂ y') x₂
        -- We need add (mul x₁ y') x₁ <= add (mul x₂ y') x₂
        -- By IH, mul x₁ y' <= mul x₂ y'.
        -- We know add a b <= add c d if a <= c and b <= d.
        -- We can compose add_Subset_left and add_Subset_right!
        Subset_trans (add_Subset_left x₁ (mul_Subset_left y' h)) (add_Subset_right (mul x₂ y') h)
    | .sup c f => TPreOrd.Subset.sup_subset fun a => Subset_sup (mul_Subset_left (f a) h) a rfl
end

theorem mul_respects_Equiv {x₁ x₂ y₁ y₂ : TPreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (mul x₁ y₁) (mul x₂ y₂) :=
  ⟨Subset_trans (mul_Subset_left y₁ hx.left) (mul_Subset_right x₂ hy.left),
   Subset_trans (mul_Subset_left y₂ hx.right) (mul_Subset_right x₁ hy.right)⟩

/-- Exponenciación constructiva de pre-ordinales de Tarski. -/
def exp (x y : TPreOrd) : TPreOrd :=
  match y with
  | .zero => succ zero
  | .succ y' => mul (exp x y') x
  | .sup c f => sup c (fun a => exp x (f a))

theorem y_Subset_add_left (x y : TPreOrd) : TPreOrd.Subset y (add x y) :=
  match y with
  | .zero => TPreOrd.Subset.zero_subset _
  | .succ y' => TPreOrd.Subset.succ_subset (TPreOrd.Mem.mem_succ (y_Subset_add_left x y'))
  | .sup c f => TPreOrd.Subset.sup_subset fun a => Subset_sup (y_Subset_add_left x (f a)) a rfl

theorem z_Subset_mul (z x : TPreOrd) (hx : Mem zero x) : TPreOrd.Subset z (mul z x) :=
  match x, hx with
  | _, Mem.mem_succ _hsub => y_Subset_add_left (mul z _) z
  | _, Mem.mem_sup a hmem => Subset_sup (z_Subset_mul z _ hmem) a rfl

theorem one_Subset_exp (x y : TPreOrd) (hx : Mem zero x) : TPreOrd.Subset (succ zero) (exp x y) :=
  match y with
  | .zero => Subset_refl _
  | .succ y' => 
      Subset_trans (one_Subset_exp x y' hx) (z_Subset_mul _ x hx)
  | .sup c f => Subset_sup (one_Subset_exp x (f (c_inhabited c)) hx) (c_inhabited c) rfl

mutual
  theorem exp_Subset_right (x : TPreOrd) (hx : Mem zero x) {y₁ y₂ : TPreOrd} (h : TPreOrd.Subset y₁ y₂) : TPreOrd.Subset (exp x y₁) (exp x y₂) :=
    match y₁, y₂, h with
    | _, _, TPreOrd.Subset.zero_subset _ => one_Subset_exp x _ hx
    | _, _, TPreOrd.Subset.succ_subset hmem => exp_Mem_Subset_right x hx hmem
    | _, _, TPreOrd.Subset.sup_subset hsub => TPreOrd.Subset.sup_subset fun a => exp_Subset_right x hx (hsub a)

  theorem exp_Mem_Subset_right (x : TPreOrd) (hx : Mem zero x) {y₁ y₂ : TPreOrd} (h : Mem y₁ y₂) : TPreOrd.Subset (mul (exp x y₁) x) (exp x y₂) :=
    match y₁, y₂, h with
    | _, _, Mem.mem_succ hsub => mul_Subset_left x (exp_Subset_right x hx hsub)
    | _, _, Mem.mem_sup a hmem => Subset_sup (exp_Mem_Subset_right x hx hmem) a rfl
end

mutual
  theorem exp_Subset_left (y : TPreOrd) {x₁ x₂ : TPreOrd} (h : TPreOrd.Subset x₁ x₂) : TPreOrd.Subset (exp x₁ y) (exp x₂ y) :=
    match y with
    | .zero => Subset_refl _
    | .succ y' => 
        Subset_trans (mul_Subset_left x₁ (exp_Subset_left y' h)) (mul_Subset_right (exp x₂ y') h)
    | .sup c f => TPreOrd.Subset.sup_subset fun a => Subset_sup (exp_Subset_left (f a) h) a rfl
end

theorem exp_respects_Equiv {x₁ x₂ y₁ y₂ : TPreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) (hx_pos : Mem zero x₁) : Equiv (exp x₁ y₁) (exp x₂ y₂) :=
  -- wait, hx_pos is only for the first base. But since x₁ ≈ x₂, we could deduce Mem zero x₂, but we don't need it.
  -- exp_Subset_left handles left side unconditionally!
  -- exp_Subset_right requires Mem zero x for the base.
  ⟨Subset_trans (exp_Subset_left y₁ hx.left) (exp_Subset_right x₂ (Mem_Subset_trans hx_pos hx.left) hy.left),
   Subset_trans (exp_Subset_left y₂ hx.right) (exp_Subset_right x₁ hx_pos hy.right)⟩

instance : Add TPreOrd := ⟨add⟩
instance : Mul TPreOrd := ⟨mul⟩

def addOrd : TOrdinal → TOrdinal → TOrdinal :=
  Quotient.lift₂ (fun x y => (Quotient.mk TPreOrd.Setoid (add x y) : TOrdinal))
    (fun _ _ _ _ hx hy => Quotient.sound (add_respects_Equiv hx hy))

def mulOrd : TOrdinal → TOrdinal → TOrdinal :=
  Quotient.lift₂ (fun x y => (Quotient.mk TPreOrd.Setoid (mul x y) : TOrdinal))
    (fun _ _ _ _ hx hy => Quotient.sound (mul_respects_Equiv hx hy))

open Classical

noncomputable def expOrd (x y : TOrdinal) : TOrdinal :=
  if x = (Quotient.mk TPreOrd.Setoid zero : TOrdinal) then
    if y = (Quotient.mk TPreOrd.Setoid zero : TOrdinal) then 
      (Quotient.mk TPreOrd.Setoid (succ zero) : TOrdinal) 
    else 
      (Quotient.mk TPreOrd.Setoid zero : TOrdinal)
  else
    Quotient.liftOn₂ x y
      (fun a b => if ha : Mem zero a then (Quotient.mk TPreOrd.Setoid (exp a b) : TOrdinal) else (Quotient.mk TPreOrd.Setoid zero : TOrdinal))
      (fun a₁ b₁ a₂ b₂ eq_a eq_b => by
        have heq : Mem zero a₁ ↔ Mem zero a₂ := TOrdinal.Mem_respects_Equiv (Equiv_refl zero) eq_a
        by_cases h1 : Mem zero a₁
        · have h2 : Mem zero a₂ := heq.mp h1
          simp only [h1, h2, dite_true]
          exact Quotient.sound (exp_respects_Equiv eq_a eq_b h1)
        · have h2 : ¬ Mem zero a₂ := fun h => h1 (heq.mpr h)
          simp only [h1, h2, dite_false]
      )

instance : Add TOrdinal := ⟨addOrd⟩
instance : Mul TOrdinal := ⟨mulOrd⟩
noncomputable instance : Pow TOrdinal TOrdinal := ⟨expOrd⟩

end TarskiOrd
