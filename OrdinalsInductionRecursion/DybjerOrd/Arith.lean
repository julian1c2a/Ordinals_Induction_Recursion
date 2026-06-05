import OrdinalsInductionRecursion.DybjerOrd.Ordinals

namespace DybjerOrd

open DPreOrd

def c_inhabited {A : Type} (c : UCodeFam A) : A :=
  match c with
  | .unit => PUnit.unit
  | .bool => false
  | .nat => 0
  | .sum a _ => Sum.inl (c_inhabited a)
  | .prod a b => (c_inhabited a, c_inhabited b)
  | .sigma a b => 
      let xa := c_inhabited a
      ⟨xa, c_inhabited (b xa)⟩
  | .pi _a b => fun x => c_inhabited (b x)

/-- Suma constructiva de pre-ordinales de Dybjer. -/
def add (x y : DPreOrd) : DPreOrd :=
  match y with
  | .zero => x
  | .succ y' => .succ (add x y')
  | .sup c f => .sup c (fun a => add x (f a))

theorem x_Subset_add (x y : DPreOrd) : DSubset x (add x y) :=
  match y with
  | .zero => DSubset_refl x
  | .succ y' => Dmem_implies_subset (DMem.mem_succ (x_Subset_add x y'))
  | .sup c f => DSubset_sup (x_Subset_add x (f (c_inhabited c))) (c_inhabited c) rfl

mutual
  theorem add_Subset_right (x : DPreOrd) {y₁ y₂ : DPreOrd} (h : DSubset y₁ y₂) : DSubset (add x y₁) (add x y₂) :=
    match y₁, y₂, h with
    | _, _, DSubset.zero_subset _ => x_Subset_add x _
    | _, _, DSubset.succ_subset hmem => DSubset.succ_subset (add_Mem_right x hmem)
    | _, _, @DSubset.sup_subset _ _ _ _ hsub => DSubset.sup_subset fun a => add_Subset_right x (hsub a)

  theorem add_Mem_right (x : DPreOrd) {y₁ y₂ : DPreOrd} (h : DMem y₁ y₂) : DMem (add x y₁) (add x y₂) :=
    match y₁, y₂, h with
    | _, _, DMem.mem_succ hsub => DMem.mem_succ (add_Subset_right x hsub)
    | _, _, @DMem.mem_sup _ _ _ _ a hmem => DMem.mem_sup a (add_Mem_right x hmem)
end

mutual
  theorem add_Subset_left {x₁ x₂ : DPreOrd} (y : DPreOrd) (h : DSubset x₁ x₂) : DSubset (add x₁ y) (add x₂ y) :=
    match y with
    | .zero => h
    | .succ y' => DSubset.succ_subset (DMem.mem_succ (add_Subset_left y' h))
    | .sup _c f => DSubset.sup_subset fun a => DSubset_sup (add_Subset_left (f a) h) a rfl
end

theorem add_respects_Equiv {x₁ x₂ y₁ y₂ : DPreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (add x₁ y₁) (add x₂ y₂) :=
  ⟨DSubset_trans (add_Subset_left y₁ hx.left) (add_Subset_right x₂ hy.left),
   DSubset_trans (add_Subset_left y₂ hx.right) (add_Subset_right x₁ hy.right)⟩

/-- Multiplicación constructiva de pre-ordinales de Dybjer. -/
def mul (x y : DPreOrd) : DPreOrd :=
  match y with
  | .zero => .zero
  | .succ y' => add (mul x y') x
  | .sup c f => .sup c (fun a => mul x (f a))

mutual
  theorem mul_Subset_right (x : DPreOrd) {y₁ y₂ : DPreOrd} (h : DSubset y₁ y₂) : DSubset (mul x y₁) (mul x y₂) :=
    match y₁, y₂, h with
    | _, _, DSubset.zero_subset _ => DSubset.zero_subset _
    | _, _, DSubset.succ_subset hmem => mul_Mem_Subset_right x hmem
    | _, _, @DSubset.sup_subset _ _ _ _ hsub => DSubset.sup_subset fun a => mul_Subset_right x (hsub a)

  theorem mul_Mem_Subset_right (x : DPreOrd) {y₁ y₂ : DPreOrd} (h : DMem y₁ y₂) : DSubset (add (mul x y₁) x) (mul x y₂) :=
    match y₁, y₂, h with
    | _, _, DMem.mem_succ hsub => add_Subset_left x (mul_Subset_right x hsub)
    | _, _, @DMem.mem_sup _ _ _ _ a hmem => DSubset_sup (mul_Mem_Subset_right x hmem) a rfl
end

mutual
  theorem mul_Subset_left {x₁ x₂ : DPreOrd} (y : DPreOrd) (h : DSubset x₁ x₂) : DSubset (mul x₁ y) (mul x₂ y) :=
    match y with
    | .zero => DSubset.zero_subset _
    | .succ y' => 
        DSubset_trans (add_Subset_left x₁ (mul_Subset_left y' h)) (add_Subset_right (mul x₂ y') h)
    | .sup _c f => DSubset.sup_subset fun a => DSubset_sup (mul_Subset_left (f a) h) a rfl
end

theorem mul_respects_Equiv {x₁ x₂ y₁ y₂ : DPreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (mul x₁ y₁) (mul x₂ y₂) :=
  ⟨DSubset_trans (mul_Subset_left y₁ hx.left) (mul_Subset_right x₂ hy.left),
   DSubset_trans (mul_Subset_left y₂ hx.right) (mul_Subset_right x₁ hy.right)⟩

/-- Exponenciación constructiva de pre-ordinales de Dybjer. -/
def exp (x y : DPreOrd) : DPreOrd :=
  match y with
  | .zero => .succ .zero
  | .succ y' => mul (exp x y') x
  | .sup c f => .sup c (fun a => exp x (f a))

theorem y_Subset_add_left (x y : DPreOrd) : DSubset y (add x y) :=
  match y with
  | .zero => DSubset.zero_subset _
  | .succ y' => DSubset.succ_subset (DMem.mem_succ (y_Subset_add_left x y'))
  | .sup _c f => DSubset.sup_subset fun a => DSubset_sup (y_Subset_add_left x (f a)) a rfl

theorem z_Subset_mul (z x : DPreOrd) (hx : DMem .zero x) : DSubset z (mul z x) :=
  match x, hx with
  | _, DMem.mem_succ _hsub => y_Subset_add_left (mul z _) z
  | _, @DMem.mem_sup _ _ _ _ a hmem => DSubset_sup (z_Subset_mul z _ hmem) a rfl

theorem one_Subset_exp (x y : DPreOrd) (hx : DMem .zero x) : DSubset (.succ .zero) (exp x y) :=
  match y with
  | .zero => DSubset_refl _
  | .succ y' => 
      DSubset_trans (one_Subset_exp x y' hx) (z_Subset_mul _ x hx)
  | .sup c f => DSubset_sup (one_Subset_exp x (f (c_inhabited c)) hx) (c_inhabited c) rfl

mutual
  theorem exp_Subset_right (x : DPreOrd) (hx : DMem .zero x) {y₁ y₂ : DPreOrd} (h : DSubset y₁ y₂) : DSubset (exp x y₁) (exp x y₂) :=
    match y₁, y₂, h with
    | _, _, DSubset.zero_subset _ => one_Subset_exp x _ hx
    | _, _, DSubset.succ_subset hmem => exp_Mem_Subset_right x hx hmem
    | _, _, @DSubset.sup_subset _ _ _ _ hsub => DSubset.sup_subset fun a => exp_Subset_right x hx (hsub a)

  theorem exp_Mem_Subset_right (x : DPreOrd) (hx : DMem .zero x) {y₁ y₂ : DPreOrd} (h : DMem y₁ y₂) : DSubset (mul (exp x y₁) x) (exp x y₂) :=
    match y₁, y₂, h with
    | _, _, DMem.mem_succ hsub => mul_Subset_left x (exp_Subset_right x hx hsub)
    | _, _, @DMem.mem_sup _ _ _ _ a hmem => DSubset_sup (exp_Mem_Subset_right x hx hmem) a rfl
end

mutual
  theorem exp_Subset_left (y : DPreOrd) {x₁ x₂ : DPreOrd} (h : DSubset x₁ x₂) : DSubset (exp x₁ y) (exp x₂ y) :=
    match y with
    | .zero => DSubset_refl _
    | .succ y' => 
        DSubset_trans (mul_Subset_left x₁ (exp_Subset_left y' h)) (mul_Subset_right (exp x₂ y') h)
    | .sup _c f => DSubset.sup_subset fun a => DSubset_sup (exp_Subset_left (f a) h) a rfl
end

theorem exp_respects_Equiv {x₁ x₂ y₁ y₂ : DPreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) (hx_pos : DMem .zero x₁) : Equiv (exp x₁ y₁) (exp x₂ y₂) :=
  ⟨DSubset_trans (exp_Subset_left y₁ hx.left) (exp_Subset_right x₂ (DMem_DSubset_trans hx_pos hx.left) hy.left),
   DSubset_trans (exp_Subset_left y₂ hx.right) (exp_Subset_right x₁ hx_pos hy.right)⟩

instance : Add DPreOrd := ⟨add⟩
instance : Mul DPreOrd := ⟨mul⟩

def addOrd : DOrdinal → DOrdinal → DOrdinal :=
  Quotient.lift₂ (fun x y => (Quotient.mk Setoid (add x y) : DOrdinal))
    (fun _ _ _ _ hx hy => Quotient.sound (add_respects_Equiv hx hy))

def mulOrd : DOrdinal → DOrdinal → DOrdinal :=
  Quotient.lift₂ (fun x y => (Quotient.mk Setoid (mul x y) : DOrdinal))
    (fun _ _ _ _ hx hy => Quotient.sound (mul_respects_Equiv hx hy))

open Classical

noncomputable def expOrd (x y : DOrdinal) : DOrdinal :=
  if x = (Quotient.mk Setoid .zero : DOrdinal) then
    if y = (Quotient.mk Setoid .zero : DOrdinal) then 
      (Quotient.mk Setoid (.succ .zero) : DOrdinal) 
    else 
      (Quotient.mk Setoid .zero : DOrdinal)
  else
    Quotient.liftOn₂ x y
      (fun a b => if ha : DMem .zero a then (Quotient.mk Setoid (exp a b) : DOrdinal) else (Quotient.mk Setoid .zero : DOrdinal))
      (fun a₁ b₁ a₂ b₂ eq_a eq_b => by
        have heq : DMem .zero a₁ ↔ DMem .zero a₂ := DOrdinal.Mem_respects_Equiv (Equiv_refl .zero) eq_a
        by_cases h1 : DMem .zero a₁
        · have h2 : DMem .zero a₂ := heq.mp h1
          simp only [h1, h2, dite_true]
          exact Quotient.sound (exp_respects_Equiv eq_a eq_b h1)
        · have h2 : ¬ DMem .zero a₂ := fun h => h1 (heq.mpr h)
          simp only [h1, h2, dite_false]
      )

instance : Add DOrdinal := ⟨addOrd⟩
instance : Mul DOrdinal := ⟨mulOrd⟩
noncomputable instance : Pow DOrdinal DOrdinal := ⟨expOrd⟩

end DybjerOrd
