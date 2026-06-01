import OrdinalsInductionRecursion.ExtPreOrd

namespace PreOrd

theorem subset_inter_fixed {x y : PreOrd} (H_mem : ∀ z, Mem z x → Mem z y → Mem z (inter x y))
  {z : PreOrd} (hx : Subset z x) (hy : Subset z y) : Subset z (inter x y) :=
  match z, hx, hy with
  | .zero, _, _ => .zero_subset _
  | .succ z', .succ_subset hx_mem, .succ_subset hy_mem => .succ_subset (H_mem z' hx_mem hy_mem)
  | .sup f, .sup_subset hx_sub, .sup_subset hy_sub => .sup_subset fun n => subset_inter_fixed H_mem (hx_sub n) (hy_sub n)

theorem mem_inter_succ_y_fixed {x' y : PreOrd} (H_sub : ∀ z y', Subset z x' → Subset z y' → Subset z (inter x' y'))
  {z : PreOrd} (hx : Subset z x') (hy : Mem z y) : Mem z (inter_succ_y (inter x') y) :=
  match y, hy with
  | .succ y', .mem_succ hy_sub => .mem_succ (H_sub z y' hx hy_sub)
  | .sup g, .mem_sup n hmem => .mem_sup n (mem_inter_succ_y_fixed H_sub hx hmem)

def mem_succ_cases {x' z : PreOrd} (hx : Mem z (succ x')) {motive : Mem z (succ x') → Prop}
  (f : ∀ hx_sub, motive (.mem_succ hx_sub)) : motive hx :=
  match hx with
  | .mem_succ hx_sub => f hx_sub

def mem_sup_cases {F : ℕ₀ → PreOrd} {z : PreOrd} (hx : Mem z (sup F)) {motive : Mem z (sup F) → Prop}
  (g : ∀ n hx_mem, motive (.mem_sup n hx_mem)) : motive hx :=
  match hx with
  | .mem_sup n hx_mem => g n hx_mem

def mem_zero_cases {z : PreOrd} (hx : Mem z zero) {motive : Mem z zero → Prop} : motive hx :=
  nomatch hx

def InterProp (x : PreOrd) : Prop :=
  ∀ y, (∀ z, Subset z x → Subset z y → Subset z (inter x y)) ∧
       (∀ z, Mem z x → Mem z y → Mem z (inter x y))

theorem inter_prop (x : PreOrd) : InterProp x :=
  match x with
  | .zero => fun y =>
    ⟨fun z hx hy => subset_inter_fixed (fun z hx hy => mem_zero_cases (motive := fun _ => Mem z (inter zero y)) hx) hx hy,
     fun z hx hy => mem_zero_cases (motive := fun _ => Mem z (inter zero y)) hx⟩
  | .succ x' => fun y =>
    let ih_x' := inter_prop x'
    let mem_prop : ∀ z, Mem z (succ x') → Mem z y → Mem z (inter (succ x') y) :=
      fun z hx hy => mem_succ_cases (motive := fun _ => Mem z (inter (succ x') y)) hx
        (fun hx_sub => mem_inter_succ_y_fixed (fun z y' => (ih_x' y').1 z) hx_sub hy)
    ⟨fun z hx hy => subset_inter_fixed mem_prop hx hy, mem_prop⟩
  | .sup f => fun y =>
    let ih_f := fun n => inter_prop (f n)
    let mem_prop : ∀ z, Mem z (sup f) → Mem z y → Mem z (inter (sup f) y) :=
      fun z hx hy => mem_sup_cases (motive := fun _ => Mem z (inter (sup f) y)) hx
        (fun n hx_mem => Mem.mem_sup n ((ih_f n y).2 z hx_mem hy))
    ⟨fun z hx hy => subset_inter_fixed mem_prop hx hy, mem_prop⟩

theorem subset_inter {x y z : PreOrd} (hx : Subset z x) (hy : Subset z y) : Subset z (inter x y) :=
  (inter_prop x y).1 z hx hy

theorem mem_inter {x y z : PreOrd} (hx : Mem z x) (hy : Mem z y) : Mem z (inter x y) :=
  (inter_prop x y).2 z hx hy

end PreOrd
