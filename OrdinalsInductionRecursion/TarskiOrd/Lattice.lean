import OrdinalsInductionRecursion.TarskiOrd.Arith
import OrdinalsInductionRecursion.TarskiOrd.Order

namespace TarskiOrd
open TPreOrd
open Classical

-- ==========================================
-- Lattice Operations (Unión e Intersección Binarias)
-- ==========================================

instance : LE TOrdinal := ⟨TOrdinal.Subset⟩
instance : LT TOrdinal := ⟨fun x y => x ≤ y ∧ ¬ (y ≤ x)⟩

noncomputable local instance (x y : TOrdinal) : Decidable (x ≤ y) := Classical.propDecidable _
noncomputable local instance (x y : TOrdinal) : Decidable (x = y) := Classical.propDecidable _

noncomputable instance : Max TOrdinal where
  max x y := if x ≤ y then y else x

noncomputable instance : Min TOrdinal where
  min x y := if x ≤ y then x else y

theorem TOrdinal_le_antisymm (x y : TOrdinal) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  revert x y
  apply Quotient.ind
  intro a
  apply Quotient.ind
  intro b h1 h2
  exact Quotient.sound (And.intro h1 h2)

theorem max_comm (x y : TOrdinal) : Max.max x y = Max.max y x := by
  dsimp [Max.max]
  by_cases h1 : x ≤ y
  · by_cases h2 : y ≤ x
    · simp [h1, h2]
      exact TOrdinal_le_antisymm y x h2 h1
    · simp [h1, h2]
  · by_cases h2 : y ≤ x
    · simp [h1, h2]
    · match ordinal_total_order x y with
      | Or.inl h => exact False.elim (h1 h)
      | Or.inr h => exact False.elim (h2 h)

-- ==========================================
-- SUnion y SInter (Operaciones Unarias Generales)
-- ==========================================

def preord_sUnion (x : TPreOrd) : TPreOrd :=
  match x with
  | .zero => .zero
  | .succ x' => x'
  | .sup c f => .sup c (fun a => preord_sUnion (f a))

theorem Mem_sUnion {x y : TPreOrd} (h : TPreOrd.Mem x y) : TPreOrd.Subset x (preord_sUnion y) :=
  match y, h with
  | _, TPreOrd.Mem.mem_succ hsub => hsub
  | _, TPreOrd.Mem.mem_sup a hmem => TPreOrd.Subset_sup (Mem_sUnion hmem) a rfl

theorem sUnion_Subset {x₁ x₂ : TPreOrd} (h : TPreOrd.Subset x₁ x₂) : TPreOrd.Subset (preord_sUnion x₁) (preord_sUnion x₂) :=
  match x₁, x₂, h with
  | _, _, TPreOrd.Subset.zero_subset _ => TPreOrd.Subset.zero_subset _
  | _, _, TPreOrd.Subset.succ_subset hmem => Mem_sUnion hmem
  | _, _, TPreOrd.Subset.sup_subset hsub => TPreOrd.Subset.sup_subset fun a => sUnion_Subset (hsub a)

def sUnion (x : TOrdinal) : TOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk TPreOrd.Setoid (preord_sUnion a) : TOrdinal))
    (fun _ _ h => Quotient.sound ⟨sUnion_Subset h.left, sUnion_Subset h.right⟩)

def sInter (x : TOrdinal) : TOrdinal :=
  (Quotient.mk TPreOrd.Setoid zero : TOrdinal)

theorem sInter_eq_zero (x : TOrdinal) : sInter x = (Quotient.mk TPreOrd.Setoid zero : TOrdinal) := rfl

/-- Demostración de que 0 es realmente el ínfimo para cualquier ordinal positivo. -/
theorem zero_is_infimum_of_pos {x : TPreOrd} (hx : TPreOrd.Mem zero x) : 
  (∀ y, TPreOrd.Mem y x → TPreOrd.Subset zero y) ∧ (TPreOrd.Mem zero x) := 
  ⟨fun y _ => TPreOrd.Subset.zero_subset y, hx⟩

end TarskiOrd
