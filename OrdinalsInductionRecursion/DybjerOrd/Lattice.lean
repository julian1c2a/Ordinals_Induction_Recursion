import OrdinalsInductionRecursion.DybjerOrd.Order

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Lattice Operations (Unión e Intersección Binarias)
-- ==========================================

instance : LE DOrdinal := ⟨DOrdinal.Subset⟩
instance : LT DOrdinal := ⟨fun x y => x ≤ y ∧ ¬ (y ≤ x)⟩

noncomputable local instance (x y : DOrdinal) : Decidable (x ≤ y) := Classical.propDecidable _
noncomputable local instance (x y : DOrdinal) : Decidable (x = y) := Classical.propDecidable _

noncomputable instance : Max DOrdinal where
  max x y := if x ≤ y then y else x

noncomputable instance : Min DOrdinal where
  min x y := if x ≤ y then x else y

theorem DOrdinal_le_antisymm (x y : DOrdinal) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  revert x y
  apply Quotient.ind
  intro a
  apply Quotient.ind
  intro b h1 h2
  exact Quotient.sound (And.intro h1 h2)

theorem max_comm (x y : DOrdinal) : Max.max x y = Max.max y x := by
  dsimp [Max.max]
  by_cases h1 : x ≤ y
  · by_cases h2 : y ≤ x
    · simp [h1, h2]
      exact DOrdinal_le_antisymm y x h2 h1
    · simp [h1, h2]
  · by_cases h2 : y ≤ x
    · simp [h1, h2]
    · match ordinal_total_order x y with
      | Or.inl h => exact False.elim (h1 h)
      | Or.inr h => exact False.elim (h2 h)

-- ==========================================
-- SUnion y SInter (Operaciones Unarias Generales)
-- ==========================================

def preord_sUnion (x : DPreOrd) : DPreOrd :=
  match x with
  | .zero => .zero
  | .succ x' => x'
  | .sup c f => .sup c (fun a => preord_sUnion (f a))

theorem Mem_sUnion {x y : DPreOrd} (h : DMem x y) : DSubset x (preord_sUnion y) :=
  match y, h with
  | _, DMem.mem_succ hsub => hsub
  | _, DMem.mem_sup a hmem => DSubset_sup (Mem_sUnion hmem) a rfl

theorem sUnion_Subset {x₁ x₂ : DPreOrd} (h : DSubset x₁ x₂) : DSubset (preord_sUnion x₁) (preord_sUnion x₂) :=
  match x₁, x₂, h with
  | _, _, DSubset.zero_subset _ => DSubset.zero_subset _
  | _, _, DSubset.succ_subset hmem => Mem_sUnion hmem
  | _, _, @DSubset.sup_subset _ _ _ _ hsub => DSubset.sup_subset fun a => sUnion_Subset (hsub a)

def sUnion (x : DOrdinal) : DOrdinal :=
  Quotient.liftOn x (fun a => (Quotient.mk Setoid (preord_sUnion a) : DOrdinal))
    (fun _ _ h => Quotient.sound ⟨sUnion_Subset h.left, sUnion_Subset h.right⟩)

def sInter (_ : DOrdinal) : DOrdinal :=
  (Quotient.mk Setoid .zero : DOrdinal)

theorem sInter_eq_zero (x : DOrdinal) : sInter x = (Quotient.mk Setoid .zero : DOrdinal) := rfl

/-- Demostración de que 0 es realmente el ínfimo para cualquier ordinal positivo. -/
theorem zero_is_infimum_of_pos {x : DPreOrd} (hx : DMem .zero x) : 
  (∀ y, DMem y x → DSubset .zero y) ∧ (DMem .zero x) := 
  ⟨fun y _ => DSubset.zero_subset y, hx⟩

end DybjerOrd
