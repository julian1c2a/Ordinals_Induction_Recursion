import OrdinalsInductionRecursion.DybjerOrd.PreOrd

namespace DybjerOrd

/-- 
El tipo Ordinal de Dybjer es el cociente de los árboles de Brouwer dependientes (DPreOrd)
bajo la relación de equivalencia extensional.
-/
abbrev DOrdinal := Quotient DybjerOrd.Setoid

namespace DOrdinal

theorem Subset_respects_Equiv {x₁ x₂ y₁ y₂ : DPreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) :
  DSubset x₁ y₁ ↔ DSubset x₂ y₂ :=
  ⟨fun h => DSubset_trans hx.right (DSubset_trans h hy.left),
   fun h => DSubset_trans hx.left (DSubset_trans h hy.right)⟩

def Subset (a b : DOrdinal) : Prop :=
  Quotient.lift₂ (fun x y => DSubset x y) (fun _ _ _ _ hx hy => propext (Subset_respects_Equiv hx hy)) a b

theorem Mem_respects_Equiv {x₁ x₂ y₁ y₂ : DPreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) :
  DMem x₁ y₁ ↔ DMem x₂ y₂ :=
  ⟨fun h => DSubset_DMem_trans hx.right (DMem_DSubset_trans h hy.left),
   fun h => DSubset_DMem_trans hx.left (DMem_DSubset_trans h hy.right)⟩

def Mem (a b : DOrdinal) : Prop :=
  Quotient.lift₂ (fun x y => DMem x y) (fun _ _ _ _ hx hy => propext (Mem_respects_Equiv hx hy)) a b

instance : HasSubset DOrdinal := ⟨Subset⟩
instance : Membership DOrdinal DOrdinal := ⟨fun a s => Mem s a⟩

end DOrdinal

end DybjerOrd
