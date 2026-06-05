import OrdinalsInductionRecursion.TarskiOrd.PreOrd

namespace TarskiOrd

/-- 
El tipo Ordinal de Tarski es el cociente de los árboles de Brouwer limitados por códigos (TPreOrd)
bajo la relación de equivalencia extensional.
-/
abbrev TOrdinal := Quotient TPreOrd.Setoid

namespace TOrdinal

theorem Subset_respects_Equiv {x₁ x₂ y₁ y₂ : TPreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) :
  TPreOrd.Subset x₁ y₁ ↔ TPreOrd.Subset x₂ y₂ :=
  ⟨fun h => TPreOrd.Subset_trans hx.right (TPreOrd.Subset_trans h hy.left),
   fun h => TPreOrd.Subset_trans hx.left (TPreOrd.Subset_trans h hy.right)⟩

def Subset (a b : TOrdinal) : Prop :=
  Quotient.lift₂ (fun x y => TPreOrd.Subset x y) (fun _ _ _ _ hx hy => propext (Subset_respects_Equiv hx hy)) a b

theorem Mem_respects_Equiv {x₁ x₂ y₁ y₂ : TPreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) :
  TPreOrd.Mem x₁ y₁ ↔ TPreOrd.Mem x₂ y₂ :=
  ⟨fun h => TPreOrd.Subset_Mem_trans hx.right (TPreOrd.Mem_Subset_trans h hy.left),
   fun h => TPreOrd.Subset_Mem_trans hx.left (TPreOrd.Mem_Subset_trans h hy.right)⟩

def Mem (a b : TOrdinal) : Prop :=
  Quotient.lift₂ (fun x y => TPreOrd.Mem x y) (fun _ _ _ _ hx hy => propext (Mem_respects_Equiv hx hy)) a b

instance : HasSubset TOrdinal := ⟨Subset⟩
instance : Membership TOrdinal TOrdinal := ⟨fun a s => Mem s a⟩

end TOrdinal

end TarskiOrd
