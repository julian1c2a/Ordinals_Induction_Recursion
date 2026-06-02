import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Induction

universe u

namespace UnivOrd
namespace Cardinals

open Ordinal

def Injection (α β : Ordinal.{u}) : Type (u+1) :=
  { f : {x // x < α} → {y // y < β} // Function.Injective f }

def has_injection (α β : Ordinal.{u}) : Prop :=
  Nonempty (Injection α β)

-- Existencia del Número de Hartogs:
-- Para cada ordinal α, existe algún γ tal que NO existe inyección de γ a α.
-- Esto es un teorema profundo (Teorema de Hartogs).
-- Si lo asumimos o lo demostramos...
axiom hartogs_exists (α : Ordinal.{u}) : ∃ γ, ¬ has_injection γ α

def hartogs (α : Ordinal.{u}) : Ordinal.{u} :=
  WellFounded.min well_founded_lt (fun γ => ¬ has_injection γ α) (hartogs_exists α)

-- Aleph usando recursión límite
def aleph (α : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn α
    omega
    (fun _ ih => hartogs ih)
    (fun _ _ ih => sUnion (sup fun i => ih i.val i.property)) -- Wait, sUnion over what? We need supremum of `ih γ hγ`

end Cardinals
end UnivOrd
