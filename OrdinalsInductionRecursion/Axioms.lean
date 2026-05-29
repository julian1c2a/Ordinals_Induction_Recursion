/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- Barrel module: imports all Axioms sub-modules
-- Public API: mem_sep, mem_union, mem_sUnion, mem_inter, mem_setminus,
--             mem_pair, mem_powerset, mem_symDiff, foundation, mem_singleton,
--             orderedPair_eq_iff, mem_decidable, subset_refl, subset_antisymm,
--             union_comm, inter_comm, ..., mem_image, choose, choose_mem, ...

import OrdinalsInductionRecursion.Axioms.BooleanAlgebra
import OrdinalsInductionRecursion.Axioms.Cardinal
import OrdinalsInductionRecursion.Axioms.BooleanRing
import OrdinalsInductionRecursion.Axioms.Choice
import OrdinalsInductionRecursion.Axioms.Decidable
import OrdinalsInductionRecursion.Axioms.Foundation
import OrdinalsInductionRecursion.Axioms.Function
import OrdinalsInductionRecursion.Axioms.Intersection
import OrdinalsInductionRecursion.Axioms.Lattice
import OrdinalsInductionRecursion.Axioms.OrderedPair
import OrdinalsInductionRecursion.Axioms.Pair
import OrdinalsInductionRecursion.Axioms.Powerset
import OrdinalsInductionRecursion.Axioms.Relation
import OrdinalsInductionRecursion.Axioms.Replacement
import OrdinalsInductionRecursion.Axioms.Separation
import OrdinalsInductionRecursion.Axioms.Setminus
import OrdinalsInductionRecursion.Axioms.Singleton
import OrdinalsInductionRecursion.Axioms.Subset
import OrdinalsInductionRecursion.Axioms.Succ
import OrdinalsInductionRecursion.Axioms.SymDiff
import OrdinalsInductionRecursion.Axioms.Union
import OrdinalsInductionRecursion.Axioms.VonNeumann
import OrdinalsInductionRecursion.Axioms.Composition
import OrdinalsInductionRecursion.Axioms.Restriction
import OrdinalsInductionRecursion.Axioms.Bijection
import OrdinalsInductionRecursion.Axioms.Inverse
import OrdinalsInductionRecursion.Axioms.FunctionComp
import OrdinalsInductionRecursion.Axioms.Identity
import OrdinalsInductionRecursion.Axioms.Rank
import OrdinalsInductionRecursion.Axioms.Product
import OrdinalsInductionRecursion.Axioms.Image
import OrdinalsInductionRecursion.Axioms.Adjunction
import OrdinalsInductionRecursion.Axioms.Induction
import OrdinalsInductionRecursion.Axioms.CartProd
import OrdinalsInductionRecursion.Axioms.NPow
import OrdinalsInductionRecursion.Axioms.Ordinal
import OrdinalsInductionRecursion.Axioms.OrdinalNat
import OrdinalsInductionRecursion.Axioms.Fintype
import OrdinalsInductionRecursion.Axioms.Order
import OrdinalsInductionRecursion.Axioms.WellOrder
import OrdinalsInductionRecursion.Axioms.LinearOrder
