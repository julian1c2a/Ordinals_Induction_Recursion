/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivOrd.ExtPreOrd

-- ==========================================
-- Tipo Cociente: Ordinal
-- ==========================================

universe u

namespace UnivOrd

/-- El tipo de Ordinales de Von Neumann, definido como el cociente
    de los Pre-Ordinales respecto a la igualdad extensional -/
def Ordinal.{u_} := Quotient PreOrd.Setoid.{u_}

namespace Ordinal

-- ==========================================
-- Relaciones de Orden (≤ y <)
-- ==========================================

instance : LE Ordinal.{u} where
  le x y := Quotient.lift₂ PreOrd.Subset (fun _ _ _ _ hx hy => PreOrd.Subset_respects hx hy) x y

instance : LT Ordinal.{u} where
  lt x y := Quotient.lift₂ PreOrd.Mem (fun _ _ _ _ hx hy => PreOrd.Mem_respects hx hy) x y

-- ==========================================
-- Operaciones de Conjuntos
-- ==========================================

def union (x y : Ordinal.{u}) : Ordinal.{u} :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.union a b)) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.union_respects hx hy)) x y

def inter (x y : Ordinal.{u}) : Ordinal.{u} :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.inter a b)) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.inter_respects hx hy)) x y

def sUnion (x : Ordinal.{u}) : Ordinal.{u} :=
  Quotient.lift (fun a => Quotient.mk PreOrd.Setoid (PreOrd.sUnion a)) (fun _ _ h => Quotient.sound (PreOrd.sUnion_respects h)) x

def sInter (x : Ordinal.{u}) : Ordinal.{u} :=
  Quotient.lift (fun a => Quotient.mk PreOrd.Setoid (PreOrd.sInter a)) (fun _ _ h => Quotient.sound (PreOrd.sInter_respects h)) x

-- ==========================================
-- Constantes Base
-- ==========================================

def fromNat (n : ℕ₀) : Ordinal.{u} := Quotient.mk PreOrd.Setoid (PreOrd.preFromNat n)

def omega : Ordinal.{u} := Quotient.mk PreOrd.Setoid PreOrd.preomega
notation "ω" => omega

end Ordinal
end UnivOrd
