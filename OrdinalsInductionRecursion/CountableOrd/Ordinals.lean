/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.CountableOrd.ExtPreOrd

namespace CountableOrd

-- ==========================================
-- Tipo Cociente: Ordinal
-- ==========================================

/-- El tipo de Ordinales de Von Neumann, definido como el cociente
    de los Pre-Ordinales respecto a la igualdad extensional -/
def Ordinal := Quotient PreOrd.Setoid

namespace Ordinal

-- ==========================================
-- Relaciones de Orden (≤ y <)
-- ==========================================

instance : LE Ordinal where
  le x y := Quotient.lift₂ PreOrd.Subset (fun _ _ _ _ hx hy => PreOrd.Subset_respects hx hy) x y

instance : LT Ordinal where
  lt x y := Quotient.lift₂ PreOrd.Mem (fun _ _ _ _ hx hy => PreOrd.Mem_respects hx hy) x y

-- ==========================================
-- Operaciones de Conjuntos
-- ==========================================

def union (x y : Ordinal) : Ordinal :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.union a b)) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.union_respects hx hy)) x y

def inter (x y : Ordinal) : Ordinal :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.inter a b)) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.inter_respects hx hy)) x y

def sUnion (x : Ordinal) : Ordinal :=
  Quotient.lift (fun a => Quotient.mk PreOrd.Setoid (PreOrd.sUnion a)) (fun _ _ h => Quotient.sound (PreOrd.sUnion_respects h)) x

def sInter (x : Ordinal) : Ordinal :=
  Quotient.lift (fun a => Quotient.mk PreOrd.Setoid (PreOrd.sInter a)) (fun _ _ h => Quotient.sound (PreOrd.sInter_respects h)) x

-- ==========================================
-- Constantes Base
-- ==========================================


def zero : Ordinal := Quotient.mk PreOrd.Setoid PreOrd.zero

def succ (x : Ordinal) : Ordinal :=
  Quotient.lift (fun a => Quotient.mk PreOrd.Setoid (PreOrd.succ a)) (fun _ _ h => Quotient.sound (PreOrd.succ_respects h)) x

def IsLimit (x : Ordinal) : Prop := x ≠ zero ∧ ∀ y < x, succ y < x



def fromNat (n : ℕ₀) : Ordinal := Quotient.mk PreOrd.Setoid (PreOrd.preFromNat n)

def omega : Ordinal := Quotient.mk PreOrd.Setoid PreOrd.preomega
notation "ω" => omega

end Ordinal

end CountableOrd
