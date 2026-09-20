import Linglib.Syntax.Minimalist.FunctionalSequence

/-!
# Complement sizes

This file defines the size of a clausal complement as its highest projected head. Wurmbrand
classifies infinitival complements by the structure they project, a bare vP for restructuring,
a TP for propositional attitudes and a modal projection for future infinitives, beside the full
CP of a finite clause, and a complement is at most as large as another when its highest head is
no higher in the functional sequence. Two sizes with distinct heads at one level, tense and
negation for instance, are then equivalent but not equal, so the order is a preorder.

## Main definitions

* `Minimalist.ComplementSize`: a clausal complement measured by its highest head.
* `Minimalist.ComplementSize.fLevel`: the functional level of the highest head.
* `Minimalist.ComplementSize.vP`, `Minimalist.ComplementSize.tP`,
  `Minimalist.ComplementSize.modP`, `Minimalist.ComplementSize.finP`,
  `Minimalist.ComplementSize.cP`: the standard sizes.

## Main results

* `Minimalist.ComplementSize.le_def`, `Minimalist.ComplementSize.lt_def`: the order is that of
  functional levels.

## References

* [wurmbrand-2014]
* [grimshaw-2005]
-/

namespace Minimalist

/-- A clausal complement measured by the highest head it projects. -/
structure ComplementSize where
  /-- The highest functional head in the complement. -/
  highestHead : Cat
  deriving DecidableEq, Repr

namespace ComplementSize

variable {a b : ComplementSize}

/-- The functional level of a complement is that of its highest head. -/
def fLevel (cs : ComplementSize) : ℕ := cs.highestHead.fValue

/-- Complement sizes are ordered by functional level, so that a complement is at most another when
it projects no higher in the functional sequence. -/
instance : Preorder ComplementSize := Preorder.lift fLevel

instance : DecidableLE ComplementSize := fun a b ↦ inferInstanceAs (Decidable (a.fLevel ≤ b.fLevel))

instance : DecidableLT ComplementSize := fun a b ↦ inferInstanceAs (Decidable (a.fLevel < b.fLevel))

theorem le_def : a ≤ b ↔ a.fLevel ≤ b.fLevel := Iff.rfl

theorem lt_def : a < b ↔ a.fLevel < b.fLevel := Iff.rfl

/-- The vP-sized complement of a restructuring infinitive. -/
def vP : ComplementSize := ⟨.v⟩

/-- The TP-sized complement of a propositional infinitive. -/
def tP : ComplementSize := ⟨.T⟩

/-- The modal complement of a future infinitive. -/
def modP : ComplementSize := ⟨.Mod⟩

/-- The FinP-sized complement, the lowest layer of the left periphery. -/
def finP : ComplementSize := ⟨.Fin⟩

/-- The CP-sized complement of a finite clause. -/
def cP : ComplementSize := ⟨.C⟩

end ComplementSize

end Minimalist
