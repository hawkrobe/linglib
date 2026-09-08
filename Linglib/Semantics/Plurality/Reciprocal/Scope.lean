import Mathlib.Order.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Simps.Basic

/-!
# Reciprocal scope: anaphoric relations, locus, and readings

On the relational analysis of reciprocals (Sternefeld, Beck, Dotlačil, Haug and Dalrymple)
*each other* is a pronoun bearing an anaphoric relation to its antecedent; on the
quantificational analysis (Heim, Lasnik and May) it contains a distributive quantifier. The
narrow/wide scope ambiguity of a reciprocal in a complement clause is then, relationally, the
ambiguity Williams found in any plural anaphor between group identity with the matrix subject
(the we-reading) and binding by it (the I-reading).

The relations are conditions on plural information states in
`Semantics/Dynamic/PPCDRT/Anaphora.lean`. This file holds their labels and the two-parameter
classification of readings of Haug and Dalrymple §3.3: the locus of the reciprocal, high or
low, crossed with the antecedent relation. Three of the four cells are attested; a bound local
antecedent denotes an individual and so does not make available the plurality a low reciprocal
needs.

## Main definitions

* `Reciprocal.AnaphoricRelation` — binding, group identity, reciprocity.
* `Reciprocal.Locus`, `Reciprocal.Scope` — the locus of the reciprocal, ordered by scope, and
  the two scope readings.
* `Reciprocal.ScopeReading` — locus × antecedent relation × reciprocal relation, with the
  three attested cells and `Reciprocal.Scope.reading`.

## References

* [D. T. T. Haug and M. Dalrymple, *Reciprocity: Anaphora, scope, and quantification*
  (2020)][haug-dalrymple-2020]
* [M. Dalrymple and D. T. T. Haug, *Constraints on reciprocal scope* (2024)][dalrymple-haug-2024]
* [I. Heim, H. Lasnik and R. May, *Reciprocity and plurality* (1991)][heim-lasnik-may-1991]
* [E. Williams, *Reciprocal scope* (1991)][williams-1991]
* [J. Higginbotham, *On semantics* (1985)][higginbotham-1985]
* [W. Sternefeld, *Reciprocity and cumulative predication* (1998)][sternefeld-1998]
* [S. Beck, *Reciprocals are definites* (2001)][beck-2001]
* [J. Dotlačil, *Reciprocals distribute over information states* (2013)][dotlacil-2013]
-/

namespace Reciprocal

/-- The three anaphoric relations Dalrymple and Haug label their arrows with (the arrow is
    Higginbotham's, the binding/group-identity ambiguity Williams's): properties of a
    resolution rather than of the pronoun, since the same *they* can be bound or
    group-identical. -/
inductive AnaphoricRelation where
  /-- The pronoun is a bound variable of its antecedent and denotes an individual. -/
  | binding
  /-- The pronoun denotes the same plurality as its antecedent. -/
  | groupIdentity
  /-- The same plurality across situations and distinct individuals in each. -/
  | reciprocity
  deriving DecidableEq, Repr

/-- The locus of the reciprocal in the matrix update, ordered by scope. -/
inductive Locus where
  /-- In situ in the complement clause. -/
  | low
  /-- Lifted to the matrix clause. -/
  | high
  deriving DecidableEq, Repr, Fintype

/-- The height of a locus. -/
def Locus.toNat : Locus → ℕ
  | .low => 0
  | .high => 1

instance : LinearOrder Locus := LinearOrder.lift' Locus.toNat (by decide)

@[simp] theorem Locus.lt_iff (a b : Locus) : a < b ↔ a = .low ∧ b = .high := by
  revert a b; decide

/-- The scope readings of a reciprocal in a complement clause. -/
inductive Scope where
  /-- The we-reading: "Tracy and Chris each thought 'We saw each other'". -/
  | narrow
  /-- The I-reading: "Tracy thought 'I saw Chris' and Chris thought 'I saw Tracy'". -/
  | wide
  deriving DecidableEq, Repr, Fintype

/-- A reading in the two-parameter classification. -/
structure ScopeReading where
  /-- The locus of the reciprocal. -/
  locus : Locus
  /-- The relation between the matrix subject and the reciprocal's local antecedent. -/
  antecedentRel : AnaphoricRelation
  /-- The relation between the local antecedent and the reciprocal. -/
  reciprocalRel : AnaphoricRelation
  deriving DecidableEq, Repr

namespace ScopeReading

/-- Narrow scope: low locus, group-identical antecedent, reciprocity in situ. -/
@[simps] def narrow : ScopeReading := ⟨.low, .groupIdentity, .reciprocity⟩

/-- Wide scope: high locus, bound antecedent, reciprocity in the matrix clause. -/
@[simps] def wide : ScopeReading := ⟨.high, .binding, .reciprocity⟩

/-- The crossed reading: high locus, group-identical antecedent and reciprocal, with
    reciprocity contributed by the distinctness presupposition alone. -/
@[simps] def crossed : ScopeReading := ⟨.high, .groupIdentity, .groupIdentity⟩

/-- The three attested cells; the fourth, a low reciprocal with a bound antecedent, is empty. -/
def attested : List ScopeReading := [narrow, wide, crossed]

end ScopeReading

/-- The cell of each scope reading. -/
def Scope.reading : Scope → ScopeReading
  | .narrow => .narrow
  | .wide => .wide

@[simp] theorem Scope.reading_narrow : Scope.narrow.reading = .narrow := rfl

@[simp] theorem Scope.reading_wide : Scope.wide.reading = .wide := rfl

end Reciprocal
