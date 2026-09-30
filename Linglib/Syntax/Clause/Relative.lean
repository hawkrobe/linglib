module

public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Relativization

Theory-neutral types for cross-linguistic relativization data: the relativizable positions of
[keenan-comrie-1977]'s Accessibility Hierarchy as a bounded linear order, the placement of the
relative clause relative to its head, what occupies the relativized position (NP_rel), and the
relativizers the fragments record.

## Main declarations

* `Relativization.Position` — the relativizable positions, linearly ordered by accessibility
  with the subject on top: the Accessibility Hierarchy.
* `Relativization.Placement` — the clause's placement relative to the head noun.
* `Relativization.NPRel` — what occupies the relativized position.
* `Relativizer` — a relativizer with its placement and what occupies NP_rel at each position.

## Implementation notes

A relativizer's realization is a finite relation between positions and NP_rel types, given as a
`Finset`-valued function so that fragments enter it by cases and every check decides. A fragment
records one entry per relativizer, as a grammar describes it, with free variation where the
grammar reports it (Hebrew *she-* with a gap or a resumptive at the direct object).
A classification of relative clauses is a predicate on `NPRel` pulled back along the
realization, and lives with the paper that draws it: [keenan-comrie-1977]'s ±case and its
"RC-forming strategies" are derived in `Studies/KeenanComrie1977.lean`.

The semantics of relative clauses, their denotation, is `RelativeClause.denote` in
`Semantics/Modification/RelativeClause.lean`.

## References

* [keenan-comrie-1977]
* [ryding-2005]
* [scott-2021]
* [sichel-2014]
-/

@[expose] public section

namespace Relativization

/-! ### The Accessibility Hierarchy -/

/-- The relativizable positions of [keenan-comrie-1977]'s Accessibility Hierarchy,
subject > direct object > indirect object > oblique > genitive > object of comparison. A higher
position is relativizable in more languages and by lighter strategies. -/
inductive Position where
  | subject
  | directObject
  | indirectObject
  | oblique
  | genitive
  /-- The object of comparison, "the person [that I am taller than _]". -/
  | objComparison
  deriving DecidableEq, Repr, Fintype

namespace Position

/-- The rank of a position, higher for the more accessible. -/
def rank : Position → ℕ
  | .subject        => 5
  | .directObject   => 4
  | .indirectObject => 3
  | .oblique        => 2
  | .genitive       => 1
  | .objComparison  => 0

theorem rank_injective : Function.Injective rank := by
  intro a b h; cases a <;> cases b <;> simp_all [rank]

/-- The accessibility order: `p ≤ q` iff `p` is no more accessible than `q`. -/
instance : LinearOrder Position := LinearOrder.lift' rank rank_injective

/-- The subject is the top of the hierarchy, the object of comparison its bottom. -/
instance : BoundedOrder Position where
  top := .subject
  le_top := by decide
  bot := .objComparison
  bot_le := by decide

instance : LocallyFiniteOrder Position := Fintype.toLocallyFiniteOrder

end Position

/-! ### Placement of the clause -/

/-- The placement of the relative clause relative to its head noun. -/
inductive Placement where
  /-- The clause follows the head, English "the man [who left]". -/
  | postNominal
  /-- The clause precedes the head, Japanese "[ _ kaetta] hito". -/
  | preNominal
  /-- The head sits inside the clause, as in Bambara. -/
  | internallyHeaded
  /-- The head appears both inside and outside the clause, Hindi-Urdu *jo … vo*. -/
  | correlative
  deriving DecidableEq, Repr, Fintype

/-! ### What occupies the relativized position -/

/-- What occupies the relativized position NP_rel inside the clause. A relativizer that does not
vary with the relativized position, such as a complementizer or a relative pronoun agreeing
with the head, leaves NP_rel a `gap`. -/
inductive NPRel where
  /-- Nothing overt at the relativized position, English "the man [that _ left]". -/
  | gap
  /-- A personal pronoun, Modern Standard Arabic *al-kitaab-u lladhii qaraʾ-naa-hu* 'the book
  that we read (it)' ([ryding-2005]). -/
  | resumptive
  /-- A resumptive that is a partially pronounced lower copy of an Ā-movement chain, diagnosed
  by parasitic gaps ([scott-2021]). -/
  | resumptiveMovement
  /-- A base-generated resumptive bound by the head, obligatory inside adjunct islands
  ([scott-2021]). -/
  | resumptiveBound
  /-- A relative pronoun marked for the relativized position, by its case or an accompanying
  adposition, German "der Mann [den ich sah]". -/
  | relPronoun
  /-- The head noun repeated in full inside the clause, as in Bambara. -/
  | nonReduction
  deriving DecidableEq, Repr, Fintype

end Relativization

/-! ### Relativizers -/

open Relativization in
/-- A relativizer of a language, the particle, pronoun or affix introducing a relative clause or
the zero relativizer, with the placement of its clause and what occupies NP_rel at each position
of the hierarchy: empty where it does not relativize the position, several values where they
alternate. -/
structure Relativizer where
  /-- The form, "∅" for the zero relativizer. -/
  form : String
  /-- The clause's placement relative to the head. -/
  placement : Placement
  /-- What may occupy NP_rel at each position. -/
  realize : Position → Finset NPRel
