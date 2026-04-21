import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic

/-!
# Exhaustification: abstract excluder
@cite{fox-2007} @cite{chierchia-2013} @cite{magri-2009} @cite{santorio-2018}

Different exhaustification theories disagree on **which** alternatives the
operator should negate, but agree on the rest of the architecture: assert
the prejacent and negate the chosen alternatives. This module factors out
the agreement: an `Excluder` is a strategy for choosing alternatives, and
`Excluder.exh` applies it.

Concrete excluders live in sibling modules:
- `Innocent.lean` — Fox 2007 innocent exclusion
- `Tolerant.lean` — Chierchia 2013 contradiction-tolerating exclusion
- `Relevance.lean` — Magri 2009 relevance-sensitive exclusion

## Why a structure rather than a type class

Excluders are first-class data: a single semantic theory may invoke
several (e.g. recursive exhaustification with two different excluders at
two layers). They are not properties of a world type to be inferred by
typeclass resolution.
-/

namespace Exhaustification

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Convert a `Bool` predicate on worlds to its support `Finset`. -/
def predToFinset (p : W → Bool) : Finset W :=
  Finset.univ.filter (fun w => p w)

/-- Convert a list of `Bool` predicates to a `Finset` of supports.
    Uses `DecidableEq (Finset W)` (free from `[DecidableEq W]`); does
    NOT need `DecidableEq (W → Bool)`. -/
def altsFromPreds (alts : List (W → Bool)) : Finset (Finset W) :=
  (alts.map predToFinset).toFinset

/-- An exhaustification strategy: a choice, for each prejacent and
    alternative set, of which alternatives to negate.

    Different theories instantiate `excluded` differently (Fox's innocent
    exclusion, Chierchia's contradiction-tolerating, Magri's
    relevance-sensitive, Santorio's stability). The `excluded_subset`
    field guarantees the strategy only picks alternatives that were
    offered. -/
structure Excluder (W : Type*) [Fintype W] [DecidableEq W] where
  /-- Given a prejacent `φ` and an alternative set `ALT`, return the
      alternatives whose negation should be conjoined with `φ`. -/
  excluded : Finset (Finset W) → Finset W → Finset (Finset W)
  /-- The strategy returns a sub-collection of the offered alternatives. -/
  excluded_subset : ∀ ALT φ, excluded ALT φ ⊆ ALT

namespace Excluder

variable (E : Excluder W) (ALT : Finset (Finset W)) (φ : Finset W)

/-- Exhaustified meaning: assert the prejacent and negate every
    excluded alternative. A world `w` survives iff `w ∈ φ` and `w ∉ a`
    for every `a ∈ E.excluded ALT φ`. -/
def exh : Finset W :=
  φ \ (E.excluded ALT φ).biUnion id

/-- The exhaustified meaning is contained in the prejacent. -/
theorem exh_subset_phi : E.exh ALT φ ⊆ φ := Finset.sdiff_subset

/-- Membership characterization for `exh`. -/
theorem mem_exh_iff {w : W} :
    w ∈ E.exh ALT φ ↔ w ∈ φ ∧ ∀ a ∈ E.excluded ALT φ, w ∉ a := by
  simp only [exh, Finset.mem_sdiff, Finset.mem_biUnion, id_eq, not_exists, not_and]

end Excluder

end Exhaustification
