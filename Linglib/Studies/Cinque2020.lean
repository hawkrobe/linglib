import Linglib.Typology.RelativeClause.Basic

/-!
# Cinque (2020): a unified double-Headed analysis of relative clauses
@cite{cinque-2020}

Formalizes the core of @cite{cinque-2020}: all attested relative-clause types
derive from a single **double-Headed** structure — an *internal* Head and an
*external* Head (both indefinite `dP`s, smaller than DP), with the relative
clause merged pre-nominally — via two derivation routes (§1.5):

* **Raising** — the *internal* Head raises to Spec,CP and is the overt Head,
  licensing deletion of the external Head (@cite{kayne-1994} ch. 8).
  Reconstruction / island effects are detectable: the overt Head is in a chain
  with the RC-internal position.
* **Matching** — the *external* Head raises and is overt, licensing deletion of
  the internal Head. Reconstruction is not detectable.

Deletion of the internal Head is licit only when it exactly matches the external
Head (both indefinite `dP`); when the relativized internal Head is bigger — a
DP/KP, or a DP/KP inside a PP (an oblique) — no deletion is possible and the
internal Head is realized by a *wh*-pronoun or a resumptive (§1.5).

The different RC types merge at different heights of the nominal extended
projection (§3.5): non-restrictives attach above DP (external Head includes
strong determiners), restrictives lower (external Head = weak determiners only),
participials lower still. The internal-Head realization "strategies" (ch. 4)
are gap + invariant relativizer, gap + relative pronoun, resumptive, PRO,
non-reduction, and verb-coding.

This is the genuine syntactic treatment that **computes** a
`RelativeClause.Realization` from the reified derivation — the consumer the
substrate's projection hook was built for, and the honest counterpart to the
HPSG `RelClauseDerivation.realization` (which `RelativeClause.Realization`
already serves). @cite{de-vries-2018} surveys the framework-neutral typology
this single structure is meant to cover.

## Main declarations
* `Cinque2020.RC` — the reified double-Headed relative clause.
* `Cinque2020.RC.realization` — its computed projection onto
  `RelativeClause.Realization`.
* `Cinque2020.RC.WellFormed` — the deletion-licensing condition.

## Implementation notes
The reification stays at the level §1.5 states explicitly (two Heads, derivation
route, internal-Head category and strategy, merge height); the tree geometry
(Spec,CP, the `dP`/DP cartography) is below this level and not modelled. PRO and
the verb-coding strategy have no exact `RelativeClause.NPRelType` counterpart in
the Keenan-Comrie/WALS inventory the substrate was built from and are
approximated when projecting.
-/

namespace Cinque2020

open RelativeClause

/-! ### The two derivations from the single double-Headed structure -/

/-- The derivation route (@cite{cinque-2020} §1.5). -/
inductive Derivation
  /-- The internal Head raises to Spec,CP and is overt; the external Head is
      deleted (@cite{kayne-1994}). -/
  | raising
  /-- The external Head is overt; the internal Head is deleted / a proform. -/
  | matching
  deriving DecidableEq, Repr

/-- Which of the two Heads surfaces overtly. -/
inductive HeadChoice
  | internal
  | external
  deriving DecidableEq, Repr

/-- The overt Head is fixed by the derivation, not stipulated separately. -/
def Derivation.overtHead : Derivation → HeadChoice
  | .raising  => .internal
  | .matching => .external

/-! ### The internal Head and its realization strategy -/

/-- Category of the relativized internal Head (@cite{cinque-2020} §1.5).
    Deletion under identity with the external Head turns on this: only an
    indefinite `dP` exactly matches the (indefinite `dP`) external Head. -/
inductive InternalHeadCategory
  /-- An indefinite `dP` exactly matching the external Head — deletion licit. -/
  | indefiniteDP
  /-- A DP/KP, or a DP/KP inside a PP (oblique) — bigger than `dP`, no deletion. -/
  | biggerDPKP
  deriving DecidableEq, Repr

/-- Strategies for realizing the internal Head (@cite{cinque-2020} ch. 4). -/
inductive Strategy
  /-- Gap + invariant relativizer (English *that*, Italian *che*). -/
  | invariantRelativizer
  /-- Gap + relative pronoun / adjective (*who*/*which*, Italian *cui*). -/
  | relativePronoun
  /-- Resumptive pronoun / epithet. -/
  | resumptive
  /-- PRO (participial relative clauses). -/
  | pro
  /-- Full repetition of the Head (non-reduction). -/
  | nonReduction
  /-- The verb-coding strategy. -/
  | verbCoding
  deriving DecidableEq, Repr

/-- Does this strategy realize the internal Head by *deleting* it (leaving no
    overt internal element)? Only the invariant-relativizer strategy and PRO do. -/
def Strategy.deletesInternalHead : Strategy → Bool
  | .invariantRelativizer => true
  | .pro                  => true
  | _                     => false

/-- Project a Cinque strategy onto the substrate `NPRelType`. PRO and
    verb-coding have no exact counterpart in the substrate inventory and are
    approximated (PRO ≈ a silent gap; verb-coding ≈ non-reduction). -/
def Strategy.toNPRelType : Strategy → NPRelType
  | .invariantRelativizer => .gap
  | .relativePronoun      => .relPronoun
  | .resumptive           => .resumptive
  | .pro                  => .gap
  | .nonReduction         => .nonReduction
  | .verbCoding           => .nonReduction

/-! ### Relative-clause types and merge height -/

/-- RC types, by increasing height of external merge in the nominal extended
    projection (@cite{cinque-2020} §3.5): a bigger external Head merges higher. -/
inductive RCType
  | participial
  | restrictive
  | maximalizing
  | kindDefining
  | nonRestrictive
  deriving DecidableEq, Repr

/-- Relative merge height (bigger external Head = higher). Participials have the
    smallest external Head; non-restrictives the biggest (above DP). -/
def RCType.mergeHeight : RCType → Nat
  | .participial    => 0
  | .restrictive    => 1
  | .maximalizing   => 2
  | .kindDefining   => 3
  | .nonRestrictive => 4

/-! ### The reified relative clause -/

/-- A relative clause in @cite{cinque-2020}'s unified analysis: the single
    double-Headed structure (both Heads present by construction), a derivation
    route, the internal-Head category and realization strategy, the relativized
    AH position, and the position of the RC w.r.t. the Head. -/
structure RC where
  rcType : RCType
  derivation : Derivation
  internalHeadCategory : InternalHeadCategory
  strategy : Strategy
  position : AHPosition
  rcPosition : RCPosition
  deriving Repr

/-- The overt Head of an RC, determined by its derivation. -/
def RC.overtHead (r : RC) : HeadChoice := r.derivation.overtHead

/-- Reconstruction / island effects are detectable iff the overt Head is the
    *internal* one (raising) — it is then in a chain with the RC-internal
    position (@cite{cinque-2020} §1.5). -/
def RC.reconstructs (r : RC) : Bool :=
  match r.derivation with
  | .raising  => true
  | .matching => false

/-- @cite{cinque-2020}'s deletion-licensing condition: the internal Head may be
    deleted (the gap, invariant-relativizer / PRO strategies) only when it
    exactly matches the external Head (an indefinite `dP`). A bigger internal
    Head (oblique DP/KP, or DP/KP in a PP) must be spelled out — a relative
    pronoun or resumptive. (Stated as the decidable `¬deletes ∨ matches`.) -/
def RC.WellFormed (r : RC) : Prop :=
  r.strategy.deletesInternalHead = false ∨ r.internalHeadCategory = .indefiniteDP

instance (r : RC) : Decidable r.WellFormed := by
  unfold RC.WellFormed; infer_instance

/-- The framework-neutral `RelativeClause.Realization` this derivation projects
    to — **computed** from the reified structure (the relativized position and
    the NP_rel type the internal-Head strategy yields), not stipulated. The hook
    by which Cinque's analysis connects to the relativization substrate. -/
def RC.realization (r : RC) : Realization :=
  { position := r.position, npRel := r.strategy.toNPRelType }

/-! ### Consequences -/

/-- Raising makes the *internal* Head overt. -/
theorem overtHead_raising : Derivation.raising.overtHead = .internal := rfl

/-- Matching makes the *external* Head overt. -/
theorem overtHead_matching : Derivation.matching.overtHead = .external := rfl

/-- A matching derivation shows no reconstruction. -/
theorem matching_no_reconstruction (r : RC) (h : r.derivation = .matching) :
    r.reconstructs = false := by
  unfold RC.reconstructs; rw [h]

/-- **Deletion licensing.** A well-formed RC whose relativized internal Head is
    bigger than an indefinite `dP` cannot use the gap-deletion (invariant
    relativizer) strategy — it must spell the internal Head out. -/
theorem bigger_head_no_gap_deletion (r : RC) (h : r.WellFormed)
    (hbig : r.internalHeadCategory = .biggerDPKP) :
    r.strategy ≠ .invariantRelativizer := by
  intro hs
  rcases h with hf | hi
  · rw [hs] at hf; exact absurd hf (by decide)
  · rw [hbig] at hi; exact absurd hi (by decide)

/-- Non-restrictive RCs merge higher than restrictives (@cite{cinque-2020} §3.5). -/
theorem nonRestrictive_above_restrictive :
    RCType.restrictive.mergeHeight < RCType.nonRestrictive.mergeHeight := by decide

/-- Participial RCs have the lowest external merge. -/
theorem participial_lowest (t : RCType) :
    RCType.participial.mergeHeight ≤ t.mergeHeight := by
  cases t <;> decide

/-! ### Worked examples -/

/-- English "the book that John read ___": matching, internal Head exactly
    matches the external (indefinite `dP`), gap via the invariant relativizer
    *that*; object relative. -/
def englishThatObject : RC :=
  { rcType := .restrictive, derivation := .matching,
    internalHeadCategory := .indefiniteDP, strategy := .invariantRelativizer,
    position := .directObject, rcPosition := .postNominal }

example : englishThatObject.WellFormed := by decide

/-- It **computes** to the substrate realization `(directObject, gap)` — the same
    value HPSG's `RelClauseDerivation.realization` computes for this sentence,
    now from Cinque's derivation rather than stipulated. -/
example : englishThatObject.realization = { position := .directObject, npRel := .gap } := rfl

/-- "the man to whom I spoke": oblique relativization. The internal Head is
    bigger than `dP` (a PP-internal DP/KP), so deletion is barred and a relative
    pronoun is used. -/
def englishWhomOblique : RC :=
  { rcType := .restrictive, derivation := .matching,
    internalHeadCategory := .biggerDPKP, strategy := .relativePronoun,
    position := .oblique, rcPosition := .postNominal }

example : englishWhomOblique.WellFormed := by decide
example :
    englishWhomOblique.realization = { position := .oblique, npRel := .relPronoun } := rfl

/-- The deletion-licensing bite: an oblique (bigger) internal Head *cannot* be
    deleted via the invariant relativizer — that derivation is ill-formed. -/
example :
    ¬ ({ rcType := .restrictive, derivation := .matching,
         internalHeadCategory := .biggerDPKP, strategy := .invariantRelativizer,
         position := .oblique, rcPosition := .postNominal } : RC).WellFormed := by decide

/-- Hebrew resumptive relativization at the genitive: matching, internal Head
    spelled out as a resumptive pronoun. -/
def hebrewResumptiveGenitive : RC :=
  { rcType := .restrictive, derivation := .matching,
    internalHeadCategory := .biggerDPKP, strategy := .resumptive,
    position := .genitive, rcPosition := .postNominal }

example :
    hebrewResumptiveGenitive.realization = { position := .genitive, npRel := .resumptive } := rfl

/-- A raising derivation (overt Head = internal Head) shows reconstruction. -/
def englishRaisingObject : RC :=
  { rcType := .restrictive, derivation := .raising,
    internalHeadCategory := .indefiniteDP, strategy := .invariantRelativizer,
    position := .directObject, rcPosition := .postNominal }

example : englishRaisingObject.reconstructs = true := rfl
example : englishThatObject.reconstructs = false := rfl

end Cinque2020
