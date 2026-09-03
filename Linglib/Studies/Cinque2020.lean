import Linglib.Syntax.RelativeClause.Basic
import Linglib.Fragments.English.Relativization
import Linglib.Fragments.Hebrew.Relativization

/-!
# Cinque 2020: The Syntax of Relative Clauses

Every attested type of relative clause — externally headed post-nominal and pre-nominal,
internally headed, double-headed, headless, correlative and adjoined — derives from one
double-headed structure, the clause merged pre-nominally with an external Head, the indefinite
chunk `dP` of the modified noun's extended projection, and an internal Head, by movement,
deletion under identity and replacement by a proform (Introduction, §1.5). In a raising
derivation the internal Head raises to Spec,CP, is the overt Head and licenses deletion of the
external one ([kayne-1994]), so reconstruction and island effects are detectable; in a matching
derivation the external Head raises and is overt, and the internal Head is deleted or replaced.
Deletion is under identity: it is possible only when the internal Head is an exact match of the
external `dP`, as with the invariant relativizers *that* and *che*, while an internal Head that
is bigger, a DP or KP or one inside a PP, is categorially distinct and is represented by a
wh-pronoun or a resumptive (§1.5, Chapter 2). The types merge at increasing heights of the
nominal extended projection, participial below maximalizing below restrictive below
kind-defining below non-restrictive (§3.5), and Chapter 4 surveys the six strategies for the
internal Head: a gap with an invariant relativizer, a relative pronoun, a resumptive, PRO,
non-reduction and verb-coding.

`RC` is the double-headed structure with its derivation, the category `Head` of its internal
Head, the strategy realizing it, the relativized position and the clause's position;
`RC.overtHead` and `RC.Reconstructs` follow from the derivation, and `RC.WellFormed` is deletion
under identity, from which `bigger_head_no_gap_deletion` derives the wh-pronoun or resumptive for
a Head bigger than `dP`. `RC.realization` projects the structure onto the substrate's
`RelativeClause.Realization`, and the three worked examples — English *that* on an object,
English *to whom* on an oblique and Hebrew *she-* with a resumptive on a genitive — project
onto realizations the English and Hebrew Fragments' markers attest. The tree geometry of
Spec,CP and the `dP`/DP cartography is not modelled, and PRO and verb-coding are approximated in
the substrate's inventory of NP_rel types.

## References

* [G. Cinque, *The Syntax of Relative Clauses: A Unified Analysis* (2020)][cinque-2020]
* [R. S. Kayne, *The Antisymmetry of Syntax* (1994)][kayne-1994]
-/

namespace Cinque2020

open RelativeClause

/-! ### The two derivations (§1.5) -/

/-- Which Head raises and is overt. -/
inductive Derivation
  /-- The internal Head raises to Spec,CP and is overt; the external Head is deleted. -/
  | raising
  /-- The external Head is overt; the internal Head is deleted or replaced by a proform. -/
  | matching
  deriving DecidableEq, Repr

/-- The two Heads. -/
inductive HeadChoice
  | internal | external
  deriving DecidableEq, Repr

/-- The overt Head of a derivation. -/
def Derivation.overtHead : Derivation → HeadChoice
  | .raising => .internal
  | .matching => .external

/-- A Head as a chunk of the relativized noun's extended projection: the indefinite `dP`, with
weak determiners only, a DP or KP above it, or either inside a larger phrase such as a PP. -/
inductive Head
  | dP
  | DP
  | KP
  /-- A DP or KP inside a larger phrase. -/
  | inside (h : Head)
  deriving DecidableEq, Repr

/-- The external Head is the indefinite `dP`. -/
def externalHead : Head := .dP

/-! ### Strategies for the internal Head (Chapter 4) -/

/-- The strategies realizing the internal Head. -/
inductive Strategy
  /-- A gap with an invariant relativizer, English *that*, Italian *che*. -/
  | invariantRelativizer
  /-- A relative pronoun or adjective, *who* and *which*, Italian *cui*. -/
  | relativePronoun
  /-- A resumptive pronoun or epithet. -/
  | resumptive
  /-- PRO, in participial relative clauses. -/
  | pro
  /-- Full repetition of the Head. -/
  | nonReduction
  /-- Verb-coding. -/
  | verbCoding
  deriving DecidableEq, Repr

/-- The strategy deletes the internal Head under identity with the external one, the gap with an
invariant relativizer; PRO replaces the Head by a null proform rather than deleting it. -/
def Strategy.DeletesInternalHead (s : Strategy) : Prop := s = .invariantRelativizer

instance (s : Strategy) : Decidable s.DeletesInternalHead := by
  unfold Strategy.DeletesInternalHead; infer_instance

/-- The strategy's NP_rel type in the substrate's inventory, which has no PRO or verb-coding:
PRO as a gap, verb-coding as non-reduction. -/
def Strategy.toNPRelType : Strategy → NPRelType
  | .invariantRelativizer => .gap
  | .relativePronoun => .relPronoun
  | .resumptive => .resumptive
  | .pro => .gap
  | .nonReduction => .nonReduction
  | .verbCoding => .nonReduction

/-! ### Types and merge height (§3.5) -/

/-- The types of relative clause, by increasing height of external merge. -/
inductive RCType
  | participial | maximalizing | restrictive | kindDefining | nonRestrictive
  deriving DecidableEq, Repr

/-- The height of external merge in the nominal extended projection, a bigger external Head
merging higher: maximalizing below restrictive by the refinement of §3.5.5, kind-defining
between restrictive and non-restrictive by §3.5.3. -/
def RCType.mergeHeight : RCType → ℕ
  | .participial => 0
  | .maximalizing => 1
  | .restrictive => 2
  | .kindDefining => 3
  | .nonRestrictive => 4

/-! ### The relative clause -/

/-- A relative clause in the double-headed structure: its type, derivation, internal Head and
the strategy realizing it, the relativized position and the clause's position. -/
structure RC where
  rcType : RCType
  derivation : Derivation
  internalHead : Head
  strategy : Strategy
  position : AHPosition
  rcPosition : RCPosition
  deriving Repr

/-- The overt Head. -/
def RC.overtHead (r : RC) : HeadChoice := r.derivation.overtHead

/-- Reconstruction and island effects are detectable iff the overt Head is the internal one, in
a chain with the clause-internal position. -/
def RC.Reconstructs (r : RC) : Prop := r.overtHead = .internal

instance (r : RC) : Decidable r.Reconstructs := by
  unfold RC.Reconstructs; infer_instance

/-- Deletion under identity: the internal Head may be deleted only when it is an exact match of
the external Head. -/
def RC.WellFormed (r : RC) : Prop :=
  r.strategy.DeletesInternalHead → r.internalHead = externalHead

instance (r : RC) : Decidable r.WellFormed := by
  unfold RC.WellFormed; infer_instance

/-- The framework-neutral realization the derivation projects onto. -/
def RC.realization (r : RC) : Realization := ⟨r.position, r.strategy.toNPRelType⟩

/-- An internal Head bigger than the external `dP` is categorially distinct from it and cannot be
deleted, so it is a wh-pronoun or a resumptive. -/
theorem bigger_head_no_gap_deletion (r : RC) (h : r.WellFormed)
    (hbig : r.internalHead ≠ externalHead) : r.strategy ≠ .invariantRelativizer :=
  fun hs => hbig (h hs)

/-! ### Worked examples -/

/-- *The book that John read*: matching, the internal Head an exact match, deleted under the
invariant relativizer. -/
def englishThatObject : RC :=
  ⟨.restrictive, .matching, .dP, .invariantRelativizer, .directObject, .postNominal⟩

/-- Its realization, a direct-object gap, is what the English Fragment's *that* attests. -/
theorem englishThatObject_attested :
    englishThatObject.WellFormed ∧ ¬ englishThatObject.Reconstructs ∧
      English.relThat.Covers englishThatObject.realization.position ∧
      englishThatObject.realization.npRel = English.relThat.npRel := by
  decide

/-- *The man to whom I spoke*: the internal Head, a DP inside a PP, is bigger than `dP`, so it is
a relative pronoun. -/
def englishWhomOblique : RC :=
  ⟨.restrictive, .matching, .inside .DP, .relativePronoun, .oblique, .postNominal⟩

/-- Its realization, an oblique relative pronoun, is what the English Fragment's *whom*
attests. -/
theorem englishWhomOblique_attested :
    englishWhomOblique.WellFormed ∧
      English.relWhom.Covers englishWhomOblique.realization.position ∧
      englishWhomOblique.realization.npRel = English.relWhom.npRel := by
  decide

/-- Hebrew *she-* with a resumptive at the genitive: the internal Head, a DP inside a DP, is
replaced by a proform. -/
def hebrewResumptiveGenitive : RC :=
  ⟨.restrictive, .matching, .inside .DP, .resumptive, .genitive, .postNominal⟩

/-- Its realization, a genitive resumptive, is what the Hebrew Fragment's *she-* with a pronoun
attests. -/
theorem hebrewResumptiveGenitive_attested :
    hebrewResumptiveGenitive.WellFormed ∧
      Hebrew.relSheResumptive.Covers hebrewResumptiveGenitive.realization.position ∧
      hebrewResumptiveGenitive.realization.npRel = Hebrew.relSheResumptive.npRel := by
  decide

end Cinque2020
