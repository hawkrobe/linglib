/-
# Kratzer & Selkirk (2020): Deconstructing Information Structure

Formalization of Kratzer & Selkirk's two-feature theory of information structure.

## Core Insight

What has traditionally been analyzed as a single [F]-feature (Rooth 1985, 1992;
Schwarzschild 1999) must be decomposed into TWO privative morphosyntactic features:

- **[FoC]** (FoCus): Introduces alternatives, signals contrast via ~ operator
- **[G]** (Givenness): Presupposes discourse salience, signals match

These features have distinct syntactic, semantic, prosodic, and pragmatic properties.
Crucially, there is NO feature for newness: apparent prosodic effects of new material
are the result of default prosody.

## Grounding in Linglib

- [FoC] and [G] both contribute **use-conditional** (expressive) meaning, not at-issue
  content → grounded in `Expressives/Basic.lean` `TwoDimProp`
- [G] is a **contextual presupposition** → grounded in `Core/Presupposition.lean`
- [FoC] introduces **alternatives** → grounded in `Core/Alternatives.lean`
- The ~ operator is [FoC]'s obligatory companion → refines existing `Squiggle`

## Key Formal Results

1. [FoC] and [G] are mutually exclusive (no constituent bears both)
2. Givenness = singleton alternatives set
3. Contrast requires antecedent ∈ alternatives, antecedent ≠ O-value
4. [G] containing [FoC] requires an alternatives-consuming operator inside
5. Spellout ranking: [G]=No-φ >> [FoC]=φ-Level-Head (English)

## References

- Kratzer, A. & Selkirk, E. (2020). Deconstructing information structure.
  Glossa 5(1): 113. DOI: https://doi.org/10.5334/gjgl.968
- Rooth, M. (1992). A Theory of Focus Interpretation. NLS 1: 75-116.
- Schwarzschild, R. (1999). GIVENness, AvoidF, and other constraints on
  the placement of focus. NLS 7: 141-177.
- Potts, C. (2005). The Logic of Conventional Implicatures. OUP.
- Selkirk, E. (2008). Contrastive focus, givenness, and the unmarked
  status of "discourse-new". Acta Linguistica Hungarica 55: 1-16.
- Beaver, D. et al. (2007). When semantics meets phonetics. Language 83: 245-276.
-/

import Linglib.Core.Alternatives
import Linglib.Core.InformationStructure
import Linglib.Core.Prosody
import Linglib.Theories.TruthConditional.Expressives.Basic
import Linglib.Core.Presupposition

open Core.Alternatives
open Core.InformationStructure
open Core.Prosody
open TruthConditional.Expressives
open Core.Presupposition
open Core.Proposition

namespace Theories.TruthConditional.Sentence.Focus.KratzerSelkirk2020

variable {W : Type*} {Entity : Type}

/-! ## §8 (45, 47). Both Features are Use-Conditional

Neither [FoC] nor [G] changes the truth-conditional (at-issue) content of
the expression it attaches to. Both contribute use-conditional / expressive
meaning (Kaplan 1999, Kratzer 2004, Potts 2005, Gutzmann 2015).

This grounds K&S's features in Potts' two-dimensional semantics, already
formalized in `Expressives/Basic.lean`. -/

/-- [FoC] is use-conditional: at-issue content is unchanged.
    Grounded in TwoDimProp from Expressives/Basic.lean. -/
def focAsTwoDim (atIssue : BProp W) (contrastPresup : BProp W) : TwoDimProp W :=
  TwoDimProp.withCI atIssue contrastPresup

/-- [G] is use-conditional: at-issue content is unchanged.
    [G] resembles discourse particles (German "ja", "doch") — it places a
    condition on context salience without affecting truth conditions. -/
def gAsTwoDim (atIssue : BProp W) (givennessPresup : BProp W) : TwoDimProp W :=
  TwoDimProp.withCI atIssue givennessPresup

/-- [FoC] does not change at-issue content (grounding theorem). -/
theorem foc_at_issue_unchanged (atIssue contrastPresup : BProp W) :
    (focAsTwoDim atIssue contrastPresup).atIssue = atIssue := rfl

/-- [G] does not change at-issue content (grounding theorem). -/
theorem g_at_issue_unchanged (atIssue givennessPresup : BProp W) :
    (gAsTwoDim atIssue givennessPresup).atIssue = atIssue := rfl

/-- Both features project their use-conditional content through negation,
    just like conventional implicatures (Potts 2005).

    "It's not the case that [ELIZA]_{FoC} mailed the caramels" still
    contrasts Eliza with alternatives. -/
theorem foc_projects_through_neg (atIssue contrastPresup : BProp W) :
    (TwoDimProp.neg (focAsTwoDim atIssue contrastPresup)).ci
    = (focAsTwoDim atIssue contrastPresup).ci :=
  TwoDimProp.ci_projects_through_neg _

theorem g_projects_through_neg (atIssue givennessPresup : BProp W) :
    (TwoDimProp.neg (gAsTwoDim atIssue givennessPresup)).ci
    = (gAsTwoDim atIssue givennessPresup).ci :=
  TwoDimProp.ci_projects_through_neg _

/-! ## §8 (49). Contrast Representation

An expression α represents a contrast with discourse referent a iff:
(i)   a ∈ ⟦α⟧_{A,C}           — the referent is among the alternatives
(ii)  a ≠ ⟦α⟧_{O,C}           — the referent differs from the actual value
(iii) There is no FoC/G-variant β of α with ⟦β⟧_{A,C} ⊂ ⟦α⟧_{A,C}
      and a ∈ ⟦β⟧_{A,C}       — no smaller alternatives set also captures a

Condition (iii) prevents over-FoCusing (Schwarzschild 1993). -/

/-- Conditions (i) and (ii) of Contrast (K&S 49).
    Condition (iii) — the minimality condition — is structural and requires
    checking FoC/G-variants, which we leave to the prosodic spellout layer. -/
structure Contrast (α : Type) [BEq α] where
  /-- The expression's A-value (alternatives) -/
  aValue : List α
  /-- The expression's O-value (ordinary denotation) -/
  oValue : α
  /-- The contrasting discourse referent -/
  referent : α
  /-- (i): referent is among the alternatives -/
  ref_in_alts : referent ∈ aValue
  /-- (ii): referent differs from the O-value -/
  ref_ne_oValue : (referent == oValue) = false

/-! ## §8 (53-54). The ~ Operator

[FoC]-marked constituents must be c-commanded by a ~ operator.
The ~ operator:
- Takes a set of discourse referents 𝔠 as its contextual variable
- Requires α to represent a contrast with each member of 𝔠
- Stops the propagation of alternatives (consumes them)
- Contributes expressive meaning: the contrast is signaled

Unlike Rooth's original ~ (which allows questions as antecedents),
K&S's ~ always signals contrast. Questions do NOT have a special
direct relation to FoCus. -/

/-- The ~ operator (K&S version, allowing multiple antecedents).

    K&S (54): ⟦~_𝔠 α⟧_{O,C} is defined iff 𝔠 is a set of discourse
    referents in C, and α represents a contrast with each member of 𝔠.

    If defined, ⟦~_𝔠 α⟧_{O,C} = ⟦α⟧_{O,C}
    A-values: ⟦~_𝔠 α⟧_{A,C} = {⟦α⟧_{O,C}} (singleton — alternatives consumed). -/
structure ContrastOperator (α : Type) [BEq α] where
  /-- The expression's meaning -/
  meaning : AltMeaning α
  /-- The contrasting discourse referent(s) -/
  antecedents : List α
  /-- Each antecedent is in the alternatives -/
  antecedents_in_alts : ∀ a ∈ antecedents, a ∈ meaning.aValue
  /-- Each antecedent differs from the O-value -/
  antecedents_ne_oValue : ∀ a ∈ antecedents, (a == meaning.oValue) = false

/-- The ~ operator consumes alternatives: result A-value is singleton. -/
def ContrastOperator.result {α : Type} [BEq α]
    (op : ContrastOperator α) : AltMeaning α :=
  { oValue := op.meaning.oValue, aValue := [op.meaning.oValue] }

/-- ~ preserves O-value. -/
theorem squiggle_preserves_oValue {α : Type} [BEq α] (op : ContrastOperator α) :
    op.result.oValue = op.meaning.oValue := rfl

/-- ~ collapses A-value to singleton. -/
theorem squiggle_singleton_aValue {α : Type} [BEq α] (op : ContrastOperator α) :
    op.result.aValue = [op.meaning.oValue] := rfl

/-! ## §8 (56). The Semantics of *only*

K&S's *only* directly takes a contextual variable 𝔠 (the contrast set),
rather than accessing focus alternatives indirectly:

  ⟦only_𝔠⟧ = λp λw. ∀q. (q ∈ 𝔠 ∧ q(w)) → q = p

The contrast set 𝔠 is supplied by the ~ operator that comes with [FoC].
Since ~ stops alternative propagation, *only* associates with [FoC]
indirectly via a second occurrence of 𝔠. -/

/-- Semantics of *only* with explicit contrast set (K&S 56).
    Takes a contrast set 𝔠 and a prejacent proposition p.
    True at w iff every true member of 𝔠 equals p. -/
def onlySemantics (contrastSet : List (BProp W)) (prejacent : BProp W)
    (w : W) : Bool :=
  contrastSet.all (λ q => !q w || (q w == prejacent w))

/-! ## §8 (58). [G] Containing [FoC] Requires Alternatives Consumption

A constituent α containing [FoC]-marked β can be [G]-marked only if α also
contains an operator that consumes the alternatives generated by β.

Proof: For α to be [G], its A-value must be a singleton {a}. But [FoC] on β
would make α's A-value non-singleton (alternatives propagate upward) UNLESS
some operator inside α (like ~ or *only*) has consumed them.

This explains Second Occurrence Focus: in "the fáculty only quote
[the faculty]_{FoC}", the second "the faculty" is [FoC]-marked but sits
inside a [G]-marked VP. This is possible because *only* + ~ consume
the alternatives before they reach the VP level. -/

/-- After ~ consumption, the result A-value is a singleton,
    which is the precondition for [G]-marking. -/
theorem consumed_alts_enable_g {α : Type} [BEq α] [LawfulBEq α]
    (op : ContrastOperator α) :
    isGiven op.result.aValue op.meaning.oValue = true := by
  show isGiven [op.meaning.oValue] op.meaning.oValue = true
  simp [isGiven]

/-! ## §7. Prosodic Spellout

In Standard American and British English, [FoC] and [G] are spelled out
prosodically at the syntax-phonology interface (MSO → PI mapping).

The architecture has three levels:
- MSO: Morphosyntactic Output (syntactic structure with [FoC]/[G])
- PI: Phonological Input (prosodic constituency)
- PO: Phonological Output (tones, prominence)

Match constraints (MatchWord, MatchPhrase, MatchClause) generate
prosodic constituency in PI from syntactic constituency in MSO.
Then spellout constraints map [FoC] and [G] to prosodic properties. -/

/-- Spellout of [FoC]: maps to head at a prosodic level.
    K&S (34, 43): [FoC] = {ω, φ, ι}-Level-Head.

    A [FoC]-marked constituent in MSO is spelled out as a head at the
    corresponding prosodic level in PI. Being a head in a chain ending
    at ι means being the MOST PROMINENT constituent in the sentence. -/
inductive FoCSpellout where
  /-- [FoC] = ω-Level-Head: head of prosodic word -/
  | ω_level_head
  /-- [FoC] = φ-Level-Head: head of phonological phrase -/
  | φ_level_head
  /-- [FoC] = ι-Level-Head: head of intonational phrase (highest prominence) -/
  | ι_level_head
  deriving DecidableEq, Repr

/-- Spellout of [G]: removes φ constituency (dephrasing).
    K&S (38): [G] = No-φ.

    A [G]-marked constituent in MSO corresponds to a prosodic constituent
    in PI that is NOT a φ and contains no φ. The phonological consequences:
    - No obligatory H accent tone (which requires φ-head status)
    - No L edge tone (which requires φ-final position)

    This replaces the traditional "destressing" analysis with a structural one. -/
structure GSpellout where
  /-- A [G]-marked constituent has no φ in PI -/
  no_phi : Bool := true

/-- K&S (41, 44): When [G] and [FoC] spellout conflict, [G] wins.

    Ranking in Standard American and British English:
      [G]=No-φ >> MatchPhrase >> [FoC]=φ-Level-Head

    This means: dephrasing a [G]-marked constituent takes priority over
    giving a [FoC]-marked constituent φ-level prominence.

    Consequence: Second Occurrence Focus [FoC] inside [G] gets only
    ω-level head status, not φ-level. Hence reduced prosody for SOF. -/
inductive SpelloutRanking where
  /-- [G]=No-φ outranks MatchPhrase -/
  | g_over_match
  /-- MatchPhrase outranks [FoC]=φ-Level-Head -/
  | match_over_foc_phi
  deriving DecidableEq, Repr

/-- The ranking is fixed for Standard American and British English. -/
def englishSpelloutRanking : List SpelloutRanking :=
  [.g_over_match, .match_over_foc_phi]

/-! ## §4, §7.3. Second Occurrence Focus

SOF is the strongest empirical argument for the two-feature system.

Example (Beaver et al. 2007, K&S 42):
  "Both Sid and his accomplices should have been named in this morning's
   court session. But the defendant only named [Síd]_{FoC} in court today."

  MSO: Even [the prosecutor]_{FoC} [only named [Sid]_{FoC} in court today]_{G}

The second "Sid" is [FoC]-marked (it associates with *only*) but sits inside
a [G]-marked constituent. The ranking [G]=No-φ >> [FoC]=φ-Level-Head
predicts: Sid gets ω-level head status but NOT φ-level prominence.
Result: an H accent but no phrase-level pitch scaling — exactly what
Beaver et al. (2007) found experimentally. -/

/-- A Second Occurrence Focus datum: [FoC] inside [G]. -/
structure SOFDatum where
  /-- The full sentence -/
  sentence : String
  /-- The SOF word -/
  sofWord : String
  /-- The operator that consumes SOF's alternatives -/
  consumingOperator : String
  /-- Whether H accent present (yes for SOF) -/
  hasHAccent : Bool
  /-- Whether φ-level prominence present (no for SOF) -/
  hasPhiProminence : Bool
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Beaver et al. (2007) SOF example. -/
def beaverEtAl2007_sid : SOFDatum := {
  sentence := "Even the prosecutor only named Sid in court today"
  sofWord := "Sid"
  consumingOperator := "only"
  hasHAccent := true        -- ω-level head → H accent present
  hasPhiProminence := false -- [G]=No-φ outranks → no φ-level prominence
  source := "Beaver et al. (2007: 256), K&S (42)"
}

/-- Katz & Selkirk (2011) FoC-New vs New-FoC vs New-New triples.
    K&S (36): Phonetic evidence distinguishing [FoC] from newness. -/
structure ProsodicTripleDatum where
  /-- First post-verbal phrase status -/
  firstStatus : DiscourseStatus
  /-- Second post-verbal phrase status -/
  secondStatus : DiscourseStatus
  /-- Description of the pitch pattern -/
  pitchPattern : String
  /-- Source -/
  source : String := ""
  deriving Repr

def katzSelkirk2011_focNew : ProsodicTripleDatum := {
  firstStatus := .focused
  secondStatus := .new
  pitchPattern := "Considerable downstep (⇓H) between phrases"
  source := "Katz & Selkirk (2011), K&S (36a)"
}

def katzSelkirk2011_newFoc : ProsodicTripleDatum := {
  firstStatus := .new
  secondStatus := .focused
  pitchPattern := "Optional small upstep (↑H) on focused phrase"
  source := "Katz & Selkirk (2011), K&S (36b)"
}

def katzSelkirk2011_newNew : ProsodicTripleDatum := {
  firstStatus := .new
  secondStatus := .new
  pitchPattern := "Small default downstep (↓H) between phrases"
  source := "Katz & Selkirk (2011), K&S (36c)"
}

/-! ## §8 (61, 66). Pressure for [G]-Marking and [FoC]-Marking

[G]-marking and [FoC]-marking are obligatory under certain discourse conditions
in Standard American and British English.

(61) Pressure for [G]-Marking:
     [G]-mark a constituent if it is Given w.r.t. a salient discourse referent.

(66) Pressure for [FoC]-Marking:
     Represent non-trivial contrasts with salient discourse referents.

These are not semantic/syntactic constraints but PRAGMATIC pressures,
possibly reducible to Maximize Presuppositions (Heim 1991). -/

/-- Pragmatic pressure for [G]-marking (K&S 61). -/
structure PressureForG where
  /-- The constituent -/
  constituent : String
  /-- The salient discourse referent it matches -/
  referent : String
  /-- Is [G]-marking obligatory here? -/
  obligatory : Bool := true

/-- Pragmatic pressure for [FoC]-marking (K&S 66). -/
structure PressureForFoC where
  /-- The constituent -/
  constituent : String
  /-- The contrasting discourse referent -/
  referent : String
  /-- Would failure to [FoC]-mark violate Pressure for [FoC]-Marking? -/
  faultedIfMissed : Bool := true

/-! ## Bridge: K&S vs Schwarzschild (1999)

Schwarzschild's "A-Givenness" (within Rooth's Alternatives Semantics)
falls out as a special case of K&S's [G]-feature.

A-Givenness: α is A-Given in C iff there is a salient discourse referent
that is a member of ⟦α⟧_{A,C}.

K&S's Givenness (46): α is Given w.r.t. a iff ⟦α⟧_{A,C} = {a}.

K&S's condition is STRONGER (singleton vs membership). The old A-Givenness
condition was too weak — Schwarzschild noted it was trivially satisfiable
for universal quantifiers (every cat is a complainer → trivially A-Given). -/

/-- Schwarzschild's A-Givenness: some referent is in the alternatives set. -/
def isAGiven {α : Type} [BEq α] (aValue : List α) (referent : α) : Bool :=
  aValue.any (· == referent)

/-- K&S Givenness entails Schwarzschild A-Givenness.
    If the alternatives set is a singleton {a}, then certainly a ∈ alternatives. -/
theorem givenness_entails_aGivenness {α : Type} [BEq α] [LawfulBEq α]
    (aValue : List α) (referent : α)
    (h : isGiven aValue referent = true) :
    isAGiven aValue referent = true := by
  cases aValue with
  | nil => simp [isGiven] at h
  | cons a tl =>
    cases tl with
    | nil => simp [isGiven] at h; simp [isAGiven, List.any]; exact h
    | cons _ _ => simp [isGiven] at h

/-- The converse fails: A-Givenness does NOT entail K&S Givenness.
    A non-singleton alternatives set can satisfy A-Givenness but not Givenness.

    This is the Schwarzschild overgeneration problem (K&S fn. 14):
    "Every cat is a complainer" is trivially A-Given because ∃P[every P
    is a complainer] is always true. K&S's singleton condition avoids this. -/
theorem aGivenness_not_sufficient : ∃ (aValue : List Nat) (referent : Nat),
    isAGiven aValue referent = true ∧ isGiven aValue referent = false := by
  exact ⟨[1, 2], 1, by native_decide, by native_decide⟩

end Theories.TruthConditional.Sentence.Focus.KratzerSelkirk2020
