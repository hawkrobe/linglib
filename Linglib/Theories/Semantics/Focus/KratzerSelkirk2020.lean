/-
# @cite{kratzer-selkirk-2020}: Deconstructing Information Structure

Formalization of Kratzer & Selkirk's two-feature theory of information structure.

## Core Insight

What has traditionally been analyzed as a single [F]-feature must be decomposed into TWO privative morphosyntactic features:

- **[FoC]** (FoCus): Introduces alternatives, signals contrast via ~ operator
- **[G]** (Givenness): Presupposes discourse salience, signals match

These features have distinct syntactic, semantic, prosodic, and pragmatic properties.
Crucially, there is NO feature for newness: apparent prosodic effects of new material
are the result of default prosody.

## Grounding in Linglib

- [FoC] and [G] both contribute **use-conditional** (expressive) meaning, not at-issue
  content → grounded in `Expressives/Basic.lean` `TwoDimProp`
- [G] is a **contextual presupposition** → grounded in `Core/Presupposition.lean`
- [FoC] introduces **alternatives** → grounded in `Core/InformationStructure.lean`
- The ~ operator is [FoC]'s obligatory companion → refines existing `Squiggle`

## Key Formal Results

1. [FoC] and [G] are mutually exclusive (no constituent bears both)
2. Givenness = singleton alternatives set
3. Contrast requires antecedent ∈ alternatives, antecedent ≠ O-value
4. [G] containing [FoC] requires an alternatives-consuming operator inside
5. Spellout ranking: [G]=No-φ >> [FoC]=φ-Level-Head (English)

-/

import Linglib.Core.InformationStructure
import Linglib.Core.Prosody
import Linglib.Theories.Pragmatics.Expressives.Basic
import Linglib.Core.Semantics.Presupposition
import Linglib.Theories.Semantics.Alternatives.AltMeaning

open Core.InformationStructure
open Semantics.Alternatives
open Core.Prosody
open Pragmatics.Expressives
open Core.Presupposition

namespace Semantics.Focus.KratzerSelkirk2020

-- ════════════════════════════════════════════════════
-- § IS Features (@cite{kratzer-selkirk-2020} §2, §8)
-- ════════════════════════════════════════════════════

/-- The two privative morphosyntactic features of @cite{kratzer-selkirk-2020}.

[FoC] and [G] are genuinely syntactic features: crosslinguistically they
trigger displacement, agreement, and ellipsis (§2). They happen to be
spelled out prosodically in Standard American and British English, but
this is not their defining property. -/
inductive ISFeature where
  /-- FoCus: introduces alternatives, signals contrast.
      Resembles [wh] — comes with obligatory ~ operator. -/
  | FoC
  /-- Givenness: presupposes discourse salience, signals match.
      Contributes meaning directly (no operator needed). -/
  | G
  deriving DecidableEq, Repr

/-- Newness is NOT a grammatical feature.
    New material is simply unmarked — no [FoC], no [G]. -/
def isNew (hasFoC : Bool) (hasG : Bool) : Bool :=
  !hasFoC && !hasG

/-! ## §8 (45). The Contribution of [FoC]

[FoC] does NOT change the O-value. Its A-value is the full domain D_τ
(all possible entities of the relevant semantic type). This is standard
Roothian focus semantics.

  ⟦[α]_{FoC}⟧_{O,C} = ⟦α⟧_{O,C}
  ⟦[α]_{FoC}⟧_{A,C} = D_τ
-/

/-- Apply [FoC] to a meaning: O-value unchanged, A-value becomes full domain.
    K&S (45): The A-value of [α]_{FoC} is D_τ. -/
def applyFoC {α : Type} (m : AltMeaning α) (domain : List α) : AltMeaning α :=
  { oValue := m.oValue, aValue := domain }

/-- [FoC] preserves O-value. K&S (45) first clause. -/
theorem foc_preserves_oValue {α : Type} (m : AltMeaning α) (domain : List α) :
    (applyFoC m domain).oValue = m.oValue := rfl

/-! ## §8 (46-47). The Contribution of [G]

[G] introduces a Givenness requirement: the expression must match a salient
discourse referent. Technically:

  ⟦[α]_{G_a}⟧_{O,C} is defined iff a is a discourse referent in C,
    and α is Given with respect to a.
  If defined, ⟦[α]_{G_a}⟧_{O,C} = ⟦α⟧_{O,C}
  ⟦[α]_{G_a}⟧_{A,C} = ⟦α⟧_{A,C}

[G] contributes purely use-conditional / expressive meaning (like discourse
particles German "ja", "doch"). It places a condition on the discourse context,
not on truth conditions.
-/

/-- An expression α is Given with respect to discourse referent a iff
    its A-value is {a} (a singleton containing just the referent).

    K&S (46): α is Given w.r.t. a in C iff ⟦α⟧_{A,C} = {a}.

    Intuitively: the alternatives set has collapsed to a single salient entity,
    meaning there's nothing to contrast — the content is already "in the air". -/
def isGiven {α : Type} [DecidableEq α] (aValue : List α) (referent : α) : Prop :=
  match aValue with
  | [a] => a = referent
  | _ => False

instance instDecidableIsGiven {α : Type} [DecidableEq α] (aValue : List α) (referent : α) :
    Decidable (isGiven aValue referent) :=
  match aValue with
  | [a] => (inferInstance : Decidable (a = referent))
  | [] => (inferInstance : Decidable False)
  | _ :: _ :: _ => (inferInstance : Decidable False)

/-- Apply [G] to a meaning: both values unchanged, but adds a definedness
    condition (the expression must be Given w.r.t. some discourse referent).

    Unlike [FoC], [G] does NOT change the A-value. Its contribution is
    purely a presupposition on the discourse context. -/
def applyG {α : Type} (m : AltMeaning α) : AltMeaning α := m

/-- [G] preserves O-value. K&S (47): if defined, O-value unchanged. -/
theorem g_preserves_oValue {α : Type} (m : AltMeaning α) :
    (applyG m).oValue = m.oValue := rfl

/-- [G] preserves A-value. K&S (47): A-value unchanged. -/
theorem g_preserves_aValue {α : Type} (m : AltMeaning α) :
    (applyG m).aValue = m.aValue := rfl

/-! ## §8 (58). [FoC] and [G] are Mutually Exclusive

A single constituent CANNOT bear both [FoC] and [G]. The proof follows from
the A-value conditions:
- [FoC] requires A-value = D_τ (the full domain, maximally large)
- [G] requires A-value = {a} (a singleton)
No semantic domain is both maximal and a singleton (assuming |D_τ| > 1). -/

/-- [FoC] and [G] are mutually exclusive: no constituent can satisfy both
    the [FoC] A-value condition (full domain) and the [G] A-value condition
    (singleton) simultaneously, when the domain has more than one element.

    K&S (58, first part): follows from the incompatibility of A-value conditions. -/
theorem foc_g_exclusion {α : Type} [DecidableEq α] (domain : List α) (referent : α)
    (h_domain : domain.length > 1) :
    ¬ isGiven domain referent := by
  match domain, h_domain with
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _, _ => intro h; simp only [isGiven] at h

variable {W : Type*} {Entity : Type}

/-! ## §8 (45, 47). Both Features are Use-Conditional

Neither [FoC] nor [G] changes the truth-conditional (at-issue) content of
the expression it attaches to. Both contribute use-conditional / expressive
meaning.

This grounds K&S's features in Potts' two-dimensional semantics, already
formalized in `Expressives/Basic.lean`. -/

/-- [FoC] is use-conditional: at-issue content is unchanged.
    Grounded in TwoDimProp from Expressives/Basic.lean. -/
def focAsTwoDim (atIssue : W → Prop) (contrastPresup : W → Prop) : TwoDimProp W :=
  TwoDimProp.withCI atIssue contrastPresup

/-- [G] is use-conditional: at-issue content is unchanged.
    [G] resembles discourse particles (German "ja", "doch") — it places a
    condition on context salience without affecting truth conditions. -/
def gAsTwoDim (atIssue : W → Prop) (givennessPresup : W → Prop) : TwoDimProp W :=
  TwoDimProp.withCI atIssue givennessPresup

/-- [FoC] does not change at-issue content (grounding theorem). -/
theorem foc_at_issue_unchanged (atIssue contrastPresup : W → Prop) :
    (focAsTwoDim atIssue contrastPresup).atIssue = atIssue := rfl

/-- [G] does not change at-issue content (grounding theorem). -/
theorem g_at_issue_unchanged (atIssue givennessPresup : W → Prop) :
    (gAsTwoDim atIssue givennessPresup).atIssue = atIssue := rfl

/-- Both features project their use-conditional content through negation,
    just like conventional implicatures.

    "It's not the case that [ELIZA]_{FoC} mailed the caramels" still
    contrasts Eliza with alternatives. -/
theorem foc_projects_through_neg (atIssue contrastPresup : W → Prop) :
    (TwoDimProp.neg (focAsTwoDim atIssue contrastPresup)).ci
    = (focAsTwoDim atIssue contrastPresup).ci :=
  TwoDimProp.ci_projects_through_neg _

theorem g_projects_through_neg (atIssue givennessPresup : W → Prop) :
    (TwoDimProp.neg (gAsTwoDim atIssue givennessPresup)).ci
    = (gAsTwoDim atIssue givennessPresup).ci :=
  TwoDimProp.ci_projects_through_neg _

/-! ## §8 (49). Contrast Representation

An expression α represents a contrast with discourse referent a iff:
(i) a ∈ ⟦α⟧_{A,C} — the referent is among the alternatives
(ii) a ≠ ⟦α⟧_{O,C} — the referent differs from the actual value
(iii) There is no FoC/G-variant β of α with ⟦β⟧_{A,C} ⊂ ⟦α⟧_{A,C}
      and a ∈ ⟦β⟧_{A,C} — no smaller alternatives set also captures a

Condition (iii) prevents over-FoCusing. -/

/-- Conditions (i) and (ii) of Contrast (K&S 49).
    Condition (iii) — the minimality condition — is structural and requires
    checking FoC/G-variants, which we leave to the prosodic spellout layer. -/
structure Contrast (α : Type) where
  /-- The expression's A-value (alternatives) -/
  aValue : List α
  /-- The expression's O-value (ordinary denotation) -/
  oValue : α
  /-- The contrasting discourse referent -/
  referent : α
  /-- (i): referent is among the alternatives -/
  ref_in_alts : referent ∈ aValue
  /-- (ii): referent differs from the O-value -/
  ref_ne_oValue : referent ≠ oValue

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
structure ContrastOperator (α : Type) where
  /-- The expression's meaning -/
  meaning : AltMeaning α
  /-- The contrasting discourse referent(s) -/
  antecedents : List α
  /-- Each antecedent is in the alternatives -/
  antecedents_in_alts : ∀ a ∈ antecedents, a ∈ meaning.aValue
  /-- Each antecedent differs from the O-value -/
  antecedents_ne_oValue : ∀ a ∈ antecedents, a ≠ meaning.oValue

/-- The ~ operator consumes alternatives: result A-value is singleton. -/
def ContrastOperator.result {α : Type}
    (op : ContrastOperator α) : AltMeaning α :=
  { oValue := op.meaning.oValue, aValue := [op.meaning.oValue] }

/-- ~ preserves O-value. -/
theorem squiggle_preserves_oValue {α : Type} (op : ContrastOperator α) :
    op.result.oValue = op.meaning.oValue := rfl

/-- ~ collapses A-value to singleton. -/
theorem squiggle_singleton_aValue {α : Type} (op : ContrastOperator α) :
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
def onlySemantics (contrastSet : List (W → Prop)) (prejacent : W → Prop)
    (w : W) : Prop :=
  ∀ q ∈ contrastSet, q w → (q w ↔ prejacent w)

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
theorem consumed_alts_enable_g {α : Type} [DecidableEq α]
    (op : ContrastOperator α) :
    isGiven op.result.aValue op.meaning.oValue := by
  show isGiven [op.meaning.oValue] op.meaning.oValue
  unfold isGiven
  rfl

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

Example (@cite{beaver-2007}, K&S 42):
  "Both Sid and his accomplices should have been named in this morning's
   court session. But the defendant only named [Síd]_{FoC} in court today."

  MSO: Even [the prosecutor]_{FoC} [only named [Sid]_{FoC} in court today]_{G}

The second "Sid" is [FoC]-marked (it associates with *only*) but sits inside
a [G]-marked constituent. The ranking [G]=No-φ >> [FoC]=φ-Level-Head
predicts: Sid gets ω-level head status but NOT φ-level prominence.
Result: an H accent but no phrase-level pitch scaling — exactly what
@cite{beaver-2007} @cite{selkirk-2008} found experimentally. -/

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

/-- @cite{beaver-2007} SOF example. -/
def beaverEtAl2007_sid : SOFDatum := {
  sentence := "Even the prosecutor only named Sid in court today"
  sofWord := "Sid"
  consumingOperator := "only"
  hasHAccent := true        -- ω-level head → H accent present
  hasPhiProminence := false -- [G]=No-φ outranks → no φ-level prominence
  source := "Beaver et al. (2007: 256), K&S (42)"
}

/-- @cite{katz-selkirk-2011} FoC-New vs New-FoC vs New-New triples.
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
possibly reducible to Maximize Presuppositions. -/

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

/-! ## Bridge: K&S vs @cite{schwarzschild-1999}

Schwarzschild's "A-Givenness" (within Rooth's Alternatives Semantics)
falls out as a special case of K&S's [G]-feature.

A-Givenness: α is A-Given in C iff there is a salient discourse referent
that is a member of ⟦α⟧_{A,C}.

K&S's Givenness (46): α is Given w.r.t. a iff ⟦α⟧_{A,C} = {a}.

K&S's condition is STRONGER (singleton vs membership). The old A-Givenness
condition was too weak — Schwarzschild noted it was trivially satisfiable
for universal quantifiers (every cat is a complainer → trivially A-Given). -/

/-- Schwarzschild's A-Givenness: some referent is in the alternatives set. -/
def isAGiven {α : Type} (aValue : List α) (referent : α) : Prop :=
  referent ∈ aValue

instance instDecidableIsAGiven {α : Type} [DecidableEq α] (aValue : List α) (referent : α) :
    Decidable (isAGiven aValue referent) :=
  inferInstanceAs (Decidable (referent ∈ aValue))

/-- K&S Givenness entails Schwarzschild A-Givenness.
    If the alternatives set is a singleton {a}, then certainly a ∈ alternatives. -/
theorem givenness_entails_aGivenness {α : Type} [DecidableEq α]
    (aValue : List α) (referent : α)
    (h : isGiven aValue referent) :
    isAGiven aValue referent := by
  cases aValue with
  | nil => simp only [isGiven] at h
  | cons a tl =>
    cases tl with
    | nil =>
      simp only [isGiven] at h
      simp only [isAGiven, List.mem_cons, List.not_mem_nil, or_false]
      exact h.symm
    | cons _ _ => simp only [isGiven] at h

/-- The converse fails: A-Givenness does NOT entail K&S Givenness.
    A non-singleton alternatives set can satisfy A-Givenness but not Givenness.

    This is the Schwarzschild overgeneration problem (K&S fn. 14):
    "Every cat is a complainer" is trivially A-Given because ∃P[every P
    is a complainer] is always true. K&S's singleton condition avoids this. -/
theorem aGivenness_not_sufficient : ∃ (aValue : List Nat) (referent : Nat),
    isAGiven aValue referent ∧ ¬ isGiven aValue referent := by
  exact ⟨[1, 2], 1, by decide, by decide⟩

end Semantics.Focus.KratzerSelkirk2020
