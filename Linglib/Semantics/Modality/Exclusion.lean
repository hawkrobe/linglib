import Linglib.Semantics.Context.Tower
import Linglib.Semantics.Context.Shifts
import Linglib.Semantics.Mood.Basic

/-!
# Exclusion features and X/O-marking strategies

[iatridou-2000] [von-fintel-iatridou-2023] [anderson-1951]
[schlenker-2004] [mizuno-2024]

Framework primitives for the **Exclusion Feature** analysis of past
morphology ([iatridou-2000]) and the **X-marking / O-marking** typology
of counterfactuality ([von-fintel-iatridou-2023]). Paper-specific
typologies and empirical claims live in the corresponding `Studies/`
files:

- `Studies/Iatridou2000.lean` —
  `IatridouPredType` / `CounterfactualType` / `classifyCounterfactual`
  (FLV/PresCF/PastCF taxonomy) and the tower-bridge theorems
  consuming `ExclF`
- `Studies/Mizuno2024.lean` —
  Anderson-conditional empirical observations (English X-marking,
  Japanese/Mandarin O-marking, FLV correlation)

## Core claims

Past morphology encodes **exclusion** ([iatridou-2000]):
- **Temporal**: T(topic) ≠ T(speaker)
- **Modal**: w(topic) ≠ w(speaker)

This maps onto the `ContextTower`'s `origin` / `innermost` distinction —
[schlenker-2004]'s Context of Thought θ (= `tower.origin`) vs Context of
Utterance υ (= `tower.innermost`): `ExclF dim tower` holds iff the
relevant coordinate of `tower.innermost` differs from that of
`tower.origin`. At a root tower the two coincide, so no `ExclF` holds;
a subjunctive shift produces the modal feature and a temporal shift the
temporal one (`subjShift_produces_modal_exclF`,
`temporalShift_produces_temporal_exclF`).

The **X-marking / O-marking** distinction ([von-fintel-iatridou-2023])
is the typological label for whether a language uses counterfactual
morphology (X-marking) or some other strategy (O-marking, e.g., the
Japanese Historical Present of [mizuno-2024]) to grammatically
distinguish live from non-live possibilities.
-/

namespace Semantics.Modality.Exclusion

open Semantics.Context (KContext ContextTower temporalShift)
open Semantics.Mood (subjShift)

/-! ### ExclF: the exclusion feature -/

/-- The two dimensions along which past morphology can exclude.

[iatridou-2000]'s key insight: past morphology has a single
semantic contribution (exclusion) that applies to different dimensions.
The temporal/modal ambiguity of "past" is not lexical ambiguity — it
is the same feature targeting different coordinates. -/
inductive ExclDimension where
  /-- Temporal: T(topic) ≠ T(speaker) -/
  | temporal
  /-- Modal: w(topic) ≠ w(speaker) -/
  | modal
  deriving DecidableEq, Repr

variable {W : Type*} {E : Type*} {P : Type*} {T : Type*}

/-- The Exclusion Feature: past morphology signals that the topic
coordinate differs from the speaker coordinate on the given dimension.

This is a predicate over context towers: `ExclF dim tower` holds iff
the relevant coordinate of the innermost context (topic) differs from
the origin context (speaker). At a root tower innermost and origin
coincide, so neither dimension's feature holds. -/
def ExclF (dim : ExclDimension) (tower : ContextTower (KContext W E P T)) : Prop :=
  match dim with
  | .temporal => tower.innermost.time ≠ tower.origin.time
  | .modal    => tower.innermost.world ≠ tower.origin.world

/-! ### Shifts produce ExclF -/

/-- `subjShift` changes world → produces modal ExclF.

When a subjunctive clause introduces a new world that differs from the
origin, the resulting tower has modal ExclF. This is the tower-level
formalization of [iatridou-2000]'s claim that counterfactual
morphology signals world exclusion. -/
theorem subjShift_produces_modal_exclF (c : KContext W E P T) (w' : W) (t' : T)
    (h : w' ≠ c.world) :
    ExclF .modal ((ContextTower.root c).push (subjShift w' t')) :=
  h

/-- `temporalShift` changes time → produces temporal ExclF.

When an embedding shifts the evaluation time away from the speech time,
the resulting tower has temporal ExclF. This is ordinary temporal past. -/
theorem temporalShift_produces_temporal_exclF (c : KContext W E P T) (t' : T)
    (h : t' ≠ c.time) :
    ExclF .temporal ((ContextTower.root c).push (temporalShift t')) :=
  h

/-- Two shifts → both ExclFs: a subjunctive (world) shift followed by a
temporal one yields modal and temporal exclusion together — the PastCF
configuration of [iatridou-2000] (two past layers). -/
theorem two_shifts_two_exclFs (c : KContext W E P T) (w' : W) (t' t'' : T)
    (hw : w' ≠ c.world) (ht : t'' ≠ c.time) :
    ExclF .modal (((ContextTower.root c).push (subjShift w' t')).push (temporalShift t'')) ∧
      ExclF .temporal (((ContextTower.root c).push (subjShift w' t')).push (temporalShift t'')) :=
  ⟨hw, ht⟩

/-! ### X-marking / O-marking typology ([von-fintel-iatridou-2023]) -/

/-- The two crosslinguistic strategies for grammatically distinguishing
live from non-live possibilities ([von-fintel-iatridou-2023]'s
typological label).

Used by [mizuno-2024] to characterize how different languages
express Anderson conditionals: English uses X-marking (counterfactual
morphology), Japanese uses O-marking (Non-Past + Historical Present). -/
inductive MarkingStrategy where
  /-- X-marking: counterfactual morphology expands the domain from D
      to D⁺. English ([mizuno-2024], ex. 1a): "If Jones *had taken*
      arsenic last night, he *would* show those symptoms which he is
      now showing." -/
  | xMarking
  /-- O-marking: the absence of X-marking. In Japanese Anderson
      conditionals, Non-Past morphology triggers a perspectival shift
      analogous to the Historical Present ([schlenker-2004]); the
      backward time shift expands the domain under branching time,
      avoiding triviality without counterfactual morphology.
      Japanese ([mizuno-2024], ex. 4a): "Jones-si-ga ... nom-*eba*,
      ... mise-*ru* hazuda." -/
  | oMarking
  deriving DecidableEq, Repr

/-- X-marking strategy uses counterfactual morphology; O-marking does
    not. -/
def MarkingStrategy.hasXMarking : MarkingStrategy → Bool
  | .xMarking => true
  | .oMarking => false

/-- The complementary marking strategy. O-marking "is generally defined
    as the absence of X-marking" ([mizuno-2024], §2), so the two
    strategies complement each other: in a minimal pair, the alternative
    realizes the `other` of the attested strategy. -/
def MarkingStrategy.other : MarkingStrategy → MarkingStrategy
  | .xMarking => .oMarking
  | .oMarking => .xMarking

@[simp]
theorem MarkingStrategy.other_other : ∀ s : MarkingStrategy, s.other.other = s
  | .xMarking | .oMarking => rfl

/-! ### X-marking exponents ([von-fintel-iatridou-2023] §2, "The form") -/

/-- The morphological material realizing X-marking. [von-fintel-iatridou-2023]
(§2) divide languages into those with *dedicated* X-morphology and those whose
exponents have other functions — "past tense, imperfective, future and/or
subjunctive"; [mizuno-2024] (§4.2) extends the inventory with the Mandarin
perfective. -/
inductive XMarkingHost where
  /-- Dedicated X-morphology with no other use (Hungarian -nA). -/
  | dedicated
  /-- Fake past ([iatridou-2000]; English, Greek, Romance). -/
  | past
  /-- Fake imperfective (Greek, Romance). -/
  | imperfective
  /-- Future / woll (English would; the Greek and Romance consequent). -/
  | future
  /-- Past subjunctive (German, Icelandic). -/
  | subjunctive
  /-- Perfective ([mizuno-2024], §4.2: Mandarin consequent-final le). -/
  | perfective
  deriving DecidableEq, Repr

/-- A language's X-marking exponent: its citation form and its (possibly
complex — [von-fintel-iatridou-2023] §2: Greek combines fake past with fake
imperfective) morphological components. Per-language entries live in
`Fragments/{Language}/Conditionals.lean` as `Option`-valued `xMarking`
projections; [von-fintel-iatridou-2023]'s total-uniformity hypothesis
(p. 1471) includes the bet that every language has one. -/
structure XMarkingExponent where
  form : String
  components : List XMarkingHost
  deriving DecidableEq, Repr

end Semantics.Modality.Exclusion
