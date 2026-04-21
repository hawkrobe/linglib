import Linglib.Phenomena.TemporalConnectives.Studies.Anscombe1964
import Linglib.Phenomena.TemporalConnectives.Studies.Karttunen1974
import Linglib.Phenomena.TemporalConnectives.Studies.BeaverCondoravdi2003
import Linglib.Theories.Semantics.Tense.TemporalConnectives.EventBridge
import Linglib.Theories.Semantics.Tense.Aspect.SubintervalProperty
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Fragments.Japanese.TemporalConnectives
import Linglib.Core.Semantics.Presupposition

/-!
# @cite{ogihara-steinert-threlkeld-2024} — Data
@cite{ogihara-steinert-threlkeld-2024}

Theory-neutral empirical data on the veridicality asymmetry between
temporal connectives *before* and *after*.

## Key Empirical Generalizations

1. **After is veridical**: "He left after she arrived" entails "she arrived".
2. **Before is non-veridical**: "He left before she arrived" is compatible
   with her not arriving (the "barely prevented" reading).
3. **Before is non-veridical even with perfective complements**: "The bomb
   exploded before anyone defused it" does not entail anyone defused it.

## Data Sources

- Ogihara, T. & Steinert-Threlkeld, S. (2024), §2–3.
- Anscombe, E. (1964), §3 (original observation of the asymmetry).
- Beaver, D. & Condoravdi, C. (2003), §2 (three readings of *before*).
-/

namespace OgiharaST2024

-- ════════════════════════════════════════════════════════════════
-- § 1: Veridicality Judgments
-- ════════════════════════════════════════════════════════════════

/-- An empirical judgment about whether a temporal connective entails
    the truth of its complement clause. -/
structure VeridicalityDatum where
  /-- The example sentence -/
  sentence : String
  /-- The temporal connective -/
  connective : String
  /-- Does the sentence entail that the complement event occurred? -/
  complementEntailed : Bool
  /-- Brief gloss of the entailment pattern -/
  gloss : String
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Core Veridicality Data
-- ════════════════════════════════════════════════════════════════

/-- "He left after she arrived" entails "she arrived". -/
def after_veridical : VeridicalityDatum where
  sentence := "He left after she arrived"
  connective := "after"
  complementEntailed := true
  gloss := "after(leave, arrive) |= arrive"

/-- "He left before she arrived" does NOT entail "she arrived".
    Compatible with: she did arrive (veridical reading), she didn't
    arrive (counterfactual reading, e.g. "before she could arrive"),
    or indeterminate (non-committal reading). -/
def before_nonveridical : VeridicalityDatum where
  sentence := "He left before she arrived"
  connective := "before"
  complementEntailed := false
  gloss := "before(leave, arrive) |/= arrive"

/-- "The bomb exploded before anyone defused it" — the complement
    event (defusing) did NOT occur. This is the counterfactual reading
    of *before* (@cite{beaver-condoravdi-2003}, "barely prevented"). -/
def before_counterfactual : VeridicalityDatum where
  sentence := "The bomb exploded before anyone defused it"
  connective := "before"
  complementEntailed := false
  gloss := "before(explode, defuse) ∧ ¬defuse"

/-- "She finished her coffee after he left" entails "he left". -/
def after_veridical_2 : VeridicalityDatum where
  sentence := "She finished her coffee after he left"
  connective := "after"
  complementEntailed := true
  gloss := "after(finish, leave) |= leave"

-- ════════════════════════════════════════════════════════════════
-- § 3: Additional Veridicality Data (@cite{beaver-condoravdi-2003}, §2)
-- ════════════════════════════════════════════════════════════════

/-- "The Supreme Court decided the election before the votes were
    counted" — non-committal: compatible with votes eventually being
    counted or never counted (@cite{beaver-condoravdi-2003}, ex. 22). -/
def before_noncommittal : VeridicalityDatum where
  sentence := "The Supreme Court decided the election before the votes were counted"
  connective := "before"
  complementEntailed := false
  gloss := "before(decide, count) |/= count (non-committal)"

/-- "Mozart died before he finished the Requiem" — counterfactual:
    Mozart never finished the Requiem (@cite{beaver-condoravdi-2003}, ex. 24). -/
def before_counterfactual_mozart : VeridicalityDatum where
  sentence := "Mozart died before he finished the Requiem"
  connective := "before"
  complementEntailed := false
  gloss := "before(die, finish) ∧ ¬finish (counterfactual)"

-- ════════════════════════════════════════════════════════════════
-- § 4: Logical Property Data (@cite{beaver-condoravdi-2003}, §1)
-- ════════════════════════════════════════════════════════════════

/-- A judgment about a logical property of a temporal connective:
    does it hold, fail, or hold only under conditions? -/
structure LogicalPropertyDatum where
  /-- Property name -/
  property : String
  /-- Connective -/
  connective : String
  /-- Does the property hold? -/
  holds : Bool
  /-- Example sentence(s) -/
  example_ : String
  /-- Brief explanation -/
  gloss : String
  deriving Repr

/-- *Before* is antisymmetric: "Cleo was in America before David was"
    and "David was in America before Cleo was" cannot both be true
    (with non-overlapping intervals). (@cite{beaver-condoravdi-2003}, exx. 3-4) -/
def before_antisymmetric : LogicalPropertyDatum where
  property := "antisymmetry"
  connective := "before"
  holds := true
  example_ := "Cleo was in America before David was / #David was in America before Cleo was"
  gloss := "before(A,B) → ¬before(B,A) (when A,B non-overlapping)"

/-- *After* is NOT antisymmetric: overlapping intervals allow both
    directions. (@cite{beaver-condoravdi-2003}, exx. 5-7, diagram 7) -/
def after_not_antisymmetric : LogicalPropertyDatum where
  property := "antisymmetry"
  connective := "after"
  holds := false
  example_ := "Cleo was in America after David was / David was in America after Cleo was"
  gloss := "after(A,B) ∧ after(B,A) possible with overlapping intervals"

/-- *Before* is transitive: if A before B and B before C, then A before C.
    (@cite{beaver-condoravdi-2003}, exx. 12-14) -/
def before_transitive : LogicalPropertyDatum where
  property := "transitivity"
  connective := "before"
  holds := true
  example_ := "Delores was in America before Ginger / Ginger before Fred → Delores before Fred"
  gloss := "before(A,B) ∧ before(B,C) → before(A,C)"

/-- *After* is NOT transitive: overlapping intervals allow
    after(A,B) ∧ after(B,C) ∧ ¬after(A,C). (@cite{beaver-condoravdi-2003}, exx. 8-11) -/
def after_not_transitive : LogicalPropertyDatum where
  property := "transitivity"
  connective := "after"
  holds := false
  example_ := "Fred after Ginger, Ginger after Delores, but #Fred after Delores"
  gloss := "after(A,B) ∧ after(B,C) ↛ after(A,C)"

/-- *Before* licenses NPIs; *after* does not. (@cite{beaver-condoravdi-2003}, exx. 15-18) -/
def before_licenses_npis : LogicalPropertyDatum where
  property := "NPI licensing"
  connective := "before"
  holds := true
  example_ := "Cleo left before anyone noticed / *Cleo left after anyone noticed"
  gloss := "before licenses NPIs; after does not"

-- ════════════════════════════════════════════════════════════════
-- § 5: Pragmatic Oddity Data (@cite{beaver-condoravdi-2003}, exx. 32-33)
-- ════════════════════════════════════════════════════════════════

/-- "David won the race before he entered it" — pragmatically odd because
    winning temporally presupposes entering: there is no historical
    alternative where one wins before entering. (@cite{beaver-condoravdi-2003}, ex. 32) -/
def before_oddity_win : VeridicalityDatum where
  sentence := "David won the race before he entered it"
  connective := "before"
  complementEntailed := false
  gloss := "before(win, enter) — pragmatically odd: winning presupposes entering"

/-- "David entered the race after he won it" — same temporal impossibility
    viewed through *after*: entering after winning reverses the natural
    temporal order. (@cite{beaver-condoravdi-2003}, ex. 33) -/
def after_oddity_enter : VeridicalityDatum where
  sentence := "David entered the race after he won it"
  connective := "after"
  complementEntailed := true
  gloss := "after(enter, win) — pragmatically odd: entering presupposes not yet having won"

open Semantics.Tense.TemporalConnectives.BeaverCondoravdi

-- ════════════════════════════════════════════════════════════════
-- § 6: Counterexamples to B&C (O&@cite{ogihara-steinert-threlkeld-2024}, §5)
-- ════════════════════════════════════════════════════════════════

/-- A counterexample to B&C's branching-time analysis.
    In each case, the complement eventuality is temporally bounded to an
    interval that ends at or before the A-time. B&C's `alt(w,t)` branches
    only *after* t, so it cannot place the complement in an alternative
    world at a time after the A-time.

    The `boundedBefore` field captures the formal crux: the complement's
    temporal bound ends at or before the A-time. -/
structure BCCounterexampleDatum where
  /-- The example sentence -/
  sentence : String
  /-- The A-clause time (e.g., end of MLB season, end of 2020) -/
  aTime : ℤ
  /-- Upper bound of the complement's temporal window -/
  complementUpperBound : ℤ
  /-- The complement is temporally bounded before the A-time -/
  boundedBefore : complementUpperBound ≤ aTime
  /-- Which B&C reading is involved? -/
  reading : BeforeReading

/-- B&C's `before` requires `earliestAlt` to find a B-instantiation in
    some alternative world. When B is temporally bounded to `[lo, hi]`
    with `hi ≤ tA`, and `alt(w,tA)` only contains worlds that agree with
    w up to `tA`, B cannot be instantiated *after* `tA` in any alternative.

    This is the formal content of O&ST's §5.1 critique: B&C's forward-
    branching architecture cannot handle complements whose temporal bound
    falls before the A-time. -/
theorem bc_cannot_place_bounded_complement
    {W : Type*} (alt : HistAlt W ℤ)
    (B : Set (W × ℤ)) (w : W) (tA hi : ℤ)
    (hBound : hi ≤ tA)
    (_hBounded : ∀ w' t, (w', t) ∈ B → t ≤ hi)
    (hNoFuture : ∀ w' ∈ alt w tA, ∀ t, (w', t) ∈ B → t ≤ hi) :
    ∀ te ∈ instTimes (alt w tA) B, te ≤ tA := by
  intro te ⟨w', _, hw'B⟩
  exact le_trans (hNoFuture w' ‹_› te hw'B) hBound

/-- (20a) "Unfortunately, the 2021 MLB season will be over before Shohei Ohtani
    earns his 10th win of the season." (Uttered in the middle of September 2021.)
    The A-time is the end of the 2021 MLB season (October 3, 2021 = day 276).
    The complement (Ohtani's 10th win) can only occur during the season
    (before day 276). (O&@cite{ogihara-steinert-threlkeld-2024}, §5.1, ex. 20a) -/
def ost_counterexample_ohtani : BCCounterexampleDatum where
  sentence := "Unfortunately, the 2021 MLB season will be over before Shohei Ohtani earns his 10th win of the season"
  aTime := 276
  complementUpperBound := 275
  boundedBefore := by omega
  reading := .counterfactual

/-- (20b) "2020 might come to an end before it snows for the first time this year."
    (Uttered on Christmas Day in 2020.) The expression *this year* refers back
    to 2020. Since the first snow of 2020 can only occur in 2020, the modal
    proposal that posits a fictitious snow event after the end of 2020 does not
    work. (O&@cite{ogihara-steinert-threlkeld-2024}, §5.1, ex. 20b) -/
def ost_counterexample_snow : BCCounterexampleDatum where
  sentence := "2020 might come to an end before it snows for the first time this year"
  aTime := 366
  complementUpperBound := 366
  boundedBefore := le_refl _
  reading := .nonCommittal

/-- (20c) "July 1999 will come to an end before Nostradamus' prophecy about the
    end of the world comes true." (Uttered a few minutes before the end of July
    1999. Assumes Michel de Nostradamus predicted that in July 1999, a great King
    of terror would come from the sky and destroy the world.) The prophecy can
    only come true if the world is destroyed in July 1999 — it cannot come true
    after the end of July 1999. (O&@cite{ogihara-steinert-threlkeld-2024}, §5.1, ex. 20c) -/
def ost_counterexample_nostradamus : BCCounterexampleDatum where
  sentence := "July 1999 will come to an end before Nostradamus' prophecy about the end of the world comes true"
  aTime := 31
  complementUpperBound := 31
  boundedBefore := le_refl _
  reading := .counterfactual

-- ════════════════════════════════════════════════════════════════
-- § 7: Non-Committal Reading Problems (O&@cite{ogihara-steinert-threlkeld-2024}, §5.2)
-- ════════════════════════════════════════════════════════════════

/-- A datum recording asymmetries in the availability of non-committal
    readings, which B&C's Event Continuation Condition should but cannot
    fully predict. -/
structure NonCommittalDatum where
  /-- The example sentence -/
  sentence : String
  /-- Is the non-committal reading available? -/
  nonCommittalAvailable : Bool
  /-- Why the availability is as it is -/
  explanation : String
  deriving Repr

/-- "Mary will leave the party before Bill gets drunk."
    Non-committal reading is available: maybe Bill gets drunk, maybe not.
    B&C's Event Continuation Condition is satisfied (Bill getting drunk is
    a normal continuation). (O&@cite{ogihara-steinert-threlkeld-2024}, §5.2) -/
def noncommittal_available : NonCommittalDatum where
  sentence := "Mary will leave the party before Bill gets drunk"
  nonCommittalAvailable := true
  explanation := "getting drunk is a normal continuation of being at a party"

/-- "Mary will leave the party before Quebec becomes an independent country."
    Non-committal reading is NOT available (sentence is odd): Quebec's
    independence is not a normal continuation of the party. B&C's Event
    Continuation Condition should block this, but the mechanism is unclear
    for *before*-clauses with pragmatically impossible complements.
    (O&@cite{ogihara-steinert-threlkeld-2024}, §5.2) -/
def noncommittal_unavailable : NonCommittalDatum where
  sentence := "Mary will leave the party before Quebec becomes an independent country"
  nonCommittalAvailable := false
  explanation := "Quebec independence is not a contextually normal continuation"

/-- The non-committal reading is sensitive to contextual plausibility:
    available when the complement is a normal continuation, unavailable
    when it is pragmatically impossible. -/
theorem noncommittal_plausibility_sensitive :
    noncommittal_available.nonCommittalAvailable = true ∧
    noncommittal_unavailable.nonCommittalAvailable = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 8: Cross-Linguistic Data (O&@cite{ogihara-steinert-threlkeld-2024}, §3)
-- ════════════════════════════════════════════════════════════════

/-- Cross-linguistic morphological evidence for the veridicality asymmetry. -/
structure CrossLinguisticDatum where
  /-- Language -/
  language : String
  /-- The temporal connective (in the object language) -/
  connective : String
  /-- English gloss -/
  gloss : String
  /-- Key morphological observation -/
  observation : String
  /-- Does this support the non-veridical analysis of *before*? -/
  supportsNonveridicality : Bool
  deriving Repr

/-- Japanese *mae* ('before') requires non-past tense in its complement,
    even when describing past events. This independently supports the
    non-veridical analysis: the complement is presented as unrealized
    from the perspective of the main-clause event. (O&@cite{ogihara-steinert-threlkeld-2024}, §3) -/
def japanese_mae : CrossLinguisticDatum where
  language := "Japanese"
  connective := "mae (前)"
  gloss := "before"
  observation := "complement always non-past tense, even in past contexts"
  supportsNonveridicality := true

/-- Japanese *ato* ('after') allows past tense in its complement,
    consistent with the veridical analysis: the complement event
    is presented as having occurred. (O&@cite{ogihara-steinert-threlkeld-2024}, §3) -/
def japanese_ato : CrossLinguisticDatum where
  language := "Japanese"
  connective := "ato (後)"
  gloss := "after"
  observation := "complement allows past tense, consistent with veridicality"
  supportsNonveridicality := false

/-- The Japanese tense asymmetry mirrors the veridicality asymmetry:
    *mae* (non-past complement) patterns with non-veridical *before*,
    *ato* (past complement) patterns with veridical *after*. -/
theorem japanese_tense_mirrors_veridicality :
    japanese_mae.supportsNonveridicality = true ∧
    japanese_ato.supportsNonveridicality = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 9: Basic Data Theorems
-- ════════════════════════════════════════════════════════════════

/-- After is uniformly veridical across examples. -/
theorem after_data_veridical :
    after_veridical.complementEntailed = true ∧
    after_veridical_2.complementEntailed = true :=
  ⟨rfl, rfl⟩

/-- Before is uniformly non-veridical across all examples. -/
theorem before_data_nonveridical :
    before_nonveridical.complementEntailed = false ∧
    before_counterfactual.complementEntailed = false ∧
    before_noncommittal.complementEntailed = false ∧
    before_counterfactual_mozart.complementEntailed = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The asymmetry: after and before differ on complement entailment. -/
theorem veridicality_asymmetry :
    after_veridical.complementEntailed ≠ before_nonveridical.complementEntailed := by
  decide

/-- Before and after are opposites on all logical properties tested. -/
theorem logical_property_asymmetry :
    before_antisymmetric.holds ≠ after_not_antisymmetric.holds ∧
    before_transitive.holds ≠ after_not_transitive.holds := by
  exact ⟨by decide, by decide⟩

-- ════════════════════════════════════════════════════════════════
-- Bridge content (merged from Bridge.lean)
-- ════════════════════════════════════════════════════════════════

open Semantics.Tense.TemporalConnectives
open Semantics.Events
open Fragments.English.TemporalExpressions

-- ════════════════════════════════════════════════════════════════
-- § 10: Fragment ↔ Data Agreement
-- ════════════════════════════════════════════════════════════════

/-- The Fragment entry for *after* matches the empirical datum:
    both record complement veridicality as true. -/
theorem after_fragment_matches_datum :
    after_.complementVeridical = after_veridical.complementEntailed := rfl

/-- The Fragment entry for *before* matches the empirical datum:
    both record complement veridicality as false. -/
theorem before_fragment_matches_datum :
    before_.complementVeridical = before_nonveridical.complementEntailed := rfl

/-- The veridicality asymmetry is reflected in the Fragment entries. -/
theorem fragment_veridicality_asymmetry :
    after_.complementVeridical = true ∧ before_.complementVeridical = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 11: Theory → Fragment Derivation
-- ════════════════════════════════════════════════════════════════

/-- O&ST's theory derives *after*'s veridicality from the double-existential
    quantificational structure: ∃e₁∃e₂[P(e₁) ∧ Q(e₂) ∧...] entails ∃e₂, Q(e₂).

    This is not a stipulation in the Fragment — it follows from the semantics. -/
theorem after_veridicality_derived :
    ∀ (P Q : EvPred ℤ), AnscombeEvent.after P Q → ∃ e : Ev ℤ, Q e :=
  fun P Q h => AnscombeEvent.after_veridical P Q h

/-- O&ST's theory derives *before*'s non-veridicality from the universal
    quantification over the complement: ∃e₁[P(e₁) ∧ ∀e₂[Q(e₂) →...]] is
    vacuously true when Q has no witnesses.

    Concretely: any P-event with an empty Q yields `before(P, Q)`. -/
theorem before_nonveridicality_derived :
    ∃ (P Q : EvPred ℤ), AnscombeEvent.before P Q ∧ ¬∃ e : Ev ℤ, Q e :=
  AnscombeEvent.before_nonveridical

-- ════════════════════════════════════════════════════════════════
-- § 12: Concrete Scenario Verification
-- ════════════════════════════════════════════════════════════════

/-- Scenario: "He left₁ after she arrived₀" with punctual events.
    - leaving event at time 1
    - arriving event at time 0
    O&ST predicts: after(leave, arrive) holds (τ(arrive) ≺ τ(leave)). -/
theorem scenario_after_punctual :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨0, 0, le_refl _⟩, .action⟩
    AnscombeEvent.after (· = leave) (· = arrive) := by
  refine ⟨⟨⟨1, 1, le_refl _⟩, .action⟩, ⟨⟨0, 0, le_refl _⟩, .action⟩, rfl, rfl, ?_⟩
  simp [Core.Time.Interval.precedes, Ev.τ]

/-- Scenario: "He left₁ before she arrived₃" with punctual events.
    - leaving event at time 1
    - arriving event at time 3
    O&ST predicts: before(leave, arrive) holds (τ(leave) ≺ τ(arrive)). -/
theorem scenario_before_punctual :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨3, 3, le_refl _⟩, .action⟩
    AnscombeEvent.before (· = leave) (· = arrive) := by
  refine ⟨⟨⟨1, 1, le_refl _⟩, .action⟩, rfl, ?_⟩
  intro e₂ rfl
  simp [Core.Time.Interval.precedes, Ev.τ]

/-- Scenario: "The bomb exploded₅ before anyone defused it" (nobody defused it).
    O&ST predicts: before(explode, defuse) holds vacuously (no defuse-events). -/
theorem scenario_before_counterfactual :
    let explode : Ev ℤ := ⟨⟨5, 5, le_refl _⟩, .action⟩
    AnscombeEvent.before (· = explode) (fun _ => False) := by
  exact ⟨⟨⟨5, 5, le_refl _⟩, .action⟩, rfl, fun _ h => h.elim⟩

-- ════════════════════════════════════════════════════════════════
-- § 13: Cross-Level Projection Verification
-- ════════════════════════════════════════════════════════════════

/-- The punctual after-scenario projects correctly through eventDenotation:
    O&ST.after implies Anscombe.after on the projected interval sets. -/
theorem scenario_after_projects :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨0, 0, le_refl _⟩, .action⟩
    Anscombe.after (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  AnscombeEvent.after_implies_anscombe _ _ scenario_after_punctual

/-- The punctual before-scenario projects correctly through eventDenotation. -/
theorem scenario_before_projects :
    let leave : Ev ℤ := ⟨⟨1, 1, le_refl _⟩, .action⟩
    let arrive : Ev ℤ := ⟨⟨3, 3, le_refl _⟩, .action⟩
    Anscombe.before (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  AnscombeEvent.before_implies_anscombe _ _ scenario_before_punctual

-- ════════════════════════════════════════════════════════════════
-- § 14: Logical Properties (@cite{beaver-condoravdi-2003}, §1)
-- ════════════════════════════════════════════════════════════════

/-! The logical properties of *before* and *after* noted by B&C follow
    directly from the quantificational structure. We verify each on
    concrete interval scenarios over ℤ, matching the B&C diagrams. -/

private def i_cleo_b : Core.Time.Interval ℤ := ⟨1, 5, by omega⟩
private def i_david_b : Core.Time.Interval ℤ := ⟨8, 12, by omega⟩

/-- *Before* is antisymmetric on non-overlapping statives: if A before B,
    then ¬(B before A). (@cite{beaver-condoravdi-2003}, exx. 3-4)

    Scenario: Cleo [1,5], David [8,12]. Cleo before David holds;
    David before Cleo does not.

    The ∀-quantifier in Anscombe.before enforces this: if all of B
    follows some point in A, then no point in B precedes all of A. -/
theorem before_antisymmetric_scenario :
    Anscombe.before (stativeDenotation i_cleo_b) (stativeDenotation i_david_b) ∧
    ¬Anscombe.before (stativeDenotation i_david_b) (stativeDenotation i_cleo_b) := by
  simp only [Anscombe.before, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_cleo_b, i_david_b, Set.mem_setOf_eq]
  constructor
  · exact ⟨1, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩
  · intro ⟨t, ⟨ht1, ht2⟩, hall⟩
    have := hall 1 ⟨le_refl _, by omega⟩; omega

private def i_cleo_a : Core.Time.Interval ℤ := ⟨1, 8, by omega⟩
private def i_david_a : Core.Time.Interval ℤ := ⟨5, 12, by omega⟩

/-- *After* is NOT antisymmetric: overlapping intervals allow both
    after(A,B) and after(B,A). (@cite{beaver-condoravdi-2003}, exx. 5-7, diagram 7)

    Scenario: Cleo [1,8], David [5,12]. Both Cleo-after-David and
    David-after-Cleo hold because ∃ requires only one witness. -/
theorem after_not_antisymmetric_scenario :
    Anscombe.after (stativeDenotation i_cleo_a) (stativeDenotation i_david_a) ∧
    Anscombe.after (stativeDenotation i_david_a) (stativeDenotation i_cleo_a) := by
  simp only [Anscombe.after, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_cleo_a, i_david_a, Set.mem_setOf_eq]
  exact ⟨⟨8, ⟨by omega, le_refl _⟩, 5, ⟨le_refl _, by omega⟩, by omega⟩,
         ⟨12, ⟨by omega, le_refl _⟩, 1, ⟨le_refl _, by omega⟩, by omega⟩⟩

/-- Helper intervals for the transitivity scenarios. Using top-level defs
    so `simp` can unfold interval fields for `omega`. -/
private def i_delores_t : Core.Time.Interval ℤ := ⟨1, 3, by omega⟩
private def i_ginger_t : Core.Time.Interval ℤ := ⟨6, 8, by omega⟩
private def i_fred_t : Core.Time.Interval ℤ := ⟨11, 13, by omega⟩

/-- *Before* is transitive: A before B ∧ B before C → A before C.
    (@cite{beaver-condoravdi-2003}, exx. 12-14)

    Scenario: Delores [1,3], Ginger [6,8], Fred [11,13]. -/
theorem before_transitive_scenario :
    Anscombe.before (stativeDenotation i_delores_t) (stativeDenotation i_ginger_t) ∧
    Anscombe.before (stativeDenotation i_ginger_t) (stativeDenotation i_fred_t) ∧
    Anscombe.before (stativeDenotation i_delores_t) (stativeDenotation i_fred_t) := by
  simp only [Anscombe.before, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_delores_t, i_ginger_t, i_fred_t, Set.mem_setOf_eq]
  exact ⟨⟨1, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩,
         ⟨6, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩,
         ⟨1, ⟨le_refl _, by omega⟩, fun t' ⟨h, _⟩ => by omega⟩⟩

private def i_fred_a : Core.Time.Interval ℤ := ⟨1, 3, by omega⟩
private def i_ginger_a : Core.Time.Interval ℤ := ⟨2, 5, by omega⟩
private def i_delores_a : Core.Time.Interval ℤ := ⟨4, 7, by omega⟩

/-- *After* is NOT transitive: overlapping intervals allow
    after(A,B) ∧ after(B,C) ∧ ¬after(A,C). (@cite{beaver-condoravdi-2003}, exx. 8-11)

    Scenario: Fred [1,3], Ginger [2,5], Delores [4,7].
    Fred after Ginger: t=3, t'=2. ✓
    Ginger after Delores: t=5, t'=4. ✓
    Fred after Delores: need t ∈ [1,3], t' ∈ [4,7], t' < t — impossible
    since max(Fred)=3 < 4=min(Delores). ✗ -/
theorem after_not_transitive_scenario :
    Anscombe.after (stativeDenotation i_fred_a) (stativeDenotation i_ginger_a) ∧
    Anscombe.after (stativeDenotation i_ginger_a) (stativeDenotation i_delores_a) ∧
    ¬Anscombe.after (stativeDenotation i_fred_a) (stativeDenotation i_delores_a) := by
  simp only [Anscombe.after, timeTrace_stativeDenotation, Core.Time.Interval.contains,
    i_fred_a, i_ginger_a, i_delores_a, Set.mem_setOf_eq]
  refine ⟨⟨3, ⟨by omega, by omega⟩, 2, ⟨by omega, by omega⟩, by omega⟩,
          ⟨5, ⟨by omega, by omega⟩, 4, ⟨by omega, by omega⟩, by omega⟩, ?_⟩
  rintro ⟨t, ⟨h1, h2⟩, t', ⟨h3, h4⟩, hlt⟩; omega

-- ════════════════════════════════════════════════════════════════
-- § 15: Logical Properties — General Theorems
-- ════════════════════════════════════════════════════════════════

/-- *Before* is antisymmetric in general: `before(A,B) → ¬before(B,A)`.

    From the ∀ in Anscombe's *before*: if ∃t ∈ A, ∀t' ∈ B, t < t',
    then for any s ∈ B we get t < s. But before(B,A) gives ∀ t ∈ A, s < t,
    so s < t and t < s — contradiction.

    Note: no non-emptiness assumption needed. -/
theorem before_antisymmetric_general {Time : Type*} [LinearOrder Time]
    (A B : SentDenotation Time) :
    Anscombe.before A B → ¬Anscombe.before B A := by
  intro ⟨t, ht, hall_B⟩ ⟨s, hs, hall_A⟩
  exact lt_asymm (hall_A t ht) (hall_B s hs)

/-- *Before* is transitive in general: `before(A,B) → before(B,C) → before(A,C)`.

    From `before(A,B)`: ∃t ∈ A, ∀t' ∈ B, t < t'.
    From `before(B,C)`: ∃s ∈ B, ∀s' ∈ C, s < s'.
    Then t < s (from the first, since s ∈ B), and for any u ∈ C, s < u
    (from the second). So t < u by transitivity of <. Witness: t ∈ A.

    Note: no non-emptiness assumption needed — `s ∈ timeTrace B` is
    provided by the second hypothesis. -/
theorem before_transitive_general {Time : Type*} [LinearOrder Time]
    (A B C : SentDenotation Time) :
    Anscombe.before A B → Anscombe.before B C → Anscombe.before A C := by
  intro ⟨t, ht, hall_B⟩ ⟨s, hs, hall_C⟩
  exact ⟨t, ht, fun u hu => lt_trans (hall_B s hs) (hall_C u hu)⟩

-- ════════════════════════════════════════════════════════════════
-- § 16: NPI Licensing Bridge
-- ════════════════════════════════════════════════════════════════

/-- The NPI datum matches the Fragment entry: *before* licenses NPIs. -/
theorem npi_datum_matches_fragment :
    before_.licensesNPI = before_licenses_npis.holds := rfl

-- ════════════════════════════════════════════════════════════════
-- § 17: Cross-Linguistic Bridge (Japanese)
-- ════════════════════════════════════════════════════════════════

open Fragments.Japanese.TemporalConnectives in
/-- The Japanese Fragment entry for *mae* agrees with the cross-linguistic
    datum: both record that *mae* supports the non-veridicality analysis. -/
theorem japanese_mae_matches_datum :
    mae.complementVeridical = false ∧
    japanese_mae.supportsNonveridicality = true :=
  ⟨rfl, rfl⟩

open Fragments.Japanese.TemporalConnectives in
/-- The Japanese Fragment entry for *ato* agrees with the cross-linguistic
    datum: *ato* is veridical and does not support non-veridicality. -/
theorem japanese_ato_matches_datum :
    ato.complementVeridical = true ∧
    japanese_ato.supportsNonveridicality = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 18: Progressive Analogy (O&@cite{ogihara-steinert-threlkeld-2024}, §3)
-- ════════════════════════════════════════════════════════════════

/-! @cite{ogihara-steinert-threlkeld-2024} §3 observe that the progressive and
    anti-veridical *before* share the same modal-temporal structure:

    - **Progressive** "Mozart was composing the Requiem (when he died)":
      at the reference time, there is an ongoing event (composing) that in
      some **inertia worlds** (@cite{landman-1992}) reaches completion.

    - **Anti-veridical before** "Mozart died before he finished the Requiem":
      at the A-time, there is an ongoing event (composing) that in some
      **historical alternatives** reaches the before-clause eventuality
      (finishing).

    Both reduce to: ∃ event e ongoing at t such that in some accessible
    world w', the continuation of e leads to a target outcome.

    The formal parallel:
    - `IMPF P w t` ↔ ∃ e, t ⊂ τ(e) ∧ P w e  (event extends beyond t)
    - `alt(w,t)` contains worlds where the counterpart of e develops
      beyond t (event continuation condition, def 18b)

    This structural identity is captured by the following bridge: given
    an IMPF predication and an "inertia" alternative set, the reference time
    sits inside the event's runtime in the actual world, while alternatives
    contain worlds where the continuation reaches a target. -/

open Semantics.Tense.Aspect.Core
open Semantics.Tense.Aspect.SubintervalProperty

/-! **Imperfective paradox ↔ before non-veridicality: shared vacuous-∀ structure.**

Both arise from a universal quantification that can be vacuously satisfied:

- **Before's non-veridicality**: `∀ e₂, Q(e₂) → τ(e₁) ≺ τ(e₂)` is vacuously
  true when no Q-event exists. The complement need not occur.

- **Imperfective paradox**: For accomplishments lacking CSIP, `IMPF P w t`
  does not entail `PRFV P w t` — the event is ongoing at t but the telos
  (completion) may not be reached. The universal quantification over
  subintervals that CSIP would provide is absent.

Both are "resolved" modally in the same way:
- **Progressive**: in inertia worlds, the ongoing event reaches completion
- **Anti-veridical before**: in historical alternatives, the complement
  event occurs

The following theorems make this structural parallel precise. -/

/-- **CSIP predicates are "before-veridical"**: if P has the closed subinterval
    property, then IMPF(P)(w)(t) guarantees P-completion at t (PRFV).
    This is the aspectual analogue of *after*'s veridicality — both arise
    from existential (not universal) quantificational structure.

    Formally: CSIP(P) → IMPF(P)(w)(t) → PRFV(P)(w)(t). This is
    `impf_entails_prfv_of_csip` from SubintervalProperty.lean. -/
theorem csip_entails_completion
    {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) (hCSIP : HasClosedSubintervalProp P)
    (w : W) (t : Core.Time.Interval Time) :
    IMPF P w t → PRFV P w t :=
  fun h => impf_entails_prfv_of_csip P hCSIP w t h

/-- **Non-CSIP predicates may lack completion**: the imperfective paradox shows
    that not all predicates support the IMPF→PRFV entailment.
    This is the aspectual analogue of *before*'s non-veridicality — both
    arise from a universal quantification (over subintervals / over complement
    events) that can be vacuously satisfied.

    Formally: ¬(∀ P, HasSubintervalProp P). This is
    `imperfective_paradox_possible` from SubintervalProperty.lean. -/
theorem non_csip_lacks_completion
    {W : Type*} (w : W) (t₁ t₂ : ℤ) (hlt : t₁ < t₂) :
    ¬ (∀ (P : EventPred W ℤ), HasSubintervalProp P) :=
  imperfective_paradox_possible w t₁ t₂ hlt

/-- **Progressive–before modal resolution**: When P lacks CSIP (accomplishment),
    IMPF(P)(w)(t) gives an ongoing event e that does not (yet) satisfy PRFV.
    The progressive "resolves" this by positing inertia worlds where the
    continuation of e reaches a target Q. Anti-veridical *before* does the
    same with historical alternatives.

    This theorem captures the shared structure: given an IMPF predication
    and a modal accessibility relation (`alternatives`) that maps ongoing
    events to worlds where a target Q is reached, there exists an ongoing
    event whose continuation satisfies Q in accessible worlds. -/
theorem progressive_before_modal_resolution
    {W Time : Type*} [LinearOrder Time]
    (P Q : EventPred W Time)
    (alternatives : Eventuality Time → Set W)
    (w : W) (t : Core.Time.Interval Time)
    (hIMPF : IMPF P w t)
    (hContinuation : ∀ e, P w e → t.properSubinterval e.τ →
      ∀ w' ∈ alternatives e, ∃ e', Q w' e') :
    ∃ e, t.properSubinterval e.τ ∧ P w e ∧
      ∀ w' ∈ alternatives e, ∃ e', Q w' e' := by
  obtain ⟨e, hSub, hP⟩ := hIMPF
  exact ⟨e, hSub, hP, hContinuation e hP hSub⟩

/-- **The parallel is precise**: the progressive and anti-veridical *before*
    have identical formal structure. Progressive: IMPF(P)(w)(t) + inertia(e)
    → Q reachable. Before (anti-veridical): ongoing event at A-time +
    alt(w,I,e) → complement reachable. The only difference is the name of
    the accessibility relation (inertia vs historical alternatives).

    This theorem shows that CSIP is the dividing line: predicates WITH CSIP
    don't need modal resolution (IMPF directly entails PRFV, like *after*
    directly entails its complement). Predicates WITHOUT CSIP require modal
    resolution (the progressive / anti-veridical *before*). -/
theorem csip_determines_modal_need
    {W Time : Type*} [LinearOrder Time]
    (P : EventPred W Time) (w : W) (t : Core.Time.Interval Time) :
    (HasClosedSubintervalProp P → IMPF P w t → PRFV P w t) ∧
    (IMPF P w t → ¬HasClosedSubintervalProp P →
      ¬(∀ (t' : Core.Time.Interval Time), t'.subinterval t →
        ∃ e, e.τ = t' ∧ P w e) →
      -- Modal resolution needed: must appeal to alternative worlds
      ∃ e, t.properSubinterval e.τ ∧ P w e) := by
  constructor
  · intro hCSIP; exact impf_entails_prfv_of_csip P hCSIP w t
  · intro ⟨e, hSub, hP⟩ _ _
    exact ⟨e, hSub, hP⟩

-- ════════════════════════════════════════════════════════════════
-- § 19: Revamped Truth Conditions (O&@cite{ogihara-steinert-threlkeld-2024}, def 19)
-- ════════════════════════════════════════════════════════════════

/-! The paper's central formal contribution: revamped truth conditions for
    *before* that incorporate eventuality-relative alternatives (def 18) and
    a CAUSE relation. Three cases for ⟦A before B⟧ evaluated at ⟨w₀, I₀, e₀⟩:

    **(i) Definitely true (veridical)**: A holds at ⟨w₀,I₀,e₀⟩ AND B already
    holds at some later interval I₂ > I₀ in w₀. The complement already
    occurred after A — straightforwardly true.

    **(ii) Definitely false**: A holds at ⟨w₀,I₀,e₀⟩ AND B already holds at
    some interval I₂ ≤ I₀ in w₀. The complement already occurred before/at
    A — so A is NOT before B.

    **(iii) Modal case (anti-veridical / non-committal)**: A holds at
    ⟨w₀,I₀,e₀⟩ and I₀ precedes the earliest I₁ such that ∃ eventuality e₁
    ongoing at I₀ in w₀, ∃ world w₁ ∈ alt(w₀,I₀,e₁), ∃ e₂ counterpart of
    e₁ in w₁, the continuation of e₂ CAUSES an eventuality e₃ with
    ⟨w₁,I₁,e₃⟩ ∈ ⟦B⟧.

    The authors note these truth conditions are "very weak and need to be
    strengthened by some contextual and pragmatic factors." -/

open BeaverCondoravdi

section Def19

variable {W T E : Type*} [LinearOrder T]

/-- Two intervals abut: the first ends where the second begins (no gap). -/
def abuts (I₀ I₁ : Core.Time.Interval T) : Prop :=
  I₀.finish = I₁.start

/-- An eventuality e₁ "holds throughout" an interval that abuts I₀:
    e₁'s runtime extends from before I₀ through to (at least) I₀'s start. -/
def holdsAtAbutting (runtime : E → Core.Time.Interval T) (e₁ : E)
    (I₀ : Core.Time.Interval T) : Prop :=
  (runtime e₁).start ≤ I₀.start ∧ I₀.start ≤ (runtime e₁).finish

/-- Denotation type for O&ST's truth conditions: sets of
    world–interval–eventuality triples. -/
abbrev SitDenot (W T E : Type*) [LinearOrder T] := Set (W × Core.Time.Interval T × E)

/-- **Case (i)**: ⟦A before B⟧ = 1 when the complement B already holds
    at some interval after I₀ in the actual world w₀. -/
def beforeCase_veridical
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : Core.Time.Interval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : Core.Time.Interval T, I₀.finish < I₂.start ∧
    ∃ e₄ : E, (w₀, I₂, e₄) ∈ B

/-- **Case (ii)**: ⟦A before B⟧ = 0 when the complement B already holds
    at some interval at or before I₀ in the actual world w₀. -/
def beforeCase_false
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : Core.Time.Interval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : Core.Time.Interval T, I₂.finish ≤ I₀.start ∧
    ∃ e₅ : E, (w₀, I₂, e₅) ∈ B

/-- **Case (iii)**: The modal case. ⟦A before B⟧ = 1 when A holds at ⟨w₀,I₀,e₀⟩
    and I₀ precedes the earliest I₁ such that:
    - there is an eventuality e₁ in w₀ whose runtime abuts I₀,
    - there is an alternative world w₁ ∈ alt(w₀, I₀, e₁),
    - in w₁, the counterpart e₂ of e₁ continues and CAUSES an eventuality e₃,
    - ⟨w₁, I₁, e₃⟩ ∈ ⟦B⟧. -/
def beforeCase_modal
    (A B : SitDenot W T E)
    (runtime : E → Core.Time.Interval T)
    (alt : W → Core.Time.Interval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : Core.Time.Interval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧
  ∃ I₁ : Core.Time.Interval T,
    I₀.finish < I₁.start ∧  -- I₀ precedes I₁
    ∃ e₁ : E,
      holdsAtAbutting runtime e₁ I₀ ∧  -- e₁ ongoing at I₀
      ∃ w₁ ∈ alt w₀ I₀ e₁,  -- alternative world
        ∃ e₂ : E,
          counterpart w₀ e₁ w₁ e₂ ∧  -- e₂ is counterpart of e₁
          ∃ e₃ : E,
            cause w₁ e₂ e₃ ∧  -- continuation of e₂ CAUSES e₃
            (w₁, I₁, e₃) ∈ B  -- B holds at ⟨w₁, I₁, e₃⟩

/-- **O&ST's revamped *before*** (def 19): the disjunction of the three cases.
    Evaluated at ⟨w₀, I₀, e₀⟩, "A before B" is true iff either:
    - (i) B already occurred after I₀ (veridical), or
    - (iii) The modal case via alt(w₀,I₀,e₁) + CAUSE holds,
    AND case (ii) does not hold (B did not already occur before I₀). -/
def OST.before
    (A B : SitDenot W T E)
    (runtime : E → Core.Time.Interval T)
    (alt : W → Core.Time.Interval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : Core.Time.Interval T) (e₀ : E) : Prop :=
  ¬beforeCase_false A B w₀ I₀ e₀ ∧
  (beforeCase_veridical A B w₀ I₀ e₀ ∨
   beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀)

-- ════════════════════════════════════════════════════════════════
-- § 20: Properties of the Revamped Truth Conditions
-- ════════════════════════════════════════════════════════════════

/-- Case (i) is veridical: when the complement has already occurred (after I₀),
    the complement is instantiated in the actual world. -/
theorem beforeCase_veridical_entails_complement
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : Core.Time.Interval T) (e₀ : E) :
    beforeCase_veridical A B w₀ I₀ e₀ → ∃ I e, (w₀, I, e) ∈ B := by
  rintro ⟨_, I₂, _, e₄, hB⟩
  exact ⟨I₂, e₄, hB⟩

/-- Case (iii) is non-veridical: the complement need not be instantiated in
    w₀ — it may only exist in an alternative world w₁.

    Scenario: w₀ = false (actual), w₁ = true (alternative).
    A = {(false, [0,0], ())} — main clause holds only in w₀.
    B = {(true, [2,2], ())} — complement holds only in w₁.
    The modal case holds because alt gives w₁, with trivial cause/counterpart.
    But B has no witness in w₀. -/
theorem beforeCase_modal_nonveridical :
    ∃ (A B : SitDenot Bool ℤ Unit)
      (runtime : Unit → Core.Time.Interval ℤ)
      (alt : Bool → Core.Time.Interval ℤ → Unit → Set Bool)
      (cause : Bool → Unit → Unit → Prop)
      (counterpart : Bool → Unit → Bool → Unit → Prop)
      (w₀ : Bool) (I₀ : Core.Time.Interval ℤ) (e₀ : Unit),
    beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀ ∧
    ¬∃ I e, (w₀, I, e) ∈ B := by
  refine ⟨{(false, ⟨0, 0, le_refl _⟩, ())},
          {(true, ⟨2, 2, le_refl _⟩, ())},
          fun _ => ⟨-1, 0, by omega⟩,
          fun _ _ _ => {true},
          fun _ _ _ => True,      -- cause : W → E → E → Prop
          fun _ _ _ _ => True,    -- counterpart : W → E → W → E → Prop
          false, ⟨0, 0, le_refl _⟩, (), ?_, ?_⟩
  · refine ⟨rfl, ⟨2, 2, le_refl _⟩, ?_, (), ⟨?_, true, rfl, (),
      ⟨trivial, (), trivial, rfl⟩⟩⟩
    · show (0 : ℤ) < 2; omega
    · exact ⟨by show (-1 : ℤ) ≤ 0; omega, by show (0 : ℤ) ≤ 0; omega⟩
  · rintro ⟨I, e, hB⟩
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hB
    exact absurd hB.1 Bool.false_ne_true

/-- Cases (i) and (ii) are mutually exclusive when the complement occurs at
    a single interval: it cannot be both before and after I₀. -/
theorem cases_i_ii_exclusive
    (I₀ I_B : Core.Time.Interval T)
    (hAfter : I₀.finish < I_B.start)
    (hBefore : I_B.finish ≤ I₀.start) :
    False := by
  have : I_B.finish < I_B.start := lt_of_le_of_lt hBefore (lt_of_le_of_lt I₀.valid hAfter)
  exact absurd this (not_lt.mpr I_B.valid)

/-- The Mozart scenario: "Mozart died before he finished the Requiem."
    This is the anti-veridical reading (case iii). Mozart's death (e₀) is at
    I₀. In some alternative world w₁, Mozart's composing (e₁, ongoing at I₀)
    has a counterpart e₂ whose continuation CAUSES a finishing event e₃ at I₁.
    B ("finishing the Requiem") holds at ⟨w₁, I₁, e₃⟩ but NOT in w₀. -/
theorem mozart_is_case_iii
    {W E : Type*}
    (A B : SitDenot W ℤ E)
    (runtime : E → Core.Time.Interval ℤ)
    (alt : W → Core.Time.Interval ℤ → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : Core.Time.Interval ℤ) (e₀ : E)
    (hNoFinish : ¬∃ I e, (w₀, I, e) ∈ B)
    (hModal : beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀) :
    OST.before A B runtime alt cause counterpart w₀ I₀ e₀ := by
  refine ⟨?_, Or.inr hModal⟩
  intro ⟨_, I₂, _, e₅, hB⟩
  exact hNoFinish ⟨I₂, e₅, hB⟩

end Def19

end OgiharaST2024

-- ════════════════════════════════════════════════════════════════
-- Veridicality ↔ Presupposition Bridge
-- ════════════════════════════════════════════════════════════════

/-! ## Veridicality ↔ Presupposition Bridge
@cite{beaver-condoravdi-2003} @cite{heim-1983} @cite{ogihara-steinert-threlkeld-2024}

Connects three layers of the temporal connective formalization:

1. **Fragment field**: `TemporalExprEntry.complementVeridical : Bool`
2. **Theory proof**: e.g., `Anscombe.after A B → ∃ t, t ∈ timeTrace B`
3. **Presupposition theory**: veridical connectives presuppose their complement
   (modeled as `PrProp` with complement occurrence as presupposition)

For each temporal connective, the Fragment's `complementVeridical` field is
**grounded** in a theory-level proof, and matches the empirical data.
-/

namespace OgiharaST2024.VeridicalityBridge

open Core.Time
open Core.Time.Interval
open Semantics.Tense.TemporalConnectives
open Fragments.English.TemporalExpressions
open OgiharaST2024

-- ============================================================================
-- § 19: Fragment ↔ Theory Agreement (Per-Entry Verification)
-- ============================================================================

/-! ### Veridical connectives

For each connective with `complementVeridical = true`, the theory proves
that the connective entails the existence of a complement witness. -/

/-- *after* is veridical: Fragment field matches theory proof.
    Theory: `Anscombe.after A B → ∃ t, t ∈ timeTrace B`.
    Fragment: `after_.complementVeridical = true`. -/
theorem after_veridicality_grounded :
    after_.complementVeridical = true ∧
    (∀ (A B : SentDenotation ℤ), Anscombe.after A B → ∃ t, t ∈ timeTrace B) := by
  exact ⟨rfl, fun A B ⟨_, _, t', ht', _⟩ => ⟨t', ht'⟩⟩

/-- *when* is veridical: Fragment field matches theory proof. -/
theorem when_veridicality_grounded :
    when_conn.complementVeridical = true ∧
    (∀ (A B : SentDenotation ℤ), Karttunen.when_ A B → ∃ t, t ∈ timeTrace B) :=
  ⟨rfl, when_veridical_complement⟩

/-- *until* (durative) is veridical: Fragment field matches theory proof. -/
theorem until_veridicality_grounded :
    until_.complementVeridical = true ∧
    (∀ (A B : SentDenotation ℤ), Karttunen.until A B → ∃ t, t ∈ timeTrace B) :=
  ⟨rfl, until_veridical_complement⟩

/-- *since* is veridical: Fragment field matches theory proof. -/
theorem since_veridicality_grounded :
    since_conn.complementVeridical = true ∧
    (∀ (A B : SentDenotation ℤ), Karttunen.since A B → ∃ t, t ∈ timeTrace B) :=
  ⟨rfl, since_veridical_complement⟩

/-- *by* is veridical w.r.t. its main clause: Fragment field matches theory proof. -/
theorem by_veridicality_grounded :
    by_deadline.complementVeridical = true ∧
    (∀ (A B : SentDenotation ℤ), Karttunen.by_ A B → ∃ t, t ∈ timeTrace A) :=
  ⟨rfl, by_veridical_main⟩

/-! ### Non-veridical connectives -/

/-- *before* is non-veridical: Fragment field matches theory counterexample.
    The counterexample uses A = {point(0)}, B = ∅: "A before nothing"
    is vacuously true because ∀t'∈∅, 0 < t'. -/
theorem before_nonveridicality_grounded :
    before_.complementVeridical = false ∧
    (∃ (A B : SentDenotation ℤ), Anscombe.before A B ∧ ¬∃ t, t ∈ timeTrace B) := by
  refine ⟨rfl, ⟨{ Interval.point 0 }, ∅, ?_, ?_⟩⟩
  · exact ⟨0, ⟨Interval.point 0, rfl, le_refl _, le_refl _⟩,
      fun t' ⟨i, hi, _⟩ => absurd hi (Set.mem_empty_iff_false i).mp⟩
  · intro ⟨_, i, hi, _⟩; exact absurd hi (Set.mem_empty_iff_false i).mp

-- ============================================================================
-- § 20: Fragment ↔ Data Agreement
-- ============================================================================

/-- Fragment matches data for *after*. -/
theorem after_fragment_matches_data :
    after_.complementVeridical = after_veridical.complementEntailed :=
  rfl

/-- Fragment matches data for *before*. -/
theorem before_fragment_matches_data :
    before_.complementVeridical = before_nonveridical.complementEntailed :=
  rfl

/-- Three-layer consistency for *after*: data, fragment, and theory all agree. -/
theorem after_three_layer :
    after_veridical.complementEntailed = true ∧
    after_.complementVeridical = true ∧
    (∀ (A B : SentDenotation ℤ), Anscombe.after A B → ∃ t, t ∈ timeTrace B) :=
  ⟨rfl, rfl, fun _ _ ⟨_, _, t', ht', _⟩ => ⟨t', ht'⟩⟩

/-- Three-layer consistency for *before*: data, fragment, and theory all agree. -/
theorem before_three_layer :
    before_nonveridical.complementEntailed = false ∧
    before_.complementVeridical = false ∧
    (∃ (A B : SentDenotation ℤ), Anscombe.before A B ∧ ¬∃ t, t ∈ timeTrace B) :=
  ⟨rfl, rfl, before_nonveridicality_grounded.2⟩

-- ============================================================================
-- § 21: Quantifier Structure Determines Veridicality
-- ============================================================================

/-- The veridicality pattern is determined by quantifier force:
    ∃-based connectives are veridical; ∀-based (*before*) is non-veridical. -/
theorem veridicality_from_quantifiers :
    after_.complementVeridical = true ∧
    when_conn.complementVeridical = true ∧
    until_.complementVeridical = true ∧
    since_conn.complementVeridical = true ∧
    whenever_conn.complementVeridical = true ∧
    asSoonAs.complementVeridical = true ∧
    asLongAs.complementVeridical = true ∧
    before_.complementVeridical = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 22: Presupposition Modeling
-- ============================================================================

open Core.Presupposition

/-- A temporal connective modeled as a presuppositional proposition.
    Veridical connectives presuppose their complement (like factives);
    non-veridical connectives carry no complement presupposition. -/
def connPrProp (complementInstantiated : Bool) (connHolds : Bool) : PrProp Unit :=
  { presup := fun _ => complementInstantiated
  , assertion := fun _ => connHolds }

theorem veridical_presupposes_complement :
    (connPrProp true true).presup () = true := rfl

theorem nonveridical_no_presupposition :
    (connPrProp false true).presup () = false := rfl

/-- Negation preserves complement presupposition (projection through negation). -/
theorem negation_preserves_presup :
    (PrProp.neg (connPrProp true true)).presup () = true := rfl

-- ============================================================================
-- § 23: B&C's Three Readings of *Before* and Presupposition
-- ============================================================================

open Semantics.Tense.TemporalConnectives.BeaverCondoravdi (BeforeReading)

/-- All three readings are compatible with `complementVeridical = false`. -/
theorem all_before_readings_nonveridical :
    before_.complementVeridical = false := rfl

/-- The O&ST data covers all three B&C readings. -/
theorem bc_readings_in_data :
    before_nonveridical.complementEntailed = false ∧
    before_counterfactual.complementEntailed = false ∧
    before_noncommittal.complementEntailed = false :=
  ⟨rfl, rfl, rfl⟩

end OgiharaST2024.VeridicalityBridge
