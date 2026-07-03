import Linglib.Studies.Anscombe1964
import Linglib.Studies.Karttunen1974
import Linglib.Studies.BeaverCondoravdi2003
import Linglib.Semantics.Tense.TemporalConnectives.Projection
import Linglib.Semantics.Aspect.SubintervalProperty
import Linglib.Fragments.English.TemporalExpressions
import Linglib.Fragments.Japanese.TemporalConnectives
import Linglib.Semantics.Presupposition.Basic
import Linglib.Data.Examples.OgiharaSteinertThrelkeld2024

/-!
# [ogihara-steinert-threlkeld-2024] — Data
[ogihara-steinert-threlkeld-2024]

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

namespace OgiharaSteinertThrelkeld2024

open Data.Examples (LinguisticExample)
open OgiharaSteinertThrelkeld2024.Examples

/-- A `paperFeatures` flag read as a Bool (`true` iff the value is `"true"`). -/
def flagOf (e : LinguisticExample) (k : String) : Bool := e.feature? k == some "true"

-- ════════════════════════════════════════════════════════════════
-- § 1: Veridicality Judgments
-- ════════════════════════════════════════════════════════════════

/-- An empirical judgment about whether a temporal connective entails the truth of its
    complement clause. Stimuli live in `Data/Examples/OgiharaSteinertThrelkeld2024.json`
    (generated `OgiharaSteinertThrelkeld2024.Examples`); this record is derived from a
    `LinguisticExample` by `ofVeridicality`. -/
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

/-- Derive a `VeridicalityDatum` from a generated `LinguisticExample`: the sentence is the
    `primaryText`; the connective and complement-entailment are `paperFeatures` tags. -/
def ofVeridicality (e : LinguisticExample) : VeridicalityDatum where
  sentence := e.primaryText
  connective := (e.feature? "connective").getD ""
  complementEntailed := flagOf e "complement_entailed"
  gloss := e.comment

-- ════════════════════════════════════════════════════════════════
-- § 2: Core Veridicality Data
-- ════════════════════════════════════════════════════════════════

/-- "He left after she arrived" entails "she arrived". -/
def after_veridical : VeridicalityDatum := ofVeridicality ost2024_after_veridical

/-- "He left before she arrived" does NOT entail "she arrived" (compatible with the
    veridical, counterfactual, or non-committal reading). -/
def before_nonveridical : VeridicalityDatum := ofVeridicality ost2024_before_nonveridical

/-- "The bomb exploded before anyone defused it" — counterfactual *before*: the defusing
    did not occur ([beaver-condoravdi-2003], "barely prevented"). -/
def before_counterfactual : VeridicalityDatum := ofVeridicality ost2024_before_counterfactual

/-- "She finished her coffee after he left" entails "he left". -/
def after_veridical_2 : VeridicalityDatum := ofVeridicality ost2024_after_veridical_2

-- ════════════════════════════════════════════════════════════════
-- § 3: Additional Veridicality Data ([beaver-condoravdi-2003], §2)
-- ════════════════════════════════════════════════════════════════

/-- "I left the party before there was any trouble" — non-committal
    ([beaver-condoravdi-2003], ex. 43; B&C's (22) Supreme Court case is counterfactual). -/
def before_noncommittal : VeridicalityDatum := ofVeridicality ost2024_before_noncommittal

/-- "Mozart died before he finished the Requiem" — counterfactual
    ([beaver-condoravdi-2003], ex. 24). -/
def before_counterfactual_mozart : VeridicalityDatum := ofVeridicality ost2024_before_counterfactual_mozart

-- B&C's before/after logical-property asymmetries (antisymmetry, transitivity, NPI
-- licensing) are Anscombe's ([anscombe-1964] §I-II), formalized canonically in
-- `Studies/Anscombe1964.lean` (`Anscombe.before_antisymmetric`, `before_transitive`,
-- `after_not_antisymmetric`, `after_not_transitive`, `before_complement_DE`,
-- `after_complement_UE`). They are not Ogihara & Steinert-Threlkeld's contribution, so
-- this study consumes them rather than restating them.

-- B&C's (32)/(33) — the "ketchup"/"squares had four sides" Anscombe overgeneration —
-- are formalized as `Anscombe.before_overgenerates` (in `Studies/Anscombe1964.lean`),
-- not as the fabricated "win before entering" examples this file previously carried.

open Tense.TemporalConnectives.BeaverCondoravdi

-- ════════════════════════════════════════════════════════════════
-- § 6: Counterexamples to B&C (O&[ogihara-steinert-threlkeld-2024], §5)
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
    (before day 276). (O&[ogihara-steinert-threlkeld-2024], §5.1, ex. 20a) -/
def ost_counterexample_ohtani : BCCounterexampleDatum where
  sentence := ost2024_ohtani.primaryText
  aTime := 276
  complementUpperBound := 275
  boundedBefore := by omega
  reading := .counterfactual

/-- (20b) "2020 might come to an end before it snows for the first time this year."
    (Uttered on Christmas Day in 2020.) The expression *this year* refers back
    to 2020. Since the first snow of 2020 can only occur in 2020, the modal
    proposal that posits a fictitious snow event after the end of 2020 does not
    work. (O&[ogihara-steinert-threlkeld-2024], §5.1, ex. 20b) -/
def ost_counterexample_snow : BCCounterexampleDatum where
  sentence := ost2024_snow.primaryText
  aTime := 366
  complementUpperBound := 366
  boundedBefore := le_refl _
  reading := .nonCommittal

/-- (20c) "July 1999 will come to an end before Nostradamus' prophecy about the
    end of the world comes true." (Uttered a few minutes before the end of July
    1999. Assumes Michel de Nostradamus predicted that in July 1999, a great King
    of terror would come from the sky and destroy the world.) The prophecy can
    only come true if the world is destroyed in July 1999 — it cannot come true
    after the end of July 1999. (O&[ogihara-steinert-threlkeld-2024], §5.1, ex. 20c) -/
def ost_counterexample_nostradamus : BCCounterexampleDatum where
  sentence := ost2024_nostradamus.primaryText
  aTime := 31
  complementUpperBound := 31
  boundedBefore := le_refl _
  reading := .counterfactual

-- ════════════════════════════════════════════════════════════════
-- § 7: Non-Committal Reading Problems (O&[ogihara-steinert-threlkeld-2024], §5.2)
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

/-- Derive a `NonCommittalDatum` from a generated `LinguisticExample`. -/
def ofNonCommittal (e : LinguisticExample) : NonCommittalDatum where
  sentence := e.primaryText
  nonCommittalAvailable := flagOf e "noncommittal_available"
  explanation := e.comment

/-- "Mary will leave the party before Bill gets drunk" — non-committal reading available
    (getting drunk is a normal continuation). (O&[ogihara-steinert-threlkeld-2024], §5.2) -/
def noncommittal_available : NonCommittalDatum := ofNonCommittal ost2024_noncommittal_available

/-- "Mary will leave the party before Quebec becomes an independent country" — non-committal
    reading unavailable (Quebec independence is not a normal continuation); B&C's Event
    Continuation Condition should block this. (O&[ogihara-steinert-threlkeld-2024], §5.2) -/
def noncommittal_unavailable : NonCommittalDatum := ofNonCommittal ost2024_noncommittal_unavailable

/-- The non-committal reading is sensitive to contextual plausibility:
    available when the complement is a normal continuation, unavailable
    when it is pragmatically impossible. -/
theorem noncommittal_plausibility_sensitive :
    noncommittal_available.nonCommittalAvailable = true ∧
    noncommittal_unavailable.nonCommittalAvailable = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 8: Cross-Linguistic Data (O&[ogihara-steinert-threlkeld-2024], §3)
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
    from the perspective of the main-clause event. (O&[ogihara-steinert-threlkeld-2024], §3) -/
def japanese_mae : CrossLinguisticDatum where
  language := "Japanese"
  connective := "mae (前)"
  gloss := "before"
  observation := "complement always non-past tense, even in past contexts"
  supportsNonveridicality := true

/-- Japanese *ato* ('after') allows past tense in its complement,
    consistent with the veridical analysis: the complement event
    is presented as having occurred. (O&[ogihara-steinert-threlkeld-2024], §3) -/
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


-- ════════════════════════════════════════════════════════════════
-- Bridge content (merged from Bridge.lean)
-- ════════════════════════════════════════════════════════════════

open Tense.TemporalConnectives
open English.TemporalExpressions

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
    ∀ (P Q : Event ℤ → Prop), AnscombeEvent.after P Q → ∃ e : Event ℤ, Q e :=
  fun P Q h => AnscombeEvent.after_veridical P Q h

/-- O&ST's theory derives *before*'s non-veridicality from the universal
    quantification over the complement: ∃e₁[P(e₁) ∧ ∀e₂[Q(e₂) →...]] is
    vacuously true when Q has no witnesses.

    Concretely: any P-event with an empty Q yields `before(P, Q)`. -/
theorem before_nonveridicality_derived :
    ∃ (P Q : Event ℤ → Prop), AnscombeEvent.before P Q ∧ ¬∃ e : Event ℤ, Q e :=
  AnscombeEvent.before_nonveridical

-- ════════════════════════════════════════════════════════════════
-- § 12: Concrete Scenario Verification
-- ════════════════════════════════════════════════════════════════

/-- Scenario: "He left₁ after she arrived₀" with punctual events.
    - leaving event at time 1
    - arriving event at time 0
    O&ST predicts: after(leave, arrive) holds (τ(arrive) ≺ τ(leave)). -/
theorem scenario_after_punctual :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .dynamic⟩
    let arrive : Event ℤ := ⟨⟨⟨0, 0⟩, le_refl _⟩, .dynamic⟩
    AnscombeEvent.after (· = leave) (· = arrive) := by
  refine ⟨⟨⟨⟨1, 1⟩, le_refl _⟩, .dynamic⟩, ⟨⟨⟨0, 0⟩, le_refl _⟩, .dynamic⟩, rfl, rfl, ?_⟩
  simp [NonemptyInterval.precedes, Event.τ]

/-- Scenario: "He left₁ before she arrived₃" with punctual events.
    - leaving event at time 1
    - arriving event at time 3
    O&ST predicts: before(leave, arrive) holds (τ(leave) ≺ τ(arrive)). -/
theorem scenario_before_punctual :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .dynamic⟩
    let arrive : Event ℤ := ⟨⟨⟨3, 3⟩, le_refl _⟩, .dynamic⟩
    AnscombeEvent.before (· = leave) (· = arrive) := by
  refine ⟨⟨⟨⟨1, 1⟩, le_refl _⟩, .dynamic⟩, rfl, ?_⟩
  intro e₂ rfl
  simp [NonemptyInterval.precedes, Event.τ]

/-- Scenario: "The bomb exploded₅ before anyone defused it" (nobody defused it).
    O&ST predicts: before(explode, defuse) holds vacuously (no defuse-events). -/
theorem scenario_before_counterfactual :
    let explode : Event ℤ := ⟨⟨⟨5, 5⟩, le_refl _⟩, .dynamic⟩
    AnscombeEvent.before (· = explode) (fun _ => False) := by
  exact ⟨⟨⟨⟨5, 5⟩, le_refl _⟩, .dynamic⟩, rfl, fun _ h => h.elim⟩

-- ════════════════════════════════════════════════════════════════
-- § 13: Cross-Level Projection Verification
-- ════════════════════════════════════════════════════════════════

/-- The punctual after-scenario projects correctly through eventDenotation:
    O&ST.after implies Anscombe.after on the projected interval sets. -/
theorem scenario_after_projects :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .dynamic⟩
    let arrive : Event ℤ := ⟨⟨⟨0, 0⟩, le_refl _⟩, .dynamic⟩
    Anscombe.after (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  AnscombeEvent.after_implies_anscombe _ _ scenario_after_punctual

/-- The punctual before-scenario projects correctly through eventDenotation. -/
theorem scenario_before_projects :
    let leave : Event ℤ := ⟨⟨⟨1, 1⟩, le_refl _⟩, .dynamic⟩
    let arrive : Event ℤ := ⟨⟨⟨3, 3⟩, le_refl _⟩, .dynamic⟩
    Anscombe.before (eventDenotation (· = leave)) (eventDenotation (· = arrive)) :=
  AnscombeEvent.before_implies_anscombe _ _ scenario_before_punctual

-- ════════════════════════════════════════════════════════════════
-- § 17: Cross-Linguistic Bridge (Japanese)
-- ════════════════════════════════════════════════════════════════

open Japanese.TemporalConnectives in
/-- The Japanese Fragment entry for *mae* agrees with the cross-linguistic
    datum: both record that *mae* supports the non-veridicality analysis. -/
theorem japanese_mae_matches_datum :
    mae.complementVeridical = false ∧
    japanese_mae.supportsNonveridicality = true :=
  ⟨rfl, rfl⟩

open Japanese.TemporalConnectives in
/-- The Japanese Fragment entry for *ato* agrees with the cross-linguistic
    datum: *ato* is veridical and does not support non-veridicality. -/
theorem japanese_ato_matches_datum :
    ato.complementVeridical = true ∧
    japanese_ato.supportsNonveridicality = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 18: Progressive Analogy (O&[ogihara-steinert-threlkeld-2024], §3)
-- ════════════════════════════════════════════════════════════════

/-! [ogihara-steinert-threlkeld-2024] §3 observe that the progressive and
    anti-veridical *before* share the same modal-temporal structure:

    - **Progressive** "Mozart was composing the Requiem (when he died)":
      at the reference time, there is an ongoing event (composing) that in
      some **inertia worlds** ([landman-1992]) reaches completion.

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

open Semantics.Aspect
open Semantics.Aspect.SubintervalProperty

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
    `impf_entails_prfv_of_csub` from SubintervalProperty.lean. -/
theorem csip_entails_completion
    {W Time : Type*} [LinearOrder Time]
    (P : W → Event Time → Prop) (hCSIP : HasClosedSubintervalProp P)
    (w : W) (t : NonemptyInterval Time) :
    IMPF P w t → PRFV P w t :=
  fun h => impf_entails_prfv_of_csub P hCSIP w t h

/-- **Non-CSIP predicates may lack completion**: the imperfective paradox shows
    that not all predicates support the IMPF→PRFV entailment.
    This is the aspectual analogue of *before*'s non-veridicality — both
    arise from a universal quantification (over subintervals / over complement
    events) that can be vacuously satisfied.

    Formally: ¬(∀ P, HasSubintervalProp P). This is
    `imperfective_paradox_possible` from SubintervalProperty.lean. -/
theorem non_csip_lacks_completion
    {W : Type*} (w : W) (t₁ t₂ : ℤ) (hlt : t₁ < t₂) :
    ¬ (∀ (P : W → Event ℤ → Prop), HasSubintervalProp P) :=
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
    (P Q : W → Event Time → Prop)
    (alternatives : Event Time → Set W)
    (w : W) (t : NonemptyInterval Time)
    (hIMPF : IMPF P w t)
    (hContinuation : ∀ e, P w e → t < e.τ →
      ∀ w' ∈ alternatives e, ∃ e', Q w' e') :
    ∃ e, t < e.τ ∧ P w e ∧
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
    (P : W → Event Time → Prop) (w : W) (t : NonemptyInterval Time) :
    (HasClosedSubintervalProp P → IMPF P w t → PRFV P w t) ∧
    (IMPF P w t → ¬HasClosedSubintervalProp P →
      ¬(∀ (t' : NonemptyInterval Time), t' ≤ t →
        ∃ e, e.τ = t' ∧ P w e) →
      -- Modal resolution needed: must appeal to alternative worlds
      ∃ e, t < e.τ ∧ P w e) := by
  constructor
  · intro hCSIP; exact impf_entails_prfv_of_csub P hCSIP w t
  · intro ⟨e, hSub, hP⟩ _ _
    exact ⟨e, hSub, hP⟩

-- ════════════════════════════════════════════════════════════════
-- § 19: Revamped Truth Conditions (O&[ogihara-steinert-threlkeld-2024], def 19)
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
def abuts (I₀ I₁ : NonemptyInterval T) : Prop :=
  I₀.snd = I₁.fst

/-- An eventuality e₁ "holds throughout" an interval that abuts I₀:
    e₁'s runtime extends from before I₀ through to (at least) I₀'s start. -/
def holdsAtAbutting (runtime : E → NonemptyInterval T) (e₁ : E)
    (I₀ : NonemptyInterval T) : Prop :=
  (runtime e₁).fst ≤ I₀.fst ∧ I₀.fst ≤ (runtime e₁).snd

/-- Denotation type for O&ST's truth conditions: sets of
    world–interval–eventuality triples. -/
abbrev SitDenot (W T E : Type*) [LinearOrder T] := Set (W × NonemptyInterval T × E)

/-- **Case (i)**: ⟦A before B⟧ = 1 when the complement B already holds
    at some interval after I₀ in the actual world w₀. -/
def beforeCase_veridical
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : NonemptyInterval T, I₀.snd < I₂.fst ∧
    ∃ e₄ : E, (w₀, I₂, e₄) ∈ B

/-- **Case (ii)**: ⟦A before B⟧ = 0 when the complement B already holds
    at some interval at or before I₀ in the actual world w₀. -/
def beforeCase_false
    (A B : SitDenot W T E)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧ ∃ I₂ : NonemptyInterval T, I₂.snd ≤ I₀.fst ∧
    ∃ e₅ : E, (w₀, I₂, e₅) ∈ B

/-- **Case (iii)**: The modal case. ⟦A before B⟧ = 1 when A holds at ⟨w₀,I₀,e₀⟩
    and I₀ precedes the earliest I₁ such that:
    - there is an eventuality e₁ in w₀ whose runtime abuts I₀,
    - there is an alternative world w₁ ∈ alt(w₀, I₀, e₁),
    - in w₁, the counterpart e₂ of e₁ continues and CAUSES an eventuality e₃,
    - ⟨w₁, I₁, e₃⟩ ∈ ⟦B⟧. -/
def beforeCase_modal
    (A B : SitDenot W T E)
    (runtime : E → NonemptyInterval T)
    (alt : W → NonemptyInterval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
  (w₀, I₀, e₀) ∈ A ∧
  ∃ I₁ : NonemptyInterval T,
    I₀.snd < I₁.fst ∧  -- I₀ precedes I₁
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
    (runtime : E → NonemptyInterval T)
    (alt : W → NonemptyInterval T → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) : Prop :=
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
    (w₀ : W) (I₀ : NonemptyInterval T) (e₀ : E) :
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
      (runtime : Unit → NonemptyInterval ℤ)
      (alt : Bool → NonemptyInterval ℤ → Unit → Set Bool)
      (cause : Bool → Unit → Unit → Prop)
      (counterpart : Bool → Unit → Bool → Unit → Prop)
      (w₀ : Bool) (I₀ : NonemptyInterval ℤ) (e₀ : Unit),
    beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀ ∧
    ¬∃ I e, (w₀, I, e) ∈ B := by
  refine ⟨{(false, ⟨⟨0, 0⟩, le_refl _⟩, ())},
          {(true, ⟨⟨2, 2⟩, le_refl _⟩, ())},
          fun _ => ⟨⟨-1, 0⟩, by omega⟩,
          fun _ _ _ => {true},
          fun _ _ _ => True,      -- cause : W → E → E → Prop
          fun _ _ _ _ => True,    -- counterpart : W → E → W → E → Prop
          false, ⟨⟨0, 0⟩, le_refl _⟩, (), ?_, ?_⟩
  · refine ⟨rfl, ⟨⟨2, 2⟩, le_refl _⟩, ?_, (), ⟨?_, true, rfl, (),
      ⟨trivial, (), trivial, rfl⟩⟩⟩
    · show (0 : ℤ) < 2; omega
    · exact ⟨by show (-1 : ℤ) ≤ 0; omega, by show (0 : ℤ) ≤ 0; omega⟩
  · rintro ⟨I, e, hB⟩
    simp only [Set.mem_singleton_iff, Prod.mk.injEq] at hB
    exact absurd hB.1 Bool.false_ne_true

/-- Cases (i) and (ii) are mutually exclusive when the complement occurs at
    a single interval: it cannot be both before and after I₀. -/
theorem cases_i_ii_exclusive
    (I₀ I_B : NonemptyInterval T)
    (hAfter : I₀.snd < I_B.fst)
    (hBefore : I_B.snd ≤ I₀.fst) :
    False := by
  have : I_B.snd < I_B.fst := lt_of_le_of_lt hBefore (lt_of_le_of_lt I₀.fst_le_snd hAfter)
  exact absurd this (not_lt.mpr I_B.fst_le_snd)

/-- The Mozart scenario: "Mozart died before he finished the Requiem."
    This is the anti-veridical reading (case iii). Mozart's death (e₀) is at
    I₀. In some alternative world w₁, Mozart's composing (e₁, ongoing at I₀)
    has a counterpart e₂ whose continuation CAUSES a finishing event e₃ at I₁.
    B ("finishing the Requiem") holds at ⟨w₁, I₁, e₃⟩ but NOT in w₀. -/
theorem mozart_is_case_iii
    {W E : Type*}
    (A B : SitDenot W ℤ E)
    (runtime : E → NonemptyInterval ℤ)
    (alt : W → NonemptyInterval ℤ → E → Set W)
    (cause : W → E → E → Prop)
    (counterpart : W → E → W → E → Prop)
    (w₀ : W) (I₀ : NonemptyInterval ℤ) (e₀ : E)
    (hNoFinish : ¬∃ I e, (w₀, I, e) ∈ B)
    (hModal : beforeCase_modal A B runtime alt cause counterpart w₀ I₀ e₀) :
    OST.before A B runtime alt cause counterpart w₀ I₀ e₀ := by
  refine ⟨?_, Or.inr hModal⟩
  intro ⟨_, I₂, _, e₅, hB⟩
  exact hNoFinish ⟨I₂, e₅, hB⟩

end Def19

end OgiharaSteinertThrelkeld2024

-- ════════════════════════════════════════════════════════════════
-- Veridicality ↔ Presupposition Bridge
-- ════════════════════════════════════════════════════════════════

/-! ## Veridicality ↔ Presupposition Bridge
[beaver-condoravdi-2003] [heim-1983] [ogihara-steinert-threlkeld-2024]

Connects three layers of the temporal connective formalization:

1. **Fragment field**: `TemporalExprEntry.complementVeridical : Bool`
2. **Theory proof**: e.g., `Anscombe.after A B → ∃ t, t ∈ timeTrace B`
3. **Presupposition theory**: veridical connectives presuppose their complement
   (modeled as `PartialProp` with complement occurrence as presupposition)

For each temporal connective, the Fragment's `complementVeridical` field is
**grounded** in a theory-level proof, and matches the empirical data.
-/

namespace OgiharaSteinertThrelkeld2024.VeridicalityBridge

open Core.Order
open NonemptyInterval
open Tense.TemporalConnectives
open English.TemporalExpressions
open OgiharaSteinertThrelkeld2024

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
  refine ⟨rfl, ⟨{ NonemptyInterval.pure 0 }, ∅, ?_, ?_⟩⟩
  · exact ⟨0, ⟨NonemptyInterval.pure 0, rfl, le_refl _, le_refl _⟩,
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

open Semantics.Presupposition

/-- A temporal connective modeled as a presuppositional proposition.
    Veridical connectives presuppose their complement (like factives);
    non-veridical connectives carry no complement presupposition. -/
def connPartialProp (complementInstantiated : Bool) (connHolds : Bool) : PartialProp Unit :=
  { presup := fun _ => complementInstantiated
  , assertion := fun _ => connHolds }

theorem veridical_presupposes_complement :
    (connPartialProp true true).presup () = true := rfl

theorem nonveridical_no_presupposition :
    (connPartialProp false true).presup () = false := rfl

/-- Negation preserves complement presupposition (projection through negation). -/
theorem negation_preserves_presup :
    (PartialProp.neg (connPartialProp true true)).presup () = true := rfl

-- ============================================================================
-- § 23: B&C's Three Readings of *Before* and Presupposition
-- ============================================================================

open Tense.TemporalConnectives.BeaverCondoravdi (BeforeReading)

/-- All three readings are compatible with `complementVeridical = false`. -/
theorem all_before_readings_nonveridical :
    before_.complementVeridical = false := rfl

/-- The O&ST data covers all three B&C readings. -/
theorem bc_readings_in_data :
    before_nonveridical.complementEntailed = false ∧
    before_counterfactual.complementEntailed = false ∧
    before_noncommittal.complementEntailed = false :=
  ⟨rfl, rfl, rfl⟩

end OgiharaSteinertThrelkeld2024.VeridicalityBridge
