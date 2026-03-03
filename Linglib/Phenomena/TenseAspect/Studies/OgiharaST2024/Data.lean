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

namespace Phenomena.TenseAspect.Studies.OgiharaST2024

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

-- ════════════════════════════════════════════════════════════════
-- § 6: Counterexamples to B&C (O&@cite{ogihara-steinert-threlkeld-2024}, §5)
-- ════════════════════════════════════════════════════════════════

/-- A datum recording an empirical problem for B&C's branching-time analysis.
    These are cases where *before* is used with complement events that are
    in the past, which B&C's forward-branching `alt(w,t)` cannot handle. -/
structure BCCounterexampleDatum where
  /-- The example sentence -/
  sentence : String
  /-- Which reading of *before* is involved? -/
  reading : String
  /-- Why B&C's analysis fails -/
  problem : String
  deriving Repr

/-- "Shohei Ohtani was named the 2023 AL MVP before the 2023 MLB season ended."
    The complement event (season ending) is in the PAST relative to the
    naming event but also temporally precedes it. B&C's `alt(w,t)` at the
    naming time cannot branch to alternatives where the season doesn't end,
    because the season ending is already in the past. (O&@cite{ogihara-steinert-threlkeld-2024}, §5.1) -/
def ost_counterexample_ohtani : BCCounterexampleDatum where
  sentence := "Ohtani was named the 2023 AL MVP before the 2023 MLB season ended"
  reading := "veridical (complement occurred)"
  problem := "complement event in past; alt(w,t) cannot generate alternatives where it didn't happen"

/-- "It snowed a lot in 2020 before the pandemic hit."
    Both events are in the past. B&C's analysis requires `alt(w,t)` at the
    snow time to include alternatives where the pandemic doesn't hit, but
    the pandemic is also in the past. (O&@cite{ogihara-steinert-threlkeld-2024}, §5.1) -/
def ost_counterexample_snow : BCCounterexampleDatum where
  sentence := "It snowed a lot in 2020 before the pandemic hit"
  reading := "veridical (complement occurred)"
  problem := "both events past; branching-future model strained for past complement"

/-- "Nostradamus predicted many things before they happened."
    The complement events (predictions coming true) are in the past relative
    to utterance time. B&C would need alternatives where the predicted events
    never happen, but these events are already settled. (O&@cite{ogihara-steinert-threlkeld-2024}, §5.1) -/
def ost_counterexample_nostradamus : BCCounterexampleDatum where
  sentence := "Nostradamus predicted many things before they happened"
  reading := "veridical (complement occurred)"
  problem := "complement events settled in past; alt cannot 'unbranch' past events"

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

end Phenomena.TenseAspect.Studies.OgiharaST2024
