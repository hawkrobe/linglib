/-!
# Negation × Temporal Connective Interaction Data
@cite{giannakidou-2002} @cite{greco-2020} @cite{rett-2026} @cite{jin-koenig-2021}

Theory-neutral empirical data on the interaction between negation and
temporal connectives, focusing on:

1. **The two-*until* hypothesis**: Greek lexicalizes the
   distinction between NPI-*until* (= ¬*before*) and durative *until*.

2. **Expletive negation**: *before*-clauses license truth-
   conditionally vacuous negation cross-linguistically, explained by
   ambidirectionality.

## Key Empirical Generalizations

- Greek *prin* (πριν, 'before') requires subjunctive; *mexri* (μέχρι,
  'until') requires indicative. This mood distinction tracks veridicality.
- *Mexri* requires imperfective/stative main clause; *prin* has no aspect
  restriction. This mirrors Karttunen's durative selectional restriction.
- Expletive negation (EN) in *before*-clauses is attested in 50 of 74
  EN-attesting languages (722 surveyed). EN is NOT attested in *after*-clauses.
- Italian: *prima che non* (before + EN), *finché non* (until + EN).
  French: *avant que ne* (before + EN).

-/

namespace Phenomena.TemporalConnectives.NegationData

-- ============================================================================
-- § 1: The Two-*Until* Hypothesis (@cite{giannakidou-2002})
-- ============================================================================

/-- Whether a temporal connective entails that the main-clause event
    actually occurred at the boundary time.

    - `entailment`: actualization is part of the assertion — cancellation
      yields contradiction (@cite{giannakidou-2002}, ex. 38).
    - `implicature`: actualization is a Q-implicature — cancellable
      (@cite{giannakidou-2002}, ex. 7: "Sure, the princess slept until
      midnight. In fact she only woke up at 2am.").
    - `none`: no actualization inference at all (@cite{giannakidou-2002},
      ex. 72–73: *prin/before* is compatible with the complement event
      never occurring). -/
inductive ActualizationStatus where
  | entailment
  | implicature
  | none
  deriving DecidableEq, Repr, BEq

/-- A judgment about the two-*until* distinction, encoding
    @cite{giannakidou-2002}'s cross-linguistic evidence.

    `semanticType` classifies connectives into three groups:
    - **before-type** (non-veridical, NPI-licensing, no durative restriction)
    - **endpoint-type** (veridical, no NPI-licensing, durative restriction)
    - **eventive-type** (requires anti-veridical trigger, actualization entailment)

    Greek lexicalizes all three: *prin* (before-type), *mexri* (endpoint-type),
    *para monon* (eventive-type). English collapses eventive and before under
    the single lexeme *until*, disambiguated by negation context. -/
structure TwoUntilDatum where
  /-- Language -/
  language : String
  /-- Connective form -/
  form : String
  /-- Semantic type: "before", "endpoint", or "eventive". -/
  semanticType : String
  /-- Required mood of complement (if applicable) -/
  moodRestriction : Option String
  /-- Does it require a DE (downward-entailing) licensor? -/
  requiresDE : Bool
  /-- Is the complement veridical? -/
  complementVeridical : Bool
  /-- Does it restrict the main clause to durative aspect? -/
  requiresDurativeMain : Bool
  /-- Does it license NPIs in the complement? -/
  licensesNPIs : Bool
  /-- Example sentence -/
  example_ : String
  /-- Does the connective entail actualization of a change-of-state event
      at the boundary time? This is the central distinction between
      NPI-*until* (entailment) and durative *until* (implicature). -/
  actualizationStatus : ActualizationStatus
  deriving Repr

-- ============================================================================
-- § 2: Greek Data (@cite{giannakidou-2002}, §§2–4)
-- ============================================================================

/-- Greek *prin* (πριν): before-type.
    Requires subjunctive, does not require DE context (unlike English
    NPI-*until* or Greek *para monon*), non-veridical complement, licenses NPIs.
    No actualization entailment: *prin* is compatible with the complement
    event never occurring (@cite{giannakidou-2002}, §6, ex. (72):
    "I prigipisa dhen eftase prin apo ta mesanixta" — the princess may or
    may not have arrived).
    "Efije prin na erthi o Janis."
    'She left before Janis came.' -/
def greek_prin : TwoUntilDatum where
  language := "Greek"
  form := "prin (πριν)"
  semanticType := "before"
  moodRestriction := some "subjunctive"
  requiresDE := false
  complementVeridical := false
  requiresDurativeMain := false
  licensesNPIs := true
  example_ := "Efije prin na erthi o Janis (She left before Janis came)"
  actualizationStatus := .none

/-- Greek *mexri* (μέχρι): endpoint-type.
    Requires indicative, veridical complement, requires imperfective/stative
    main clause, does NOT license NPIs. Actualization is a conversational
    implicature, not an entailment.
    "I Maria perimine mexri irthi o Janis."
    'Maria waited until Janis came.' -/
def greek_mexri : TwoUntilDatum where
  language := "Greek"
  form := "mexri (μέχρι)"
  semanticType := "endpoint"
  moodRestriction := some "indicative"
  requiresDE := false
  complementVeridical := true
  requiresDurativeMain := true
  licensesNPIs := false
  example_ := "I Maria perimine mexri irthi o Janis (Maria waited until Janis came)"
  actualizationStatus := .implicature

/-- English NPI-*until*: eventive-type (@cite{giannakidou-2002}).
    Requires DE licensor (negation). Unlike Greek *prin*, English collapses
    both types under the single lexeme *until*, disambiguated by context.

    Classified as "eventive" (not "before") because English NPI-*until*
    patterns with Greek *para monon* on all diagnostics: actualization is
    an entailment, a DE trigger is required, and there is no durative
    restriction on the main clause. Karttunen's logical form (NPI-*until*
    = ¬*before*) captures the truth conditions, but the phenomenological
    classification tracks the same semantic type as *para monon*.

    "The princess didn't wake up until the prince kissed her." -/
def english_npi_until : TwoUntilDatum where
  language := "English"
  form := "until (NPI)"
  semanticType := "eventive"
  moodRestriction := none
  requiresDE := true
  complementVeridical := false
  requiresDurativeMain := false
  licensesNPIs := true
  example_ := "The princess didn't wake up until the prince kissed her"
  actualizationStatus := .entailment

/-- English durative *until*: endpoint-type. No DE requirement, veridical
    complement, durative main clause required.
    "John slept until 3pm." -/
def english_dur_until : TwoUntilDatum where
  language := "English"
  form := "until (durative)"
  semanticType := "endpoint"
  moodRestriction := none
  requiresDE := false
  complementVeridical := true
  requiresDurativeMain := true
  licensesNPIs := false
  example_ := "John slept until 3pm"
  actualizationStatus := .implicature

/-- Greek *para monon* (παρά μονον, lit. 'but only'): eventive-type.
    The true NPI-*until* in Greek — lexically distinct from both *mexri*
    (durative until) and *prin* (before). Requires anti-veridical trigger
    (negation, 'without'). Entails actualization: the main-clause event
    occurred at the boundary time. Scalar (introduces a scale of
    contextually relevant times).

    @cite{giannakidou-2002}, §3.2: *para monon* is incompatible with
    negated perfective eventives (ex. 35: *I prigipisa dhen eftase para
    monon ta mesanixta*) but compatible with perfective statives that
    shift to achievement reading (ex. 37: *I prigipisa dhen (apo)kimithike
    para monon ta mesanixta* = 'The princess didn't fall asleep until
    midnight').

    Cancellation of actualization yields contradiction (ex. 38):
    '#I prigipisa dhen eftase para monon ta mesanixta. Dhen eftase kan
    ekino to vradi.' ('#The princess didn't arrive until midnight. She
    didn't even arrive that night.') -/
def greek_para_monon : TwoUntilDatum where
  language := "Greek"
  form := "para monon (παρά μονον)"
  semanticType := "eventive"
  moodRestriction := none
  requiresDE := true
  complementVeridical := false
  requiresDurativeMain := false
  licensesNPIs := false
  example_ := "I prigipisa dhen (apo)kimithike para monon ta mesanixta (The princess didn't fall asleep until midnight)"
  actualizationStatus := .entailment

-- ============================================================================
-- § 3: Two-*Until* Diagnostic Tests
-- ============================================================================

/-- The mood diagnostic: NPI-*until* type takes subjunctive (in languages
    with the distinction); durative *until* takes indicative. -/
theorem mood_diagnostic :
    greek_prin.moodRestriction = some "subjunctive" ∧
    greek_mexri.moodRestriction = some "indicative" :=
  ⟨rfl, rfl⟩

/-- The veridicality diagnostic: NPI-*until* is non-veridical;
    durative *until* is veridical. -/
theorem veridicality_diagnostic :
    greek_prin.complementVeridical = false ∧
    greek_mexri.complementVeridical = true :=
  ⟨rfl, rfl⟩

/-- The aspect diagnostic: durative *until* requires durative main clause;
    NPI-*until* has no such restriction. -/
theorem aspect_diagnostic :
    greek_prin.requiresDurativeMain = false ∧
    greek_mexri.requiresDurativeMain = true :=
  ⟨rfl, rfl⟩

/-- The NPI licensing diagnostic: NPI-*until* (= ¬before) licenses NPIs;
    durative *until* does not. -/
theorem npi_licensing_diagnostic :
    greek_prin.licensesNPIs = true ∧
    greek_mexri.licensesNPIs = false :=
  ⟨rfl, rfl⟩

/-- All four diagnostics consistently distinguish the two types. -/
theorem diagnostics_aligned :
    -- before-type
    greek_prin.semanticType = "before" ∧
    greek_prin.complementVeridical = false ∧
    greek_prin.requiresDurativeMain = false ∧
    greek_prin.licensesNPIs = true ∧
    -- endpoint-type
    greek_mexri.semanticType = "endpoint" ∧
    greek_mexri.complementVeridical = true ∧
    greek_mexri.requiresDurativeMain = true ∧
    greek_mexri.licensesNPIs = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 3.5: Actualization Diagnostics (@cite{giannakidou-2002}, §§3.2, 6)
-- ============================================================================

/-- The actualization diagnostic: the three-way split.
    - *para monon* / English NPI-*until*: actualization is an entailment
    - *mexri* / English durative *until*: actualization is an implicature
    - *prin*: no actualization at all -/
theorem actualization_three_way :
    greek_para_monon.actualizationStatus = .entailment ∧
    english_npi_until.actualizationStatus = .entailment ∧
    greek_mexri.actualizationStatus = .implicature ∧
    english_dur_until.actualizationStatus = .implicature ∧
    greek_prin.actualizationStatus = .none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- *Para monon* requires an anti-veridical trigger (negation, 'without');
    *mexri* does not; *prin* does not.
    This distinguishes eventive-type from both endpoint-type and before-type. -/
theorem de_requirement_diagnostic :
    greek_para_monon.requiresDE = true ∧
    greek_mexri.requiresDE = false ∧
    greek_prin.requiresDE = false :=
  ⟨rfl, rfl, rfl⟩

/-- *Para monon* patterns with English NPI-*until* on actualization and
    DE-requirement, confirming it is the Greek lexicalization of
    Karttunen's punctual *until*. -/
theorem para_monon_matches_english_npi_until :
    greek_para_monon.actualizationStatus = english_npi_until.actualizationStatus ∧
    greek_para_monon.requiresDE = english_npi_until.requiresDE ∧
    greek_para_monon.requiresDurativeMain = english_npi_until.requiresDurativeMain :=
  ⟨rfl, rfl, rfl⟩

/-- *Para monon* differs from *prin* on actualization:
    *prin/before* has no actualization, *para monon* entails it.
    This is the paper's central finding — NPI-*until* ≠ *before*
    on actualization status (@cite{giannakidou-2002}, §6). -/
theorem para_monon_differs_from_prin :
    greek_para_monon.actualizationStatus ≠ greek_prin.actualizationStatus ∧
    greek_para_monon.semanticType ≠ greek_prin.semanticType :=
  ⟨by decide, by decide⟩

/-- The three Greek connectives are pairwise distinct on semantic type. -/
theorem greek_three_way_lexicalized :
    greek_prin.semanticType ≠ greek_mexri.semanticType ∧
    greek_prin.semanticType ≠ greek_para_monon.semanticType ∧
    greek_mexri.semanticType ≠ greek_para_monon.semanticType :=
  ⟨by decide, by decide, by decide⟩

-- ============================================================================
-- § 4: Expletive Negation Data (@cite{greco-2020})
-- ============================================================================

/-- An attested instance of expletive negation (EN) in a temporal clause.
    EN is truth-conditionally vacuous: the sentence has the same truth
    conditions with or without the negative marker. -/
structure ExpletiveNegDatum where
  /-- Language -/
  language : String
  /-- Temporal connective hosting EN -/
  connective : String
  /-- Surface form with EN -/
  formWithEN : String
  /-- Surface form without EN (same truth conditions) -/
  formWithoutEN : String
  /-- Is EN obligatory in this context? -/
  obligatory : Bool
  /-- Does EN trigger a manner implicature ("much before")? -/
  mannerImplicature : Bool
  /-- Example sentence -/
  example_ : String
  deriving Repr

/-- Italian *prima che non* — EN in *before*-clause.
    "Mario è partito prima che non arrivasse Gianni."
    'Mario left before Gianni arrived.'
    EN is optional; triggers "well before" reading. -/
def italian_prima_EN : ExpletiveNegDatum where
  language := "Italian"
  connective := "prima che (before)"
  formWithEN := "prima che non"
  formWithoutEN := "prima che"
  obligatory := false
  mannerImplicature := true
  example_ := "Mario è partito prima che non arrivasse Gianni"

/-- Italian *finché non* — EN in *until*-clause.
    "Maria ha aspettato finché non è arrivato Gianni."
    'Maria waited until Gianni arrived.'
    EN is often felt as obligatory in colloquial Italian. -/
def italian_finche_EN : ExpletiveNegDatum where
  language := "Italian"
  connective := "finché (until)"
  formWithEN := "finché non"
  formWithoutEN := "finché"
  obligatory := false
  mannerImplicature := false
  example_ := "Maria ha aspettato finché non è arrivato Gianni"

/-- French *avant que ne* — EN in *before*-clause.
    "Jean est parti avant que Marie ne soit arrivée."
    'Jean left before Marie arrived.'
    Historically obligatory in formal registers; now optional. -/
def french_avant_EN : ExpletiveNegDatum where
  language := "French"
  connective := "avant que (before)"
  formWithEN := "avant que ne"
  formWithoutEN := "avant que"
  obligatory := false
  mannerImplicature := false
  example_ := "Jean est parti avant que Marie ne soit arrivée"

-- ============================================================================
-- § 5: EN Distribution Generalizations
-- ============================================================================

/-! Note: The ambidirectionality↔EN correspondence formalized here is
    also verified (more comprehensively) in
    `Phenomena.Negation.ExpletiveNegation.rett_generalization`
    over the `ENConstruction` enum, which covers all six construction
    types. The `ENDistribution` entries below provide the same
    generalization over a subset (temporal connectives only). -/

/-- EN is attested with *before* and *until* but NOT with *after* or *when*.
    This follows from ambidirectionality: *before* is ambidirectional
    (negating the complement doesn't change truth conditions), so EN is vacuous.
    *After* is NOT ambidirectional, so EN would change truth conditions
    (genuine negation, not expletive). -/
structure ENDistribution where
  /-- Connective -/
  connective : String
  /-- Is EN attested cross-linguistically? -/
  enAttested : Bool
  /-- Is the connective ambidirectional? -/
  ambidirectional : Bool
  deriving Repr

def before_EN : ENDistribution where
  connective := "before"
  enAttested := true
  ambidirectional := true

def after_EN : ENDistribution where
  connective := "after"
  enAttested := false
  ambidirectional := false

def until_EN : ENDistribution where
  connective := "until (NPI type)"
  enAttested := true
  ambidirectional := true

def when_EN : ENDistribution where
  connective := "when"
  enAttested := false
  ambidirectional := false

/-- EN is attested iff the connective is ambidirectional.
    This is the core empirical generalization: EN is licensed exactly in
    those environments where negation is truth-conditionally vacuous. -/
theorem en_iff_ambidirectional :
    before_EN.enAttested = before_EN.ambidirectional ∧
    after_EN.enAttested = after_EN.ambidirectional ∧
    until_EN.enAttested = until_EN.ambidirectional ∧
    when_EN.enAttested = when_EN.ambidirectional :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Cross-Linguistic EN Prevalence (@cite{jin-koenig-2021})
-- ============================================================================

/-! EN survey data (722 languages, 74 with EN, 37 genera) is defined
    in `Phenomena.Negation.Typology.enSurvey` to avoid duplication. -/

end Phenomena.TemporalConnectives.NegationData
