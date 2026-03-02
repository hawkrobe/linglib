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
- Expletive negation (EN) in *before*-clauses is attested in 50/70
  languages. EN is NOT attested in *after*-clauses.
- Italian: *prima che non* (before + EN), *finché non* (until + EN).
  French: *avant que ne* (before + EN).

-/

namespace Phenomena.TemporalConnectives.NegationData

-- ============================================================================
-- § 1: The Two-*Until* Hypothesis (Giannakidou 2002)
-- ============================================================================

/-- A judgment about the two-*until* distinction, encoding @cite{giannakidou-2002}'s cross-linguistic evidence.

    `semanticType` classifies connectives into the **before-type** (non-veridical,
    NPI-licensing, no durative restriction) vs **endpoint-type** (veridical,
    no NPI-licensing, durative restriction). This is the two-way distinction
    Giannakidou argues is lexicalized cross-linguistically.

    Note: Greek has a THIRD element — *para monon* (§§4.2, 6) — which is the
    true NPI-*until* (requires negation, entails actualization). *Prin* shares
    NPI-licensing and non-veridicality with NPI-*until* but differs in that
    it does NOT entail actualization (Giannakidou 2002, ex. 72–73, 77). -/
structure TwoUntilDatum where
  /-- Language -/
  language : String
  /-- Connective form -/
  form : String
  /-- Semantic type: before-type (non-veridical, NPI-licensing) or
      endpoint-type (veridical, durative). -/
  semanticType : String  -- "before" or "endpoint"
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
  deriving Repr

-- ============================================================================
-- § 2: Greek Data (Giannakidou 2002, §§2–4)
-- ============================================================================

/-- Greek *prin* (πριν): before-type.
    Requires subjunctive, does not require DE context (unlike English
    NPI-*until* or Greek *para monon*), non-veridical complement, licenses NPIs.
    No actualization entailment: "Efije prin na erthi o Janis" is compatible
    with Janis never coming (Giannakidou 2002, §6, ex. 72).
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

/-- English NPI-*until*: before-type (Karttunen: NPI-*until* = ¬*before*).
    Requires DE licensor (negation). Unlike Greek *prin*, English collapses
    both types under the single lexeme *until*, disambiguated by context.
    The actualization entailment of "not...until" comes from the presupposition
    (A BEFORE T ∨ A WHEN T) + assertion ¬(A BEFORE T) → A WHEN T, not from
    *until* itself being veridical.
    "The princess didn't wake up until the prince kissed her." -/
def english_npi_until : TwoUntilDatum where
  language := "English"
  form := "until (NPI)"
  semanticType := "before"
  moodRestriction := none
  requiresDE := true
  complementVeridical := false
  requiresDurativeMain := false
  licensesNPIs := true
  example_ := "The princess didn't wake up until the prince kissed her"

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
-- § 4: Expletive Negation Data (Greco 2020)
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
-- § 6: Cross-Linguistic EN Prevalence (Jin & Koenig 2021)
-- ============================================================================

/-- Cross-linguistic survey data on EN prevalence.
    @cite{jin-koenig-2021} surveyed 70 languages; 50 have EN in
    *before*-clauses. This makes EN the norm, not the exception. -/
structure ENSurvey where
  /-- Total languages surveyed -/
  totalLanguages : Nat
  /-- Languages with EN in before-clauses -/
  withEN : Nat
  /-- Languages without EN in before-clauses -/
  withoutEN : Nat
  deriving Repr

def jinKoenig2021 : ENSurvey where
  totalLanguages := 70
  withEN := 50
  withoutEN := 20

theorem en_majority :
    jinKoenig2021.withEN > jinKoenig2021.withoutEN :=
  by decide

theorem en_survey_consistent :
    jinKoenig2021.withEN + jinKoenig2021.withoutEN = jinKoenig2021.totalLanguages :=
  rfl

end Phenomena.TemporalConnectives.NegationData
