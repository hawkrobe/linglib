/-!
# Negation × Temporal Connective Interaction Data
@cite{giannakidou-2002} @cite{greco-2020}

Theory-neutral empirical data on the interaction between negation and
temporal connectives, focusing on:

1. **The two-*until* hypothesis** (Giannakidou 2002): Greek lexicalizes the
   distinction between NPI-*until* (= ¬*before*) and durative *until*.

2. **Expletive negation** (Greco 2019): *before*-clauses license truth-
   conditionally vacuous negation cross-linguistically, explained by
   ambidirectionality (Rett 2026).

## Key Empirical Generalizations

- Greek *prin* (πριν, 'before') requires subjunctive; *mexri* (μέχρι,
  'until') requires indicative. This mood distinction tracks veridicality.
- *Mexri* requires imperfective/stative main clause; *prin* has no aspect
  restriction. This mirrors Karttunen's durative selectional restriction.
- Expletive negation (EN) in *before*-clauses is attested in 50/70
  languages (Jin & Koenig 2021). EN is NOT attested in *after*-clauses.
- Italian: *prima che non* (before + EN), *finché non* (until + EN).
  French: *avant que ne* (before + EN).

## References

- Giannakidou, A. (2002). UNTIL, aspect and negation. *SALT* 12.
- Greco, M. (2020). On the syntax of surprise negation sentences: A case
  study on expletive negation. *NLLT* 38(3), 775–825.
- Jin, Y. & Koenig, J.-P. (2021). A cross-linguistic study of expletive
  negation. *Linguistic Typology* 25(1), 39–78.
- Rett, J. (2026). Semantic ambivalence and expletive negation. Ms.
-/

namespace Phenomena.TemporalConnectives.NegationData

-- ============================================================================
-- § 1: The Two-*Until* Hypothesis (Giannakidou 2002)
-- ============================================================================

/-- A judgment about the two-*until* distinction, encoding Giannakidou's
    (2002) cross-linguistic evidence. -/
structure TwoUntilDatum where
  /-- Language -/
  language : String
  /-- Connective form -/
  form : String
  /-- Semantic type: NPI-until (= ¬before) or durative until -/
  semanticType : String  -- "NPI" or "durative"
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

/-- Greek *prin* (πριν): NPI-*until* / *before* type.
    Requires subjunctive, does not require DE context (unlike English
    NPI-*until*), non-veridical complement, licenses NPIs.
    "Efije prin na erthi o Janis."
    'She left before Janis came.' -/
def greek_prin : TwoUntilDatum where
  language := "Greek"
  form := "prin (πριν)"
  semanticType := "NPI"
  moodRestriction := some "subjunctive"
  requiresDE := false
  complementVeridical := false
  requiresDurativeMain := false
  licensesNPIs := true
  example_ := "Efije prin na erthi o Janis (She left before Janis came)"

/-- Greek *mexri* (μέχρι): durative *until* type.
    Requires indicative, veridical complement, requires imperfective/stative
    main clause, does NOT license NPIs.
    "I Maria perimine mexri irthi o Janis."
    'Maria waited until Janis came.' -/
def greek_mexri : TwoUntilDatum where
  language := "Greek"
  form := "mexri (μέχρι)"
  semanticType := "durative"
  moodRestriction := some "indicative"
  requiresDE := false
  complementVeridical := true
  requiresDurativeMain := true
  licensesNPIs := false
  example_ := "I Maria perimine mexri irthi o Janis (Maria waited until Janis came)"

/-- English NPI-*until*: requires DE licensor (negation).
    "The princess didn't wake up until the prince kissed her." -/
def english_npi_until : TwoUntilDatum where
  language := "English"
  form := "until (NPI)"
  semanticType := "NPI"
  moodRestriction := none
  requiresDE := true
  complementVeridical := false
  requiresDurativeMain := false
  licensesNPIs := true
  example_ := "The princess didn't wake up until the prince kissed her"

/-- English durative *until*: no DE requirement, veridical complement,
    durative main clause required.
    "John slept until 3pm." -/
def english_dur_until : TwoUntilDatum where
  language := "English"
  form := "until (durative)"
  semanticType := "durative"
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
    -- NPI type
    greek_prin.semanticType = "NPI" ∧
    greek_prin.complementVeridical = false ∧
    greek_prin.requiresDurativeMain = false ∧
    greek_prin.licensesNPIs = true ∧
    -- durative type
    greek_mexri.semanticType = "durative" ∧
    greek_mexri.complementVeridical = true ∧
    greek_mexri.requiresDurativeMain = true ∧
    greek_mexri.licensesNPIs = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: Expletive Negation Data (Greco 2019)
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

/-- EN is attested with *before* and *until* but NOT with *after* or *when*.
    This follows from ambidirectionality (Rett 2026): *before* is ambidirectional
    (negating the complement doesn't change truth conditions), so EN is vacuous.
    *After* is NOT ambidirectional, so EN would change truth conditions
    (genuine negation, not expletive). -/
structure ENDistribution where
  /-- Connective -/
  connective : String
  /-- Is EN attested cross-linguistically? -/
  enAttested : Bool
  /-- Is the connective ambidirectional (Rett 2026)? -/
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

/-- EN is attested iff the connective is ambidirectional (Rett 2026).
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
    Jin & Koenig (2021) surveyed 70 languages; 50 have EN in
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
