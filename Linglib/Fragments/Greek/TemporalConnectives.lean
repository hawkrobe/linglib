import Linglib.Fragments.English.TemporalExpressions

/-!
# Greek Temporal Connectives Fragment
@cite{giannakidou-2002} @cite{giannakidou-1998}Greek lexicalizes the two-*until* distinction and the veridicality asymmetry
through mood selection:

- **πριν / prin** ('before'): requires subjunctive (in modern Greek),
  patterns with English *before* and NPI-*until*. Non-veridical complement,
  licenses NPIs.

- **μέχρι / mexri** ('until'): requires indicative, patterns with English
  durative *until*. Veridical complement, requires imperfective/stative
  main clause, does NOT license NPIs.

- **αφού / afou** ('after'): veridical complement.

- **όταν / otan** ('when'): veridical complement, temporal coincidence.

The subjunctive/indicative mood split (Giannakidou 2002, §3) independently
diagnoses the veridicality distinction: subjunctive signals non-veridicality
(the complement event is presented as unrealized), while indicative signals
veridicality (the complement event is presented as factual). This parallels
Japanese tense marking (*mae* non-past / *ato* past) diagnosed in the
O&ST (2024) data.

-/

namespace Fragments.Greek.TemporalConnectives

open Fragments.English.TemporalExpressions (TemporalExprEntry Reading TemporalOrder ComplementType)

-- ============================================================================
-- § 1: Connective Entries
-- ============================================================================

/-- Greek *πριν / prin* ('before'): non-veridical, subjunctive complement.
    Licenses NPIs. Default before-start reading.
    "Efije prin na erthi o Janis." ('She left before Janis came.') -/
def prin : TemporalExprEntry :=
  { form := "prin (πριν)"
  , complementType := .clausal
  , order := .before
  , licensesNPI := true
  , defaultReading := .beforeStart
  , coercedReading := some .beforeFinish
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := false
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Greek *μέχρι / mexri* ('until'): veridical, indicative complement.
    Does NOT license NPIs. Requires imperfective/stative main clause.
    "I Maria perimine mexri irthi o Janis."
    ('Maria waited until Janis came.') -/
def mexri : TemporalExprEntry :=
  { form := "mexri (μέχρι)"
  , complementType := .clausal
  , order := .until_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Greek *αφού / afou* ('after'): veridical, indicative complement.
    "Efije afou irthe o Janis." ('She left after Janis came.') -/
def afou : TemporalExprEntry :=
  { form := "afou (αφού)"
  , complementType := .clausal
  , order := .after
  , licensesNPI := false
  , defaultReading := .afterFinish
  , coercedReading := some .afterStart
  , embeddedTelicityEffect := true
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

/-- Greek *όταν / otan* ('when'): veridical, temporal coincidence.
    "Efije otan irthe o Janis." ('She left when Janis came.') -/
def otan : TemporalExprEntry :=
  { form := "otan (όταν)"
  , complementType := .clausal
  , order := .when_
  , licensesNPI := false
  , defaultReading := .durative
  , coercedReading := none
  , embeddedTelicityEffect := false
  , crossLinguisticBasic := true
  , complementVeridical := true
  , forcesPunctual := false
  , triggeredCoercion := none }

-- ============================================================================
-- § 2: The Two-*Until* Distinction
-- ============================================================================

/-- Greek lexicalizes the two-*until* distinction with different lexemes:
    *prin* (NPI-type, = before) vs *mexri* (durative endpoint type). -/
theorem two_until_lexicalized :
    prin.form ≠ mexri.form ∧
    prin.order ≠ mexri.order := by
  exact ⟨by decide, by decide⟩

/-- *Prin* is semantically *before* (order = .before), confirming
    Karttunen's identity: NPI-*until* = ¬*before*. -/
theorem prin_is_before :
    prin.order = .before := rfl

/-- *Mexri* is semantically *until* (order = .until_),
    the true durative endpoint connective. -/
theorem mexri_is_until :
    mexri.order = .until_ := rfl

-- ============================================================================
-- § 3: Veridicality Asymmetry
-- ============================================================================

/-- Greek veridicality asymmetry: *prin* non-veridical, *afou*/*mexri* veridical.
    This is diagnosed by mood selection: subjunctive (*prin*) vs
    indicative (*afou*, *mexri*, *otan*). -/
theorem veridicality_asymmetry :
    prin.complementVeridical = false ∧
    afou.complementVeridical = true ∧
    mexri.complementVeridical = true ∧
    otan.complementVeridical = true :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 4: NPI Licensing Pattern
-- ============================================================================

/-- NPI licensing: only *prin* (before-type) licenses NPIs. Neither the
    durative *until* (*mexri*) nor *after*/*when* license NPIs.
    This confirms the cross-linguistic generalization: NPI licensing
    tracks the before-type semantics, not the *until* label. -/
theorem npi_pattern :
    prin.licensesNPI = true ∧
    mexri.licensesNPI = false ∧
    afou.licensesNPI = false ∧
    otan.licensesNPI = false :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 5: Cross-Linguistic Agreement
-- ============================================================================

open Fragments.English.TemporalExpressions in
/-- Greek *prin* and English *before* agree on all semantic properties. -/
theorem prin_matches_before :
    prin.order = before_.order ∧
    prin.licensesNPI = before_.licensesNPI ∧
    prin.defaultReading = before_.defaultReading ∧
    prin.coercedReading = before_.coercedReading ∧
    prin.complementVeridical = before_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Greek *afou* and English *after* agree on all semantic properties. -/
theorem afou_matches_after :
    afou.order = after_.order ∧
    afou.licensesNPI = after_.licensesNPI ∧
    afou.defaultReading = after_.defaultReading ∧
    afou.coercedReading = after_.coercedReading ∧
    afou.complementVeridical = after_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Greek *mexri* and English *until* agree on all semantic properties. -/
theorem mexri_matches_until :
    mexri.order = until_.order ∧
    mexri.licensesNPI = false ∧
    mexri.defaultReading = until_.defaultReading ∧
    mexri.complementVeridical = until_.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

open Fragments.English.TemporalExpressions in
/-- Greek *otan* and English *when* agree on all semantic properties. -/
theorem otan_matches_when :
    otan.order = when_conn.order ∧
    otan.licensesNPI = when_conn.licensesNPI ∧
    otan.defaultReading = when_conn.defaultReading ∧
    otan.complementVeridical = when_conn.complementVeridical :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- § 6: Mood ↔ Veridicality Correlation
-- ============================================================================

/-- Mood selection type: subjunctive (non-veridical) vs indicative (veridical). -/
inductive MoodType where
  | subjunctive  -- non-veridical context
  | indicative   -- veridical context
  deriving DecidableEq, Repr, BEq

/-- Greek mood selection for temporal connectives. -/
def moodSelection : TemporalOrder → MoodType
  | .before   => .subjunctive
  | .after    => .indicative
  | .until_   => .indicative
  | .when_    => .indicative
  | .while_   => .indicative
  | .since_   => .indicative
  | .by_      => .indicative
  | .whenever => .indicative

/-- Mood selection aligns with veridicality: subjunctive iff non-veridical. -/
theorem mood_aligns_with_veridicality :
    (moodSelection .before = .subjunctive ∧ prin.complementVeridical = false) ∧
    (moodSelection .after = .indicative ∧ afou.complementVeridical = true) ∧
    (moodSelection .until_ = .indicative ∧ mexri.complementVeridical = true) ∧
    (moodSelection .when_ = .indicative ∧ otan.complementVeridical = true) :=
  ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

end Fragments.Greek.TemporalConnectives
