import Linglib.Theories.Semantics.Reference.Reciprocals
import Linglib.Theories.Semantics.Lexical.Plural.Distributivity
import Linglib.Fragments.Hungarian.Reciprocals
import Linglib.Fragments.Wan.Reciprocals

/-!
# Dalrymple & Haug (2024): Constraints on Reciprocal Scope
@cite{dalrymple-haug-2024}

*Linguistic Inquiry*, Early Access. DOI: 10.1162/ling_a_00546.

Properties of the **local antecedent** of the reciprocal (the embedded-clause
pronoun coreferent with the matrix subject) determine reciprocal scope.
This paper systematically surveys five construction types and shows that
the relational analysis of reciprocals makes correct predictions in all
cases, while the quantificational analysis fails for distributive operators
(§5) and logophoric antecedents (§6).

## Construction Types Surveyed

| §  | Construction                  | Narrow | Wide | Both agree? |
|----|-------------------------------|--------|------|-------------|
| 2  | Bound antecedent (Hungarian)  | ✗      | ✓    | ✓           |
| 2  | Nonbound antecedent (Japanese)| ✓      | ✗    | ✓           |
| 3  | Collective conjunct           | ✓      | ✗    | ✓           |
| 4  | Partial control               | ✓      | ?    | ✓           |
| 4  | Exhaustive control, collective| ✓      | ✗    | ✓           |
| 4  | Exhaustive control, non-coll. | ✗      | ✓    | ✓           |
| 5  | Distributive operator         | ✓      | ✓    | ✗ (quant. ✗)|
| 6  | Logophoric antecedent (Wan)   | ✓      | ✗    | ✗ (quant. ✗)|

## Connections

- `Theories/Semantics/Reference/Reciprocals.lean` — the three anaphoric
  relations (=, ∪, R) and prediction functions
- `Theories/Semantics/Lexical/Plural/Distributivity.lean` — distributive
  operators (§5 shows *each* does NOT block wide scope, contra
  @cite{heim-lasnik-may-1991})
- `Fragments/Hungarian/Reciprocals.lean` — Hungarian *egymás* with
  singular null pronoun antecedent (§2, Rákosi 2019)
- `Fragments/Wan/Reciprocals.lean` — Wan logophoric reciprocal data (§6)
- `Core/Discourse/Logophoricity.lean` — Sells (1987) logophoric roles
- `Phenomena/Control/Studies/Landau2015.lean` — control tier distinction
  (exhaustive vs. partial) relevant to §4
-/

namespace Phenomena.Anaphora.Studies.DalrympleHaug2024

open Semantics.Reference.Reciprocals

-- ════════════════════════════════════════════════════════════════
-- § 1: Scope Judgment Data
-- ════════════════════════════════════════════════════════════════

/-- A reciprocal scope judgment: which readings are available for a
    particular construction type. -/
structure ScopeJudgment where
  /-- Description of the construction -/
  construction : String
  /-- Example sentence -/
  example_ : String
  /-- Available scope readings -/
  available : List RecipScope
  /-- Which section of the paper -/
  section_ : Nat
  deriving Repr

-- ════════════════════════════════════════════════════════════════
-- § 2: Bound and Nonbound Pronoun Antecedents
-- ════════════════════════════════════════════════════════════════

/-- Hungarian: singular null pronoun antecedent forces bound reading (=),
    yielding only wide scope.

    (10) Péter és Éva az-t gondolja, hogy szereti egymás-t.
    'Péter and Éva think that [they] love each other.'
    → Wide scope only (I-reading) -/
def hungarianBound : ScopeJudgment :=
  { construction := "Bound singular null pronoun antecedent (Hungarian)"
    example_ := "Péter és Éva azt gondolja, hogy szereti egymást."
    available := [.wide]
    section_ := 2 }

/-- Japanese: *zibun-tati* (plural reflexive) resists bound reading,
    favoring group identity (∪). As antecedent of reciprocal, only narrow
    scope available.

    (11) John to Mary ga [zibun-tati ga otagai o mi-ta to] omow-ta.
    'John and Mary thought that selves saw each other.'
    → Narrow scope only (we-reading) -/
def japaneseNonbound : ScopeJudgment :=
  { construction := "Nonbound plural reflexive antecedent (Japanese)"
    example_ := "John to Mary ga [zibun-tati ga otagai o mi-ta to] omow-ta."
    available := [.narrow]
    section_ := 2 }

-- ════════════════════════════════════════════════════════════════
-- § 3: Collectivity
-- ════════════════════════════════════════════════════════════════

/-- When the reciprocal VP is coordinated with a collective predicate,
    only narrow scope is available. Wide scope gives the local antecedent
    an individual denotation, which cannot satisfy the collectivity
    requirement.

    (12) The girls hoped that they would [meet at the tennis court] and
         [defeat each other].
    → Narrow scope only -/
def collectiveConjunct : ScopeJudgment :=
  { construction := "VP coordination with collective predicate"
    example_ := "The girls hoped that they would meet at the tennis court and defeat each other."
    available := [.narrow]
    section_ := 3 }

-- ════════════════════════════════════════════════════════════════
-- § 4: Control and Reciprocal Scope
-- ════════════════════════════════════════════════════════════════

/-- The canonical wide-scope-only case in control constructions
    (Higginbotham 1980).

    (13) They wanted to visit each other.
    → Wide scope only (I-reading)

    This has been "generally accepted" since Higginbotham 1980. Note
    that *want* is actually partial control per @cite{landau-2015}, so
    the scope fixing here may be due to pragmatic factors rather than
    syntactic constraints on control type. -/
def wantControl : ScopeJudgment :=
  { construction := "Control with 'want' (Higginbotham 1980)"
    example_ := "They wanted to visit each other."
    available := [.wide]
    section_ := 4 }

/-- Exhaustive control with a collectively interpreted controller
    rules out wide scope (collective interpretation requires plurality).

    (14) They decided to keep each other's comments confidential.
    → Narrow scope available (collective "decided")

    @cite{heim-lasnik-may-1991} claim this has two readings (collective
    narrow, distributive wide), but the distinction is hard to verify
    for many verbs. -/
def exhaustiveControlCollective : ScopeJudgment :=
  { construction := "Exhaustive control, collective controller"
    example_ := "They decided to keep each other's comments confidential."
    available := [.narrow]
    section_ := 4 }

/-- Partial control verbs (*want*, *hope*) with a singular controller
    allow narrow scope because PRO can denote a superset of the
    controller.

    (15a) I asked a girl who I liked if she wanted to get to know
          each other better.
    (15b) I vow to keep reminding you McDonald's is unhealthy ...
          because I want to live long, happy lives by each other's side.
    → Narrow scope available

    These are attested corpus examples. Substituting exhaustive control
    verbs (*try*, *manage*) makes the sentences worse (16a-b), confirming
    the role of partial control. The matrix argument is singular, so a
    collective interpretation is impossible — narrow scope arises purely
    from the partial-control PRO denoting a superset. -/
def partialControl : ScopeJudgment :=
  { construction := "Partial control (PRO superset of controller)"
    example_ := "She wanted to get to know each other better."
    available := [.narrow]
    section_ := 4 }

/-- Exhaustive control with non-collective interpretation: wide scope only.

    (17) Unbeknownst to each other, Tracy and Chris intended to help
         each other.
    → Wide scope only

    "Unbeknownst to each other" forces a distributive reading of the
    matrix subject (each individual is unaware), so the controller is
    not interpreted collectively. -/
def exhaustiveControlNonCollective : ScopeJudgment :=
  { construction := "Exhaustive control, non-collective"
    example_ := "Unbeknownst to each other, Tracy and Chris intended to help each other."
    available := [.wide]
    section_ := 4 }

-- ════════════════════════════════════════════════════════════════
-- § 5: Distributive Operators
-- ════════════════════════════════════════════════════════════════

/-- @cite{heim-lasnik-may-1991} claim that (18a) is unambiguous (narrow
    only) and that (18b) is ungrammatical:

    (18a) They each think they are taller than each other.
    (18b) *They each examined each other.

    Their reasoning: on the quantificational analysis, distributive *each*
    cannot apply to the already-distributed NP *each* inside *each other*.
    This is "a commonplace in the literature on distributivity"
    (Champollion 2016).

    However, corpus examples with *each of them* / *each* and a reciprocal
    antecedent are plentiful (19-20, 23-26), and both readings are
    available (24-25 for narrow, 25-26 for wide). -/
def hlmDistributiveClaim : ScopeJudgment :=
  { construction := "HLM: *each...each other* ungrammatical (REFUTED)"
    example_ := "*They each examined each other."
    available := []  -- HLM predicts ungrammatical / narrow only
    section_ := 5 }

/-- Contra @cite{heim-lasnik-may-1991}, a distributive operator (*each*)
    in the matrix clause does NOT block wide scope. Corpus data shows
    both readings are available.

    (24) They each liked each other. [narrow: mutual knowledge]
    (25) They each liked each other before. [wide: I-reading]
    (27b) They each think they liked each other. [narrow]
    (27c) They each think they liked each other. [wide]

    The quantificational analysis incorrectly predicts that applying a
    distributor to an already-distributed NP should be impossible. The
    relational analysis correctly allows both: *each other* is a pronoun,
    not a quantified NP, so there is no double-distribution problem.
    Distributive *each* can access the group denoted by the antecedent
    even if we distribute on that antecedent
    (@cite{haug-dalrymple-2020} §2.3). -/
def distributiveOperator : ScopeJudgment :=
  { construction := "Distributive 'each' in matrix clause"
    example_ := "They each think they liked each other."
    available := [.narrow, .wide]
    section_ := 5 }

/-- The *each...different* diagnostic (exx. 21-23) shows that *each* in
    *they each [V] each other* is not vacuous: it licenses internal
    readings of *different* that bare *each other* cannot.

    (21a) The men told each girl a different story.
          → Internal reading available (different story per girl)
    (21b) The men told each other a different story.
          → External reading only (not: different per pair member)
    (22)  The men each told each other a different story.
          → Internal reading emerges with *each* present

    This proves that higher *each* has genuine semantic content (it
    distributes on the antecedent), contra the HLM prediction that it
    should be impossible. -/
def eachDifferentDiagnostic : ScopeJudgment :=
  { construction := "each...each other licenses internal 'different'"
    example_ := "The men each told each other a different story."
    available := [.narrow, .wide]
    section_ := 5 }

-- ════════════════════════════════════════════════════════════════
-- § 6: Logophoricity
-- ════════════════════════════════════════════════════════════════

/-- In Wan (Mande), when the antecedent of the reciprocal is a logophor,
    only narrow scope is available.

    (28) wì mù tēŋ gé mɔ̄ á ē ɔ̄ŋ lɔ̄ lé
    'All the animals say they-LOG will eat each other.'
    → Narrow scope only (logophor + reciprocal)

    The wide scope reading IS available with an ordinary (non-logophoric)
    pronoun (32), confirming that logophoricity is the constraining factor.

    The relational analysis predicts this: on the wide scope reading, the
    embedded subject must be interpreted in the matrix clause for
    accessibility, but a logophor is confined to the report context.
    The quantificational analysis predicts both readings should be
    available since the quantifier scopes independently of logophoricity. -/
def logophoricAntecedent : ScopeJudgment :=
  { construction := "Logophoric antecedent (Wan)"
    example_ := "wì mù tēŋ gé mɔ̄ á ē ɔ̄ŋ lɔ̄ lé"
    available := [.narrow]
    section_ := 6 }

/-- With an ordinary (non-logophoric) pronoun, the wide scope reading
    IS available in Wan.

    (32) wì mù tēŋ tú gé à ɔ̄ŋ lɔ̄ lé
    'They all say they-3PL are going to eat each other.'
    → Both readings available -/
def nonLogophoricAntecedent : ScopeJudgment :=
  { construction := "Non-logophoric antecedent (Wan)"
    example_ := "wì mù tēŋ tú gé à ɔ̄ŋ lɔ̄ lé"
    available := [.narrow, .wide]
    section_ := 6 }

/-- All scope judgments from the paper. -/
def allJudgments : List ScopeJudgment :=
  [ hungarianBound
  , japaneseNonbound
  , collectiveConjunct
  , wantControl
  , partialControl
  , exhaustiveControlCollective
  , exhaustiveControlNonCollective
  , hlmDistributiveClaim
  , distributiveOperator
  , eachDifferentDiagnostic
  , logophoricAntecedent
  , nonLogophoricAntecedent ]

-- ════════════════════════════════════════════════════════════════
-- § 7: Verification — Relational Analysis Predictions
-- ════════════════════════════════════════════════════════════════

/-- Antecedent properties for each construction. -/

def hungarianProps : AntecedentProperties :=
  { isBound := true, hasCollectiveConjunct := false
    isExhaustiveControl := false, controllerIsCollective := false
    isLogophoric := false, hasDistributiveOperator := false }

def japaneseProps : AntecedentProperties :=
  { isBound := false, hasCollectiveConjunct := false
    isExhaustiveControl := false, controllerIsCollective := false
    isLogophoric := false, hasDistributiveOperator := false }

def collectiveProps : AntecedentProperties :=
  { isBound := false, hasCollectiveConjunct := true
    isExhaustiveControl := false, controllerIsCollective := false
    isLogophoric := false, hasDistributiveOperator := false }

def ecCollectiveProps : AntecedentProperties :=
  { isBound := false, hasCollectiveConjunct := false
    isExhaustiveControl := true, controllerIsCollective := true
    isLogophoric := false, hasDistributiveOperator := false }

def ecNonCollectiveProps : AntecedentProperties :=
  { isBound := false, hasCollectiveConjunct := false
    isExhaustiveControl := true, controllerIsCollective := false
    isLogophoric := false, hasDistributiveOperator := false }

def distributiveProps : AntecedentProperties :=
  { isBound := false, hasCollectiveConjunct := false
    isExhaustiveControl := false, controllerIsCollective := false
    isLogophoric := false, hasDistributiveOperator := true }

def logophoricProps : AntecedentProperties :=
  { isBound := false, hasCollectiveConjunct := false
    isExhaustiveControl := false, controllerIsCollective := false
    isLogophoric := true, hasDistributiveOperator := false }

/-- Hungarian bound antecedent: relational predicts wide only. -/
theorem relational_hungarian :
    relationalPrediction hungarianProps = [.wide] := rfl

/-- Japanese nonbound antecedent: relational predicts both (empirically
    narrow preferred, but the prediction function gives both when not
    constrained by other factors). -/
theorem relational_japanese :
    relationalPrediction japaneseProps = [.narrow, .wide] := rfl

/-- Collective conjunct: relational predicts narrow only. -/
theorem relational_collective :
    relationalPrediction collectiveProps = [.narrow] := rfl

/-- Exhaustive control, collective: relational predicts narrow only. -/
theorem relational_ec_collective :
    relationalPrediction ecCollectiveProps = [.narrow] := rfl

/-- Exhaustive control, non-collective: relational predicts wide only. -/
theorem relational_ec_noncollective :
    relationalPrediction ecNonCollectiveProps = [.wide] := rfl

/-- Distributive operator: relational predicts both readings.
    The distributor is orthogonal because *each other* is a pronoun. -/
theorem relational_distributive :
    relationalPrediction distributiveProps = [.narrow, .wide] := rfl

/-- Logophoric antecedent: relational predicts narrow only. -/
theorem relational_logophoric :
    relationalPrediction logophoricProps = [.narrow] := rfl

-- ════════════════════════════════════════════════════════════════
-- § 8: Quantificational Analysis — Where It Agrees
-- ════════════════════════════════════════════════════════════════

/-- The quantificational analysis makes the SAME prediction as the
    relational analysis for bound antecedents. -/
theorem quant_agrees_hungarian :
    quantificationalPrediction hungarianProps = [.wide] := rfl

/-- The quantificational analysis makes the SAME prediction for
    collective conjuncts. -/
theorem quant_agrees_collective :
    quantificationalPrediction collectiveProps = [.narrow] := rfl

/-- The quantificational analysis agrees on exhaustive control. -/
theorem quant_agrees_ec_noncollective :
    quantificationalPrediction ecNonCollectiveProps = [.wide] := rfl

theorem quant_agrees_ec_collective :
    quantificationalPrediction ecCollectiveProps = [.narrow] := rfl

-- ════════════════════════════════════════════════════════════════
-- § 9: Quantificational Analysis — Where It Fails
-- ════════════════════════════════════════════════════════════════

/-- DIVERGENCE 1 (§5): The quantificational analysis incorrectly
    predicts that distributive *each* blocks wide scope for reciprocals.
    It predicts narrow scope only, but empirically both readings
    are attested (exx. 19-20, 24-26).

    The relational analysis correctly predicts both readings are
    available, because *each other* is a pronoun, not a quantified NP. -/
theorem quant_fails_distributive :
    quantificationalPrediction distributiveProps = [.narrow] ∧
    relationalPrediction distributiveProps = [.narrow, .wide] ∧
    distributiveOperator.available = [.narrow, .wide] := ⟨rfl, rfl, rfl⟩

/-- DIVERGENCE 2 (§6): The quantificational analysis fails to restrict
    scope for logophoric antecedents. It predicts both readings should
    be available, but empirically only narrow is attested.

    On the quantificational analysis, the quantifier part of *each other*
    scopes independently of whether the embedded subject is logophoric.
    The relational analysis correctly predicts narrow only, because the
    logophor is confined to the report context and the reciprocal's
    R-relation cannot "drag" its antecedent out. -/
theorem quant_fails_logophoric :
    quantificationalPrediction logophoricProps = [.narrow, .wide] ∧
    relationalPrediction logophoricProps = [.narrow] ∧
    logophoricAntecedent.available = [.narrow] := ⟨rfl, rfl, rfl⟩

/-- The relational analysis matches the empirical data in ALL cases
    where the two analyses diverge. The quantificational analysis
    is empirically inadequate for distributive operators and logophoric
    antecedents. -/
theorem relational_superior :
    -- §5: relational correctly predicts both readings with distributors
    relationalPrediction distributiveProps = distributiveOperator.available ∧
    -- §5: quantificational incorrectly restricts
    quantificationalPrediction distributiveProps ≠ distributiveOperator.available ∧
    -- §6: relational correctly restricts logophoric to narrow
    relationalPrediction logophoricProps = logophoricAntecedent.available ∧
    -- §6: quantificational incorrectly overgenerates
    quantificationalPrediction logophoricProps ≠ logophoricAntecedent.available := by
  refine ⟨rfl, ?_, rfl, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════════════════
-- § 10: Cross-References to Fragment Data
-- ════════════════════════════════════════════════════════════════

/-- Hungarian *egymás* is formally distinct from the reflexive *maga*,
    per the fragment data. This distinction matters: reflexives and
    reciprocals have different scope possibilities. -/
theorem hungarian_recip_not_reflexive :
    Fragments.Hungarian.Reciprocals.egymas.form ≠
    Fragments.Hungarian.Reciprocals.maga.form := by decide

/-- Hungarian allows singular antecedents for the reciprocal, which
    forces wide scope (the singular null pronoun must be bound). -/
theorem hungarian_singular_forces_wide :
    Fragments.Hungarian.Reciprocals.allowsSingularAntecedent = true ∧
    Fragments.Hungarian.Reciprocals.singularAntecedentForcesWideScope = true := ⟨rfl, rfl⟩

/-- Wan logophoric pronoun *mɔ̄* is formally distinct from the ordinary
    3pl pronoun *tú*. The scope constraint is specific to logophoric
    antecedents — wide scope IS available with the ordinary pronoun. -/
theorem wan_log_distinct :
    Fragments.Wan.Reciprocals.logPl.form ≠
    Fragments.Wan.Reciprocals.ordinaryPl.form := by decide

/-- Wan reflexive *ē* is distinct from the logophoric pronoun *mɔ̄*.
    The reciprocal construction uses REFL + RECIP morphology (*ē ɔ̄ŋ*),
    while the logophoric pronoun (*mɔ̄*) is the subject of the embedded
    clause. -/
theorem wan_refl_distinct_from_log :
    Fragments.Wan.Reciprocals.refl.form ≠
    Fragments.Wan.Reciprocals.logPl.form := by decide

/-- The Wan logophoric pronoun satisfies at least the pivot role in
    @cite{sells-1987}'s hierarchy, connecting this fragment to the
    logophoricity theory in `Core/Discourse/Logophoricity.lean`. -/
theorem wan_log_is_at_least_pivot :
    Fragments.Wan.Reciprocals.logophoricRole.rank ≥
    Core.Logophoricity.LogophoricRole.pivot.rank := by decide

end Phenomena.Anaphora.Studies.DalrympleHaug2024
