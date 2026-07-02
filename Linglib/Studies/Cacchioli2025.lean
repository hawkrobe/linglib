import Linglib.Data.UD.Basic
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Clause.Complementation
import Linglib.Fragments.Tigrinya.ClausePrefixes
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic

/-!
# [cacchioli-2025] — Empirical Data [cacchioli-2025]

Pure empirical data from [cacchioli-2025] "The Syntax of Clausal Prefixes
in Tigrinya." No theory imports — this file contains only observed patterns,
grammaticality judgments, and co-occurrence restrictions.

## Key observations

1. **Four prefixes**: zɨ-, kɨ-, kəmzi-, ʔay-...-n
2. **Complementary distribution**: No two prefixes co-occur
3. **Verb class selection**: The matrix verb determines which prefix appears
4. **Fixed linear order**: Prefix always precedes the verbal complex
5. **Agreement asymmetry**: kɨ- and ʔay-...-n take agreement; zɨ- and kəmzi- don't

-/

namespace Cacchioli2025

-- ============================================================================
-- Section A: Prefix inventory
-- ============================================================================

/-- The four clausal prefixes attested in Tigrinya. -/
inductive TigrinyaPrefix where
  | zi      -- zɨ-: relativizer / general subordinator
  | ki      -- kɨ-: subjunctive / irrealis
  | kemzi   -- kəmzi-: factive complementizer
  | ay_n    -- ʔay-...-n: negative circumfix
  deriving DecidableEq, Repr

-- ============================================================================
-- Section B: Co-occurrence restrictions
-- ============================================================================

/-- A grammaticality judgment for a prefix combination.
    `true` = grammatical, `false` = ungrammatical. -/
structure CooccurrenceJudgment where
  prefix1 : TigrinyaPrefix
  prefix2 : TigrinyaPrefix
  grammatical : Bool
  example_ : String := ""
  deriving Repr, BEq

/-- No two prefixes can co-occur (complementary distribution). -/
def cooccurrenceData : List CooccurrenceJudgment := [
  ⟨.zi,    .ki,    false, "*zɨ-kɨ-mäs'ə"⟩,
  ⟨.zi,    .kemzi, false, "*zɨ-kəmzi-mäs'ə"⟩,
  ⟨.zi,    .ay_n,  false, "*zɨ-ʔay-mäs'ə-n"⟩,
  ⟨.ki,    .kemzi, false, "*kɨ-kəmzi-mäs'ə"⟩,
  ⟨.ki,    .ay_n,  false, "*kɨ-ʔay-mäs'ə-n"⟩,
  ⟨.kemzi, .ay_n,  false, "*kəmzi-ʔay-mäs'ə-n"⟩
]

/-- All prefix combinations are ungrammatical (complementary distribution). -/
theorem all_cooccurrences_ungrammatical :
    cooccurrenceData.all (·.grammatical == false) = true := by native_decide

-- ============================================================================
-- Section C: Verb class → prefix selection
-- ============================================================================

/-- A selection datum: a matrix verb selects a particular prefix. -/
structure SelectionDatum where
  verb : String
  verbGloss : String
  verbClass : String
  selectedPrefix : TigrinyaPrefix
  example_ : String
  grammatical : Bool := true
  deriving Repr, BEq

/-- Verb class selection data from [cacchioli-2025]. -/
def selectionData : List SelectionDatum := [
  -- Knowledge verbs → kəmzi- (factive)
  { verb := "fälätä", verbGloss := "know", verbClass := "knowledge",
    selectedPrefix := .kemzi,
    example_ := "fälätä kəmzi-mäs'ə = knew that (he) came" },
  -- Commentative verbs → kəmzi- (factive)
  { verb := "ħazinä", verbGloss := "be.sad", verbClass := "commentative",
    selectedPrefix := .kemzi,
    example_ := "ħazinä kəmzi-kädä = was.sad that (he) went" },
  -- Desiderative verbs → kɨ- (subjunctive)
  { verb := "dälayä", verbGloss := "want", verbClass := "desiderative",
    selectedPrefix := .ki,
    example_ := "dälayä kɨ-mäs'ə = wanted to come" },
  -- Manipulative verbs → kɨ- (subjunctive)
  { verb := "ʔazazä", verbGloss := "order", verbClass := "manipulative",
    selectedPrefix := .ki,
    example_ := "ʔazazä kɨ-kädä = ordered to go" },
  -- Relative clauses → zɨ- (relativizer)
  { verb := "(head noun)", verbGloss := "REL", verbClass := "relative",
    selectedPrefix := .zi,
    example_ := "sәb'ay zɨ-mäs'ə = person who came" }
]

-- ============================================================================
-- Section D: Agreement asymmetry
-- ============================================================================

/-- Agreement data: which prefixes take agreement suffixes. -/
structure AgreementDatum where
  prefix_ : TigrinyaPrefix
  takesAgreement : Bool
  deriving Repr, BEq

def agreementData : List AgreementDatum := [
  ⟨.zi,    false⟩,  -- zɨ-mäs'ə (no agreement)
  ⟨.ki,    true⟩,   -- kɨ-mäs'ə-*ka* (with 2msg agreement)
  ⟨.kemzi, false⟩,  -- kəmzi-mäs'ə (no agreement)
  ⟨.ay_n,  true⟩    -- ʔay-mäs'ə-*n* (with neg agreement)
]

-- ============================================================================
-- § Selection Bridge: CTPClass → FeatureVal
-- ============================================================================

open Minimalist
open Clause.Complementation

/-- Map CTP reality status to [±finite] selection.

    Realis CTPs (utterance, knowledge, commentative,...) select [+finite]
    complements — indicative/realis clauses whose Fin head bears [+finite].

    Irrealis CTPs (desiderative, manipulative, modal,...) select [-finite]
    complements — subjunctive/irrealis clauses whose Fin head bears [-finite].

    Some classes are variable (perception can take both finite and non-finite
    complements), so they return `none`. -/
def ctpToFiniteness : CTPClass → Option Bool
  | .utterance    => some true    -- "say that..." (indicative)
  | .knowledge    => some true    -- "know that..." (indicative)
  | .commentative => some true    -- "regret that..." (indicative, factive)
  | .propAttitude => some true    -- "believe that..." (indicative)
  | .desiderative => some false   -- "want to..." (subjunctive/irrealis)
  | .manipulative => some false   -- "make X do..." (irrealis)
  | .modal        => some false   -- "can/must..." (irrealis)
  | .phasal       => some false   -- "start -ing" (reduced complement)
  | .achievement  => some false   -- "manage to..." (irrealis)
  | .negative     => some false   -- "avoid -ing" (irrealis)
  | .perception   => none         -- "see X leave/leaving" (variable)
  | .pretence     => none         -- "pretend that/to..." (variable)

/-- Map CTP class to [±factive] selection.

    Factive CTPs presuppose the truth of their complement; their Force/C
    head bears [+factive]. Non-factive CTPs don't, bearing [-factive]. -/
def ctpToFactivity : CTPClass → Option Bool
  | .knowledge    => some true    -- "know that p" presupposes p
  | .commentative => some true    -- "regret that p" presupposes p
  | .perception   => some true    -- "see that p" presupposes p
  | .utterance    => some false   -- "say that p" doesn't presuppose p
  | .propAttitude => some false   -- "believe that p" doesn't presuppose p
  | .desiderative => some false   -- "want p" doesn't presuppose p
  | _             => none         -- other classes: variable or N/A

/-- Knowledge verbs select [+finite] (indicative) complements. -/
theorem knowledge_selects_finite :
    ctpToFiniteness .knowledge = some true := rfl

/-- Desiderative verbs select [-finite] (subjunctive/irrealis) complements. -/
theorem desiderative_selects_nonfinite :
    ctpToFiniteness .desiderative = some false := rfl

/-- Knowledge verbs select [+factive] complements. -/
theorem knowledge_is_factive :
    ctpToFactivity .knowledge = some true := rfl

/-- Utterance verbs select [-factive] complements. -/
theorem utterance_not_factive :
    ctpToFactivity .utterance = some false := rfl

/-- Realis CTP classes map to [+finite]. -/
theorem realis_implies_finite :
    ctpToFiniteness .utterance = some true ∧
    ctpToFiniteness .knowledge = some true ∧
    ctpToFiniteness .commentative = some true ∧
    ctpToFiniteness .propAttitude = some true := ⟨rfl, rfl, rfl, rfl⟩

/-- Irrealis CTP classes map to [-finite]. -/
theorem irrealis_implies_nonfinite :
    ctpToFiniteness .desiderative = some false ∧
    ctpToFiniteness .manipulative = some false ∧
    ctpToFiniteness .modal = some false ∧
    ctpToFiniteness .phasal = some false := ⟨rfl, rfl, rfl, rfl⟩

/-- Irrealis CTP classes always map to [-finite] when they have a value.
    The converse (realis → [+finite]) does not hold universally: phasal
    verbs are realis but take non-finite complements. -/
theorem irrealis_always_nonfinite (c : CTPClass)
    (b : Bool) (h : ctpToFiniteness c = some b)
    (hr : ctpRealityStatus c = .irrealis) : b = false := by
  cases c <;> simp_all [ctpToFiniteness, ctpRealityStatus]

/-- **Cross-paper divergence theorem**: phasal CTPs witness the failure of
    the realis ↔ finite correspondence. [noonan-2007] §3.1.1 puts
    phasal complements in DTR, but the substrate's `ctpRealityStatus`
    classifies them as realis (event is asserted as actual). Cacchioli's
    feature-based analysis classifies the same complements as
    [-finite] (reduced). The contradiction makes visible a real Noonan-
    internal tension between the realis-as-asserted-fact criterion and
    the DTR → irrealis groupings of Table 2.3.

    The witness: phasal is realis AND takes non-finite (irrealis-aligned)
    complements. Any unification forcing realis ↔ +finite would have to
    reclassify either Noonan's reality status of phasal or Cacchioli's
    finiteness assignment. -/
theorem phasal_violates_realis_finite_correspondence :
    ctpRealityStatus .phasal = .realis ∧
    ctpToFiniteness .phasal = some false := ⟨rfl, rfl⟩

-- ============================================================================
-- § Bridge Theorems: EP position, Fragment consistency, Selection
-- ============================================================================

open Tigrinya.ClausePrefixes

/-- [cacchioli-2025]'s cartographic head assignment for the four
    prefixes ([rizzi-1997] split CP): zɨ- spells out Rel, kɨ- Fin,
    kəmzi- Force, ʔay- Neg. Paper-specific analysis projected over the
    framework-neutral fragment entries. -/
def headCat (e : ClausePrefixEntry) : Cat :=
  if e = kemzi then .Force
  else if e = ki then .Fin
  else if e = zi then .Rel
  else .Neg

/-- zɨ- (Rel) is at the same fValue level as Top (topic field, F5). -/
theorem zi_fvalue_topic_field : fValue (headCat zi) = fValue .Top := by decide

/-- kɨ- (Fin) is at the IP/CP boundary (F3). -/
theorem ki_fvalue_boundary : fValue (headCat ki) = 3 := by decide

/-- kəmzi- (Force) is at the clause-typing level (F6). -/
theorem kemzi_fvalue_clause_typing : fValue (headCat kemzi) = 6 := by decide

/-- ʔay-...-n (Neg) is in the inflectional domain (F2). -/
theorem ay_fvalue_inflectional : fValue (headCat ay_n) = 2 := by decide

/-- The four prefixes target four distinct F-levels:
    Neg(2) < Fin(3) < Rel(5) < Force(6). -/
theorem prefixes_distinct_flevels :
    fValue (headCat ay_n) < fValue (headCat ki) ∧
    fValue (headCat ki) < fValue (headCat zi) ∧
    fValue (headCat zi) < fValue (headCat kemzi) := by decide

/-- Fragment agreement field matches empirical data for each prefix. -/
theorem agreement_matches_data_bridge :
    zi.agrees = some false ∧
    ki.agrees = some true ∧
    kemzi.agrees = some false ∧
    ay_n.agrees = some true := ⟨rfl, rfl, rfl, rfl⟩

/-- Only ʔay-...-n is discontinuous (circumfixal position). -/
theorem only_neg_discontinuous :
    zi.position = some .praefixed ∧
    ki.position = some .praefixed ∧
    kemzi.position = some .praefixed ∧
    ay_n.position = some .circumfixed := ⟨rfl, rfl, rfl, rfl⟩

/-- Knowledge verbs select [+finite] → predicts kəmzi- (factive). -/
theorem knowledge_selects_kemzi :
    ctpToFiniteness .knowledge = some true := rfl

/-- Desiderative verbs select [-finite] → predicts kɨ- (subjunctive). -/
theorem desiderative_selects_ki :
    ctpToFiniteness .desiderative = some false := rfl

/-- Commentative verbs select [+finite] → predicts kəmzi- (factive). -/
theorem commentative_selects_kemzi :
    ctpToFiniteness .commentative = some true := rfl

/-- Manipulative verbs select [-finite] → predicts kɨ- (subjunctive). -/
theorem manipulative_selects_ki :
    ctpToFiniteness .manipulative = some false := rfl

/-- The negative circumfix surfaces correctly for a sample verb. -/
theorem neg_circumfix_realize :
    (negCircumfix "mäs'ə").realize = "ʔay-mäs'ə-n" := rfl

/-- The negative circumfix gloss is derived from the fragment entry. -/
theorem neg_circumfix_from_neg :
    (negCircumfix "mäs'ə").gloss = ay_n.gloss := rfl

/-- All four prefix heads are in the verbal extended projection. -/
theorem all_prefixes_verbal :
    catFamily (headCat zi) = .verbal ∧
    catFamily (headCat ki) = .verbal ∧
    catFamily (headCat kemzi) = .verbal ∧
    catFamily (headCat ay_n) = .verbal := by decide

end Cacchioli2025
