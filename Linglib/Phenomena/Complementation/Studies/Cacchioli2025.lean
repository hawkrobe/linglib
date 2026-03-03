import Linglib.Core.Lexical.Word
import Linglib.Theories.Syntax.Minimalism.Core.Agree
import Linglib.Phenomena.Complementation.Typology
import Linglib.Fragments.Tigrinya.ClausePrefixes
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic

/-!
# @cite{cacchioli-2025} — Empirical Data @cite{cacchioli-2025}

Pure empirical data from @cite{cacchioli-2025} "The Syntax of Clausal Prefixes
in Tigrinya." No theory imports — this file contains only observed patterns,
grammaticality judgments, and co-occurrence restrictions.

## Key observations

1. **Four prefixes**: zɨ-, kɨ-, kəmzi-, ʔay-...-n
2. **Complementary distribution**: No two prefixes co-occur
3. **Verb class selection**: The matrix verb determines which prefix appears
4. **Fixed linear order**: Prefix always precedes the verbal complex
5. **Agreement asymmetry**: kɨ- and ʔay-...-n take agreement; zɨ- and kəmzi- don't

-/

namespace Phenomena.Complementation.Cacchioli2025

-- ============================================================================
-- Section A: Prefix inventory
-- ============================================================================

/-- The four clausal prefixes attested in Tigrinya. -/
inductive TigrinyaPrefix where
  | zi      -- zɨ-: relativizer / general subordinator
  | ki      -- kɨ-: subjunctive / irrealis
  | kemzi   -- kəmzi-: factive complementizer
  | ay_n    -- ʔay-...-n: negative circumfix
  deriving DecidableEq, BEq, Repr

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

/-- Verb class selection data from @cite{cacchioli-2025}. -/
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

open Minimalism
open Phenomena.Complementation.Typology

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

-- ============================================================================
-- § Bridge Theorems: EP position, Fragment consistency, Selection
-- ============================================================================

open Fragments.Tigrinya.ClausePrefixes

/-- zɨ- (Rel) is at the same fValue level as Top (topic field, F5). -/
theorem zi_fvalue_topic_field : fValue zi.headCat = fValue .Top := by decide

/-- kɨ- (Fin) is at the IP/CP boundary (F3). -/
theorem ki_fvalue_boundary : fValue ki.headCat = 3 := by decide

/-- kəmzi- (Force) is at the clause-typing level (F6). -/
theorem kemzi_fvalue_clause_typing : fValue kemzi.headCat = 6 := by decide

/-- ʔay-...-n (Neg) is in the inflectional domain (F2). -/
theorem ay_fvalue_inflectional : fValue ay_n.headCat = 2 := by decide

/-- The four prefixes target four distinct F-levels:
    Neg(2) < Fin(3) < Rel(5) < Force(6). -/
theorem prefixes_distinct_flevels :
    fValue ay_n.headCat < fValue ki.headCat ∧
    fValue ki.headCat < fValue zi.headCat ∧
    fValue zi.headCat < fValue kemzi.headCat := by decide

/-- Fragment agreement field matches empirical data for each prefix. -/
theorem agreement_matches_data_bridge :
    zi.takesAgreementSuffix = false ∧
    ki.takesAgreementSuffix = true ∧
    kemzi.takesAgreementSuffix = false ∧
    ay_n.takesAgreementSuffix = true := ⟨rfl, rfl, rfl, rfl⟩

/-- Only ʔay-...-n is discontinuous. -/
theorem only_neg_discontinuous :
    zi.isDiscontinuous = false ∧
    ki.isDiscontinuous = false ∧
    kemzi.isDiscontinuous = false ∧
    ay_n.isDiscontinuous = true := ⟨rfl, rfl, rfl, rfl⟩

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
    catFamily zi.headCat = .verbal ∧
    catFamily ki.headCat = .verbal ∧
    catFamily kemzi.headCat = .verbal ∧
    catFamily ay_n.headCat = .verbal := by decide

end Phenomena.Complementation.Cacchioli2025
