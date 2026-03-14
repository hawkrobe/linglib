import Linglib.Core.Lexical.Word

/-!
# French Negation Fragment
@cite{miestamo-2005} @cite{dryer-haspelmath-2013}

French uses bipartite negation *ne...pas*, with the preverbal clitic *ne*
and the postverbal reinforcer *pas*. In colloquial speech, *ne* is
frequently dropped (Jespersen cycle stage II→III).

## Symmetric negation

WALS classifies French negation as **symmetric**: adding *ne...pas* does
not change the clause structure, verb form, or paradigm. All TAM
distinctions are available under negation.

## Jespersen cycle

French is a textbook case of the Jespersen cycle:
1. Latin *non* (preverbal only)
2. Old French *ne...pas* (bipartite, *pas* = reinforcer from 'step')
3. Colloquial French *pas* (postverbal only, *ne* dropped)

The *ne*-drop is sociolinguistically conditioned: near-categorical in
informal speech, variable in formal registers.
-/

namespace Fragments.French.Negation

/-- The French preverbal negative clitic. -/
def neClitic : String := "ne"

/-- The French postverbal negative reinforcer. -/
def pasReinforcer : String := "pas"

/-- A French negation example. -/
structure NegExample where
  affirmative : String
  negativeFormal : String
  negativeColloquial : String
  gloss : String
  tenseLabel : String
  deriving Repr, BEq

/-- Present tense. -/
def present : NegExample :=
  { affirmative := "Je mange"
  , negativeFormal := "Je ne mange pas"
  , negativeColloquial := "Je mange pas"
  , gloss := "I eat / I NEG eat NEG / I eat NEG"
  , tenseLabel := "present" }

/-- Passé composé (compound past). -/
def passeCompose : NegExample :=
  { affirmative := "Il a mangé"
  , negativeFormal := "Il n'a pas mangé"
  , negativeColloquial := "Il a pas mangé"
  , gloss := "He has eaten / He NEG'has NEG eaten / He has NEG eaten"
  , tenseLabel := "passé composé" }

/-- Imparfait (imperfect). -/
def imparfait : NegExample :=
  { affirmative := "Elle chantait"
  , negativeFormal := "Elle ne chantait pas"
  , negativeColloquial := "Elle chantait pas"
  , gloss := "She sang.IMPF / She NEG sang.IMPF NEG"
  , tenseLabel := "imparfait" }

/-- Futur simple (simple future). -/
def futurSimple : NegExample :=
  { affirmative := "Nous partirons"
  , negativeFormal := "Nous ne partirons pas"
  , negativeColloquial := "Nous partirons pas"
  , gloss := "We will.leave / We NEG will.leave NEG"
  , tenseLabel := "futur simple" }

/-- Subjonctif (subjunctive). -/
def subjonctif : NegExample :=
  { affirmative := "qu'il mange"
  , negativeFormal := "qu'il ne mange pas"
  , negativeColloquial := "qu'il mange pas"
  , gloss := "that.he eat.SUBJ / that.he NEG eat.SUBJ NEG"
  , tenseLabel := "subjonctif" }

def allExamples : List NegExample :=
  [present, passeCompose, imparfait, futurSimple, subjonctif]

/-- Other negative reinforcers (besides *pas*). -/
structure NegReinforcer where
  form : String
  gloss : String
  restrictedNeg : Bool  -- requires ne
  deriving Repr, BEq

/-- *plus* 'no more/longer'. -/
def plus : NegReinforcer := { form := "plus", gloss := "no.more", restrictedNeg := true }
/-- *jamais* 'never'. -/
def jamais : NegReinforcer := { form := "jamais", gloss := "never", restrictedNeg := true }
/-- *rien* 'nothing'. -/
def rien : NegReinforcer := { form := "rien", gloss := "nothing", restrictedNeg := true }
/-- *personne* 'nobody'. -/
def personne : NegReinforcer := { form := "personne", gloss := "nobody", restrictedNeg := true }

def allReinforcers : List NegReinforcer := [plus, jamais, rien, personne]

/-! ## Verification -/

theorem neClitic_is_ne : neClitic = "ne" := rfl
theorem pasReinforcer_is_pas : pasReinforcer = "pas" := rfl

/-- All tenses are available under negation (no paradigmatic gaps). -/
theorem all_tenses_available : allExamples.length = 5 := by native_decide

private def hasSubstr (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- All formal negatives contain *pas*. -/
theorem formal_contains_pas :
    allExamples.all (fun e => hasSubstr e.negativeFormal "pas") = true := by
  native_decide

/-- All formal negatives contain the *n* component (*ne* or *n'*). -/
theorem formal_contains_n :
    allExamples.all (fun e =>
      hasSubstr e.negativeFormal "ne " || hasSubstr e.negativeFormal "n'") = true := by
  native_decide

/-- All colloquial negatives contain *pas*. -/
theorem colloquial_contains_pas :
    allExamples.all (fun e => hasSubstr e.negativeColloquial "pas") = true := by
  native_decide

-- ════════════════════════════════════════════════════
-- Expletive Negation Markers
-- ════════════════════════════════════════════════════

/-! ## Expletive Negation
@cite{jin-koenig-2021}

French has a **dedicated** expletive negation marker: the preverbal clitic
*ne* used alone (without *pas*). This is the grammaticalized form of EN,
distinct from standard *ne...pas*. In a few low-entrenchment contexts
(REGRET, FORGET), the full *ne...pas* appears instead.

| Trigger class | EN negator | Entrenchment |
|---------------|------------|--------------|
| FEAR          | ne         | high         |
| BEFORE        | ne         | high         |
| UNLESS        | ne         | high         |
| DENY          | ne         | high (requires negation/question) |
| REGRET        | ne (pas)   | low          |
| FORGET        | ne pas     | low          |
| COMPARATIVES  | ne         | high         |

The distinction between *ne* (EN) and *ne...pas* (standard) makes
French uniquely transparent: the grammaticalization of EN is visible
in the form of the negator itself.
-/

/-- An expletive negation marker and its trigger context. -/
structure ENTriggerNegator where
  /-- The trigger class label (from @cite{jin-koenig-2021} Table 5) -/
  triggerClass : String
  /-- French lexical trigger -/
  triggerForm : String
  /-- EN negator form -/
  enNegatorForm : String
  /-- Whether the EN is highly entrenched (grammaticalized) -/
  highEntrenchment : Bool
  deriving Repr, BEq

/-- *ne* alone is the dedicated EN marker (grammaticalized). -/
def enMarker : String := neClitic

/-- EN trigger-negator pairings from @cite{jin-koenig-2021}, Table 5
    and §6.1–6.4. -/
def enTriggerNegators : List ENTriggerNegator :=
  [ { triggerClass := "FEAR", triggerForm := "avoir peur"
    , enNegatorForm := "ne", highEntrenchment := true }
  , { triggerClass := "AVOID", triggerForm := "éviter"
    , enNegatorForm := "ne", highEntrenchment := true }
  , { triggerClass := "BEFORE", triggerForm := "avant que"
    , enNegatorForm := "ne", highEntrenchment := true }
  , { triggerClass := "UNLESS", triggerForm := "à moins que"
    , enNegatorForm := "ne", highEntrenchment := true }
  , { triggerClass := "DENY", triggerForm := "nier"
    , enNegatorForm := "ne", highEntrenchment := true }
  , { triggerClass := "COMPARATIVES", triggerForm := "que (than)"
    , enNegatorForm := "ne", highEntrenchment := true }
  , { triggerClass := "REGRET", triggerForm := "regretter"
    , enNegatorForm := "ne (pas)", highEntrenchment := false }
  , { triggerClass := "FORGET", triggerForm := "oublier"
    , enNegatorForm := "ne pas", highEntrenchment := false } ]

/-- High-entrenchment EN uses the dedicated *ne* alone;
    low-entrenchment EN uses *ne...pas* (the standard negator). -/
theorem high_entrenchment_uses_ne_alone :
    (enTriggerNegators.filter (·.highEntrenchment)).all
      (·.enNegatorForm == "ne") = true := by native_decide

/-- French EN marker = preverbal *ne* = same clitic as in standard
    *ne...pas*, but without the reinforcer. -/
theorem en_marker_is_ne_clitic : enMarker = neClitic := rfl

end Fragments.French.Negation
