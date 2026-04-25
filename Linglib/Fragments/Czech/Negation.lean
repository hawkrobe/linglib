import Linglib.Core.Lexical.NegMarker

/-!
# Czech Negation Fragment
@cite{miestamo-2005} @cite{haspelmath-2013} @cite{dryer-haspelmath-2013}

Czech expresses standard negation with the verbal prefix *ne-*.
Negation is **symmetric**: the prefix attaches directly to the verb
with no structural change — no finiteness restriction, no TAM gaps.

## Negative concord (Ch 115)

Czech has obligatory negative concord (WALS: co-occur), following the
standard Slavic pattern:
- *Nikdo nepřišel* 'Nobody NEG.came' = 'Nobody came'
- *Nic neviděl* 'Nothing NEG.saw' = '(He) saw nothing'

N-words of the *ni-* series (*nikdo*, *nic*, *nikdy*, *nikam*) always
co-occur with the *ne-* prefix on the verb. The lexeme entries live in
the sibling `Fragments/Czech/PolarityItems.lean` per the operator/
lexical-reactive split documented in `Core/Lexical/NegMarker.lean`. The
`NegConcordExample` data below illustrates the marker's interaction with
the n-word system at the sentence level.
-/

namespace Fragments.Czech.Negation

open Core.Lexical.NegMarker

/-- *ne-* — Czech's standard negation prefix.
    Attaches directly to the verb stem: *nepřijde* 'will not come',
    *neviděl* 'didn't see'. Symmetric across the paradigm. -/
def ne : NegMarkerEntry :=
  { form := "ne-"
  , morphemeType := .affix
  , position := .preverbal }

/-- The Czech negation system: a single verbal prefix.
    The Fragment-side joint consumed by `Phenomena/Negation/Typology.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "ces" [ne]

/-- Legacy String accessor for the prefix. Kept for back-compat with
    `Phenomena/Negation/Studies/Miestamo2005.lean`. New consumers should
    use `ne.form`. -/
def negPrefix : String := ne.form

/-- A Czech negation example. -/
structure NegExample where
  affirmative : String
  negative : String
  glossAff : String
  glossNeg : String
  tenseLabel : String
  deriving Repr, BEq

/-- Present tense: *jí* → *nejí*. -/
def present : NegExample :=
  { affirmative := "Jí"
  , negative := "Nejí"
  , glossAff := "eat.3SG.PRS"
  , glossNeg := "NEG.eat.3SG.PRS"
  , tenseLabel := "present" }

/-- Past tense: *jedl* → *nejedl*. -/
def past : NegExample :=
  { affirmative := "Jedl"
  , negative := "Nejedl"
  , glossAff := "eat.PST.M"
  , glossNeg := "NEG.eat.PST.M"
  , tenseLabel := "past" }

/-- Future (periphrastic): *bude jíst* → *nebude jíst*. -/
def future : NegExample :=
  { affirmative := "Bude jíst"
  , negative := "Nebude jíst"
  , glossAff := "will.3SG eat.INF"
  , glossNeg := "NEG.will.3SG eat.INF"
  , tenseLabel := "future" }

/-- Conditional: *jedl by* → *nejedl by*. -/
def conditional : NegExample :=
  { affirmative := "Jedl by"
  , negative := "Nejedl by"
  , glossAff := "eat.PST.M COND"
  , glossNeg := "NEG.eat.PST.M COND"
  , tenseLabel := "conditional" }

def allExamples : List NegExample := [present, past, future, conditional]

/-- A negative concord example. -/
structure NegConcordExample where
  sentence : String
  translation : String
  nword : String
  nwordGloss : String
  deriving Repr, BEq

/-- *Nikdo nepřišel* — obligatory negative concord. -/
def nikdo : NegConcordExample :=
  { sentence := "Nikdo nepřišel"
  , translation := "Nobody came"
  , nword := "nikdo"
  , nwordGloss := "nobody" }

/-- *Nic neviděl* — obligatory negative concord. -/
def nic : NegConcordExample :=
  { sentence := "Nic neviděl"
  , translation := "(He) saw nothing"
  , nword := "nic"
  , nwordGloss := "nothing" }

/-- *Nikdy nepřišel* — obligatory negative concord. -/
def nikdy : NegConcordExample :=
  { sentence := "Nikdy nepřišel"
  , translation := "(He) never came"
  , nword := "nikdy"
  , nwordGloss := "never" }

def allConcordExamples : List NegConcordExample := [nikdo, nic, nikdy]

/-! ## Verification -/

theorem all_examples_count : allExamples.length = 4 := by native_decide

/-- All negative forms begin with *Ne* (prefix attached). -/
theorem all_negative_start_ne :
    allExamples.all (fun e => e.negative.startsWith "Ne") = true := by
  native_decide

/-- All negative concord sentences contain a verb with *ne-* prefix. -/
theorem all_concord_contain_ne :
    allConcordExamples.all (fun e =>
      (e.sentence.splitOn "ne").length > 1) = true := by
  native_decide

/-- All n-words begin with *ni-*. -/
theorem all_nwords_ni_prefix :
    allConcordExamples.all (fun e => e.nword.startsWith "ni") = true := by
  native_decide

end Fragments.Czech.Negation
