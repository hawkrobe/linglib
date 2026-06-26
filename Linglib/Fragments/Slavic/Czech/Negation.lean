import Linglib.Syntax.Negation

/-!
# Czech Negation Fragment
[miestamo-2005] [haspelmath-2013] [dryer-haspelmath-2013]

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

namespace Czech.Negation

open Syntax.Negation

/-- *ne-* — Czech's standard negation prefix.
    Attaches directly to the verb stem: *nepřijde* 'will not come',
    *neviděl* 'didn't see'. Symmetric across the paradigm. -/
def ne : NegMarkerEntry :=
  { form := "ne-"
  , morphemeType := .affix
  , position := .preverbal }

/-- The Czech negation system: a single verbal prefix.
    The Fragment-side joint consumed by `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "ces" [ne]

/-- Legacy String accessor for the prefix. Kept for back-compat with
    `Studies/Miestamo2005.lean`. New consumers should
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

theorem all_examples_count : allExamples.length = 4 := by decide

/-- Czech negation profile (WALS Ch 112-115 + Greco/JinKoenig fields). -/
def negationProfile : Syntax.Negation.NegationProfile :=
  { language := "Czech"
  , iso := "ces"
  , morphemeType := .affix
  , symmetry := .symmetric
  , asymmetrySubtype := .nonAssignable
  , negIndefinite := some .cooccur
  , negMarkers := ["ne-"]
  , negIsHead := none
  , enAttested := none }

end Czech.Negation
