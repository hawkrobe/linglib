/-
# Scope Readings in Embedded Questions

Pair-list and choice readings from G&S 1984, Chapter VI, Sections 2.1-2.2.

## Pair-List Readings (Section 2.1)

When a universal quantifier takes wide scope over a wh-phrase, the
answer becomes a function: for each element in the quantifier's domain,
what's the wh-answer?

"Which student did each professor recommend?"
→ "Prof. A recommended Alice, Prof. B recommended Bob, ..."

## Choice Readings (Section 2.2)

When a disjunction or existential takes wide scope over a wh-phrase,
different disjuncts can give different complete answers.

"Whom does John or Mary love?"
→ "If John is asking: Bill. If Mary is asking: Sue."

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. VI.
- Szabolcsi (1997). Quantifiers in Pair-List Readings.
- Dayal (2016). Questions. MIT Press.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.ScopeReadings


/-- A pair-list reading datum: universal quantifier over wh-phrase. -/
structure PairListDatum where
  /-- The question -/
  question : String
  /-- The universal NP -/
  universalNP : String
  /-- The wh-phrase -/
  whPhrase : String
  /-- Example pair-list answer -/
  pairListAnswer : String
  /-- Example non-pair-list answer (if available) -/
  singleAnswer : Option String
  /-- Context/situation description -/
  context : String
  /-- Is pair-list the preferred reading? -/
  pairListPreferred : Bool
  /-- Factors affecting the reading -/
  factors : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 403: "Which student was recommended by each professor?" -/
def whichStudentEachProfessor : PairListDatum :=
  { question := "Which student was recommended by each professor?"
  , universalNP := "each professor"
  , whPhrase := "which student"
  , pairListAnswer := "Prof. Smith recommended Alice, Prof. Jones recommended Bob, Prof. Brown recommended Carol"
  , singleAnswer := some "Alice (was recommended by all professors)"
  , context := "Faculty meeting about graduate admissions"
  , pairListPreferred := true
  , factors := "Universal c-commands wh; 'each' licenses pair-list; embedded under attitude verb"
  , source := "G&S 1984, p. 403"
  }

/-- G&S p. 404: "Who does every man love?" -/
def whoEveryManLove : PairListDatum :=
  { question := "Who does every man love?"
  , universalNP := "every man"
  , whPhrase := "who"
  , pairListAnswer := "John loves Mary, Bill loves Sue, Tom loves Alice"
  , singleAnswer := some "Mary (is loved by all men)"
  , context := "Discussion about romantic relationships in a small community"
  , pairListPreferred := true
  , factors := "Matrix question with universal subject"
  , source := "G&S 1984, p. 404"
  }

/-- G&S p. 405: "Which of his teachers does every student admire?" -/
def whichTeacherEveryStudent : PairListDatum :=
  { question := "Which of his teachers does every student admire?"
  , universalNP := "every student"
  , whPhrase := "which of his teachers"
  , pairListAnswer := "John admires Prof. Smith, Mary admires Prof. Jones, Bill admires Prof. Brown"
  , singleAnswer := none  -- Bound variable forces functional reading
  , context := "Survey about student-teacher relationships"
  , pairListPreferred := true
  , factors := "Bound variable 'his' forces functional reading"
  , source := "G&S 1984, p. 405"
  }

/-- G&S: Pair-list with 'each' vs 'every' -/
def eachVsEvery : PairListDatum :=
  { question := "Which book did each student read?"
  , universalNP := "each student"
  , whPhrase := "which book"
  , pairListAnswer := "Alice read 'War and Peace', Bob read '1984', Carol read 'Pride and Prejudice'"
  , singleAnswer := some "'1984' (was read by all students)"
  , context := "Reading group meeting"
  , pairListPreferred := true
  , factors := "'Each' more strongly licenses pair-list than 'every'"
  , source := "G&S 1984"
  }

/-- Pair-list under 'know' -/
def knowPairList : PairListDatum :=
  { question := "John knows which student each professor recommended"
  , universalNP := "each professor"
  , whPhrase := "which student"
  , pairListAnswer := "John knows: Smith→Alice, Jones→Bob, Brown→Carol"
  , singleAnswer := some "John knows: Alice (recommended by all)"
  , context := "Embedded under 'know'"
  , pairListPreferred := true
  , factors := "'Know' licenses pair-list; factive verb"
  , source := "G&S 1984, p. 408"
  }

/-- Pair-list under 'wonder' (degraded) -/
def wonderPairList : PairListDatum :=
  { question := "John wonders which student each professor recommended"
  , universalNP := "each professor"
  , whPhrase := "which student"
  , pairListAnswer := "?"  -- Degraded
  , singleAnswer := some "John wonders whether there's a student all recommended"
  , context := "Embedded under 'wonder'"
  , pairListPreferred := false
  , factors := "'Wonder' disfavors pair-list; non-factive verb"
  , source := "G&S 1984, p. 409"
  }

def pairListExamples : List PairListDatum :=
  [ whichStudentEachProfessor
  , whoEveryManLove
  , whichTeacherEveryStudent
  , eachVsEvery
  , knowPairList
  , wonderPairList
  ]


/-- A choice reading datum: disjunction/existential over wh-phrase. -/
structure ChoiceDatum where
  /-- The question -/
  question : String
  /-- The disjunctive/existential NP -/
  disjNP : String
  /-- The wh-phrase -/
  whPhrase : String
  /-- The choice answer (conditional on disjunct) -/
  choiceAnswer : String
  /-- The non-choice answer -/
  nonChoiceAnswer : String
  /-- Context -/
  context : String
  /-- Is choice reading available? -/
  choiceAvailable : Bool
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 411: "Whom does John or Mary love?" -/
def whomJohnOrMaryLove : ChoiceDatum :=
  { question := "Whom does John or Mary love?"
  , disjNP := "John or Mary"
  , whPhrase := "whom"
  , choiceAnswer := "If John: Bill. If Mary: Sue."
  , nonChoiceAnswer := "Bill and Sue (loved by John-or-Mary collectively)"
  , context := "Discussing potential matches in a group"
  , choiceAvailable := true
  , source := "G&S 1984, p. 411"
  }

/-- G&S p. 412: "John knows whom Mary or Sue invited" -/
def knowWhomMaryOrSue : ChoiceDatum :=
  { question := "John knows whom Mary or Sue invited"
  , disjNP := "Mary or Sue"
  , whPhrase := "whom"
  , choiceAnswer := "John knows: If Mary invited: Bill. If Sue invited: Tom."
  , nonChoiceAnswer := "John knows who was invited by at least one of them"
  , context := "Embedded under 'know'"
  , choiceAvailable := true
  , source := "G&S 1984, p. 412"
  }

/-- G&S: Existential wide scope - "Which student does some professor recommend?" -/
def whichStudentSomeProfessor : ChoiceDatum :=
  { question := "Which student does some professor recommend?"
  , disjNP := "some professor"
  , whPhrase := "which student"
  , choiceAnswer := "Prof. Smith recommends Alice; that's the relevant answer"
  , nonChoiceAnswer := "Alice, Bob, and Carol are each recommended by at least one professor"
  , context := "Asking about recommendations"
  , choiceAvailable := true
  , source := "G&S 1984, p. 413"
  }

/-- Choice with indefinite - "Who speaks a Scandinavian language?" -/
def whoSpeaksScandinavian : ChoiceDatum :=
  { question := "Who speaks a Scandinavian language?"
  , disjNP := "a Scandinavian language"
  , whPhrase := "who"
  , choiceAnswer := "For Swedish: Anna. For Norwegian: Erik. For Danish: Karen."
  , nonChoiceAnswer := "Anna, Erik, and Karen (each speaks at least one)"
  , context := "Staffing for international conference"
  , choiceAvailable := true
  , source := "constructed"
  }

def choiceExamples : List ChoiceDatum :=
  [ whomJohnOrMaryLove
  , knowWhomMaryOrSue
  , whichStudentSomeProfessor
  , whoSpeaksScandinavian
  ]


/-- Minimal pairs showing scope effects. -/
structure ScopeMinimalPair where
  /-- The question with wide-scope quantifier reading -/
  wideScope : String
  /-- The question with narrow-scope quantifier reading -/
  narrowScope : String
  /-- Wide-scope answer -/
  wideScopeAnswer : String
  /-- Narrow-scope answer -/
  narrowScopeAnswer : String
  /-- Which factors determine the reading -/
  scopeFactors : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Each vs Every in scope -/
def eachEveryScope : ScopeMinimalPair :=
  { wideScope := "Which book did each student read?"
  , narrowScope := "Which book did every student read?"
  , wideScopeAnswer := "Alice:A, Bob:B, Carol:C (pair-list)"
  , narrowScopeAnswer := "Book X (read by all students)"
  , scopeFactors := "'Each' licenses wide scope; 'every' prefers narrow"
  , source := "G&S 1984"
  }

/-- Subject vs Object position -/
def subjectObjectScope : ScopeMinimalPair :=
  { wideScope := "Which student did every professor recommend?"
  , narrowScope := "Every professor recommended which student?"
  , wideScopeAnswer := "Smith:Alice, Jones:Bob (pair-list)"
  , narrowScopeAnswer := "? (marked; hard to get pair-list without fronted wh)"
  , scopeFactors := "Wh-fronting enables wide scope for universal"
  , source := "G&S 1984"
  }

def scopeMinimalPairs : List ScopeMinimalPair :=
  [eachEveryScope, subjectObjectScope]


/-- Data on factors affecting pair-list availability. -/
structure LicensingDatum where
  /-- The example question -/
  question : String
  /-- The quantifier type -/
  quantifier : String
  /-- The embedding verb (if any) -/
  embeddingVerb : Option String
  /-- Is pair-list available? -/
  pairListOK : Bool
  /-- Explanation -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- 'Know' licenses pair-list -/
def knowLicenses : LicensingDatum :=
  { question := "John knows which student each professor recommended"
  , quantifier := "each"
  , embeddingVerb := some "know"
  , pairListOK := true
  , explanation := "Factive 'know' licenses pair-list because the answer is presupposed true"
  , source := "G&S 1984, p. 408"
  }

/-- 'Wonder' dislikes pair-list -/
def wonderDislikes : LicensingDatum :=
  { question := "John wonders which student each professor recommended"
  , quantifier := "each"
  , embeddingVerb := some "wonder"
  , pairListOK := false
  , explanation := "Non-factive 'wonder' disfavors pair-list; questioner doesn't presuppose answer"
  , source := "G&S 1984, p. 409"
  }

/-- 'Ask' and pair-list -/
def askDislikes : LicensingDatum :=
  { question := "John asked which student each professor recommended"
  , quantifier := "each"
  , embeddingVerb := some "ask"
  , pairListOK := false
  , explanation := "Performative 'ask' reports a question act; pair-list is degraded"
  , source := "G&S 1984"
  }

/-- Matrix questions and pair-list -/
def matrixPairList : LicensingDatum :=
  { question := "Which student did each professor recommend?"
  , quantifier := "each"
  , embeddingVerb := none
  , pairListOK := true
  , explanation := "Matrix questions allow pair-list with 'each'"
  , source := "G&S 1984, p. 403"
  }

def licensingExamples : List LicensingDatum :=
  [knowLicenses, wonderDislikes, askDislikes, matrixPairList]


/-- Classification of answer types for scope readings. -/
inductive ScopeAnswerType where
  /-- Single individual answering for all -/
  | single : ScopeAnswerType
  /-- List of pairs (function) -/
  | pairList : ScopeAnswerType
  /-- Conditional on disjunct -/
  | conditional : ScopeAnswerType
  /-- Depends on which witness -/
  | witnessDependent : ScopeAnswerType
  deriving DecidableEq, Repr

/-- Map scope configuration to answer type. -/
def expectedAnswerType (quantifier : String) (isDisjunction : Bool) : ScopeAnswerType :=
  if isDisjunction then .conditional
  else if quantifier == "each" || quantifier == "every" then .pairList
  else if quantifier == "some" || quantifier == "a" then .witnessDependent
  else .single


/-- Data on functional (f-) questions: wh-phrase with bound variable. -/
structure FunctionalQuestionDatum where
  /-- The question -/
  question : String
  /-- The bound variable -/
  boundVariable : String
  /-- The binding quantifier -/
  binder : String
  /-- Why this forces functional reading -/
  explanation : String
  /-- Example functional answer -/
  functionalAnswer : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- "Which of his teachers does every student admire?" -/
def whichOfHisTeachers : FunctionalQuestionDatum :=
  { question := "Which of his teachers does every student admire?"
  , boundVariable := "his"
  , binder := "every student"
  , explanation := "Bound 'his' forces each student to have their OWN teacher as answer"
  , functionalAnswer := "John:Prof.A, Mary:Prof.B, Bill:Prof.C"
  , source := "G&S 1984, p. 405"
  }

/-- "Which of her children does each mother love most?" -/
def whichOfHerChildren : FunctionalQuestionDatum :=
  { question := "Which of her children does each mother love most?"
  , boundVariable := "her"
  , binder := "each mother"
  , explanation := "Bound 'her' forces function from mothers to their children"
  , functionalAnswer := "Mary:Alice, Sue:Bob, Karen:Carol"
  , source := "constructed"
  }

def functionalQuestionExamples : List FunctionalQuestionDatum :=
  [whichOfHisTeachers, whichOfHerChildren]


/-- Data on pair-list readings across languages. -/
structure CrossLinguisticDatum where
  /-- Language -/
  language : String
  /-- Example sentence -/
  example_ : String
  /-- Gloss -/
  gloss : String
  /-- Is pair-list available? -/
  pairListOK : Bool
  /-- Notes on language-specific factors -/
  notes : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Hungarian: flexible pair-list with wh-in-situ -/
def hungarianPairList : CrossLinguisticDatum :=
  { language := "Hungarian"
  , example_ := "Mindenki mit olvasott?"
  , gloss := "Everyone what read?"
  , pairListOK := true
  , notes := "Wh-in-situ languages may allow pair-list more freely"
  , source := "Szabolcsi 1997"
  }

/-- Japanese: wh-in-situ with pair-list -/
def japanesePairList : CrossLinguisticDatum :=
  { language := "Japanese"
  , example_ := "Daremo-ga nani-o yonda ka"
  , gloss := "Everyone-NOM what-ACC read Q"
  , pairListOK := true
  , notes := "Japanese allows pair-list with universal and wh-in-situ"
  , source := "constructed"
  }

def crossLinguisticExamples : List CrossLinguisticDatum :=
  [hungarianPairList, japanesePairList]

-- Summary: Key Principles

/-- G&S key principles for scope readings -/
def scopeReadingPrinciples : List String :=
  [ "Pair-list arises when universal quantifier takes wide scope over wh"
  , "Choice readings arise when disjunction/existential takes wide scope"
  , "'Each' licenses pair-list more strongly than 'every'"
  , "Factive verbs ('know') license pair-list; non-factives ('wonder') don't"
  , "Bound variables force functional readings"
  , "Pair-list = conjunction of individual questions"
  , "Choice = disjunction where answer depends on which disjunct"
  ]

end Phenomena.Questions.ScopeReadings
