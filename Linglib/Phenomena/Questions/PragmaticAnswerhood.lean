/-
# Pragmatic Answerhood

Pragmatic notions of answerhood relativized to information sets.

## Key Insight

Semantic answerhood is a limit case of pragmatic answerhood.
When J = I (total ignorance), pragmatic answerhood reduces to semantic answerhood.

## Key Definitions (G&S 1984, pp. 352-358)

- Q is a question in J iff ∃X∃Y: X,Y ∈ J/Q & X ≠ Y
- P is a pragmatic answer to Q in J iff P∩J ∈ J/Q
- P gives a pragmatic answer to Q in J iff P∩J ≠ ∅ & ∃P' ∈ J/Q: P∩J ⊆ P'

## Term Properties (pragmatic versions)

- Pragmatically exhaustive: like semantic, but quantification restricted to J
- Pragmatically rigid: term denotes same across indices in J
- Pragmatically definite: term picks out unique individual in J

## References

- Groenendijk & Stokhof (1984). Studies on the Semantics of Questions. Ch. IV.
-/

import Linglib.Phenomena.Questions.Basic

namespace Phenomena.Questions.PragmaticAnswerhood

-- ============================================================================
-- PART 1: Pragmatic Rigidity Examples
-- ============================================================================

/-- G&S p. 359: Terms can be pragmatically rigid without being semantically rigid.
    "Your father" is not semantically rigid, but pragmatically rigid for anyone
    who knows who their father is.
-/
structure PragmaticRigidityDatum where
  /-- The question -/
  question : String
  /-- The answer -/
  answer : String
  /-- Is the term semantically rigid? -/
  semanticallyRigid : Bool
  /-- Is the term pragmatically rigid (in typical contexts)? -/
  pragmaticallyRigid : Bool
  /-- What information makes it pragmatically rigid? -/
  requiredInformation : String
  /-- Explanation -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 359: "Your father" example -/
def yourFather : PragmaticRigidityDatum :=
  { question := "Whom did you talk to?"
  , answer := "Your father"
  , semanticallyRigid := false
  , pragmaticallyRigid := true
  , requiredInformation := "Questioner knows who their father is"
  , explanation := "The term 'your father' denotes the same individual " ++
      "across all indices compatible with the questioner's information"
  , source := "G&S 1984, p. 359"
  }

/-- G&S p. 359: Tour de France example -/
def tourDeFrance1980 : PragmaticRigidityDatum :=
  { question := "Who won the Tour de France in 1980?"
  , answer := "The one who ended second in 1979"
  , semanticallyRigid := false
  , pragmaticallyRigid := true
  , requiredInformation := "Questioner knows Joop Zoetemelk ended second in 1979"
  , explanation := "For anyone with this information, the definite description " ++
      "rigidly picks out Zoetemelk"
  , source := "G&S 1984, p. 359"
  }

def pragmaticRigidityExamples : List PragmaticRigidityDatum :=
  [yourFather, tourDeFrance1980]

-- ============================================================================
-- PART 2: True Pragmatic Answers (including false propositions)
-- ============================================================================

/-- G&S p. 360: A FALSE proposition can give a TRUE pragmatic answer.
    This happens when the questioner has false beliefs that nevertheless
    lead them to the correct conclusion.
-/
structure FalseTrueDatum where
  /-- The question -/
  question : String
  /-- The answer given -/
  answer : String
  /-- The false belief of the questioner -/
  falseBelief : String
  /-- The proposition expressed by the answer -/
  propositionExpressed : String
  /-- Is the proposition true? -/
  propositionTrue : Bool
  /-- Does it convey true information to the questioner? -/
  conveysTrue : Bool
  /-- What true information does the questioner receive? -/
  informationReceived : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 360: False proposition giving true pragmatic answer -/
def zoetemelkWinner : FalseTrueDatum :=
  { question := "Who won the Tour de France in 1980?"
  , answer := "The one who won in 1979"
  , falseBelief := "Questioner wrongly believes Joop Zoetemelk won in 1979"
  , propositionExpressed := "The 1979 winner won again in 1980"
  , propositionTrue := false  -- Hinault won 1979, Zoetemelk won 1980
  , conveysTrue := true
  , informationReceived := "Joop Zoetemelk won the Tour de France in 1980"
  , source := "G&S 1984, p. 360"
  }

def falseTrueExamples : List FalseTrueDatum :=
  [zoetemelkWinner]

-- ============================================================================
-- PART 3: Pragmatic Definiteness
-- ============================================================================

/-- G&S p. 360-361: Indefinite terms can be pragmatically definite
    when the questioner's information uniquely identifies the referent.
-/
structure PragmaticDefinitenesssDatum where
  /-- The question -/
  question : String
  /-- The answer -/
  answer : String
  /-- Is the term semantically definite? -/
  semanticallyDefinite : Bool
  /-- Is the term pragmatically definite (in context)? -/
  pragmaticallyDefinite : Bool
  /-- What context makes it pragmatically definite? -/
  contextInfo : String
  /-- Explanation -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 360: "An elderly lady wearing glasses" example -/
def elderlyLady : PragmaticDefinitenesssDatum :=
  { question := "Who served you when you bought these boots?"
  , answer := "An elderly lady wearing glasses"
  , semanticallyDefinite := false
  , pragmaticallyDefinite := true
  , contextInfo := "Sales manager knows her staff; only one elderly lady with glasses"
  , explanation := "The semantically indefinite term is pragmatically definite " ++
      "because the questioner's information uniquely identifies the referent"
  , source := "G&S 1984, p. 360-361"
  }

def pragmaticDefinitenessExamples : List PragmaticDefinitenesssDatum :=
  [elderlyLady]

-- ============================================================================
-- PART 4: Non-Exhaustive Answers
-- ============================================================================

/-- G&S p. 361-362: Non-exhaustive answers can pragmatically imply
    exhaustive information through background knowledge.
-/
structure NonExhaustiveImplicationDatum where
  /-- The question -/
  question : String
  /-- The explicitly non-exhaustive answer -/
  answer : String
  /-- Background knowledge that enables inference -/
  backgroundKnowledge : String
  /-- The exhaustive conclusion drawn -/
  exhaustiveConclusion : String
  /-- Why this works -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 362: Prof. A. example -/
def profAContribution : NonExhaustiveImplicationDatum :=
  { question := "From which authors did the editors already receive their contribution?"
  , answer := "At least from Prof. A."
  , backgroundKnowledge := "Prof. A. is always the last to send in contributions"
  , exhaustiveConclusion := "The editors have received contributions from all authors"
  , explanation := "The explicitly non-exhaustive answer pragmatically implies " ++
      "an exhaustive answer due to the questioner's background knowledge"
  , source := "G&S 1984, p. 362"
  }

/-- G&S p. 362: Same answer, different question, different result -/
def profAAcceptance : NonExhaustiveImplicationDatum :=
  { question := "From whom did the organizers receive a letter of acceptance?"
  , answer := "At least from Prof. A."
  , backgroundKnowledge := "Prof. A. is always the first to accept invitations"
  , exhaustiveConclusion := ""  -- No exhaustive conclusion possible!
  , explanation := "The same answer to a different question yields no exhaustive " ++
      "conclusion, because being first to accept doesn't entail others accepted"
  , source := "G&S 1984, p. 362"
  }

def nonExhaustiveExamples : List NonExhaustiveImplicationDatum :=
  [profAContribution, profAAcceptance]

-- ============================================================================
-- PART 5: Semantic vs Pragmatic Answerhood
-- ============================================================================

/-- G&S p. 355: Semantic answerhood is a limit case of pragmatic answerhood.
    When J = I (no factual information), pragmatic = semantic.
-/
structure AnswerhoodComparisonDatum where
  /-- The question -/
  question : String
  /-- The answer -/
  answer : String
  /-- Is it a semantic answer? -/
  semanticAnswer : Bool
  /-- Is it a pragmatic answer in typical J? -/
  pragmaticAnswer : Bool
  /-- Why the difference? -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- Definite description: pragmatically rigid but not semantically -/
def definitePragmatic : AnswerhoodComparisonDatum :=
  { question := "Who called?"
  , answer := "The student who arrived late"
  , semanticAnswer := false  -- not semantically rigid
  , pragmaticAnswer := true   -- pragmatically rigid if questioner knows who arrived late
  , explanation := "Semantically, different indices may have different late-arrivers. " ++
      "Pragmatically, the questioner's information may fix the referent."
  , source := "G&S 1984, p. 358-359"
  }

def answerhoodComparisonExamples : List AnswerhoodComparisonDatum :=
  [definitePragmatic]

-- ============================================================================
-- PART 6: Disharmonious Information
-- ============================================================================

/-- G&S p. 361: Indefinite terms are appropriate when speech participants
    have disharmonious information but must achieve information exchange.
-/
structure DisharmoniousInfoDatum where
  /-- Description of the situation -/
  situation : String
  /-- The question -/
  question : String
  /-- The answer -/
  answer : String
  /-- Questioner's information -/
  questionerInfo : String
  /-- Answerer's information -/
  answererInfo : String
  /-- Why the exchange works -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 361: Boot shop example of disharmonious information -/
def bootShop : DisharmoniousInfoDatum :=
  { situation := "Customer bought boots; sales manager wants to know who served them"
  , question := "Who served you when you bought these boots?"
  , answer := "An elderly lady wearing glasses"
  , questionerInfo := "Knows all staff members well; doesn't know who served this customer"
  , answererInfo := "Doesn't know staff names; can only give physical description"
  , explanation := "Despite disharmonious information, the indefinite description " ++
      "achieves coordination: the manager can identify the staff member"
  , source := "G&S 1984, p. 361"
  }

def disharmoniousExamples : List DisharmoniousInfoDatum :=
  [bootShop]

-- ============================================================================
-- PART 7: Institutional vs Ordinary Question-Answering
-- ============================================================================

/-- G&S p. 363, 390: In highly institutionalized settings (courts, etc.),
    semantic answers are required because information sets vary widely.
-/
structure InstitutionalAnswerDatum where
  /-- The setting -/
  setting : String
  /-- Why semantic answers are required -/
  requirement : String
  /-- Example of acceptable answer -/
  acceptableAnswer : String
  /-- Example of unacceptable answer -/
  unacceptableAnswer : String
  /-- Explanation -/
  explanation : String
  /-- Source -/
  source : String := ""
  deriving Repr

/-- G&S p. 363, 390: Court testimony example -/
def courtTestimony : InstitutionalAnswerDatum :=
  { setting := "Court of Law"
  , requirement := "Rigid, standard semantic answers"
  , acceptableAnswer := "John Smith of 123 Main Street"
  , unacceptableAnswer := "Your neighbor's husband"
  , explanation := "Questions are posed on behalf of the social community. " ++
      "Answers must work for a great variety of information sets, " ++
      "so they should stay as close to semantic answers as possible."
  , source := "G&S 1984, p. 363, 390"
  }

def institutionalExamples : List InstitutionalAnswerDatum :=
  [courtTestimony]

-- ============================================================================
-- PART 8: Key Theoretical Principles
-- ============================================================================

/-- G&S p. 355: Semantic answerhood as limit of pragmatic answerhood -/
def semanticAsLimit : String :=
  "Semantic answers are the answers one is to address to a questioner " ++
  "who has no factual information at all. Since we know our information " ++
  "about the information of others to be imperfect, the safest way to " ++
  "answer a question is to stay as close to semantic answers as one can."

/-- G&S p. 358: Why pragmatic properties make answering easier -/
def pragmaticEase : String :=
  "In actual speech situations, in which a lot of information is available, " ++
  "it is much easier to provide efficient and adequate answers than " ++
  "semantics proper suggests. This supports the view that an interesting " ++
  "theory of question-answering cannot do without a semantically based pragmatics."

/-- G&S p. 361: When indefinite terms constitute good answers -/
def indefiniteAnswers : String :=
  "Indefinite, non-rigid terms constitute perfectly good answers in situations " ++
  "where speech participants have disharmonious information about a subject matter, " ++
  "but nevertheless are to achieve effective exchange of information."

end Phenomena.Questions.PragmaticAnswerhood
