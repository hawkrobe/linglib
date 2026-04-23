/-!
# Subject-Auxiliary Inversion: Empirical Data
@cite{radford-2009} @cite{adger-2003} @cite{sag-wasow-bender-2003} @cite{chomsky-1957} @cite{henry-1995} @cite{klima-1964} @cite{mccloskey-2006} @cite{westergaard-2009}

Theory-neutral data on subject-auxiliary inversion (SAI) in English and beyond.

## The Phenomenon

In English, finite auxiliaries invert with the subject in matrix questions
but not in embedded questions. This basic pattern interacts with negation,
conditionals, exclamatives, and shows systematic dialectal variation.

## Classic Data

The core SAI pattern has been a central case study in generative syntax
since @cite{chomsky-1957}. Textbook presentations: @cite{radford-2009},
@cite{adger-2003}, @cite{sag-wasow-bender-2003}.

## Boundary Cases

Several phenomena push beyond the textbook treatment:
- Negative inversion
- Conditional inversion
- Embedded inversion in non-standard varieties
- Do-support and verb movement
- Verb-specific acquisition of inversion

-/

namespace Phenomena.WordOrder.SubjectAuxInversion

-- ============================================================================
-- Types
-- ============================================================================

/-- The syntactic context in which SAI does or does not occur. -/
inductive SAIContext where
  /-- Matrix wh-question: "What can John eat?" -/
  | matrixWh
  /-- Matrix yes/no question: "Can John eat pizza?" -/
  | matrixYN
  /-- Embedded question: "I wonder what John can eat" -/
  | embedded
  /-- Echo question: "John can eat WHAT?" -/
  | echo
  /-- Negative fronting: "Never have I seen such a thing" -/
  | negativeInversion
  /-- Conditional inversion: "Had I known, I would have come" -/
  | conditionalInversion
  /-- Exclamative: "Boy, is it hot!" -/
  | exclamative
  /-- So/neither inversion: "So did I" / "Neither can she" -/
  | soNeither
  /-- Embedded inversion (dialectal): "I asked could he come" -/
  | embeddedDialectal
  /-- Sentential negation (parallel to SAI for do-support):
      "Sue does not eat fish" / "Sue is not eating fish" -/
  | sententialNegation
  /-- Verb raising diagnostic (adverb/quantifier placement):
      "Jean embrasse souvent Marie" vs "*John kisses often Mary" -/
  | verbRaising
  /-- Tag question: "She likes him, doesn't she?" -/
  | tagQuestion
  /-- VP ellipsis (stranded tense): "She runs faster than he does" -/
  | vpEllipsis
  /-- Emphatic/verum focus: "Sue DOES eat fish" -/
  | emphatic
  deriving DecidableEq, Repr

/-- Acceptability judgment. -/
inductive Acceptability where
  | grammatical
  | ungrammatical
  | marginal
  /-- Grammatical in some dialects but not Standard American/British English -/
  | dialectal
  deriving DecidableEq, Repr

/-- A single SAI judgment. -/
structure SAIDatum where
  /-- The example sentence -/
  sentence : String
  /-- Whether the sentence shows auxiliary/verb-before-subject order -/
  inverted : Bool
  /-- The syntactic context -/
  context : SAIContext
  /-- Acceptability judgment -/
  acceptability : Acceptability
  /-- Language (default: English) -/
  language : String := "English"
  /-- Description of what this datum tests -/
  description : String := ""
  /-- Citation for the datum -/
  citation : String := ""
  deriving Repr, BEq

-- ============================================================================
-- § 1  Core Minimal Pairs (Classic)
-- ============================================================================

/-! ### Matrix wh-questions

Wh-questions in root clauses require SAI in Standard English.
The auxiliary must precede the subject. -/

def ex01 : SAIDatum :=
  { sentence := "What can John eat?"
    inverted := true
    context := .matrixWh
    acceptability := .grammatical
    description := "Matrix wh-question with inversion" }

def ex02 : SAIDatum :=
  { sentence := "What John can eat?"
    inverted := false
    context := .matrixWh
    acceptability := .ungrammatical
    description := "Matrix wh-question without inversion" }

def ex03 : SAIDatum :=
  { sentence := "Where has Mary gone?"
    inverted := true
    context := .matrixWh
    acceptability := .grammatical
    description := "Matrix wh-question with 'have' auxiliary" }

/-! ### Matrix yes/no questions

Polar questions also require SAI. -/

def ex04 : SAIDatum :=
  { sentence := "Can John eat pizza?"
    inverted := true
    context := .matrixYN
    acceptability := .grammatical
    description := "Polar question with inversion" }

def ex05 : SAIDatum :=
  { sentence := "John can eat pizza?"
    inverted := false
    context := .matrixYN
    acceptability := .ungrammatical
    description := "Polar question without inversion"
    citation := "@cite{radford-2009}" }

def ex06 : SAIDatum :=
  { sentence := "Is the cat sleeping?"
    inverted := true
    context := .matrixYN
    acceptability := .grammatical
    description := "Polar question with copula 'be'" }

/-! ### Embedded questions

Embedded questions in Standard English prohibit SAI.
The complementizer or wh-word alone marks the clause as interrogative. -/

def ex07 : SAIDatum :=
  { sentence := "I wonder what John can eat"
    inverted := false
    context := .embedded
    acceptability := .grammatical
    description := "Embedded question without inversion" }

def ex08 : SAIDatum :=
  { sentence := "I wonder what can John eat"
    inverted := true
    context := .embedded
    acceptability := .ungrammatical
    description := "Embedded question with inversion (Standard English)"
    citation := "@cite{radford-2009}" }

def ex09 : SAIDatum :=
  { sentence := "She asked whether John had left"
    inverted := false
    context := .embedded
    acceptability := .grammatical
    description := "Whether-complement without inversion" }

/-! ### Echo questions

Echo questions preserve declarative word order with prosodic focus
on the wh-element. No SAI occurs. -/

def ex10 : SAIDatum :=
  { sentence := "John can eat WHAT?"
    inverted := false
    context := .echo
    acceptability := .grammatical
    description := "Echo question — wh-in-situ, no inversion" }

-- ============================================================================
-- § 3  Negative Inversion (@cite{klima-1964})
-- ============================================================================

/-! When a negative or restrictive adverbial is fronted, SAI is obligatory.
This is surprising on a purely interrogative analysis of inversion — negative
inversion occurs in declaratives, not questions. It is a key argument for
treating SAI as a structural phenomenon (head movement to C or feature-driven)
rather than an illocutionary one. -/

def ex11 : SAIDatum :=
  { sentence := "Never have I seen such a thing"
    inverted := true
    context := .negativeInversion
    acceptability := .grammatical
    description := "Fronted negative adverb triggers inversion"
    citation := "@cite{klima-1964}" }

def ex12 : SAIDatum :=
  { sentence := "Never I have seen such a thing"
    inverted := false
    context := .negativeInversion
    acceptability := .ungrammatical
    description := "Fronted negative adverb without inversion" }

def ex13 : SAIDatum :=
  { sentence := "Rarely does she complain"
    inverted := true
    context := .negativeInversion
    acceptability := .grammatical
    description := "Fronted restrictive adverb triggers inversion" }

def ex14 : SAIDatum :=
  { sentence := "Not only did he leave, but he slammed the door"
    inverted := true
    context := .negativeInversion
    acceptability := .grammatical
    description := "Not only ... but also with inversion" }

def ex15 : SAIDatum :=
  { sentence := "Under no circumstances will I agree"
    inverted := true
    context := .negativeInversion
    acceptability := .grammatical
    description := "Fronted negative PP triggers inversion" }

-- ============================================================================
-- § 4  Conditional Inversion
-- ============================================================================

/-! Counterfactual conditionals allow omission of 'if' with obligatory SAI.
This is restricted to 'had', 'were', and 'should', suggesting it is a
lexically specific rather than fully productive process. -/

def ex16 : SAIDatum :=
  { sentence := "Had I known, I would have come"
    inverted := true
    context := .conditionalInversion
    acceptability := .grammatical
    description := "Conditional inversion with 'had'" }

def ex17 : SAIDatum :=
  { sentence := "Were she here, she would help"
    inverted := true
    context := .conditionalInversion
    acceptability := .grammatical
    description := "Conditional inversion with subjunctive 'were'" }

def ex18 : SAIDatum :=
  { sentence := "Should you need anything, please ask"
    inverted := true
    context := .conditionalInversion
    acceptability := .grammatical
    description := "Conditional inversion with 'should'" }

def ex19 : SAIDatum :=
  { sentence := "Could she swim, she would cross the river"
    inverted := true
    context := .conditionalInversion
    acceptability := .marginal
    description := "Conditional inversion with 'could' — degraded vs had/were/should" }

-- ============================================================================
-- § 5  Exclamative and So/Neither Inversion
-- ============================================================================

/-! SAI also occurs in exclamatives and in 'so'/'neither' constructions.
These extend the phenomenon beyond interrogatives. -/

def ex20 : SAIDatum :=
  { sentence := "Boy, is it hot!"
    inverted := true
    context := .exclamative
    acceptability := .grammatical
    description := "Exclamative inversion" }

def ex21 : SAIDatum :=
  { sentence := "So did I"
    inverted := true
    context := .soNeither
    acceptability := .grammatical
    description := "So-inversion (VP anaphora)" }

def ex22 : SAIDatum :=
  { sentence := "Neither can she"
    inverted := true
    context := .soNeither
    acceptability := .grammatical
    description := "Neither-inversion (negative VP anaphora)" }

-- ============================================================================
-- § 6  Embedded Inversion in Non-Standard Varieties
-- ============================================================================

/-! Standard English prohibits SAI in embedded questions, but several dialects
productively allow it. This is a key testing ground for syntactic theory:

- **Belfast English**: Embedded inversion with specific verbs
  (wonder, ask, know) but not others (tell).
- **Hiberno-English**: More general embedded inversion,
  including with 'if' complements.
The dialectal data challenges any analysis that categorically ties SAI to
root CP structure. It suggests the [+Q] or [+wh] feature can license
T-to-C in embedded clauses under the right parametric conditions. -/

def ex23 : SAIDatum :=
  { sentence := "I wonder could he come"
    inverted := true
    context := .embeddedDialectal
    acceptability := .dialectal
    description := "Belfast English embedded inversion with 'wonder'"
    citation := "@cite{henry-1995}" }

def ex24 : SAIDatum :=
  { sentence := "I asked would she help"
    inverted := true
    context := .embeddedDialectal
    acceptability := .dialectal
    description := "Belfast English embedded inversion with 'ask'"
    citation := "@cite{henry-1995}" }

def ex25 : SAIDatum :=
  { sentence := "I don't know is he coming"
    inverted := true
    context := .embeddedDialectal
    acceptability := .dialectal
    description := "Hiberno-English embedded inversion"
    citation := "@cite{mccloskey-2006}" }

def ex26 : SAIDatum :=
  { sentence := "I told him could he come"
    inverted := true
    context := .embeddedDialectal
    acceptability := .ungrammatical
    description := "Embedded inversion with 'tell' blocked even in Belfast English"
    citation := "@cite{henry-1995}" }

-- ============================================================================
-- § 7  The French/English Verb Movement Contrast (@cite{pollock-1989})
-- ============================================================================

/-! @cite{pollock-1989} established that French and English differ fundamentally in
verb movement. French lexical verbs obligatorily raise to I (T), placing them
before adverbs, negation, and floating quantifiers. English lexical verbs
stay in situ, below adverbs and negation.

This contrast is the *reason* English has do-support and restricts SAI to
auxiliaries: English lexical verbs cannot raise to T (let alone to C), so
when T must be spelled out in C (for SAI) or above negation, a dummy 'do'
is inserted instead.

  (Pollock 2) Negation:
    a. *John likes not Mary. (English: V cannot raise past negation)
    b. Jean n'aime pas Marie. (French: V raises past negation)

  (Pollock 3) Questions / SAI:
    a. *Likes he Mary? (English: lexical V cannot invert)
    b. Aime-t-il Marie? (French: lexical V inverts)

  (Pollock 4) Adverb placement:
    a. *John kisses often Mary. (English: V cannot raise past adverb)
    b. Jean embrasse souvent Marie. (French: V raises past adverb)
    c. John often kisses Mary. (English: adverb precedes V)
    d. *Jean souvent embrasse Marie. (French: adverb cannot precede V)

  (Pollock 5) Floating quantifiers:
    a. *My friends love all Mary. (English: V cannot raise past FQ)
    b. Mes amis aiment tous Marie. (French: V raises past FQ)
    c. My friends all love Mary. (English: FQ precedes V)
    d. *Mes amis tous aiment Marie. (French: FQ cannot precede V)

The four diagnostics converge: French V raises, English V does not. English
auxiliaries *do* raise (hence "John has often eaten" is grammatical), which
is why they can participate in SAI while lexical verbs cannot. -/

/-- Pollock (3): French lexical verb inversion -/

def ex_p01 : SAIDatum :=
  { sentence := "Aime-t-il Marie?"
    inverted := true
    context := .matrixYN
    acceptability := .grammatical
    language := "French"
    description := "French lexical verb inverts (V-to-I-to-C)"
    citation := "@cite{pollock-1989}" }

def ex_p02 : SAIDatum :=
  { sentence := "Likes he Mary?"
    inverted := true
    context := .matrixYN
    acceptability := .ungrammatical
    description := "English lexical verb cannot invert (*V-to-C)"
    citation := "@cite{pollock-1989}" }

/-- Pollock (4): Adverb placement diagnostic -/

def ex_p03 : SAIDatum :=
  { sentence := "Jean embrasse souvent Marie"
    inverted := false
    context := .verbRaising
    acceptability := .grammatical
    language := "French"
    description := "French V raises past adverb (V > Adv)"
    citation := "@cite{pollock-1989}" }

def ex_p04 : SAIDatum :=
  { sentence := "John kisses often Mary"
    inverted := false
    context := .verbRaising
    acceptability := .ungrammatical
    description := "English V cannot raise past adverb (*V > Adv)"
    citation := "@cite{pollock-1989}" }

def ex_p05 : SAIDatum :=
  { sentence := "John often kisses Mary"
    inverted := false
    context := .verbRaising
    acceptability := .grammatical
    description := "English Adv precedes V (Adv > V)"
    citation := "@cite{pollock-1989}" }

def ex_p06 : SAIDatum :=
  { sentence := "Jean souvent embrasse Marie"
    inverted := false
    context := .verbRaising
    acceptability := .ungrammatical
    language := "French"
    description := "French Adv cannot precede V (*Adv > V, V must raise)"
    citation := "@cite{pollock-1989}" }

/-- Pollock (2): Negation diagnostic -/

def ex_p07 : SAIDatum :=
  { sentence := "Jean n'aime pas Marie"
    inverted := false
    context := .sententialNegation
    acceptability := .grammatical
    language := "French"
    description := "French V raises past negation (V > Neg)"
    citation := "@cite{pollock-1989}" }

def ex_p08 : SAIDatum :=
  { sentence := "John likes not Mary"
    inverted := false
    context := .sententialNegation
    acceptability := .ungrammatical
    description := "English V cannot raise past negation (*V > Neg)"
    citation := "@cite{pollock-1989}" }

/-- Pollock (5): Floating quantifier diagnostic -/

def ex_p09 : SAIDatum :=
  { sentence := "Mes amis aiment tous Marie"
    inverted := false
    context := .verbRaising
    acceptability := .grammatical
    language := "French"
    description := "French V raises past floating quantifier (V > FQ)"
    citation := "@cite{pollock-1989}" }

def ex_p10 : SAIDatum :=
  { sentence := "My friends love all Mary"
    inverted := false
    context := .verbRaising
    acceptability := .ungrammatical
    description := "English V cannot raise past floating quantifier (*V > FQ)"
    citation := "@cite{pollock-1989}" }

/-- English auxiliaries DO raise (unlike lexical verbs) — same diagnostic -/

def ex_p11 : SAIDatum :=
  { sentence := "John has often eaten pizza"
    inverted := false
    context := .verbRaising
    acceptability := .grammatical
    description := "English auxiliary raises past adverb (Aux > Adv)"
    citation := "@cite{pollock-1989}" }

def ex_p12 : SAIDatum :=
  { sentence := "John often has eaten pizza"
    inverted := false
    context := .verbRaising
    acceptability := .marginal
    description := "English adverb before auxiliary — marginal (Aux should raise)"
    citation := "@cite{pollock-1989}" }

-- ============================================================================
-- § 8  Do-Support and Generalized Head Movement
--      (@cite{pollock-1989}, @cite{arregi-pietraszko-2021})
-- ============================================================================

/-! SAI interacts with do-support: when no auxiliary is present, 'do' is
inserted to host tense and carry out inversion.

@cite{arregi-pietraszko-2021} unify upward displacement (T-to-C in SAI) and
downward displacement (T-to-V lowering) as a single operation: Generalized
Head Movement (GenHM). Under GenHM, the same mechanism of M-value sharing
drives both. The crucial empirical support is that lexical verbs trigger
do-support in *all three* contexts where tense cannot lower — negation,
verum focus, and SAI — while auxiliaries invert directly in all three.
This parallel is predicted if SAI and T-lowering are the same operation
(displacement of T) with spelling out at the highest strong terminal.

  (A&P 36) Lexical verbs — do-support in negation / verum / SAI:
    a. Sue does not eat fish. (*Sue not eats fish)
    b. Sue DOES eat fish. (*Sue EATS fish [verum])
    c. Where does Sue eat fish? (*Where eats Sue fish?)

  (A&P 37) Auxiliaries — direct displacement, no do-support:
    a. Sue is not eating fish. (*Sue does not be eating fish)
    b. Sue IS eating fish. (*Sue DOES be eating fish [verum])
    c. Where is Sue eating fish? (*Where does Sue be eating fish?)

The do-support facts raise a puzzle for T-to-C analyses: if T moves to C,
why is a dummy 'do' needed rather than affix-lowering simply being blocked?
Arregi & Pietraszko resolve this by treating the spell-out position as a PF
decision, independent of the syntactic feature-sharing operation. -/

/-- Do-support with lexical verbs in SAI -/

def ex27 : SAIDatum :=
  { sentence := "Where does Sue eat fish?"
    inverted := true
    context := .matrixWh
    acceptability := .grammatical
    description := "Do-support in wh-question (lexical verb)"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex28 : SAIDatum :=
  { sentence := "Eats John pizza?"
    inverted := true
    context := .matrixYN
    acceptability := .ungrammatical
    description := "Lexical verb cannot invert directly (*V-to-C)" }

def ex29 : SAIDatum :=
  { sentence := "What did Mary buy?"
    inverted := true
    context := .matrixWh
    acceptability := .grammatical
    description := "Do-support with wh-movement (lexical verb)" }

/-- Auxiliaries invert without do-support -/

def ex30 : SAIDatum :=
  { sentence := "Where is Sue eating fish?"
    inverted := true
    context := .matrixWh
    acceptability := .grammatical
    description := "Auxiliary inverts directly — no do-support"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex31 : SAIDatum :=
  { sentence := "Where does Sue be eating fish?"
    inverted := true
    context := .matrixWh
    acceptability := .ungrammatical
    description := "Do-support with auxiliary is ungrammatical"
    citation := "@cite{arregi-pietraszko-2021}" }

/-- The negation/verum parallel (same auxiliary vs lexical verb contrast) -/

def ex32 : SAIDatum :=
  { sentence := "Sue does not eat fish"
    inverted := false
    context := .sententialNegation
    acceptability := .grammatical
    description := "Do-support in sentential negation (lexical verb)"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex33 : SAIDatum :=
  { sentence := "Sue not eats fish"
    inverted := false
    context := .sententialNegation
    acceptability := .ungrammatical
    description := "Lexical verb cannot raise past negation"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex34 : SAIDatum :=
  { sentence := "Sue is not eating fish"
    inverted := false
    context := .sententialNegation
    acceptability := .grammatical
    description := "Auxiliary raises past negation — no do-support"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex35 : SAIDatum :=
  { sentence := "Sue does not be eating fish"
    inverted := false
    context := .sententialNegation
    acceptability := .ungrammatical
    description := "Do-support with auxiliary is ungrammatical even in negation"
    citation := "@cite{arregi-pietraszko-2021}" }

-- ============================================================================
-- § 8b  Additional Do-Support Contexts (Tag Questions, VP Ellipsis, Verum)
-- ============================================================================

/-! Three further contexts where tense needs overt support, completing
the paradigm of environments that trigger do-insertion with lexical verbs. -/

/-- Tag question with do-support -/
def ex36 : SAIDatum :=
  { sentence := "She likes him, doesn't she?"
    inverted := true
    context := .tagQuestion
    acceptability := .grammatical
    description := "Tag question with do-support (lexical verb)" }

def ex37 : SAIDatum :=
  { sentence := "She likes him, likesn't she?"
    inverted := true
    context := .tagQuestion
    acceptability := .ungrammatical
    description := "Tag question without do-support — lexical verb cannot host negation" }

/-- VP ellipsis with stranded tense -/
def ex38 : SAIDatum :=
  { sentence := "She runs faster than he does"
    inverted := false
    context := .vpEllipsis
    acceptability := .grammatical
    description := "VP ellipsis — do-support strands tense (lexical verb)" }

/-- Verum focus (emphatic 'do') -/
def ex39 : SAIDatum :=
  { sentence := "Sue DOES eat fish"
    inverted := false
    context := .emphatic
    acceptability := .grammatical
    description := "Verum focus with do-support (lexical verb)"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex40 : SAIDatum :=
  { sentence := "She IS eating fish"
    inverted := false
    context := .emphatic
    acceptability := .grammatical
    description := "Verum focus with auxiliary — no do-support needed"
    citation := "@cite{arregi-pietraszko-2021}" }

def ex41 : SAIDatum :=
  { sentence := "She DOES be eating fish"
    inverted := false
    context := .emphatic
    acceptability := .ungrammatical
    description := "Do-support with auxiliary is ungrammatical even for verum"
    citation := "@cite{arregi-pietraszko-2021}" }

-- ============================================================================
-- Aggregate Collections
-- ============================================================================

/-- All individual SAI data points. -/
def allData : List SAIDatum :=
  [ ex01, ex02, ex03, ex04, ex05, ex06, ex07, ex08, ex09, ex10
  , ex11, ex12, ex13, ex14, ex15
  , ex16, ex17, ex18, ex19
  , ex20, ex21, ex22
  , ex23, ex24, ex25, ex26
  , ex_p01, ex_p02, ex_p03, ex_p04, ex_p05, ex_p06
  , ex_p07, ex_p08, ex_p09, ex_p10, ex_p11, ex_p12
  , ex27, ex28, ex29, ex30, ex31, ex32, ex33, ex34, ex35
  , ex36, ex37, ex38, ex39, ex40, ex41 ]

/-- Classic core data (matrix + embedded questions only). -/
def classicData : List SAIDatum :=
  allData.filter λ d => d.context == .matrixWh
    || d.context == .matrixYN
    || d.context == .embedded
    || d.context == .echo

/-- Non-interrogative SAI contexts (negative, conditional, exclamative). -/
def nonInterrogativeData : List SAIDatum :=
  allData.filter λ d => d.context == .negativeInversion
    || d.context == .conditionalInversion
    || d.context == .exclamative
    || d.context == .soNeither

/-- Dialectal variation data. -/
def dialectalData : List SAIDatum :=
  allData.filter λ d => d.context == .embeddedDialectal

/-- French/English verb movement contrast. -/
def pollockData : List SAIDatum :=
  [ex_p01, ex_p02, ex_p03, ex_p04, ex_p05, ex_p06,
   ex_p07, ex_p08, ex_p09, ex_p10, ex_p11, ex_p12]

/-- Cross-linguistic data (non-English). -/
def crossLinguisticData : List SAIDatum :=
  allData.filter (·.language != "English")

/-- Do-support interaction data. -/
def doSupportData : List SAIDatum :=
  [ex27, ex28, ex29, ex30, ex31, ex32, ex33, ex34, ex35,
   ex36, ex37, ex38, ex39, ex40, ex41]

-- ============================================================================
-- Empirical Generalizations
-- ============================================================================

-- Core paradigm: inverted matrix questions with a legitimate auxiliary
-- are grammatical; non-inverted matrix questions are ungrammatical.
-- (The do-support cases ex28/ex31 are inverted but ungrammatical for
-- independent reasons — wrong head type — which is exactly what
-- Arregi & Pietraszko's account predicts.)
#guard ex01.acceptability == .grammatical   -- What can John eat?
#guard ex02.acceptability == .ungrammatical -- *What John can eat?
#guard ex04.acceptability == .grammatical   -- Can John eat pizza?
#guard ex05.acceptability == .ungrammatical -- *John can eat pizza?

-- Embedded questions with inversion are ungrammatical in Standard English.
#guard ex08.acceptability == .ungrammatical -- *I wonder what can John eat

-- Negative inversion: fronted negative triggers obligatory SAI.
#guard ex11.acceptability == .grammatical   -- Never have I seen...
#guard ex12.acceptability == .ungrammatical -- *Never I have seen...

-- Belfast English embedded inversion is dialectal, not ungrammatical.
#guard ex23.acceptability == .dialectal     -- I wonder could he come
#guard ex24.acceptability == .dialectal     -- I asked would she help

-- Arregi & Pietraszko: do-support with auxiliary is always ungrammatical
-- (auxiliaries displace directly, not via do).
#guard ex31.acceptability == .ungrammatical -- *Where does Sue be eating fish?
#guard ex35.acceptability == .ungrammatical -- *Sue does not be eating fish

-- Lexical verbs cannot invert or raise past negation directly.
#guard ex28.acceptability == .ungrammatical -- *Eats John pizza?
#guard ex33.acceptability == .ungrammatical -- *Sue not eats fish

-- Do-support is the grammatical alternative for lexical verbs.
#guard ex27.acceptability == .grammatical   -- Where does Sue eat fish?
#guard ex32.acceptability == .grammatical   -- Sue does not eat fish

-- Pollock: French lexical verbs raise; English lexical verbs do not.
#guard ex_p01.acceptability == .grammatical   -- Aime-t-il Marie? (French V inverts)
#guard ex_p02.acceptability == .ungrammatical -- *Likes he Mary? (English V can't)
#guard ex_p03.acceptability == .grammatical   -- Jean embrasse souvent Marie (V > Adv)
#guard ex_p04.acceptability == .ungrammatical -- *John kisses often Mary (*V > Adv)

-- Pollock: English auxiliaries pattern with French lexical verbs (they raise).
#guard ex_p11.acceptability == .grammatical   -- John has often eaten pizza

-- Tag questions require do-support with lexical verbs.
#guard ex36.acceptability == .grammatical     -- She likes him, doesn't she?
#guard ex37.acceptability == .ungrammatical   -- *She likes him, likesn't she?

-- VP ellipsis strands tense, requiring do-support.
#guard ex38.acceptability == .grammatical     -- She runs faster than he does

-- Verum focus: do-support for lexical verbs, direct auxiliary for auxiliaries.
#guard ex39.acceptability == .grammatical     -- Sue DOES eat fish
#guard ex40.acceptability == .grammatical     -- She IS eating fish
#guard ex41.acceptability == .ungrammatical   -- *She DOES be eating fish

end Phenomena.WordOrder.SubjectAuxInversion
