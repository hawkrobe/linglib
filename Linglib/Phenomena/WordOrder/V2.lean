import Linglib.Core.Grammar

/-!
# Verb-Second (V2) Word Order: Cross-Linguistic Data
@cite{westergaard-2009} @cite{vikner-1995}

Theory-neutral observations on V2 word order variation across Germanic
languages and dialects. V2 is the requirement that the finite verb appear
in second position in main clauses.

## The Key Observation

V2 is not uniform. It varies along at least three dimensions:
1. **Clause type**: declaratives, *wh*-questions, *yes/no*-questions,
   exclamatives, imperatives, embedded clauses
2. **Lexical element**: which initial element precedes the verb
   (long vs. short *wh*-words, focus adverbs, *kanskje* 'maybe')
3. **Information structure**: given vs. new subjects correlate with
   non-V2 vs. V2 in "optional" contexts

The data below document these dimensions. Theoretical analyses belong
in `Studies/Westergaard2009.lean` and related study files.
-/

namespace Phenomena.WordOrder.V2

-- ============================================================================
-- Types
-- ============================================================================

/-- Clause types relevant to V2 variation. -/
inductive ClauseType where
  | declarative
  | whQuestion
  | yesNoQuestion
  | exclamative
  | imperative
  | embeddedDecl
  | embeddedQuestion
  deriving DecidableEq, Repr, BEq

/-- V2 status of a clause type in a given language/dialect. -/
inductive V2Status where
  /-- V2 is obligatory -/
  | obligatory
  /-- V2 is impossible (verb stays low or appears finally) -/
  | impossible
  /-- V2 alternates with non-V2, conditioned by other factors -/
  | optional
  deriving DecidableEq, Repr, BEq

/-- A single V2 observation: what happens in a given clause type. -/
structure V2Datum where
  sentence : String
  language : String
  clauseType : ClauseType
  v2Status : V2Status
  description : String := ""
  citation : String := ""
  deriving Repr, BEq

-- ============================================================================
-- § 1  Norwegian V2 Variation (Tromsø dialect, Table 2.3)
-- ============================================================================

/-! The Tromsø dialect exhibits a rich V2/non-V2 split across clause types.
This is the target grammar that children in @cite{westergaard-2009}'s
corpus are acquiring. -/

/-- Non-subject-initial declaratives: V2 obligatory. -/
def no_decl_nonsubj : V2Datum :=
  { sentence := "Av og til snakker vi tysk"
    language := "Norwegian (Tromsø)"
    clauseType := .declarative
    v2Status := .obligatory
    description := "Non-subject-initial declarative: V2 obligatory"
    citation := "Westergaard (2009) Table 2.3" }

/-- Yes/no-questions: V2 obligatory. -/
def no_yesno : V2Datum :=
  { sentence := "Snakker dere norsk?"
    language := "Norwegian (Tromsø)"
    clauseType := .yesNoQuestion
    v2Status := .obligatory
    description := "Yes/no-question: V2 obligatory"
    citation := "Westergaard (2009) (3)" }

/-- Wh-questions with long (polysyllabic) wh-phrases: V2 obligatory. -/
def no_wh_long : V2Datum :=
  { sentence := "Korfor gikk ho?"
    language := "Norwegian (Tromsø)"
    clauseType := .whQuestion
    v2Status := .obligatory
    description := "Wh-question with disyllabic korfor 'why': V2 obligatory"
    citation := "Westergaard (2009) (40)" }

/-- Wh-questions with short (monosyllabic) wh-words: V2 optional,
    conditioned by information structure. -/
def no_wh_short : V2Datum :=
  { sentence := "Ka legen sa? / Ka sa legen?"
    language := "Norwegian (Tromsø)"
    clauseType := .whQuestion
    v2Status := .optional
    description := "Wh-question with monosyllabic ka 'what': V2/non-V2 depends on subject givenness"
    citation := "Westergaard (2009) (43)–(45)" }

/-- Exclamatives: non-V2 obligatory. -/
def no_excl : V2Datum :=
  { sentence := "Kor rart han snakke!"
    language := "Norwegian (Tromsø)"
    clauseType := .exclamative
    v2Status := .impossible
    description := "Exclamative: non-V2 obligatory"
    citation := "Westergaard (2009) (5)" }

/-- Embedded declaratives: non-V2 (mostly). -/
def no_emb_decl : V2Datum :=
  { sentence := "Han sa (at) han ikke kommer"
    language := "Norwegian (Tromsø)"
    clauseType := .embeddedDecl
    v2Status := .impossible
    description := "Embedded declarative: non-V2 (verb below negation)"
    citation := "Westergaard (2009) (36)" }

-- ============================================================================
-- § 2  Cross-Germanic Contrasts
-- ============================================================================

/-- German root declaratives: V2 obligatory. -/
def de_decl : V2Datum :=
  { sentence := "Diesen Film haben die Kinder gesehen"
    language := "German"
    clauseType := .declarative
    v2Status := .obligatory
    description := "German root declarative: V2"
    citation := "Vikner (1995)" }

/-- German embedded clauses with complementizer: verb-final (no V2).
    The verb raises to I/Fin (hence +Fin° in Table 3.1) but not to C,
    so it appears clause-finally due to SOV base order. -/
def de_emb : V2Datum :=
  { sentence := "... dass die Kinder diesen Film gesehen haben"
    language := "German"
    clauseType := .embeddedDecl
    v2Status := .impossible
    description := "German embedded clause with dass: verb-final (V-to-I only, not V-to-C)"
    citation := "Vikner (1995)" }

/-- Standard English: no V2 in declaratives (SVO base order). -/
def en_decl : V2Datum :=
  { sentence := "The children have seen this film"
    language := "English"
    clauseType := .declarative
    v2Status := .impossible
    description := "English declarative: no V2 (SVO base order)"
    citation := "Westergaard (2009) Table 3.1" }

/-- Standard English: V2 in wh-questions (via SAI). -/
def en_wh : V2Datum :=
  { sentence := "What will you wear tonight?"
    language := "English"
    clauseType := .whQuestion
    v2Status := .obligatory
    description := "English wh-question: V2 (subject-auxiliary inversion)"
    citation := "Westergaard (2009) Table 3.1" }

/-- Belfast English: V2 in embedded questions too. -/
def belfast_emb_q : V2Datum :=
  { sentence := "I wonder could he come"
    language := "English (Belfast)"
    clauseType := .embeddedQuestion
    v2Status := .obligatory
    description := "Belfast English: V2 in embedded questions"
    citation := "Westergaard (2009) Table 3.1; Henry (1997)" }

/-- Danish: V2 in exclamatives (unlike Norwegian and English). -/
def da_excl : V2Datum :=
  { sentence := "Hvor er han sød!"
    language := "Danish"
    clauseType := .exclamative
    v2Status := .obligatory
    description := "Danish exclamative: V2 (unlike Norwegian/English)"
    citation := "Westergaard (2009) (17)" }

-- ============================================================================
-- Aggregate Collections
-- ============================================================================

def norwegianData : List V2Datum :=
  [no_decl_nonsubj, no_yesno, no_wh_long, no_wh_short,
   no_excl, no_emb_decl]

def crossGermanicData : List V2Datum :=
  [de_decl, de_emb, en_decl, en_wh, belfast_emb_q, da_excl]

def allData : List V2Datum :=
  norwegianData ++ crossGermanicData

-- ============================================================================
-- Empirical Generalizations
-- ============================================================================

-- Norwegian: yes/no-questions are obligatorily V2
#guard no_yesno.v2Status == .obligatory

-- Norwegian: exclamatives are obligatorily non-V2
#guard no_excl.v2Status == .impossible

-- Norwegian: short wh-questions are optional (information-structure dependent)
#guard no_wh_short.v2Status == .optional

-- English: declaratives are non-V2, wh-questions are V2
#guard en_decl.v2Status == .impossible
#guard en_wh.v2Status == .obligatory

-- German: V2 in root, verb-final in embedded
#guard de_decl.v2Status == .obligatory
#guard de_emb.v2Status == .impossible

-- Danish exclamatives differ from Norwegian
#guard da_excl.v2Status == .obligatory
#guard no_excl.v2Status == .impossible

end Phenomena.WordOrder.V2
