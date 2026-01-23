/-
# LingLean.Syntax.Basic

Core syntactic types shared across all frameworks.
-/

-- ============================================================================
-- Syntactic Categories
-- ============================================================================

/-- Syntactic categories (coarse-grained, refined per framework) -/
inductive Cat where
  | D      -- Determiner / DP
  | N      -- Noun
  | V      -- Verb (lexical)
  | Aux    -- Auxiliary verb
  | C      -- Complementizer
  | T      -- Tense (Minimalism)
  | Wh     -- Wh-phrase
  | P      -- Preposition
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Clause Types
-- ============================================================================

/-- Clause types - determines constraints on word order -/
inductive ClauseType where
  | declarative
  | matrixQuestion      -- requires inversion in English
  | embeddedQuestion    -- no inversion in English
  | echo                -- no inversion even in matrix position
  deriving Repr, DecidableEq

-- ============================================================================
-- Features
-- ============================================================================

/-- Minimal feature bundle (shared; frameworks add more) -/
structure Features where
  wh : Bool := false
  finite : Bool := true
  deriving Repr, DecidableEq

-- ============================================================================
-- Words
-- ============================================================================

/-- A word: form + category + features -/
structure Word where
  form : String
  cat : Cat
  features : Features := {}
  deriving Repr

instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form

/-- Convert a word list to a readable string -/
def wordsToString (ws : List Word) : String :=
  " ".intercalate (ws.map (·.form))

-- ============================================================================
-- Lexicon
-- ============================================================================

namespace Lexicon

-- Wh-words
def what : Word := ⟨"what", Cat.Wh, { wh := true }⟩
def who : Word := ⟨"who", Cat.Wh, { wh := true }⟩
def where_ : Word := ⟨"where", Cat.Wh, { wh := true }⟩

-- Auxiliaries
def can : Word := ⟨"can", Cat.Aux, { finite := true }⟩
def will : Word := ⟨"will", Cat.Aux, { finite := true }⟩
def does : Word := ⟨"does", Cat.Aux, { finite := true }⟩
def did : Word := ⟨"did", Cat.Aux, { finite := true }⟩
def is : Word := ⟨"is", Cat.Aux, { finite := true }⟩
def are : Word := ⟨"are", Cat.Aux, { finite := true }⟩

-- Pronouns / DPs
def i : Word := ⟨"I", Cat.D, {}⟩
def you : Word := ⟨"you", Cat.D, {}⟩
def he : Word := ⟨"he", Cat.D, {}⟩
def she : Word := ⟨"she", Cat.D, {}⟩
def it : Word := ⟨"it", Cat.D, {}⟩

-- Proper names
def john : Word := ⟨"John", Cat.D, {}⟩
def mary : Word := ⟨"Mary", Cat.D, {}⟩

-- Common nouns (as DPs for simplicity)
def pizza : Word := ⟨"pizza", Cat.D, {}⟩
def book : Word := ⟨"book", Cat.D, {}⟩

-- Verbs
def eat : Word := ⟨"eat", Cat.V, {}⟩
def see : Word := ⟨"see", Cat.V, {}⟩
def read : Word := ⟨"read", Cat.V, {}⟩
def wonder : Word := ⟨"wonder", Cat.V, {}⟩
def think : Word := ⟨"think", Cat.V, {}⟩
def know : Word := ⟨"know", Cat.V, {}⟩

-- Complementizers
def that : Word := ⟨"that", Cat.C, {}⟩
def if_ : Word := ⟨"if", Cat.C, {}⟩

end Lexicon
