/-
# Linglib.Core.Basic

Core types shared across all theoretical frameworks.
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
  | Adj    -- Adjective
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- Grammatical Features
-- ============================================================================

/-- Grammatical number -/
inductive Number where
  | sg  -- singular
  | pl  -- plural
  deriving Repr, DecidableEq, Inhabited

/-- Grammatical person -/
inductive Person where
  | first
  | second
  | third
  deriving Repr, DecidableEq, Inhabited

/-- Grammatical case -/
inductive Case where
  | nom  -- nominative (subject): I, he, she, we, they
  | acc  -- accusative (object): me, him, her, us, them
  | gen  -- genitive (possessive): my, his, her, our, their
  deriving Repr, DecidableEq, Inhabited

/-- Transitivity / argument structure -/
inductive Valence where
  | intransitive  -- sleep, arrive
  | transitive    -- see, eat
  | ditransitive  -- give, send (double object)
  | dative        -- give X to Y (prepositional dative)
  | locative      -- put X on Y
  | copular       -- be (takes predicate)
  deriving Repr, DecidableEq, Inhabited

/-- Voice: active vs passive -/
inductive Voice where
  | active
  | passive
  deriving Repr, DecidableEq, Inhabited

/-- Verb form -/
inductive VForm where
  | finite
  | infinitive
  | pastParticiple  -- eaten, given (for passive & perfect)
  | presParticiple  -- eating, giving (for progressive)
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

/-- Feature bundle for words -/
structure Features where
  wh : Bool := false
  finite : Bool := true
  number : Option Number := none
  person : Option Person := none
  case_ : Option Case := none
  valence : Option Valence := none
  voice : Option Voice := none
  vform : Option VForm := none
  countable : Option Bool := none  -- for count vs mass nouns
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

-- ============================================================================
-- Wh-words
-- ============================================================================

def what : Word := ⟨"what", Cat.Wh, { wh := true }⟩
def who : Word := ⟨"who", Cat.Wh, { wh := true }⟩
def where_ : Word := ⟨"where", Cat.Wh, { wh := true }⟩

-- ============================================================================
-- Auxiliaries (with agreement)
-- ============================================================================

-- Modal auxiliaries (no number distinction)
def can : Word := ⟨"can", Cat.Aux, { finite := true }⟩
def will : Word := ⟨"will", Cat.Aux, { finite := true }⟩

-- do-support
def does : Word := ⟨"does", Cat.Aux, { finite := true, number := some .sg, person := some .third }⟩
def do_ : Word := ⟨"do", Cat.Aux, { finite := true, number := some .pl }⟩
def did : Word := ⟨"did", Cat.Aux, { finite := true }⟩  -- past, no agreement

-- be (auxiliary)
def is : Word := ⟨"is", Cat.Aux, { finite := true, number := some .sg, person := some .third }⟩
def are : Word := ⟨"are", Cat.Aux, { finite := true, number := some .pl }⟩
def am : Word := ⟨"am", Cat.Aux, { finite := true, number := some .sg, person := some .first }⟩

-- have (auxiliary)
def has : Word := ⟨"has", Cat.Aux, { finite := true, number := some .sg, person := some .third }⟩
def have_ : Word := ⟨"have", Cat.Aux, { finite := true, number := some .pl }⟩

-- be (past tense, for passive)
def was : Word := ⟨"was", Cat.Aux, { finite := true, number := some .sg, person := some .third }⟩
def were : Word := ⟨"were", Cat.Aux, { finite := true, number := some .pl }⟩

-- ============================================================================
-- Pronouns (with case and agreement)
-- ============================================================================

-- First person
def i : Word := ⟨"I", Cat.D, { number := some .sg, person := some .first, case_ := some .nom }⟩
def me : Word := ⟨"me", Cat.D, { number := some .sg, person := some .first, case_ := some .acc }⟩
def we : Word := ⟨"we", Cat.D, { number := some .pl, person := some .first, case_ := some .nom }⟩
def us : Word := ⟨"us", Cat.D, { number := some .pl, person := some .first, case_ := some .acc }⟩

-- Second person
def you : Word := ⟨"you", Cat.D, { number := some .sg, person := some .second }⟩  -- no case distinction
def you_pl : Word := ⟨"you", Cat.D, { number := some .pl, person := some .second }⟩

-- Third person singular
def he : Word := ⟨"he", Cat.D, { number := some .sg, person := some .third, case_ := some .nom }⟩
def him : Word := ⟨"him", Cat.D, { number := some .sg, person := some .third, case_ := some .acc }⟩
def she : Word := ⟨"she", Cat.D, { number := some .sg, person := some .third, case_ := some .nom }⟩
def her : Word := ⟨"her", Cat.D, { number := some .sg, person := some .third, case_ := some .acc }⟩
def it : Word := ⟨"it", Cat.D, { number := some .sg, person := some .third }⟩  -- no case distinction

-- Third person plural
def they : Word := ⟨"they", Cat.D, { number := some .pl, person := some .third, case_ := some .nom }⟩
def them : Word := ⟨"them", Cat.D, { number := some .pl, person := some .third, case_ := some .acc }⟩

-- ============================================================================
-- Proper names (3rd person singular, no case)
-- ============================================================================

def john : Word := ⟨"John", Cat.D, { number := some .sg, person := some .third }⟩
def mary : Word := ⟨"Mary", Cat.D, { number := some .sg, person := some .third }⟩

-- ============================================================================
-- Common nouns
-- ============================================================================

def pizza : Word := ⟨"pizza", Cat.N, { number := some .sg, countable := some true }⟩
def book : Word := ⟨"book", Cat.N, { number := some .sg, countable := some true }⟩
def books : Word := ⟨"books", Cat.N, { number := some .pl, countable := some true }⟩
def cat_ : Word := ⟨"cat", Cat.N, { number := some .sg, countable := some true }⟩
def cats : Word := ⟨"cats", Cat.N, { number := some .pl, countable := some true }⟩
def dog : Word := ⟨"dog", Cat.N, { number := some .sg, countable := some true }⟩
def dogs : Word := ⟨"dogs", Cat.N, { number := some .pl, countable := some true }⟩
def girl : Word := ⟨"girl", Cat.N, { number := some .sg, countable := some true }⟩
def girls : Word := ⟨"girls", Cat.N, { number := some .pl, countable := some true }⟩
def boy : Word := ⟨"boy", Cat.N, { number := some .sg, countable := some true }⟩
def boys : Word := ⟨"boys", Cat.N, { number := some .pl, countable := some true }⟩
def ball : Word := ⟨"ball", Cat.N, { number := some .sg, countable := some true }⟩
def balls : Word := ⟨"balls", Cat.N, { number := some .pl, countable := some true }⟩
def table : Word := ⟨"table", Cat.N, { number := some .sg, countable := some true }⟩
def squirrel : Word := ⟨"squirrel", Cat.N, { number := some .sg, countable := some true }⟩

-- Mass nouns (no plural, different determiner behavior)
def water : Word := ⟨"water", Cat.N, { countable := some false }⟩
def sand : Word := ⟨"sand", Cat.N, { countable := some false }⟩

-- ============================================================================
-- Determiners (with number agreement)
-- ============================================================================

-- Number-neutral
def the : Word := ⟨"the", Cat.D, {}⟩
def some_ : Word := ⟨"some", Cat.D, {}⟩

-- Singular only
def a : Word := ⟨"a", Cat.D, { number := some .sg }⟩
def this : Word := ⟨"this", Cat.D, { number := some .sg }⟩
def every : Word := ⟨"every", Cat.D, { number := some .sg }⟩

-- Plural only
def these : Word := ⟨"these", Cat.D, { number := some .pl }⟩
def many : Word := ⟨"many", Cat.D, { number := some .pl }⟩
def few : Word := ⟨"few", Cat.D, { number := some .pl }⟩

-- ============================================================================
-- Prepositions
-- ============================================================================

def to : Word := ⟨"to", Cat.P, {}⟩
def on : Word := ⟨"on", Cat.P, {}⟩
def in_ : Word := ⟨"in", Cat.P, {}⟩
def by_ : Word := ⟨"by", Cat.P, {}⟩  -- for passive agent
def with_ : Word := ⟨"with", Cat.P, {}⟩
def at_ : Word := ⟨"at", Cat.P, {}⟩

-- ============================================================================
-- Verbs (with agreement and valence)
-- ============================================================================

-- Transitive verbs (active, finite)
def see : Word := ⟨"see", Cat.V, { valence := some .transitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def sees : Word := ⟨"sees", Cat.V, { valence := some .transitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def eat : Word := ⟨"eat", Cat.V, { valence := some .transitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def eats : Word := ⟨"eats", Cat.V, { valence := some .transitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def read : Word := ⟨"read", Cat.V, { valence := some .transitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def reads : Word := ⟨"reads", Cat.V, { valence := some .transitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def devour : Word := ⟨"devour", Cat.V, { valence := some .transitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def devours : Word := ⟨"devours", Cat.V, { valence := some .transitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def kick : Word := ⟨"kick", Cat.V, { valence := some .transitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def kicks : Word := ⟨"kicks", Cat.V, { valence := some .transitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def chase : Word := ⟨"chase", Cat.V, { valence := some .transitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def chases : Word := ⟨"chases", Cat.V, { valence := some .transitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩

-- Transitive verbs (passive participle)
def eaten : Word := ⟨"eaten", Cat.V, { valence := some .transitive, voice := some .passive, vform := some .pastParticiple }⟩
def seen : Word := ⟨"seen", Cat.V, { valence := some .transitive, voice := some .passive, vform := some .pastParticiple }⟩
def kicked : Word := ⟨"kicked", Cat.V, { valence := some .transitive, voice := some .passive, vform := some .pastParticiple }⟩
def chased : Word := ⟨"chased", Cat.V, { valence := some .transitive, voice := some .passive, vform := some .pastParticiple }⟩
def devoured : Word := ⟨"devoured", Cat.V, { valence := some .transitive, voice := some .passive, vform := some .pastParticiple }⟩

-- Intransitive verbs
def sleep : Word := ⟨"sleep", Cat.V, { valence := some .intransitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def sleeps : Word := ⟨"sleeps", Cat.V, { valence := some .intransitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def arrive : Word := ⟨"arrive", Cat.V, { valence := some .intransitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def arrives : Word := ⟨"arrives", Cat.V, { valence := some .intransitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def laugh : Word := ⟨"laugh", Cat.V, { valence := some .intransitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def laughs : Word := ⟨"laughs", Cat.V, { valence := some .intransitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩

-- Ditransitive verbs (double object: give X Y)
def give : Word := ⟨"give", Cat.V, { valence := some .ditransitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def gives : Word := ⟨"gives", Cat.V, { valence := some .ditransitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def send : Word := ⟨"send", Cat.V, { valence := some .ditransitive, number := some .pl, voice := some .active, vform := some .finite }⟩
def sends : Word := ⟨"sends", Cat.V, { valence := some .ditransitive, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩

-- Ditransitive passive participles
def given : Word := ⟨"given", Cat.V, { valence := some .ditransitive, voice := some .passive, vform := some .pastParticiple }⟩
def sent : Word := ⟨"sent", Cat.V, { valence := some .ditransitive, voice := some .passive, vform := some .pastParticiple }⟩

-- Dative verbs (give X to Y) - same verbs, different frame
def give_dat : Word := ⟨"give", Cat.V, { valence := some .dative, number := some .pl, voice := some .active, vform := some .finite }⟩
def gives_dat : Word := ⟨"gives", Cat.V, { valence := some .dative, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩

-- Locative verbs (put X on/in Y)
def put : Word := ⟨"put", Cat.V, { valence := some .locative, number := some .pl, voice := some .active, vform := some .finite }⟩
def puts : Word := ⟨"puts", Cat.V, { valence := some .locative, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩
def place : Word := ⟨"place", Cat.V, { valence := some .locative, number := some .pl, voice := some .active, vform := some .finite }⟩
def places : Word := ⟨"places", Cat.V, { valence := some .locative, number := some .sg, person := some .third, voice := some .active, vform := some .finite }⟩

-- Clause-embedding verbs
def wonder : Word := ⟨"wonder", Cat.V, { valence := some .transitive }⟩
def think : Word := ⟨"think", Cat.V, { valence := some .transitive }⟩
def know : Word := ⟨"know", Cat.V, { valence := some .transitive }⟩

-- ============================================================================
-- Adjectives
-- ============================================================================

def happy : Word := ⟨"happy", Cat.Adj, {}⟩
def tall : Word := ⟨"tall", Cat.Adj, {}⟩
def smart : Word := ⟨"smart", Cat.Adj, {}⟩

-- ============================================================================
-- Complementizers
-- ============================================================================

def that : Word := ⟨"that", Cat.C, {}⟩
def if_ : Word := ⟨"if", Cat.C, {}⟩

end Lexicon
