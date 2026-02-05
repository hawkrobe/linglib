/-!
# Basic

Core types shared across all theoretical frameworks.
-/

/-- Syntactic categories (coarse-grained, refined per framework). -/
inductive Cat where
  | D      -- Determiner / DP
  | N      -- Noun
  | V      -- Verb (lexical)
  | Aux    -- Auxiliary verb
  | C      -- Complementizer
  | Wh     -- Wh-phrase
  | P      -- Preposition
  | Adj    -- Adjective
  deriving Repr, DecidableEq, Inhabited

/-- Grammatical number. -/
inductive Number where
  | sg  -- singular
  | pl  -- plural
  deriving Repr, DecidableEq, Inhabited

/-- Grammatical person. -/
inductive Person where
  | first
  | second
  | third
  deriving Repr, DecidableEq, Inhabited

/-- Grammatical case. -/
inductive Case where
  | nom  -- nominative (subject): I, he, she, we, they
  | acc  -- accusative (object): me, him, her, us, them
  | gen  -- genitive (possessive): my, his, her, our, their
  deriving Repr, DecidableEq, Inhabited

/-- Transitivity / argument structure. -/
inductive Valence where
  | intransitive  -- sleep, arrive
  | transitive    -- see, eat
  | ditransitive  -- give, send (double object)
  | dative        -- give X to Y (prepositional dative)
  | locative      -- put X on Y
  | copular       -- be (takes predicate)
  deriving Repr, DecidableEq, Inhabited

/-- Voice: active vs passive. -/
inductive Voice where
  | active
  | passive
  deriving Repr, DecidableEq, Inhabited

/-- Verb form. -/
inductive VForm where
  | finite
  | infinitive
  | pastParticiple  -- eaten, given (for passive & perfect)
  | presParticiple  -- eating, giving (for progressive)
  deriving Repr, DecidableEq, Inhabited

/-- Clause types - determines constraints on word order. -/
inductive ClauseType where
  | declarative
  | matrixQuestion      -- requires inversion in English
  | embeddedQuestion    -- no inversion in English
  | echo                -- no inversion even in matrix position
  deriving Repr, DecidableEq

/-- Feature bundle for words. -/
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

/-- A word: form + category + features. -/
structure Word where
  form : String
  cat : Cat
  features : Features := {}
  deriving Repr

instance : BEq Word where
  beq w1 w2 := w1.form == w2.form && w1.cat == w2.cat

instance : ToString Word where
  toString w := w.form

/-- Convert a word list to a readable string. -/
def wordsToString (ws : List Word) : String :=
  " ".intercalate (ws.map (·.form))

/-- A Grammar assigns derivations to strings. Derivations are proof objects. -/
class Grammar (G : Type) where
  /-- The type of derivations/analyses this grammar produces -/
  Derivation : Type
  /-- Whether a derivation yields a given string with given clause type -/
  realizes : Derivation → List Word → ClauseType → Prop
  /-- Whether the grammar can produce *some* derivation for a string -/
  derives : G → List Word → ClauseType → Prop

/-- If two grammars both derive the same string, they agree on that string. -/
theorem derives_agreement
    {G₁ G₂ : Type} [Grammar G₁] [Grammar G₂]
    (g₁ : G₁) (g₂ : G₂) (ws : List Word) (ct : ClauseType)
    (h₁ : Grammar.derives g₁ ws ct)
    (h₂ : Grammar.derives g₂ ws ct) :
    Grammar.derives g₁ ws ct ∧ Grammar.derives g₂ ws ct :=
  ⟨h₁, h₂⟩

