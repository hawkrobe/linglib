import Mathlib.Tactic.DeriveFintype

/-!
# Universal Dependencies: part-of-speech tags
[de-marneffe-zeman-2021]

The seventeen universal part-of-speech tags of UD v2, the word-class vocabulary of the
library's tokens (`Morphology.Word.cat`), with the open, closed, nominal, predicate and
modifier classes they fall into.

Official site: <https://universaldependencies.org/>
-/

namespace UD


/-- Universal part-of-speech tags (UPOS).

    17 coarse-grained categories designed for cross-linguistic consistency.
    Every word in every language can be assigned one of these tags. -/
inductive UPOS where
  -- Open class words (content words)
  | ADJ    -- adjective: big, old, green, first
  | ADV    -- adverb: very, tomorrow, down, where, there
  | INTJ   -- interjection: psst, ouch, bravo, hello
  | NOUN   -- noun: girl, cat, tree, air, beauty
  | PROPN  -- proper noun: Mary, John, London, NATO
  | VERB   -- verb: run, runs, running, eat, ate

  -- Closed class words (function words)
  | ADP    -- adposition: in, to, during (preposition/postposition)
  | AUX    -- auxiliary: has, is, should, was, will
  | CCONJ  -- coordinating conjunction: and, or, but
  | DET    -- determiner: a, an, the, this, which
  | NUM    -- numeral: 1, 2, one, two, first
  | PART   -- particle: 's, not, to (infinitive marker)
  | PRON   -- pronoun: I, you, he, she, myself, who
  | SCONJ  -- subordinating conjunction: if, while, that

  -- Other
  | PUNCT  -- punctuation: . , ; : ! ?
  | SYM    -- symbol: $, %, @, +, :), 😀
  | X      -- other: foreign words, typos, abbreviations
  deriving DecidableEq, Repr, Inhabited, Hashable

/-- String representation matching UD conventions -/
def UPOS.toString : UPOS → String
  | .ADJ   => "ADJ"
  | .ADV   => "ADV"
  | .INTJ  => "INTJ"
  | .NOUN  => "NOUN"
  | .PROPN => "PROPN"
  | .VERB  => "VERB"
  | .ADP   => "ADP"
  | .AUX   => "AUX"
  | .CCONJ => "CCONJ"
  | .DET   => "DET"
  | .NUM   => "NUM"
  | .PART  => "PART"
  | .PRON  => "PRON"
  | .SCONJ => "SCONJ"
  | .PUNCT => "PUNCT"
  | .SYM   => "SYM"
  | .X     => "X"

instance : ToString UPOS := ⟨UPOS.toString⟩

/-- Is this an open class (content) word? -/
def UPOS.isOpenClass : UPOS → Bool
  | .ADJ | .ADV | .INTJ | .NOUN | .PROPN | .VERB => true
  | _ => false

/-- Is this a closed class (function) word? -/
def UPOS.isClosedClass : UPOS → Bool
  | .ADP | .AUX | .CCONJ | .DET | .NUM | .PART | .PRON | .SCONJ => true
  | _ => false

/-- Is this a nominal (entity-denoting) category? -/
def UPOS.isNominal : UPOS → Bool
  | .NOUN | .PROPN | .PRON | .NUM => true
  | _ => false

/-- Is this a predicate (event-denoting) category? -/
def UPOS.isPredicate : UPOS → Bool
  | .VERB | .AUX => true
  | _ => false

/-- Is this a modifier category? -/
def UPOS.isModifier : UPOS → Bool
  | .ADJ | .ADV => true
  | _ => false


end UD
