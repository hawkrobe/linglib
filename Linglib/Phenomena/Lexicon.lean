/-
# Phenomena Lexicon

Word definitions for use in Phenomena data files.
These are simple Word values (surface form + category + features)
for constructing example sentences.

Note: For compositional semantics, see Theories/Montague/Lexicon/.
For full lexical entries with argument structure, see Fragments/.
-/

import Linglib.Core.Basic

namespace Lexicon

open Cat

-- ============================================================================
-- Determiners
-- ============================================================================

def a : Word := ⟨"a", D, { number := some .sg }⟩
def an : Word := ⟨"an", D, { number := some .sg }⟩
def the : Word := ⟨"the", D, {}⟩
def this : Word := ⟨"this", D, { number := some .sg }⟩
def that : Word := ⟨"that", D, { number := some .sg }⟩
def these : Word := ⟨"these", D, { number := some .pl }⟩
def some_ : Word := ⟨"some", D, {}⟩
def every : Word := ⟨"every", D, { number := some .sg }⟩
def many : Word := ⟨"many", D, { number := some .pl }⟩
def few : Word := ⟨"few", D, { number := some .pl }⟩

-- ============================================================================
-- Proper Names
-- ============================================================================

def john : Word := ⟨"John", D, { number := some .sg, person := some .third }⟩
def mary : Word := ⟨"Mary", D, { number := some .sg, person := some .third }⟩

-- ============================================================================
-- Common Nouns (Singular)
-- ============================================================================

def boy : Word := ⟨"boy", N, { number := some .sg, countable := some true }⟩
def girl : Word := ⟨"girl", N, { number := some .sg, countable := some true }⟩
def man : Word := ⟨"man", N, { number := some .sg, countable := some true }⟩
def dog : Word := ⟨"dog", N, { number := some .sg, countable := some true }⟩
def cat_ : Word := ⟨"cat", N, { number := some .sg, countable := some true }⟩
def book : Word := ⟨"book", N, { number := some .sg, countable := some true }⟩
def ball : Word := ⟨"ball", N, { number := some .sg, countable := some true }⟩
def table : Word := ⟨"table", N, { number := some .sg, countable := some true }⟩
def pizza : Word := ⟨"pizza", N, { number := some .sg }⟩

-- ============================================================================
-- Common Nouns (Plural)
-- ============================================================================

def boys : Word := ⟨"boys", N, { number := some .pl, countable := some true }⟩
def girls : Word := ⟨"girls", N, { number := some .pl, countable := some true }⟩
def dogs : Word := ⟨"dogs", N, { number := some .pl, countable := some true }⟩
def cats : Word := ⟨"cats", N, { number := some .pl, countable := some true }⟩
def books : Word := ⟨"books", N, { number := some .pl, countable := some true }⟩
def balls : Word := ⟨"balls", N, { number := some .pl, countable := some true }⟩

-- ============================================================================
-- Personal Pronouns (Subject)
-- ============================================================================

def i : Word := ⟨"I", D, { person := some .first, number := some .sg, case_ := some .nom }⟩
def you : Word := ⟨"you", D, { person := some .second, case_ := some .nom }⟩
def he : Word := ⟨"he", D, { person := some .third, number := some .sg, case_ := some .nom }⟩
def she : Word := ⟨"she", D, { person := some .third, number := some .sg, case_ := some .nom }⟩
def we : Word := ⟨"we", D, { person := some .first, number := some .pl, case_ := some .nom }⟩
def they : Word := ⟨"they", D, { person := some .third, number := some .pl, case_ := some .nom }⟩

-- ============================================================================
-- Personal Pronouns (Object)
-- ============================================================================

def me : Word := ⟨"me", D, { person := some .first, number := some .sg, case_ := some .acc }⟩
def him : Word := ⟨"him", D, { person := some .third, number := some .sg, case_ := some .acc }⟩
def her : Word := ⟨"her", D, { person := some .third, number := some .sg, case_ := some .acc }⟩
def us : Word := ⟨"us", D, { person := some .first, number := some .pl, case_ := some .acc }⟩
def them : Word := ⟨"them", D, { person := some .third, number := some .pl, case_ := some .acc }⟩

-- ============================================================================
-- Reflexive Pronouns
-- ============================================================================

def himself : Word := ⟨"himself", D, { person := some .third, number := some .sg }⟩
def herself : Word := ⟨"herself", D, { person := some .third, number := some .sg }⟩
def themselves : Word := ⟨"themselves", D, { person := some .third, number := some .pl }⟩

-- ============================================================================
-- Wh-Words
-- ============================================================================

def who : Word := ⟨"who", Wh, { wh := true }⟩
def what : Word := ⟨"what", Wh, { wh := true }⟩

-- ============================================================================
-- Intransitive Verbs
-- ============================================================================

def sleep : Word := ⟨"sleep", V, { valence := some .intransitive, number := some .pl }⟩
def sleeps : Word := ⟨"sleeps", V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
def laugh : Word := ⟨"laugh", V, { valence := some .intransitive, number := some .pl }⟩
def laughs : Word := ⟨"laughs", V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
def arrives : Word := ⟨"arrives", V, { valence := some .intransitive, number := some .sg, person := some .third }⟩
def leave : Word := ⟨"leave", V, { valence := some .intransitive, number := some .pl }⟩

-- ============================================================================
-- Transitive Verbs
-- ============================================================================

def see : Word := ⟨"see", V, { valence := some .transitive, number := some .pl }⟩
def sees : Word := ⟨"sees", V, { valence := some .transitive, number := some .sg, person := some .third }⟩
def saw : Word := ⟨"saw", V, { valence := some .transitive, vform := some .finite }⟩
def eat : Word := ⟨"eat", V, { valence := some .transitive, number := some .pl }⟩
def eats : Word := ⟨"eats", V, { valence := some .transitive, number := some .sg, person := some .third }⟩
def eaten : Word := ⟨"eaten", V, { valence := some .transitive, vform := some .pastParticiple, voice := some .passive }⟩
def reads : Word := ⟨"reads", V, { valence := some .transitive, number := some .sg, person := some .third }⟩
def buy : Word := ⟨"buy", V, { valence := some .transitive, number := some .pl }⟩
def bought : Word := ⟨"bought", V, { valence := some .transitive, vform := some .finite }⟩
def sell : Word := ⟨"sell", V, { valence := some .transitive, number := some .pl }⟩
def met : Word := ⟨"met", V, { valence := some .transitive, vform := some .finite }⟩
def kicks : Word := ⟨"kicks", V, { valence := some .transitive, number := some .sg, person := some .third }⟩
def kicked : Word := ⟨"kicked", V, { valence := some .transitive, vform := some .pastParticiple, voice := some .passive }⟩
def chased : Word := ⟨"chased", V, { valence := some .transitive, vform := some .pastParticiple, voice := some .passive }⟩
def devours : Word := ⟨"devours", V, { valence := some .transitive, number := some .sg, person := some .third }⟩

-- ============================================================================
-- Ditransitive Verbs
-- ============================================================================

def gives : Word := ⟨"gives", V, { valence := some .ditransitive, number := some .sg, person := some .third }⟩
def gives_dat : Word := ⟨"gives", V, { valence := some .dative, number := some .sg, person := some .third }⟩
def sends : Word := ⟨"sends", V, { valence := some .ditransitive, number := some .sg, person := some .third }⟩
def puts : Word := ⟨"puts", V, { valence := some .locative, number := some .sg, person := some .third }⟩

-- ============================================================================
-- Propositional Attitude Verbs
-- ============================================================================

def think : Word := ⟨"think", V, { valence := some .transitive, number := some .pl }⟩
def wonder : Word := ⟨"wonder", V, { valence := some .transitive, number := some .pl }⟩

-- ============================================================================
-- Auxiliaries
-- ============================================================================

def do_ : Word := ⟨"do", Aux, { number := some .pl }⟩
def does : Word := ⟨"does", Aux, { number := some .sg, person := some .third }⟩
def did : Word := ⟨"did", Aux, {}⟩
def can : Word := ⟨"can", Aux, {}⟩
def was : Word := ⟨"was", Aux, { number := some .sg }⟩

-- ============================================================================
-- Prepositions
-- ============================================================================

def to : Word := ⟨"to", P, {}⟩
def on : Word := ⟨"on", P, {}⟩
def by_ : Word := ⟨"by", P, {}⟩
def before : Word := ⟨"before", P, {}⟩

-- ============================================================================
-- Complementizers
-- ============================================================================

def that_c : Word := ⟨"that", C, {}⟩
def if_ : Word := ⟨"if", C, {}⟩
def because : Word := ⟨"because", C, {}⟩

-- ============================================================================
-- Conjunctions
-- ============================================================================

def and_ : Word := ⟨"and", C, {}⟩
def or_ : Word := ⟨"or", C, {}⟩

-- ============================================================================
-- Adjectives
-- ============================================================================

def happy : Word := ⟨"happy", Adj, {}⟩
def smart : Word := ⟨"smart", Adj, {}⟩
def old : Word := ⟨"old", Adj, {}⟩
def wise : Word := ⟨"wise", Adj, {}⟩

end Lexicon
