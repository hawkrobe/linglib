import Mathlib.Data.List.Basic

/-!
# Core concepts

A *core concept* is a conceptual primitive that is universally available
to every language's grammar, regardless of whether any lexical item in
that language realizes it.

The notion comes from @cite{chemla-2007}, who introduced it to explain
the anti-duality of French *tous* despite French lacking a lexical
counterpart of *both*. @cite{buccola-kriz-chemla-2018} generalize the
notion to "conceptual alternatives" feeding pragmatic competition, and
@cite{jeretic-bassi-gonzalez-yatsushiro-meyer-sauerland-2025} refine it:
core concepts feed competition only when an *indirect* alternative —
a pronounceable expression equivalent in meaning to the unpronounceable
core-concept structure — is available (Indirect Alternatives,
`Theories/Semantics/Alternatives/Indirect.lean`).

This module is a small registry. The actual *denotation* of each core
concept lives where its semantic content does (e.g. `dualPredOnLattice`
in `Features/Number.lean` for `dual`). Use `Lexicalizes` to express the
typological claim "language L lexicalizes core concept c", which is
the formal content of "L has a word for c".
-/

set_option autoImplicit false

namespace Core.CoreConcept

/-- The currently registered core concepts. New entries should
correspond to conceptual primitives independently motivated in the
literature, with a denotation defined elsewhere in linglib. -/
inductive Id where
  /-- Number-feature dual: predicate-modifier "and has exactly 2
  atomic parts"; denotation in `Features.Number.dualPredOnLattice`. -/
  | dual
  /-- Number-feature trial. Mentioned in @cite{harbour-2014} as
  morphologically stable but rare. Denotation TBD. -/
  | trial
  /-- Universal quantifier core concept. Lexicalized as `all`/`tous`
  cross-linguistically. -/
  | universal
  /-- Existential quantifier core concept. Lexicalized as `some`/
  `quelques`. -/
  | existential
  deriving DecidableEq, Repr

/-- A lexicon (any list of lexical tokens of type `Tok`) lexicalizes a
core concept iff some entry realizes it. The realization relation
`realizes` is supplied by the caller — typically a per-language
predicate that inspects the lexical entry's denotation.

Example: in `Phenomena/Presupposition/Studies/JereticEtAl2025.lean`,
English `realizes both Id.dual = True`, French `realizes _ Id.dual = False`. -/
def Lexicalizes {Tok : Type} (lex : List Tok)
    (realizes : Tok → Id → Prop) (c : Id) : Prop :=
  ∃ tok ∈ lex, realizes tok c

/-- The dual classifier: `Lexicalizes` for `Id.dual`. -/
abbrev LexicalizesDual {Tok : Type} (lex : List Tok)
    (realizes : Tok → Id → Prop) : Prop :=
  Lexicalizes lex realizes Id.dual

end Core.CoreConcept
