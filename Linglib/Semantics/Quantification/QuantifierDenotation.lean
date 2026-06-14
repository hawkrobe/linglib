import Linglib.Syntax.Determiner.Basic
import Linglib.Semantics.Quantification.Defs

/-!
# The denotation of a quantificational determiner
[barwise-cooper-1981] [keenan-stavi-1986] [partee-1989]

Gives the `Quantifier` lexical record (`Syntax/Determiner/Basic.lean`) a meaning,
as a generalized quantifier `GQ α`. This is the *quantifier* half of the
determiner-denotation API whose *definite* half is
`Semantics/Definiteness/DeterminerDenotation.lean` (where `Quantifier` was
explicitly deferred: a quantifier denotes a `GQ`, not a `NominalDenot`). The
wiring is parallel to `Article.denotations` and `PersonalPronoun.denote`: a
lexical record, interpreted to its semantic object.

The marking `Quantifier` is *universal*; *which* form denotes *which* `GQ` is
*per-language* data, supplied as a `Lexicon` valuation — the `FreeGroup.lift`
shape (universal syntax, supplied valuation). `denote` returns a `List (GQ α)`,
mirroring `Article.denotations : … → List NominalDenot`: a determiner form may be
unambiguous (singleton), ambiguous (the cardinal-vs-proportional split of
*few*/*many*, [partee-1989]), or outside the lexicon (`[]`).

The abstract counterpart is `Quantification.Det.toGQ` (the Lindström-class
realization functor); the two meet at the canonical denotations
(`everyDet.toGQ α = every_sem`, the GQ a lexicon assigns to *every*).

## Main declarations

* `Quantifier.Lexicon` — a per-language form ↦ denotation(s) valuation.
* `Quantifier.denote` — interpret a marked quantifier under a lexicon.
* `Quantifier.denote_conservative` — a conservative lexicon makes *every* marked
  quantifier denote conservatively; the B&C conservativity universal lifted once
  at the theory layer rather than re-proved per entry or per language.
-/

namespace Quantifier

open Quantification (GQ Conservative)

variable {α : Type*}

/-- A quantifier lexicon over domain `α`: the per-language assignment of
generalized-quantifier denotation(s) to each determiner *form*. The marking
record `Quantifier` is universal (`Syntax/Determiner`); this valuation is the
per-language data (the `FreeGroup.lift` shape — universal syntax, supplied
valuation). A `List` because a form may denote one GQ, several (lexical
ambiguity), or none (outside the lexicon). -/
abbrev Lexicon (α : Type*) : Type _ := String → List (GQ α)

/-- Interpret a marked quantifier under a lexicon `L`: the GQ denotation(s) `L`
assigns to its surface form. The theory-layer interpretation of a
quantificational determiner — the `GQ`-valued analogue of `Article.denotations`
(record-first, like the rest of the determiner-denotation API). -/
def denote (q : Quantifier) (L : Lexicon α) : List (GQ α) := L q.form

@[simp] theorem denote_eq (q : Quantifier) (L : Lexicon α) :
    q.denote L = L q.form := rfl

/-- **Conservativity universal, lifted.** A lexicon all of whose denotations are
conservative makes *every* marked quantifier denote conservatively — the
cross-linguistic B&C conservativity universal ([barwise-cooper-1981]) proved once
at the theory layer and instantiated per language, rather than re-proved per
lexicon entry. The same shape lifts any `GQ`-predicate from a lexicon's range to
all of its marked quantifiers. -/
theorem denote_conservative (L : Lexicon α)
    (hL : ∀ s, ∀ g ∈ L s, Conservative g) (q : Quantifier) :
    ∀ g ∈ q.denote L, Conservative g :=
  hL q.form

end Quantifier
