import Linglib.Theories.Semantics.Reference.Basic
import Linglib.Core.Semantics.CommonGround

/-!
# Metasemantics of demonstratives: abstract account
@cite{king-2013} @cite{king-2014a} @cite{king-2014b} @cite{lewis-2020}
@cite{stojnic-2024} @cite{stojnic-stone-lepore-2017}
@cite{rostworowski-kus-mackiewicz-2022} @cite{ney-2026}

A *metasemantics* of demonstrative-like expressions is a recipe that, given
a speaker's referential intention and the conversational common ground,
yields the conditions under which the intended referent succeeds as the
expression's semantic value in context.

Different accounts in the literature — @cite{king-2013}'s coordination,
@cite{lewis-2020}'s speaker-authority, @cite{stojnic-2024}'s discourse-
structured, @cite{ney-2026}'s joint-conception revision — instantiate the
same abstract shape with different machinery. This file defines the
abstract shape; specific accounts live in sibling files
(`Coordination.lean`, etc.).

## Key definitions

- `SpeakerIntention C W E`: a directly-referential expression used in
  context with an intended referent
- `Account C W E`: an `abbrev` for `SpeakerIntention C W E → CG W → Prop`

## Design notes

`Account` is an `abbrev`, not a structure. With one field and no laws,
the structure wrapper buys nothing while forcing every consumer through
a `.succeeds` projection. The abbrev makes `m s cg` direct and lets
function-Pi typeclass inference kick in for `≤` if needed (any consumer
who wants `Preorder` gets it for free; anyone who doesn't can ignore
it). Mirrors mathlib's preference for `α → Prop`-valued abbrevs over
single-field structures.

## Shape gap exposed by this file

`SpeakerIntention.expression : ReferringExpression C W E` is a
single-character expression and `TrueDemonstrative.demonstratum : C → Option E`
is functional — at most one referent per context. @cite{ney-2026}'s
phenomenon (insinuative reference) needs *multiple* simultaneously-
licensed referents per context, so it cannot be hosted by the existing
`Demonstratives.lean` types alone. `Metasemantics/InsinuativeReference.lean`
introduces an external `licenses : E → Prop` predicate to fill the gap;
the principled fix is to refactor `demonstratum` to a relation. See
that file's docstring for the full discussion.
-/

namespace Semantics.Reference.Metasemantics

open Semantics.Reference.Basic
open Core.CommonGround

universe u v w

/-- A speaker's *referential intention*: a directly-referential expression
used in a context to refer to a particular intended object.

Following @cite{king-2013}'s setup: a speaker `S` uses a demonstrative
expression `δ` in context `c` and intends some object `o` to be its
semantic value. The metasemantic question (formalized by `Account`)
is what conditions must hold for `o` to actually be `δ`'s semantic value. -/
structure SpeakerIntention (C : Type u) (W : Type v) (E : Type w) where
  /-- The speaker (typically the agent of the context). -/
  speaker      : E
  /-- The referring expression: demonstrative, supplementive, pronoun. -/
  expression   : ReferringExpression C W E
  /-- The Kaplanian context of utterance. -/
  context      : C
  /-- The object the speaker intends to be the semantic value. -/
  intendedRef  : E

/-- A *metasemantics of demonstratives*: a recipe that, given a speaker
intention and a common ground, yields whether the intended reference
succeeds as the expression's semantic value.

`m s cg` reads "account `m` validates intention `s` under common ground
`cg`". -/
abbrev Account (C : Type u) (W : Type v) (E : Type w) :=
  SpeakerIntention C W E → CG W → Prop

end Semantics.Reference.Metasemantics
