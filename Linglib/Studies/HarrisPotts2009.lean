import Linglib.Pragmatics.Expressives.Basic

/-!
# Harris & Potts 2009: Orientation variables for CI items
[harris-potts-2009]

Harris, J. A. & Potts, C. (2009). Perspective-shifting with appositives
and expressives. *Linguistics and Philosophy* 32(6), 523–552.

## Defining commitment

Each occurrence of a conventional-implicature item (expressive, slur,
NRRC) carries a covert free **orientation variable** whose value is
flexibly resolved in discourse. Speaker-oriented readings arise when
the orientation resolves to the speaker; non-speaker-oriented readings
arise when it resolves to some other discourse participant.

This is the alternative analysis K-G argues against in §8.2 (paper
p.40-41). H&P's view: non-speaker-oriented readings of (26)-(28) come
from orientation-variable resolution, NOT from quotation. K-G's view:
they come from covert mixed quotation, with the peripheral attribution
introduced by 𝔐 substituting for the discarded original CI.

## K-G's objections (paper p.40-41)

1. H&P offer no explanation for the strong default preference for
   speaker-oriented readings of CI items (their proposal would predict
   roughly equal frequencies if context permits both).

2. H&P's account collapses certain theories of speaker-oriented uses of
   slurs (e.g., K-G 2019's directive analysis): the orientation-variable
   machinery cannot accommodate non-propositional CI content.

The two analyses make different empirical predictions on when
non-speaker-oriented readings are available — this stub encodes H&P's
key commitment so K-G's `KirkGiannini2024.lean` can host the
inequality theorems.

## Note on scope

Stub formalisation. Sufficient to host inequality theorems against
K-G's strip-then-mix architecture. Does not formalize the full appositive
syntax/semantics or the experimental data H&P present.
-/

set_option autoImplicit false

namespace HarrisPotts2009

open Pragmatics.Expressives (TwoDimProp)

/-- Discourse participants who can be the orientation of a CI item.
    H&P's apparatus is open-ended; for the stub we use a small enum. -/
inductive Orientation (Person : Type) where
  | speaker
  | other (p : Person)
  deriving DecidableEq, Repr

/-- **H&P's CI item.** The orientation is a free variable resolved in
    discourse. The CI content is *parameterized* on the orientation —
    different resolutions produce different speaker-attributions of the
    expressive/slur attitude. -/
structure CIItem (Person W : Type) where
  /-- The CI content as a function of who's oriented. -/
  ciFor : Orientation Person → W → Prop
  /-- The at-issue content (independent of orientation). -/
  atIssue : W → Prop

/-- Resolve the orientation variable to a particular value, producing
    a flat `TwoDimProp`. -/
def CIItem.resolve {Person W : Type} (item : CIItem Person W)
    (o : Orientation Person) : TwoDimProp W :=
  { atIssue := item.atIssue, ci := item.ciFor o }

/-- **H&P's central claim: non-speaker-oriented readings via free
    orientation variable, no quotation invoked.**

    For any CI item with orientation-dependent content, there exist
    discourse situations where the orientation resolves to a non-speaker
    individual `p`, producing a non-speaker-oriented reading. The
    mechanism is purely contextual resolution; nothing about the
    syntactic structure or pure quotation is invoked. -/
theorem non_speaker_oriented_via_orientation_var
    {Person W : Type} (item : CIItem Person W) (p : Person) :
    item.resolve (.other p) = { atIssue := item.atIssue
                              , ci := item.ciFor (.other p) } := rfl

/-- **The orientation variable can in principle resolve to any
    discourse participant.** This is the property K-G complains is
    too permissive: H&P predict that any contextually salient individual
    can serve as orientation, but the data show speaker-orientation is
    the strong default. -/
theorem any_orientation_available
    {Person W : Type} (item : CIItem Person W) :
    ∀ o : Orientation Person, ∃ p : TwoDimProp W, p = item.resolve o :=
  λ o => ⟨item.resolve o, rfl⟩

end HarrisPotts2009
