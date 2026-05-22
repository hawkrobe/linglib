import Linglib.Theories.Semantics.Composition.Layered
import Linglib.Theories.Semantics.Highlighting
import Linglib.Phenomena.Verum.Basic

/-!
# Höhle (1992): *Verum-Fokus im Deutschen*
@cite{hohle-1992} @cite{romero-han-2004} @cite{rooth-1992}
@cite{repp-2013} @cite{gutzmann-hartmann-matthewson-2020}
@cite{martinez-vera-2026}

Höhle's seminal proposal: pitch accent on the finite verb (or negation
particle) in German is *verum focus* — focus on the assertion operator,
emphasising the polarity/truth of the prejacent rather than its content.

The classic minimal pair (Höhle 1992: 116):

* "Karl HAT das Buch gelesen." — VF on auxiliary, emphatic affirmation
* "Karl hat das BUCH gelesen." — content focus on object

The two share truth-conditional content but differ in what they
contribute to the discourse: VF requires a salient ¬p (or salient
suspension of p) and serves to settle that prior issue.

## What this study formalises

* A minimal `verumFocusOp` on `BiLayered W` that highlights the
  prejacent's polarity in the context's salient set (the Höhle move:
  focus on the assertion operator).
* A felicity condition aligning with the cross-linguistic
  generalisation: VF is licensed exactly when the prejacent's negation
  is highlighted in the prior context.

## Relation to other studies

This file used to live at `Studies/Hohle1992.lean`
as a 158-LOC file of bare `def` data records (sentences and tags) with
no actual analysis of Höhle's verum-focus operator. Re-homed here as
part of the Verum directory landing, replacing the data-only content
with the formal operator and its felicity profile. The German prosodic
data (auxiliary stress, negation stress) is illustrative of the
substrate, not stipulated as primitive — see `Phenomena/Verum/Basic`
for the cross-linguistic verum-marker inventory.

Adjacent studies the substrate is shared with:

* `Phenomena/Verum/Studies/MartinezVera2026.lean` — the same
  highlighting + ⟨A, N⟩ machinery applied to Saraguro Kichwa `=mi`.
  Höhle's German VF and Martínez Vera's `=mi` exemplify the same
  paper-(60) prediction about the focus-account of verum.
* `Phenomena/Questions/Studies/RomeroHan2004.lean` — VERUM as a CG
  operator (rather than as focus on the assertion operator).
  R&H's `forSureCG` is the alternative-line analysis that Höhle's
  focus-account contrasts with (paper §6's FAT vs. LOT debate).
-/

namespace Phenomena.Verum.Studies.Hohle1992

open Semantics.Composition.Layered (BiLayered)
open Semantics.Highlighting (HighlightingContext Highlighted addSalient)

variable {W : Type*}

/-- Höhle's verum-focus operator. Applied to a prejacent `β`, it returns
    the same at-issue content (`β.atIssue`) — VF is truth-conditionally
    transparent — and adds a not-at-issue conjunct that the prejacent's
    polarity is the highlighted one. The not-at-issue contribution is
    Höhle's reading of pitch accent on the finite verb / negation as
    targeting the assertion operator rather than the propositional
    content. -/
def verumFocusOp (β : BiLayered W) : BiLayered W :=
  { atIssue := β.atIssue
  , notAtIssue := fun w => β.notAtIssue w ∧ β.atIssue w }

/-- VF preserves the at-issue layer (truth-conditional transparency). -/
@[simp] theorem verumFocusOp_atIssue (β : BiLayered W) :
    (verumFocusOp β).atIssue = β.atIssue := rfl

@[simp] theorem verumFocusOp_notAtIssue (β : BiLayered W) :
    (verumFocusOp β).notAtIssue = fun w => β.notAtIssue w ∧ β.atIssue w := rfl

/-- Höhle's licensing condition: a verum-focus utterance is felicitous in
    context `c` iff the prejacent's *negation* is highlighted in `c`.

    This is the cross-linguistic verum signature: the marker requires
    that ¬p be salient (asserted earlier, contextually inferable, or
    raised by a biased question). Without this, VF is infelicitous
    out-of-the-blue (Höhle 1992; @cite{romero-han-2004};
    @cite{gutzmann-hartmann-matthewson-2020}). -/
def verumFelicitous (c : HighlightingContext W) (β : BiLayered W) : Prop :=
  Highlighted c {w | ¬ β.atIssue w}

/-- VF is felicitous after a context that has highlighted ¬p. The witness:
    `addSalient c {w | ¬ β.atIssue w}` makes ¬p salient; if the QUD is
    set up to be addressed by ¬p (as it is in the standard biased-question
    or asserted-¬p discourse), then `Highlighted` holds. -/
theorem verumFelicitous_after_highlighting_neg
    (c : HighlightingContext W) (β : BiLayered W)
    (h : Semantics.Highlighting.AddressesQUD c.qud {w | ¬ β.atIssue w}) :
    verumFelicitous (addSalient c {w | ¬ β.atIssue w}) β := by
  refine ⟨?_, h⟩
  simp [addSalient]

/-- Höhle's verum-focus operator packaged as a `VerumOperator`, so that
    cross-paper bridge / refutation theorems can be stated against other
    inhabitants of the same shared structure. -/
def hohleAsVerumOperator : Phenomena.Verum.Basic.VerumOperator W :=
  { felicitous := fun c β => verumFelicitous c β }

@[simp] theorem hohleAsVerumOperator_apply (c : HighlightingContext W)
    (β : BiLayered W) :
    hohleAsVerumOperator.felicitous c β = verumFelicitous c β := rfl

end Phenomena.Verum.Studies.Hohle1992
