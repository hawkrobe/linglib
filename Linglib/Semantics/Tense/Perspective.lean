import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Tense.Reichenbach
import Linglib.Semantics.Reference.Context.Basic
import Linglib.Semantics.Tense.Basic

/-!
# Perspectival Tense Theory
[tsilia-zhao-2026] [sharvit-2003] [zhao-2025]
[anand-nevins-2004] [deal-2020]

Reusable infrastructure for perspectival tense interpretation:
tense presuppositions anchored to a perspective parameter π,
the OP_π shift operator, and the `InterpParams` architecture
enforcing independence of context and perspective.

## Core Formal System

The interpretation function ⟦·⟧^{c,π,g} takes three parameters:
- **c**: context parameter ⟨c_s, c_a, c_t, c_w⟩ — for indexical interpretation
- **π**: temporal perspective — for tense interpretation
- **g**: variable assignment

Two shift operators with the same shape ("overwrite parameter with evaluation
index") but operating on *independent* parameters:
- **OP_c**: overwrites c with the evaluation index (indexical shift,
  [anand-nevins-2004])
- **OP_π**: overwrites π with the time component of the evaluation index
  (tense shift)

## Tense Presuppositions

Tenses are presupposition triggers anchored to π:
- PRES: g(n) ○ π (reference overlaps perspective)
- PAST: g(n) < π (reference precedes perspective)
- ⌈then⌉: ¬(g(n) ○ π) (reference disjoint from perspective)

-/

open Time

namespace Tense.Perspective

open Semantics.Presupposition
open Semantics.Context (KContext)
open Tense


/-! ### Tense Presuppositions -/

/-- PRES presupposes g(n) ○ π: the temporal reference overlaps the perspective.
    Point approximation: R = P. -/
def presPresup {Time : Type*} (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime = f.perspectiveTime

/-- PAST presupposes g(n) < π: the temporal reference precedes the perspective. -/
def pastPresup {Time : Type*} [LT Time] (f : ReichenbachFrame Time) : Prop :=
  f.referenceTime < f.perspectiveTime

/-- The PRES presupposition is definitionally equal to `isPresent`. -/
theorem presPresup_iff_isPresent {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time) :
    presPresup f ↔ f.isPresent := Iff.rfl

/-- The PAST presupposition is definitionally equal to `isPast`. -/
theorem pastPresup_iff_isPast {Time : Type*} [LinearOrder Time]
    (f : ReichenbachFrame Time) :
    pastPresup f ↔ f.isPast := (ReichenbachFrame.isPast_def f).symm


/-! ### OP_π: Perspective-Shifting Operator -/

/-- OP_π shifts the perspective time to a new value.
    ⟦OP_π φ⟧^{c,π,g} = λi_κ. ⟦φ⟧^{c,i_t,g}(i) -/
def opPi {Time : Type*} (f : ReichenbachFrame Time) (newPi : Time) :
    ReichenbachFrame Time :=
  { f with perspectiveTime := newPi }

/-- OP_π corresponds to `embeddedFrame` when shifting to the matrix event time. -/
theorem opPi_eq_embeddedFrame {Time : Type*}
    (matrixFrame : ReichenbachFrame Time) (embeddedR embeddedE : Time) :
    opPi { speechTime := matrixFrame.speechTime
           perspectiveTime := matrixFrame.speechTime
           referenceTime := embeddedR
           eventTime := embeddedE }
         matrixFrame.eventTime =
    embeddedFrame matrixFrame embeddedR embeddedE := by
  simp only [opPi, embeddedFrame]


/-! ### ⌈then⌉ Presupposition -/

/-- ⌈then⌉ presupposes ¬(g(n) ○ π): its temporal reference is disjoint
    from the perspective. Point approximation: thenRef ≠ π.

    This is ⌈then⌉'s OWN presupposition, separate from the presuppositions
    of any co-clausal tense. The incompatibility with PRES arises because
    composition (via "during then") forces the PRES reference to be contained
    in the then reference, bridging the two presuppositions. -/
def thenPresup {Time : Type*} (thenRef perspective : Time) : Prop :=
  thenRef ≠ perspective


/-! ### Core Clash Theorems -/

/-- The ⌈then⌉-present clash. Three ingredients produce the contradiction:
    1. PRES presupposes presRef = π (overlap with perspective)
    2. The temporal assertion requires presRef = thenRef ("during then")
    3. ⌈then⌉ presupposes thenRef ≠ π (disjoint from perspective)

    Together: π = presRef = thenRef, but thenRef ≠ π. -/
theorem then_present_clash {Time : Type*}
    (presRef thenRef perspective : Time)
    (hPres : presRef = perspective)
    (hDuring : presRef = thenRef)
    (hThen : thenPresup thenRef perspective)
    : False :=
  hThen (hDuring ▸ hPres)

/-- General OP_π + ⌈then⌉ clash at the frame level:
    OP_π sets P = localEval; anything requiring P ≠ localEval contradicts. -/
theorem then_perspective_clash {Time : Type*}
    (f : ReichenbachFrame Time) (localEval : Time)
    (hOP : f.perspectiveTime = localEval)
    (hThen : f.perspectiveTime ≠ localEval)
    : False := hThen hOP


/-! ### Deleted vs. Shifted Tense -/

/-- Status of an embedded tense morpheme. -/
inductive EmbeddedTenseStatus where
  /-- Tense interpreted with presupposition anchored to shifted π -/
  | shifted
  /-- Tense deleted by SOT; imposes no temporal presupposition at all
      (there is no definedness condition to state, which is why
      `then_deleted_tense_compatible` below needs no presupposition
      hypothesis). -/
  | deleted
  deriving DecidableEq, Repr

/-- A shifted tense retains its presupposition (PRES or PAST relative to π). -/
def shiftedTensePresup {Time : Type*} [LT Time]
    (f : ReichenbachFrame Time) (isPres : Bool) : Prop :=
  if isPres then presPresup f else pastPresup f

/-- ⌈then⌉ + deleted tense → compatible.
    Deleted tense has no presupposition anchoring it to π, so there is no
    overlap requirement. ⌈then⌉ can freely pick a reference disjoint from π. -/
theorem then_deleted_tense_compatible {Time : Type*}
    (thenRef perspective : Time)
    (hDisjoint : thenRef ≠ perspective) :
    thenPresup thenRef perspective := hDisjoint

/-- ⌈then⌉ + shifted tense → clash (when shifted tense is PRES).
    The shifted PRES anchors to π via OP_π, so presRef overlaps with the
    shifted π. If "during then" forces presRef = thenRef, then's
    disjointness presupposition ¬(thenRef ○ π) fails. -/
theorem then_shifted_present_clash {Time : Type*}
    (presRef thenRef shiftedPi : Time)
    (hPres : presRef = shiftedPi)
    (hDuring : presRef = thenRef)
    (hThen : thenPresup thenRef shiftedPi) :
    False :=
  then_present_clash presRef thenRef shiftedPi hPres hDuring hThen


/-! ### Bridge to PartialProp -/

/-- Wrap PRES presupposition as a `PartialProp`, showing how tense presuppositions
    compose with the existing presupposition projection system. -/
def presAsPartialProp {Time : Type*} [DecidableEq Time]
    (f : ReichenbachFrame Time) : PartialProp Unit where
  presup := λ () => decide (f.referenceTime = f.perspectiveTime)
  assertion := λ () => true

/-- The `PartialProp` encoding is defined iff the PRES presupposition holds. -/
theorem presAsPartialProp_defined_iff {Time : Type*} [DecidableEq Time]
    (f : ReichenbachFrame Time) :
    (presAsPartialProp f).presup () = true ↔ f.referenceTime = f.perspectiveTime := by
  simp [presAsPartialProp]


/-! ### Interpretation Parameters: c and π -/

/-- The interpretation parameter tuple ⟨c, π⟩ from ⟦·⟧^{c,π,g}.

    Context c (for indexical interpretation, [anand-nevins-2004]) and
    perspective π (for tense interpretation) are independent parameters.
    This structure makes their independence explicit and architectural:
    `shiftPerspective` preserves `context`, and `shiftContext` preserves
    `perspective`.

    The variable assignment g is orthogonal and handled separately
    (in `Montague/Variables.lean`). -/
structure InterpParams (W E P T : Type*) where
  /-- Context parameter c = ⟨c_s, c_a, c_t, c_w⟩ — for indexicals (I, now, here) -/
  context : KContext W E P T
  /-- Temporal perspective π — for tense (PRES, PAST, ⌈then⌉).
      Defaults to c_t in root clauses; shifted by OP_π under attitude verbs. -/
  perspective : T

/-- OP_π on the interpretation parameter tuple: shift π, preserve c.
    ⟦OP_π φ⟧^{c,π,g} = λi_κ. ⟦φ⟧^{c,i_t,g}(i) -/
def InterpParams.shiftPerspective {W E P T : Type*}
    (ip : InterpParams W E P T) (newPi : T) : InterpParams W E P T :=
  { ip with perspective := newPi }

/-- OP_c on the interpretation parameter tuple: shift c, preserve π.
    ⟦OP_c φ⟧^{c,π,g} = λi_κ. ⟦φ⟧^{i,π,g}(i) -/
def InterpParams.shiftContext {W E P T : Type*}
    (ip : InterpParams W E P T) (newC : KContext W E P T) :
    InterpParams W E P T :=
  { ip with context := newC }

/-- OP_π preserves the context parameter (including c_t).
    This is the formal content of §7.1: tense shift does not entail
    indexical shift. Modern Greek allows OP_π (shifted present) but blocks
    the temporal indexical τώρα 'now' from shifting. -/
@[simp] theorem InterpParams.shiftPerspective_preserves_context
    {W E P T : Type*}
    (ip : InterpParams W E P T) (newPi : T) :
    (ip.shiftPerspective newPi).context = ip.context := rfl

/-- OP_c preserves the temporal perspective.
    Indexical shift does not entail tense shift. -/
@[simp] theorem InterpParams.shiftContext_preserves_perspective
    {W E P T : Type*}
    (ip : InterpParams W E P T) (newC : KContext W E P T) :
    (ip.shiftContext newC).perspective = ip.perspective := rfl

/-- In root clauses, π defaults to c_t (the temporal component of the
    context). This is the Truth Convention: ⟦φ⟧ is true relative to c and
    assignment g iff ⟦φ⟧^{c,c_t,g}(c) = 1. -/
def InterpParams.rootDefault {W E P T : Type*}
    (c : KContext W E P T) : InterpParams W E P T where
  context := c
  perspective := c.time

/-- Root default satisfies the co-valuation π = c_t. -/
theorem InterpParams.rootDefault_covalued {W E P T : Type*}
    (c : KContext W E P T) :
    (InterpParams.rootDefault c).perspective =
    (InterpParams.rootDefault c).context.time := rfl

/-- After OP_π, c_t is unchanged — π and c_t can diverge. -/
theorem InterpParams.perspective_context_diverge {W E P T : Type*}
    (ip : InterpParams W E P T) (newPi : T)
    (hDistinct : newPi ≠ ip.context.time) :
    (ip.shiftPerspective newPi).perspective ≠
    (ip.shiftPerspective newPi).context.time := by
  simp only [InterpParams.shiftPerspective]
  exact hDistinct

/-- OP_π on `InterpParams` corresponds to `opPi` on `ReichenbachFrame`. -/
theorem InterpParams.shiftPerspective_matches_opPi {W E P T : Type*}
    (ip : InterpParams W E P T) (f : ReichenbachFrame T) (newPi : T)
    (_hSync : f.perspectiveTime = ip.perspective) :
    (opPi f newPi).perspectiveTime = (ip.shiftPerspective newPi).perspective := by
  simp only [opPi, InterpParams.shiftPerspective]


end Tense.Perspective
