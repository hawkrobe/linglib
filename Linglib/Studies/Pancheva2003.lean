module

public import Linglib.Data.Examples.Schema
public import Linglib.Semantics.Aspect.Viewpoint
public import Linglib.Data.Examples.Pancheva2003

/-!
# Pancheva (2003): Aspectual Makeup of Perfect Participles and the Interpretations of the Perfect

Pancheva derives the universal, experiential and resultative readings of the perfect from the
aspectual makeup of the participle rather than from an ambiguous perfect. The perfect is one
interval-level operator over a participial phrase whose inner viewpoint is the non-strict
imperfective, the neutral viewpoint requiring only initial overlap, or the bounded perfective,
and the three readings are the three compositions. Since only a telic event has a lexically
inherent result state, *I have run* lacks the resultative reading that *I have lost my glasses*
has, and Greek, whose perfect participles are obligatorily perfective, lacks the universal
perfect.

## Main definitions

* `PERF_P`: the interval-level perfect.
* `INIT_OVERLAP`: the neutral inner viewpoint.
* `BOUNDED`: the bounded inner viewpoint.
* `universalPerfect`: the perfect over the non-strict imperfective.
* `experientialPerfect`: the perfect over the neutral viewpoint.
* `resultativePerfect`: the perfect over the bounded viewpoint.

## Implementation notes

The framework is the perfect time span of Iatridou, Anagnostopoulou and Izvorski, and
the non-strict imperfective is `Aspect.UNBOUNDED`; the result state of the
paper's resultative composition is not represented, the resultative reading being the
perfect over the bounded viewpoint alone.

## References

* [pancheva-2003]
* [iatridou-anagnostopoulou-izvorski-2001]
-/

@[expose] public section

namespace Pancheva2003

open Event (τ)

open Aspect

/-! ### The aspectual makeup of the participle, (7) and (9) -/

variable {T E : Type*} [LinearOrder T] [Event.TemporalTrace E T] {W : Type*}

/-- The neutral inner viewpoint, (7b) on p. 282, holds when the reference interval overlaps the
beginning of the event, which may extend beyond it. -/
def INIT_OVERLAP (P : W → E → Prop) : IntervalPred W T :=
  λ w t => ∃ e : E, t.initialOverlap (τ e) ∧ P w e

/-- The bounded inner viewpoint of (7b) holds when the run time of the event is properly contained
in the reference interval. -/
def BOUNDED (P : W → E → Prop) : IntervalPred W T :=
  λ w t => ∃ e : E, τ e < t ∧ P w e

/-- The interval-level PERFECT, (9b) on p. 284, holds when some perfect time span of which the
reference interval is a final subinterval satisfies the predicate. -/
def PERF_P (p : IntervalPred W T) : IntervalPred W T :=
  λ w i => ∃ pts : NonemptyInterval T, i.finalSubinterval pts ∧ p w pts

/-- The point-based `Aspect.PERF` is `PERF_P` at a degenerate reference interval. -/
theorem perf_p_pure_iff_perf (p : IntervalPred W T) (w : W) (t : T) :
    PERF_P p w (NonemptyInterval.pure t) ↔ PERF p ⟨w, t⟩ := by
  constructor
  · intro ⟨pts, hFin, hp⟩
    exact ⟨pts, hFin.2.symm, hp⟩
  · intro ⟨pts, hRB, hp⟩
    exact ⟨pts, ⟨⟨le_trans pts.fst_le_snd (le_of_eq hRB), le_of_eq hRB.symm⟩, hRB.symm⟩, hp⟩

/-- A `PerfectType` is one of the three readings of the perfect, (1). -/
inductive PerfectType
  | universal
  | experiential
  | resultative
  deriving DecidableEq, Repr

/-- The universal perfect, (11), is PERFECT over UNBOUNDED. -/
abbrev universalPerfect (P : W → E → Prop) : IntervalPred W T := PERF_P (UNBOUNDED P)

/-- The experiential perfect, (12), is PERFECT over NEUTRAL. -/
abbrev experientialPerfect (P : W → E → Prop) : IntervalPred W T :=
  PERF_P (INIT_OVERLAP P)

/-- The resultative perfect, (15), is PERFECT over BOUNDED, without the result state of p. 288. -/
abbrev resultativePerfect (P : W → E → Prop) : IntervalPred W T := PERF_P (BOUNDED P)

end Pancheva2003
