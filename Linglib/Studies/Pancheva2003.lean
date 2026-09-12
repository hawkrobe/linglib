import Linglib.Data.Examples.Schema
import Linglib.Semantics.Aspect.Basic
import Linglib.Data.Examples.Pancheva2003

/-!
# Pancheva (2003): Aspectual Makeup of Perfect Participles and the Interpretations of the Perfect

This file formalizes the account in [pancheva-2003] of the three interpretations of the
perfect, universal, experiential, and resultative, as arising from the aspectual makeup of
the participle rather than from an ambiguous perfect: the perfect is one interval-level
operator (`PERF_P`) over a participial phrase whose inner viewpoint is the non-strict
imperfective, the neutral viewpoint requiring only initial overlap, or the bounded
perfective (`INIT_OVERLAP`, `BOUNDED`), and the three readings are the three
compositions (`universalPerfect`, `experientialPerfect`, `resultativePerfect`). The
universal and resultative readings depend on the participial aspect and the experiential
does not: states and progressives yield the universal or experiential reading,
non-progressive activities the experiential only, and non-progressive telic predicates the
resultative or experiential, since only a telic event has a lexically inherent result state,
so *I have run* lacks the resultative reading that *I have lost my glasses* has. Greek
perfect participles are obligatorily perfective and Greek accordingly lacks the universal
perfect, while Bulgarian admits non-perfective participles and has it.

## Implementation notes

The framework is the perfect time span of [iatridou-anagnostopoulou-izvorski-2001], and
the non-strict imperfective is the substrate's `Aspect.UNBOUNDED`; the result state of the
paper's resultative composition is not represented, the resultative reading being the
perfect over the bounded viewpoint alone.

## References

* [pancheva-2003]
* [iatridou-anagnostopoulou-izvorski-2001]
-/

namespace Pancheva2003

open Aspect

/-! ### The aspectual makeup of the participle, (7) and (9) -/

variable {T : Type*} [LinearOrder T] {W : Type*}

/-- The neutral inner viewpoint of (7b), p. 282: the reference interval overlaps the beginning
of the event, which may extend beyond it. -/
def INIT_OVERLAP (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, t.initialOverlap e.τ ∧ P w e

/-- The bounded inner viewpoint of (7b): the run time of the event is properly contained in the
reference interval. -/
def BOUNDED (P : W → Event T → Prop) : IntervalPred W T :=
  λ w t => ∃ e : Event T, e.τ < t ∧ P w e

/-- The interval-level PERFECT of (9b), p. 284: some perfect time span of which the reference
interval is a final subinterval satisfies the predicate. -/
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

/-- The three readings of the perfect, (1). -/
inductive PerfectType
  | universal
  | experiential
  | resultative
  deriving DecidableEq, Repr

/-- The universal perfect, (11): PERFECT over UNBOUNDED. -/
abbrev universalPerfect (P : W → Event T → Prop) : IntervalPred W T := PERF_P (UNBOUNDED P)

/-- The experiential perfect, (12): PERFECT over NEUTRAL. -/
abbrev experientialPerfect (P : W → Event T → Prop) : IntervalPred W T :=
  PERF_P (INIT_OVERLAP P)

/-- The resultative perfect, (15): PERFECT over BOUNDED, without the result state of p. 288. -/
abbrev resultativePerfect (P : W → Event T → Prop) : IntervalPred W T := PERF_P (BOUNDED P)

end Pancheva2003
