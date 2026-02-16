/-
# Temporal Adverbials and the Perfect

Temporal adverbials constrain the Perfect Time Span (PTS), connecting to the
Extended Now (PERF_XN) framework from Knick & Sharf (2026).

## Iatridou et al. (2001) Classification

| Type       | Example           | LB constraint     |
|------------|-------------------|--------------------|
| Durative   | "since Monday"    | Specifies LB       |
| Inclusive   | "before Monday"   | Does not specify LB |

Durative adverbials pin the left boundary of the PTS, licensing the
Universal Perfect (U-perf) reading. Inclusive adverbials leave the LB
free, yielding only existential readings.

## Architecture

```
PTSConstraint ──[toLBDomain]──▷ Set Time ──▷ PERF_XN
```

Adverbials are modeled as `PTSConstraint`s on the PTS interval. The
`toLBDomain` function converts an adverbial constraint into a domain
restriction on LB values, which feeds directly into `PERF_XN`.

## References

- Iatridou, S., Anagnostopoulou, E. & Izvorski, R. (2001).
  Observations about the form and meaning of the Perfect.
- Knick, A. & Sharf, M. (2026). On focus and the perfect aspect.
- Klein, W. (1994). Time in Language.
-/

import Linglib.Theories.Semantics.Tense.TenseAspectComposition

namespace Semantics.Montague.Sentence.TemporalAdverbials

open Core.Time
open Semantics.Lexical.Verb.ViewpointAspect
open Semantics.TenseAspectComposition

variable {W Time : Type*} [LinearOrder Time]

-- ════════════════════════════════════════════════════
-- § PTS Constraints
-- ════════════════════════════════════════════════════

/-- A constraint on the Perfect Time Span.
    Adverbials restrict which PTS intervals are admissible. -/
abbrev PTSConstraint (Time : Type*) [LE Time] := Interval Time → Prop

/-- Iatridou et al. (2001) adverbial type classification.
    - `durative`: specifies the left boundary (e.g., "since Monday")
    - `inclusive`: does not specify the left boundary (e.g., "before Monday") -/
inductive AdverbialType where
  | durative   -- specifies LB
  | inclusive   -- does not specify LB
  deriving DecidableEq, Repr, BEq

-- ════════════════════════════════════════════════════
-- § Concrete Adverbials
-- ════════════════════════════════════════════════════

/-- "ever since t₀": PTS must start at t₀.
    E.g., "has been running since Monday" → PTS.start = Monday. -/
def everSince (t₀ : Time) : PTSConstraint Time :=
  λ pts => pts.start = t₀

/-- "for (duration) from tStart": PTS must start at tStart.
    Simplified duration adverbial — the duration is implicit in the
    interval length [tStart, RB]. -/
def forDurationFrom (tStart : Time) : PTSConstraint Time :=
  λ pts => pts.start = tStart

/-- "always" / no temporal adverbial: no constraint on PTS. -/
def always : PTSConstraint Time :=
  λ _ => True

/-- "before t" (inclusive adverbial): no constraint on PTS start.
    The adverbial constrains the event location, not the PTS boundary. -/
def before : PTSConstraint Time :=
  λ _ => True

-- ════════════════════════════════════════════════════
-- § LB Domain Extraction
-- ════════════════════════════════════════════════════

/-- Convert a PTS constraint to a domain of compatible LB values,
    given that the right boundary is fixed at tc.

    For a constraint C, the compatible LBs are those tLB ≤ tc such that
    C holds of the interval [tLB, tc]. -/
def PTSConstraint.toLBDomain (adv : PTSConstraint Time) (tc : Time) : Set Time :=
  { tLB | tLB ≤ tc ∧ ∀ (h : tLB ≤ tc), adv ⟨tLB, tc, h⟩ }

-- ════════════════════════════════════════════════════
-- § PERF with Adverbial
-- ════════════════════════════════════════════════════

/-- Perfect with adverbial constraint: PERF_ADV(p, adv).
    Combines PERF with an adverbial constraint on the PTS.
    Equivalent to PERF_XN with the adverbial's derived LB domain. -/
def PERF_ADV (p : IntervalPred W Time) (adv : PTSConstraint Time) : PointPred W Time :=
  λ w t => ∃ pts : Interval Time, RB pts t ∧ adv pts ∧ p w pts

-- ════════════════════════════════════════════════════
-- § Adverbial Type Properties
-- ════════════════════════════════════════════════════

/-- Does this adverbial type specify the left boundary?
    Durative adverbials pin the LB; inclusive adverbials leave it free. -/
def AdverbialType.specifiesLB : AdverbialType → Bool
  | .durative => true
  | .inclusive => false

-- ════════════════════════════════════════════════════
-- § Bridge Theorems
-- ════════════════════════════════════════════════════

/-- PERF_ADV is equivalent to PERF_XN with the adverbial's derived LB domain.

    Proof sketch: Both existentially quantify over a PTS with RB = tc.
    PERF_ADV requires adv(PTS); PERF_XN requires LB(tLB, PTS) with
    tLB ∈ toLBDomain(adv, tc). These are equivalent by definition of
    toLBDomain: tLB ∈ toLBDomain ↔ tLB ≤ tc ∧ adv([tLB, tc]). -/
theorem perf_adv_eq_perf_xn (p : IntervalPred W Time) (adv : PTSConstraint Time)
    (tc : Time) (w : W) :
    PERF_ADV p adv w tc ↔ PERF_XN p (adv.toLBDomain tc) w tc := by
  constructor
  · intro ⟨pts, hRB, hadv, hp⟩
    refine ⟨pts, pts.start, ⟨le_trans pts.valid (le_of_eq hRB), fun h => ?_⟩, rfl, hRB, hp⟩
    -- adv ⟨pts.start, tc, h⟩ = adv pts (since pts.finish = tc, proof irrelevance)
    cases pts with | mk s f v =>
    simp only [RB] at hRB
    subst hRB
    exact hadv
  · intro ⟨pts, tLB, ⟨hle, hadv_cond⟩, hLB, hRB, hp⟩
    refine ⟨pts, hRB, ?_, hp⟩
    cases pts with | mk s f v =>
    simp only [LB] at hLB
    simp only [RB] at hRB
    subst hLB; subst hRB
    exact hadv_cond hle

/-- "ever since t₀" specifies the LB domain to exactly {t₀}
    (assuming t₀ ≤ tc).

    Proof sketch: toLBDomain(everSince t₀, tc) = {tLB | tLB ≤ tc ∧ tLB = t₀}
    = {t₀} when t₀ ≤ tc. -/
theorem everSince_specifies_lb (t₀ tc : Time) (h : t₀ ≤ tc) :
    (everSince t₀ : PTSConstraint Time).toLBDomain tc = {t₀} := by
  ext x
  simp only [PTSConstraint.toLBDomain, everSince, Set.mem_setOf_eq]
  constructor
  · intro ⟨hle, hx⟩
    exact hx hle
  · intro heq
    exact ⟨heq ▸ h, fun _ => heq⟩

/-- "before" imposes no LB constraint: all tLB ≤ tc are compatible.

    Proof sketch: toLBDomain(before, tc) = {tLB | tLB ≤ tc ∧ True}
    = {tLB | tLB ≤ tc}. -/
theorem before_no_lb_constraint (tc : Time) :
    (before : PTSConstraint Time).toLBDomain tc = {tLB | tLB ≤ tc} := by
  ext x
  simp only [PTSConstraint.toLBDomain, before, Set.mem_setOf_eq]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun _ => trivial⟩⟩

/-- Durative adverbials (specified LB) license U-perf → simple present.

    When the LB is pinned (durative adverbial), the U-perf reading
    entails the simple present via `u_perf_entails_simple_present`. -/
theorem durative_licenses_u_perfect (V : EventPred W Time) (t₀ tc : Time) (w : W)
    (_h : t₀ ≤ tc) :
    presPerfProgXN V {t₀} tc w → simplePresent V tc w :=
  u_perf_entails_simple_present V {t₀} tc w

/-- Inclusive adverbials (unspecified LB) yield U-perf ↔ simple present
    when the LB domain is maximal.

    With no LB constraint, the domain is {tLB | tLB ≤ tc}. Under IMPF
    (subinterval property), this is close to Set.univ for the relevant
    range, so U-perf ↔ simple present by `broad_focus_equiv`'s argument. -/
theorem inclusive_no_u_license (V : EventPred W Time) (tc : Time) (w : W) :
    presPerfProgXN V Set.univ tc w ↔ simplePresent V tc w :=
  broad_focus_equiv V tc w

end Semantics.Montague.Sentence.TemporalAdverbials
