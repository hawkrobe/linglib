import Linglib.Theories.Semantics.Attitudes.Desire
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic

/-!
# @cite{heim-1992} — Comparative-Belief Desire Semantics

⟦α wants φ⟧^w is true iff for every doxastic alternative `w' ∈ Dox_α(w)`,
every closest `φ`-world to `w'` is more desirable to α than every closest
`¬φ`-world to `w'`. The semantics builds on @cite{lewis-1973} /
@cite{stalnaker-1968} similarity orderings, departs from a Kratzer
@cite{kratzer-1981}-style ordering source, and treats desirability as a
primitive comparative relation parameterized by agent and evaluation
world.

This study file replicates the desire-semantics half of @cite{heim-1992}
(the presupposition-projection half is at
`Phenomena/Presupposition/Studies/Heim1992.lean`). Substrate is
`Theories/Semantics/Attitudes/Desire.lean` (`wantHeim`,
`wantHeimDefined`, `HeimDesireParams`, `wantHeim_no_simultaneous_pq_and_negpq`).

## §-by-§ map

| Paper | Study file |
|-------|-----------|
| §3 naive Hintikka (informally rejected) | §2 (`wantHeimNaive` + Asher-style failure case) |
| (32) Asher Concorde example, p. 194 | §2 (analog scenario; see §2 caveat) |
| §4.2.2 (37/39) CCP-rephrased | §3 / substrate `wantHeim` |
| §4.2.3 (40) amendment | substrate `wantHeimDefined` |
| §4.3 conflicting desires (implicit) | §4 (substrate no-go) |
| Stalnaker get-well/¬have-been-sick (p. 195) | §5 (deferred — needs richer model) |

## Cross-references

* `Phenomena/Presupposition/Studies/Heim1992.lean` formalizes the
  know/believe asymmetry — the *other* half of Heim 1992 (and the more
  durably cited half).
* The substrate's `BeliefBasedDesireSemantics` typology (in `Desire.lean`)
  packages vF and Heim under one parametric no-go; later study files
  (PhillipsBrown2025, etc.) instantiate or refute it. Per project
  chronological-dependency rules, comparisons with later papers live in
  those later study files, not here.
-/

namespace Phenomena.Modality.Studies.Heim1992

open Semantics.Attitudes.Desire

/-! ## §1. World model

A simple 4-world model with two binary dimensions:

| World | recovered (`r`) | sick (`s`) |
|-------|-----------------|------------|
| w0    | T               | T          |
| w1    | T               | F          |
| w2    | F               | T          |
| w3    | F               | F          |

Models the Stalnaker @cite{stalnaker-1984}-style example "I want to
get well [recovered] but I don't want to have been sick" — the agent
prefers `r ∧ ¬s` worlds (recovered without ever being sick) but believes
they were sick (so all believed worlds have `s`). The (40) amendment
makes `wantHeim ¬s` undefined under those beliefs. -/

inductive W where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, Repr, Inhabited

instance : Fintype W where
  elems := {.w0, .w1, .w2, .w3}
  complete := λ w => by cases w <;> decide

def recovered : Set W | .w0 | .w1 => True | _ => False
def sick : Set W | .w0 | .w2 => True | _ => False

instance : DecidablePred recovered :=
  fun w => by cases w <;> unfold recovered <;> infer_instance
instance : DecidablePred sick :=
  fun w => by cases w <;> unfold sick <;> infer_instance

/-! ## §2. Naive Hintikka rule fails on Asher-style cases

The "naive Hintikka" rule for `wants` (`α wants φ` iff every doxastic
alternative is a φ-world) is rejected informally by Heim (it is *not*
her numbered (27); (27) is the CCP rule). Heim cites
@cite{asher-1987}'s example at (32), p. 194 ("Nicholas wants a free
trip on the Concorde"): the agent wants φ but does not believe φ, so
the naive rule wrongly predicts the ascription false.

The analog below is structurally weaker than Asher's Concorde case
(no inferential gradient between propositions; no probability
weighting). It exhibits only the basic shape — *want φ under beliefs
that don't entail φ* — sufficient to falsify the naive rule. A faithful
Concorde-style witness (free-trip ⊨ trip + agent assigns high prob to
"trip ∧ pay") requires a richer model and is part of the deferred
Phase 2. -/

/-- Beliefs: agent believes they are sick. `belS = {w0, w2}`.
    Neither belief-world entails `recovered`. -/
def belSick : Set W := sick
instance : DecidablePred belSick := inferInstanceAs (DecidablePred sick)

/-- The naive Hintikka rule predicts `wants recovered` false here
    (because `w2 ∈ belSick` and `¬ recovered w2`). Empirically the
    ascription can be true, so the naive rule is inadequate — this
    motivates the move to a comparative semantics. -/
theorem naive_predicts_false_for_wants_recover :
    ¬ wantHeimNaive belSick recovered := by
  intro h
  have : recovered .w2 := h .w2 (by decide : belSick .w2)
  exact this

/-! ## §3. Truth-conditional comparative-belief (31)

Heim's canonical formulation: ⟦α wants φ⟧ at w iff for every doxastic
alternative `w'`, every closest φ-world to `w'` is more desirable than
every closest ¬φ-world to `w'`. -/

/-- Trivial similarity ordering: every world is equally close to every
    other world. The closer relation is the constant True predicate. -/
def trivialSim : Core.Order.SimilarityOrdering W := by
  refine Core.Order.SimilarityOrdering.ofBool (fun _ _ _ => true) ?_ ?_
  · intros; rfl
  · intros; rfl

/-- Desirability: prefer recovered worlds to non-recovered worlds. The
    evaluation-world argument is suppressed (constant preference). -/
def prefRecovered : W → W → W → Prop :=
  fun _w_eval x y => recovered x ∧ ¬ recovered y

instance : ∀ w x y, Decidable (prefRecovered w x y) :=
  fun _ x y => by unfold prefRecovered; infer_instance

def heimParams : HeimDesireParams W where
  sim := trivialSim
  pref := prefRecovered
  prefDec := inferInstance

instance : DecidablePred (Set.univ : Set W) := fun _ => isTrue trivial

/-- The (40) amendment: `wantHeim recovered` is defined under
    `Set.univ` (both recovered and ¬recovered worlds are believed
    possible). -/
theorem wantHeim_recovered_defined :
    wantHeimDefined (Set.univ : Set W) recovered := by
  refine ⟨⟨.w0, ?_, ?_⟩, ⟨.w2, ?_, ?_⟩⟩ <;> decide

/-! ## §4. Heim (40) does not validate simultaneous `want p ∧ want ¬p`

A side-effect of (40) — flagged by Heim herself in §4.3 (cf. (41)/(42),
where she worries that (40) is in fact *too* restrictive and proposes
shrinking Dox to a "favored" subset F_α) — is that under preference
asymmetry, no `(belS, w_eval)` configuration validates both
`wantHeim p` and `wantHeim ¬p`. The substrate theorem
`wantHeim_no_simultaneous_pq_and_negpq` discharges this generically.

Whether this side-effect is a virtue (Heim's account *correctly*
rejects co-wanting p and ¬p) or a defect (Heim's account *cannot
represent* genuine ambivalence) is the locus of subsequent debate;
Heim's own §4.3 already concedes "a genuine modification is called
for." Comparative discussion of later proposals (vF 1999,
Phillips-Brown 2025, etc.) belongs in those later study files under
the chronological-dependency rule. -/

/-- `prefRecovered` is asymmetric: if x is preferred to y, then y is
    not preferred to x — and the implication "both directions ⇒
    equality" requires that no two distinct worlds are both recovered
    and not-recovered, which is vacuously true. -/
theorem prefRecovered_asymm (w_eval : W) :
    ∀ x y, prefRecovered w_eval x y → prefRecovered w_eval y x → x = y := by
  intro x y ⟨hx, hny⟩ ⟨hy, _⟩
  exact absurd hy hny

/-- Witness on this concrete model: under `Set.univ`, no
    `wantHeim recovered ∧ wantHeim ¬recovered` configuration is
    consistent. Delegates to the substrate's general theorem. -/
theorem heim_no_simultaneous_recovered :
    ¬ (wantHeim (Set.univ : Set W) heimParams .w0 recovered ∧
       wantHeim (Set.univ : Set W) heimParams .w0 (fun w => ¬ recovered w)) :=
  wantHeim_no_simultaneous_pq_and_negpq (Set.univ : Set W) heimParams .w0
    recovered (prefRecovered_asymm .w0) wantHeim_recovered_defined

/-! ## §5. Stalnaker get-well / ¬have-been-sick — deferred

Heim's central worked example (p. 195) is Stalnaker's "I want to get
well, but I don't want to have been sick": both `want recover` and
`¬want have-been-sick` come out true even though `recover ⊨ have-been-sick`.
Handling it requires the comparative-similarity machinery to do real
work — Heim's `Sim_w` selects a single closest sick-recover-world, and
desirability is compared *between selections*, not over the full
belief set.

The minimal witness model (per PDF p. 195) has three worlds with
desirability `w₁ (healthy throughout) > w₂ (sick then recovered) > w₃
(sick and stays sick)` and `Dox(w₀) = {w₂, w₃}`. The trivial
similarity ordering used in §3 collapses this case onto a static rule;
a faithful instantiation needs `Sim` non-trivial. Phase 2 will land
this scenario along with `prefRecovered`'s evaluation-world parameter
genuinely exercised. -/

end Phenomena.Modality.Studies.Heim1992
