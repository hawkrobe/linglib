import Linglib.Phonology.Constraints.Defs
import Linglib.Phonology.Constraints.Profile
import Linglib.Phonology.OptimalityTheory.Tableau
import Mathlib.Data.Finset.Union

/-!
# Harmonic Serialism
[mccarthy-2000] [mccarthy-2010] [pruitt-2023] [lamont-2022a] [lamont-2022b]

Harmonic Serialism: iterate a one-step `gen` and a durable constraint ranking to a
fixed point. `HSDerivation` bundles the two; the serial search itself is `iterateGen`,
a fuel-bounded iteration of an arbitrary step `C → Finset C` with a `pick` tie-breaker.
The general theory the search instantiates is mathlib's (`Function.IsFixedPt`,
`WellFounded` descent); the `Nat` fuel and `pick` are what make a
possibly-non-terminating, possibly-tied search total and computable. One-step EVAL
reuses the parallel `Tableau` machinery; directional EVAL ([lamont-2022b];
[eisner-2000]) needs nothing extra — a directional constraint like `*FLOAT^→` is a
position-indexed scalar block (`Tone.starFloatBlock`) spliced into the ranking under
the canonical lex order.

## Main definitions

* `iterateGen`: iterate a step for at most `n` rounds, stopping at convergence
  (`step c = {c}`), advancing by `pick`, `none` on a failed pick.
* `HSDerivation`: a one-step `gen` with a durable ranking; `stepOptimum` is one
  GEN/EVAL round, `Converged` the halting condition, `derive` the bundled search.

## Main results

* `iterateGen_eventually_constant`: under a well-founded harmony order that every
  genuine step descends, the search is eventually constant — derivations cannot loop
  while each step makes measurable progress, so the fuel bound is harmless.
* `isFixedPt_singleton_iff_converged`: `Converged` is `Function.IsFixedPt` of the
  powerset step at the singleton.
* `converged_of_singleton_gen`: GEN-restriction to the faithful candidate forces
  convergence.

## Theoretical scope

Per [pruitt-2023] (Table 1), HS does **not** solve counterfeeding underapplication and
only patches counterbleeding with extra GEN assumptions; this file makes no
"serial OT solves opacity" claim. [mcpherson-lamont-2026] is the motivating positive
case for the directional variant. Architecturally distinct alternatives in linglib:
`Phonology/Subregular/LocalRewrite.lean` (extrinsic rule ordering) and
`Phonology/OptimalityTheory/Stratal.lean` (cyclic ranking). HS and Stratal OT are
sister specializations of parallel OT, not nested: HS holds the ranking constant and
iterates the candidate; Stratal OT varies the ranking and chains the candidate
(Stratal HS, combining both axes, is deferred — cf. [pruitt-2023] §2.4).
-/

namespace OptimalityTheory

open Constraints Core.Optimization.Evaluation

/-! ### The serial search -/

section Iteration

variable {C : Type*} [DecidableEq C]

/-- Iterate `step` for at most `n` rounds, stopping early at HS convergence
(`step c = {c}`); otherwise advance by `pick`ing from the step's output (a canonical
sort + `head?`, or a directional tie-breaker), returning `none` if `pick` fails. The
`Nat` bound makes the search total — HS need not converge ([lamont-2022b]). -/
def iterateGen (step : C → Finset C) (pick : Finset C → Option C) : C → Nat → Option C
  | c, 0     => some c
  | c, n + 1 =>
    if step c = ({c} : Finset C) then some c
    else (pick (step c)).bind fun c' => iterateGen step pick c' n

variable {step : C → Finset C} {pick : Finset C → Option C} {c c' : C}

@[simp] theorem iterateGen_zero : iterateGen step pick c 0 = some c := rfl

theorem iterateGen_succ (n : Nat) :
    iterateGen step pick c (n + 1)
      = if step c = ({c} : Finset C) then some c
        else (pick (step c)).bind fun c' => iterateGen step pick c' n := rfl

/-- One round from a converged form returns it unchanged. -/
theorem iterateGen_succ_of_converged (h : step c = ({c} : Finset C)) (n : Nat) :
    iterateGen step pick c (n + 1) = some c := by
  rw [iterateGen_succ, if_pos h]

/-- One round from a non-converged form recurses with the picked successor. -/
theorem iterateGen_succ_of_step (hcv : step c ≠ ({c} : Finset C))
    (hpick : pick (step c) = some c') (n : Nat) :
    iterateGen step pick c (n + 1) = iterateGen step pick c' n := by
  rw [iterateGen_succ, if_neg hcv, hpick]; rfl

/-- One round from a non-converged form where `pick` fails yields `none`. -/
theorem iterateGen_succ_of_pickFail (hcv : step c ≠ ({c} : Finset C))
    (hpick : pick (step c) = none) (n : Nat) :
    iterateGen step pick c (n + 1) = none := by
  rw [iterateGen_succ, if_neg hcv, hpick]; rfl

/-- At a fixed point the search is constant: convergence is durable. -/
theorem iterateGen_const_of_converged (h : step c = ({c} : Finset C)) :
    ∀ n, iterateGen step pick c n = some c
  | 0     => rfl
  | n + 1 => iterateGen_succ_of_converged h n

/-- **HS terminates under a well-founded harmony order.** If every genuine step
descends a well-founded `lt` (`sound`), the search is eventually constant: some `N`
past which further fuel doesn't change the result. Derivations cannot loop while each
step makes measurable progress, so the explicit `Nat` bound is harmless. -/
theorem iterateGen_eventually_constant {lt : C → C → Prop} (wf : WellFounded lt)
    (sound : ∀ c c', step c ≠ ({c} : Finset C) → pick (step c) = some c' → c' ≠ c →
      lt c' c) (c : C) :
    ∃ N, ∀ m, N ≤ m → iterateGen step pick c m = iterateGen step pick c N := by
  induction c using wf.induction with
  | _ c IH =>
    by_cases hcv : step c = ({c} : Finset C)
    · exact ⟨0, fun m _ => by
        rw [iterateGen_const_of_converged hcv m, iterateGen_const_of_converged hcv 0]⟩
    · cases hp : pick (step c) with
      | none =>
        refine ⟨1, fun m hm => ?_⟩
        match m, hm with
        | n + 1, _ =>
          rw [iterateGen_succ_of_pickFail hcv hp, iterateGen_succ_of_pickFail hcv hp]
      | some c' =>
        by_cases hne : c' = c
        · have hp' : pick (step c) = some c := hne ▸ hp
          have h : ∀ m, iterateGen step pick c m = some c := by
            intro m
            induction m with
            | zero => rfl
            | succ _ ih => rw [iterateGen_succ_of_step hcv hp']; exact ih
          exact ⟨0, fun m _ => by rw [h m, h 0]⟩
        · obtain ⟨N', IH'⟩ := IH c' (sound c c' hcv hp hne)
          refine ⟨N' + 1, fun m hm => ?_⟩
          match m, hm with
          | n + 1, hn =>
            rw [iterateGen_succ_of_step hcv hp, iterateGen_succ_of_step hcv hp,
              IH' n (Nat.le_of_succ_le_succ hn)]

end Iteration

/-! ### HS derivations -/

/-- A Harmonic Serialism derivation: a one-step candidate-generation function (per
[mccarthy-2008b]'s restricted GEN) and a durable ranking. The inner `Tableau` width is
`ranking.length`. -/
structure HSDerivation (C : Type*) [DecidableEq C] where
  /-- The one-step candidate-generation function. -/
  gen : C → Finset C
  /-- The constraint ranking, durable across rounds (head = highest). -/
  ranking : List (Constraints.Constraint C)

namespace HSDerivation

variable {C : Type*} [DecidableEq C] (D : HSDerivation C) (c : C)

/-- The inner tableau on an explicit nonempty candidate set, scored by `D.ranking`. -/
def tableauFor (cands : Finset C) (h : cands.Nonempty) : Tableau C D.ranking.length where
  candidates := cands
  profile := buildViolationProfile D.ranking.get
  nonempty := h

@[simp] theorem tableauFor_profile (cands : Finset C) (h : cands.Nonempty) :
    (D.tableauFor cands h).profile = buildViolationProfile D.ranking.get := rfl

/-- Filter a candidate set to its optimal subset under `D.ranking`; `∅` on empty
input. This is the one-step EVAL of the serial search. -/
def evalFilter (cands : Finset C) : Finset C :=
  if h : cands.Nonempty then (D.tableauFor cands h).optimal else ∅

/-- The optimal set of one GEN/EVAL round. -/
def stepOptimum : Finset C := D.evalFilter (D.gen c)

/-- An empty `gen` output yields an empty optimal set. -/
@[simp] theorem stepOptimum_of_empty_gen (h : D.gen c = ∅) : D.stepOptimum c = ∅ := by
  simp [stepOptimum, evalFilter, h]

/-! ### Convergence -/

/-- A form has **converged** iff its one-round optimal set is the singleton of the
faithful candidate — the canonical HS halting condition ([mccarthy-2010]). -/
def Converged : Prop := D.stepOptimum c = ({c} : Finset C)

instance : Decidable (D.Converged c) := decEq (D.stepOptimum c) ({c} : Finset C)

/-- `Converged` is `Function.IsFixedPt` of the powerset step
`s ↦ ⋃ x ∈ s, stepOptimum x` at the singleton `{c}` — by `Finset.singleton_biUnion`,
with no intermediate combinator. Simp-normalized toward `Converged`. -/
@[simp] theorem isFixedPt_singleton_iff_converged :
    Function.IsFixedPt (fun s => s.biUnion D.stepOptimum) ({c} : Finset C)
      ↔ D.Converged c := by
  simp [Converged, Function.IsFixedPt, Finset.singleton_biUnion]

/-- GEN-restriction to the faithful candidate forces convergence. -/
theorem converged_of_singleton_gen (h : D.gen c = ({c} : Finset C)) : D.Converged c := by
  show D.evalFilter (D.gen c) = ({c} : Finset C)
  rw [h, evalFilter, dif_pos (Finset.singleton_nonempty c)]
  exact argMinSet_singleton c _

/-- An `n`-round HS derivation: `iterateGen` over `stepOptimum` with a caller-supplied
`pick` tie-breaker for non-singleton optima (ties not yet broken by directional eval,
or genuinely divergent ties in the [pruitt-2009] sense). -/
def derive (pick : Finset C → Option C) (steps : Nat) : Option C :=
  iterateGen D.stepOptimum pick c steps

end HSDerivation

end OptimalityTheory
