import Mathlib.Data.Finset.Union
import Mathlib.Logic.Function.Defs

/-!
# OT — Iterated GEN/EVAL (Harmonic Serialism's Serial Wrapper)
@cite{mccarthy-2000} @cite{mccarthy-2010} @cite{pruitt-2023}

Pure combinator for serial OT-style derivations. The iteration combinator
takes a one-step `gen : C → Finset C` and an `eval : Finset C → Finset C`
(returning the optimal set, not a single winner), and iterates `eval ∘ gen`
from a starting candidate until a fixed point is reached.

## Why `Finset C → Finset C`, not `Finset C → Option C`

Classical OT genuinely has ties: the optimal set need not be a singleton.
@cite{pruitt-2023} discusses divergent ties extensively
(@cite{mcpherson-lamont-2026}'s Poko paradox is precisely such a case).
Returning `Option C` would force `Classical.choice` to pick a winner among
tied candidates, lying about the math. Mathlib's analogue is
`Finset.exists_min_image`: existence is proved without commitment to a
specific extractor. Tie-breaking is a separate concern — directional HS
(@cite{lamont-2022b}) adds a rule that turns an optimal `Finset` into a
singleton; vanilla HS (with arbitrary GEN) may legitimately produce ties.

## Convergence

A derivation has converged when `eval (gen c) = {c}` — the only optimal
candidate is the faithful one. This is the canonical HS halting condition
(@cite{mccarthy-2010}).

## Ranking durability

In HS the constraint ranking is **durable** — it is the same at every
iteration step. @cite{pruitt-2023} (page 508) quotes @cite{mccarthy-2000}
(p. 11): "in HS the constraint ranking is 'durable,' in that each step
in the derivation is subject to the same constraint hierarchy." The
combinator's signature reflects this: the `eval` argument is fixed
across all iterations. There is no `Nat → Eval` parameter that would
let the EVAL function vary across steps. (Stratal architectures, where
ranking changes between strata, get a separate cyclic wrapper *outside*
the iteration loop — see
`Theories/Phonology/OptimalityTheory/StratalOT.lean`.)
-/

namespace Core.Constraint.OT

variable {C : Type*}

-- ============================================================================
-- § 1: One-Step Iteration
-- ============================================================================

/-- One step of an HS-style derivation. `gen` produces the candidate set
    from the current form; `eval` selects the (possibly non-singleton)
    optimal subset. Returns the optimal set. -/
def iterateStep (gen : C → Finset C) (eval : Finset C → Finset C) (c : C)
    : Finset C :=
  eval (gen c)

/-- Powerset-functor lift of `iterateStep`. Sends a candidate set `s` to
    `⋃_{c ∈ s} eval (gen c)`. Pairs naturally with mathlib's
    `Function.IsFixedPt` to express HS convergence as a fixed point of
    a proper endo-function on `Finset C`:

    `Function.IsFixedPt (hsStep gen eval) {c} ↔ eval (gen c) = {c}`

    by `Finset.singleton_biUnion`. We do not introduce a local rename
    for the fixed-point predicate — `Function.IsFixedPt (hsStep gen eval) {c}`
    is itself the right spelling, and study files use the equivalent
    `eval (gen c) = {c}` directly. -/
def hsStep [DecidableEq C] (gen : C → Finset C) (eval : Finset C → Finset C)
    : Finset C → Finset C :=
  fun s => s.biUnion (fun c => eval (gen c))

/-- The powerset-lifted step at the singleton `{c}` reduces to one
    application of `iterateStep`. Bridges between mathlib's
    `Function.IsFixedPt (hsStep gen eval) {c}` and the simpler form
    `iterateStep gen eval c = {c}` used in proofs. -/
@[simp] theorem hsStep_singleton [DecidableEq C] (gen : C → Finset C)
    (eval : Finset C → Finset C) (c : C) :
    hsStep gen eval ({c} : Finset C) = iterateStep gen eval c := by
  rw [hsStep, iterateStep, Finset.singleton_biUnion]

-- ============================================================================
-- § 2: n-Step Iteration with Early Convergence
-- ============================================================================

/-- Iterate `iterateStep` for at most `n` rounds. Stops early when the
    optimal set is the singleton `{c}` (HS convergence at `c`).
    Otherwise advances by picking *some* element of the optimal set —
    here, an element supplied via `pick : Finset C → Option C` (e.g., a
    canonical sort + `head?`, or a tie-breaker injected by directional HS).

    Returns the converged form (or, if the iteration bound is exhausted,
    the form reached at the bound). Returns `none` if `pick` returns
    `none` or the optimal set is empty along the way (which can happen
    for ill-typed grammars but is excluded by HS's standard guarantees).

    HS derivations are not in general guaranteed to converge — see
    @cite{lamont-2022b} for non-terminating cases. The explicit `Nat`
    bound makes this function total. -/
def iterateGen [DecidableEq C] (gen : C → Finset C)
    (eval : Finset C → Finset C) (pick : Finset C → Option C)
    : C → Nat → Option C
  | c, 0     => some c
  | c, n + 1 =>
    let optima := iterateStep gen eval c
    if optima = ({c} : Finset C) then some c
    else
      match pick optima with
      | none    => none
      | some c' => iterateGen gen eval pick c' n

/-- Zero iterations is identity. -/
@[simp] theorem iterateGen_zero [DecidableEq C] (gen : C → Finset C)
    (eval : Finset C → Finset C) (pick : Finset C → Option C) (c : C) :
    iterateGen gen eval pick c 0 = some c := rfl

/-- One iteration from a converged form returns the form unchanged.
    The natural single-step API for `iterateGen` when the input is a
    fixed point. -/
theorem iterateGen_succ_of_converged [DecidableEq C] {gen : C → Finset C}
    {eval : Finset C → Finset C} (pick : Finset C → Option C) {c : C}
    (h : iterateStep gen eval c = ({c} : Finset C)) (n : Nat) :
    iterateGen gen eval pick c (n + 1) = some c := by
  unfold iterateGen; simp [h]

/-- One iteration from a non-converged form recurses with the picked
    successor at the smaller depth. The natural single-step API for
    `iterateGen` when the input is not yet a fixed point. -/
theorem iterateGen_succ_of_step [DecidableEq C] {gen : C → Finset C}
    {eval : Finset C → Finset C} {pick : Finset C → Option C} {c c' : C}
    (n : Nat) (hcv : iterateStep gen eval c ≠ ({c} : Finset C))
    (hpick : pick (iterateStep gen eval c) = some c') :
    iterateGen gen eval pick c (n + 1) = iterateGen gen eval pick c' n := by
  show (if iterateStep gen eval c = ({c} : Finset C) then some c
        else match pick (iterateStep gen eval c) with
             | none => none
             | some c' => iterateGen gen eval pick c' n)
       = iterateGen gen eval pick c' n
  rw [if_neg hcv, hpick]

/-- One iteration from a non-converged form where `pick` returns `none`
    yields `none`. -/
theorem iterateGen_succ_of_pickFail [DecidableEq C] {gen : C → Finset C}
    {eval : Finset C → Finset C} {pick : Finset C → Option C} {c : C}
    (n : Nat) (hcv : iterateStep gen eval c ≠ ({c} : Finset C))
    (hpick : pick (iterateStep gen eval c) = none) :
    iterateGen gen eval pick c (n + 1) = none := by
  show (if iterateStep gen eval c = ({c} : Finset C) then some c
        else match pick (iterateStep gen eval c) with
             | none => none
             | some c' => iterateGen gen eval pick c' n)
       = none
  rw [if_neg hcv, hpick]

-- ============================================================================
-- § 3: Convergence Theorems
-- ============================================================================

/-- Once at a fixed point, further iterations stay there. Convergence is
    durable. The hypothesis `iterateStep gen eval c = {c}` is equivalent
    to mathlib's `Function.IsFixedPt (hsStep gen eval) {c}` via
    `hsStep_singleton`. -/
theorem iterateGen_idempotent_at_fixedPoint [DecidableEq C]
    (gen : C → Finset C) (eval : Finset C → Finset C)
    (pick : Finset C → Option C) (c : C)
    (h : iterateStep gen eval c = ({c} : Finset C)) :
    ∀ n, iterateGen gen eval pick c n = some c
  | 0     => rfl
  | n + 1 => iterateGen_succ_of_converged (gen := gen) (eval := eval) pick h n

/-- **Harmonic improvement.** At each non-fixed-point step, every newly
    chosen candidate is strictly better than the input under the supplied
    harmony order `lt`. The order is a parameter (rather than baked in)
    so this lemma stays agnostic about `EvalMode` — `HarmonicSerialism.lean`
    instantiates it with the appropriate violation-profile order.

    Soundness must be witnessed by the caller: `sound` says any candidate
    in the optimal set distinct from the input is strictly more harmonic.
    This captures the "harmonically improving" gloss of HS
    (@cite{mccarthy-2010}). -/
theorem harmonicImprovement [DecidableEq C] (lt : C → C → Prop)
    (gen : C → Finset C) (eval : Finset C → Finset C)
    (sound : ∀ c c', c' ∈ eval (gen c) → c' ≠ c → lt c' c)
    (c c' : C) (hopt : c' ∈ iterateStep gen eval c) (hne : c' ≠ c) :
    lt c' c :=
  sound c c' hopt hne

/-- **HS terminates under a well-founded harmony order.** If `lt` is
    well-founded and every non-converged step where `pick` returns a
    strictly different candidate produces a strictly more harmonic one
    (`sound`), then `iterateGen` is **eventually constant**: there is
    some `N` past which further iterations don't change the result.

    This is the structural justification for HS as a search procedure:
    derivations can't loop indefinitely as long as each genuine step
    makes measurable progress toward optimality. The explicit `Nat`
    bound on `iterateGen` is harmless in practice precisely because
    such an `N` always exists when the harmony order is well-founded.

    The eventual-constant value is determined by which terminal case
    fires: convergence (fixed point reached), `pick` failure, or
    `pick` returns the input (degenerate no-progress halt). All three
    terminate the recursion, but the substrate doesn't enforce a
    particular terminal-distinguishing API yet — see the
    `iterateGen_succ_of_*` lemmas above for the three cases. -/
theorem iterateGen_eventually_constant [DecidableEq C]
    (gen : C → Finset C) (eval : Finset C → Finset C)
    (pick : Finset C → Option C) {lt : C → C → Prop} (wf : WellFounded lt)
    (sound : ∀ c c', iterateStep gen eval c ≠ ({c} : Finset C) →
                     pick (iterateStep gen eval c) = some c' → c' ≠ c → lt c' c)
    (c : C) :
    ∃ N, ∀ m, N ≤ m → iterateGen gen eval pick c m = iterateGen gen eval pick c N := by
  induction c using wf.induction with
  | _ c IH =>
    by_cases hcv : iterateStep gen eval c = ({c} : Finset C)
    · -- Converged: ∀ m, iterateGen ... c m = some c (idempotence at fixed point).
      refine ⟨0, fun m _ => ?_⟩
      rw [iterateGen_idempotent_at_fixedPoint gen eval pick c hcv m,
          iterateGen_idempotent_at_fixedPoint gen eval pick c hcv 0]
    · cases hp : pick (iterateStep gen eval c) with
      | none =>
        -- Pick fails: iterateGen ... c (n+1) = none for all n.
        refine ⟨1, fun m hm => ?_⟩
        match m, hm with
        | 0, hm => omega
        | n + 1, _ =>
          rw [iterateGen_succ_of_pickFail _ hcv hp,
              iterateGen_succ_of_pickFail 0 hcv hp]
      | some c' =>
        by_cases hne : c' = c
        · -- Pick returns input: iterateGen ... c m = some c for all m.
          have hp' : pick (iterateStep gen eval c) = some c := hne ▸ hp
          refine ⟨0, fun m _ => ?_⟩
          have h : ∀ m, iterateGen gen eval pick c m = some c := by
            intro m
            induction m with
            | zero => rfl
            | succ _ ih => rw [iterateGen_succ_of_step _ hcv hp']; exact ih
          rw [h m, h 0]
        · -- Genuine progress: by IH at c' (strictly more harmonic).
          have hlt : lt c' c := sound c c' hcv hp hne
          obtain ⟨N', IH'⟩ := IH c' hlt
          refine ⟨N' + 1, fun m hm => ?_⟩
          match m, hm with
          | 0, hm => omega
          | n + 1, hn =>
            have hn' : N' ≤ n := Nat.le_of_succ_le_succ hn
            rw [iterateGen_succ_of_step _ hcv hp,
                iterateGen_succ_of_step _ hcv hp,
                IH' n hn']

end Core.Constraint.OT
