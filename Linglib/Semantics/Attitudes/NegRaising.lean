import Linglib.Semantics.Attitudes.Doxastic
import Linglib.Core.Logic.Aristotelian.Square
import Linglib.Semantics.Homogeneity.Decided

/-!
# Neg-Raising as O→E Pragmatic Strengthening
[gajewski-2007] [horn-2001]

Neg-raising is the phenomenon where the negation of an attitude verb is
interpreted as the attitude applied to the negated complement:

  "I don't think it's raining" ≈ "I think it's not raining"
  ¬Bel(p) → Bel(¬p)

In terms of the Square of Opposition, this is strengthening from the
O-corner (¬Bel(p)) to the E-corner (Bel(¬p)). This strengthening is
available precisely because belief and disbelief are **contraries**: one
can neither believe p nor believe ¬p (the "undecided" gap). The pragmatic
inference fills this gap by assuming the agent has a settled opinion.

## The Doxastic Square

```
        contraries
  Bel(p) ────────── Bel(¬p)
    │ │
    │ │
    │ │
  ◇p ──────────────── ¬Bel(p)
       subcontraries
```

- **A** = Bel(p): agent believes p
- **E** = Bel(¬p): agent believes not-p (disbelieves p)
- **I** = ◇p: agent's beliefs are compatible with p
- **O** = ¬Bel(p): agent doesn't believe p

Neg-raising is available for `believe` and `think` (non-veridical: there is
a gap between ¬Bel(p) and Bel(¬p)) but NOT for `know` (veridical: ¬know(p)
includes cases where p is false, so strengthening to know(¬p) would require
¬p to be true, which is a factual claim the speaker may not intend).

## See also

The domain-general structural core — neg-raising / force collapse ⟺ the modal's
domain being a subsingleton — lives in `Semantics/Plurality/Homogeneity/Decided.lean`. This
file is the doxastic (believe / think / know) application layer.
-/

namespace Semantics.Attitudes.NegRaising

open Aristotelian (Square SquareRelations)
open Semantics.Attitudes.Doxastic
  (DoxasticPredicate Veridicality boxAt diaAt AccessRel)

/-! ### The doxastic square -/

/-- The doxastic square for a belief predicate.

Given an accessibility relation, agent, and proposition, produce the four
corners of the doxastic square of opposition:
- A = Bel(p): all doxastic alternatives satisfy p
- E = Bel(¬p): all doxastic alternatives satisfy ¬p
- I = ◇p: some doxastic alternative satisfies p
- O = ¬Bel(p): not all doxastic alternatives satisfy p -/
def doxasticSquare {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Prop) : Square (W → Prop) where
  A := λ w => boxAt R agent w worlds p
  E := λ w => boxAt R agent w worlds (λ w' => ¬ p w')
  I := λ w => diaAt R agent w worlds p
  O := λ w => ¬ boxAt R agent w worlds p

/-- The doxastic square satisfies the A–O contradiction diagonal. -/
theorem doxasticSquare_contradAO {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Prop) (w : W) :
    (doxasticSquare R agent worlds p).A w ↔
    ¬ (doxasticSquare R agent worlds p).O w := by
  simp only [doxasticSquare, not_not]

/-- The doxastic square satisfies the E–I contradiction diagonal.

This requires that `diaAt` is the dual of `boxAt`: ◇p = ¬□¬p.
We prove this from the definitions. -/
theorem doxasticSquare_contradEI {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Prop) (w : W) :
    (doxasticSquare R agent worlds p).E w ↔
    ¬ (doxasticSquare R agent worlds p).I w := by
  simp only [doxasticSquare, boxAt, diaAt]
  constructor
  · rintro h ⟨w', hw', hR, hp⟩
    exact h w' hw' hR hp
  · intro h w' hw' hR hp
    exact h ⟨w', hw', hR, hp⟩

/-! ### Neg-raising and the excluded-middle premise

Neg-raising is the O→E inference `¬Bel(p) → Bel(¬p)`. It is *not* generally valid:
for a non-veridical attitude the doxastic state is mixed, so `¬Bel(p)` leaves a
gap. What licenses the strengthening is the **excluded-middle premise** that the
agent is *opinionated* about `p` (`Bel(p) ∨ Bel(¬p)`), supplied pragmatically
([gajewski-2007]); given it the inference is a disjunctive syllogism. Being
opinionated about *every* prejacent is exactly the decided/subsingleton limit
(`Homogeneity.excludedMiddle_iff_subsingleton`), where neg-raising holds as a
validity rather than a defeasible move. -/

/-- Neg-raising: the O→E inference `¬Bel(p) → Bel(¬p)` at a world. -/
def negRaisesAt {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) : Prop :=
  ¬ boxAt R agent w worlds p →
  boxAt R agent w worlds (λ w' => ¬ p w')

/-- The **excluded-middle premise**: the agent is *opinionated* about `p`,
believing `p` or believing `¬p`. Gajewski's neg-raising presupposition. -/
def opinionated {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) : Prop :=
  boxAt R agent w worlds p ∨ boxAt R agent w worlds (λ w' => ¬ p w')

/-- **The pragmatic mechanism.** Opinionatedness about `p` licenses the O→E
strengthening — a disjunctive syllogism. Neg-raising is this inference run on the
(pragmatically presupposed) excluded-middle premise, not a semantic entailment. -/
theorem negRaisesAt_of_opinionated {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) :
    opinionated R agent worlds p w → negRaisesAt R agent worlds p w :=
  fun hem hnot => hem.resolve_left hnot

/-- The accessible-worlds set at `w`; `boxAt … p` is `∀ w' ∈ accessibleSet, p w'`. -/
def accessibleSet {W E : Type*} (R : AccessRel W E) (agent : E) (worlds : List W)
    (w : W) : Set W :=
  {w' | w' ∈ worlds ∧ R agent w w'}

theorem boxAt_iff_forall_accessibleSet {W E : Type*} (R : AccessRel W E) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) :
    boxAt R agent w worlds p ↔ ∀ w' ∈ accessibleSet R agent worlds w, p w' := by
  simp only [boxAt, accessibleSet, Set.mem_setOf_eq, and_imp]

/-- **Validity ⟺ decided state.** The agent is opinionated about *every* prejacent
(neg-raising then holds as a validity) iff the accessible state is decided — a
subsingleton — connecting the doxastic layer to the shared `Homogeneity` core. -/
theorem forall_opinionated_iff_subsingleton {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (w : W) :
    (∀ p : W → Prop, opinionated R agent worlds p w) ↔
      (accessibleSet R agent worlds w).Subsingleton := by
  rw [← Homogeneity.excludedMiddle_iff_subsingleton (accessibleSet R agent worlds w)]
  simp only [opinionated, boxAt_iff_forall_accessibleSet]

/-- Neg-raising is available exactly when the predicate admits a gap
between ¬Bel(p) and Bel(¬p) — i.e., when the O→E strengthening is
a genuine pragmatic move (not a semantic entailment).

For non-veridical predicates, ¬Bel(p) does NOT semantically entail
Bel(¬p) — there is a gap (the agent might be undecided). Neg-raising
fills this gap pragmatically.

For veridical predicates (know), ¬know(p) could mean either:
(a) p is true but agent doesn't know it, or
(b) p is false
Strengthening to know(¬p) would require (b), which is a factual
claim beyond pragmatic strengthening. -/
def negRaisingAvailable (v : Veridicality) : Bool :=
  match v with
  | .nonVeridical => true   -- believe, think: gap exists
  | .veridical => false     -- know: no neg-raising

/-! ### Veridicality and square lemmas -/

/-- Neg-raising availability aligns with non-veridicality. -/
theorem negRaising_iff_nonVeridical (v : Veridicality) :
    negRaisingAvailable v = true ↔ v = .nonVeridical := by
  cases v <;> decide

/-- The standard predicates' neg-raising status is *derived* from their
veridicality, not stipulated as a flag: believe and think are non-veridical
(neg-raising available), know is veridical (not). -/
theorem believe_think_negRaise_know_not {W E : Type*} (R : AccessRel W E) :
    negRaisingAvailable (Doxastic.believeTemplate R).veridicality = true ∧
    negRaisingAvailable (Doxastic.thinkTemplate R).veridicality = true ∧
    negRaisingAvailable (Doxastic.knowTemplate R).veridicality = false :=
  ⟨rfl, rfl, rfl⟩

/-- The doxastic square for "believe" satisfies the contradiction diagonals. -/
theorem believe_square_contradictions {W E : Type*} (R : AccessRel W E)
    (agent : E) (worlds : List W) (p : W → Prop) (w : W) :
    ((doxasticSquare R agent worlds p).A w ↔
      ¬ (doxasticSquare R agent worlds p).O w) ∧
    ((doxasticSquare R agent worlds p).E w ↔
      ¬ (doxasticSquare R agent worlds p).I w) :=
  ⟨doxasticSquare_contradAO R agent worlds p w,
   doxasticSquare_contradEI R agent worlds p w⟩

-- The domain-general core — neg-raising / force-collapse / excluded middle ⟺ the
-- domain being a subsingleton — lives in `Semantics/Plurality/Homogeneity/Decided.lean`,
-- consumed here (via `forall_opinionated_iff_subsingleton`) and by the modal-force
-- studies and nominal plural homogeneity.

end Semantics.Attitudes.NegRaising
