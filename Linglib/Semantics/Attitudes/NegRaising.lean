import Linglib.Semantics.Attitudes.Doxastic
import Linglib.Logic.Aristotelian.Square
import Linglib.Semantics.Homogeneity.Decided

/-!
# Neg-raising as O→E pragmatic strengthening

Neg-raising interprets the negation of an attitude verb as the
attitude applied to the negated complement — "I don't think it's
raining" ≈ "I think it's not raining", ¬Bel(p) strengthened to
Bel(¬p) ([horn-2001]). On the doxastic square of opposition
(`doxasticSquare`: A = Bel(p), E = Bel(¬p), I = ◇p, O = ¬Bel(p)) this
is O→E strengthening, available exactly because belief and disbelief
are contraries: the agent may be undecided, so ¬Bel(p) leaves a gap.
[gajewski-2007]'s excluded-middle premise — the agent is
`Opinionated` about the prejacent — closes the gap by disjunctive
syllogism (`negRaisesAt_of_opinionated`). Being opinionated about
*every* prejacent is the decided/subsingleton limit of the shared
`Homogeneity` core (`forall_opinionated_iff_subsingleton`).

Neg-raising is available for *believe* and *think* but not *know*:
for a veridical predicate, ¬know(p) includes the case that p is
false, so strengthening to know(¬p) would smuggle in a factual claim
(`negRaisingAvailable`).
-/

namespace NegRaising

open Aristotelian (Square SquareRelations)
open Doxastic
  (DoxasticPredicate Veridicality BoxAt DiamondAt)

/-! ### The doxastic square -/

/-- The doxastic square for a belief predicate.

Given an accessibility relation, agent, and proposition, produce the four
corners of the doxastic square of opposition:
- A = Bel(p): all doxastic alternatives satisfy p
- E = Bel(¬p): all doxastic alternatives satisfy ¬p
- I = ◇p: some doxastic alternative satisfies p
- O = ¬Bel(p): not all doxastic alternatives satisfy p -/
def doxasticSquare {W E : Type*} (R : E → W → W → Prop) (agent : E)
    (worlds : List W) (p : W → Prop) : Square (W → Prop) where
  A := λ w => BoxAt R agent w worlds p
  E := λ w => BoxAt R agent w worlds (λ w' => ¬ p w')
  I := λ w => DiamondAt R agent w worlds p
  O := λ w => ¬ BoxAt R agent w worlds p

/-- The doxastic square satisfies the A–O contradiction diagonal. -/
theorem doxasticSquare_contradAO {W E : Type*} (R : E → W → W → Prop)
    (agent : E) (worlds : List W) (p : W → Prop) (w : W) :
    (doxasticSquare R agent worlds p).A w ↔
    ¬ (doxasticSquare R agent worlds p).O w := by
  simp only [doxasticSquare, not_not]

/-- The doxastic square satisfies the E–I contradiction diagonal.

This requires that `DiamondAt` is the dual of `BoxAt`: ◇p = ¬□¬p.
We prove this from the definitions. -/
theorem doxasticSquare_contradEI {W E : Type*} (R : E → W → W → Prop)
    (agent : E) (worlds : List W) (p : W → Prop) (w : W) :
    (doxasticSquare R agent worlds p).E w ↔
    ¬ (doxasticSquare R agent worlds p).I w := by
  simp only [doxasticSquare, BoxAt, DiamondAt]
  constructor
  · rintro h ⟨w', hw', hR, hp⟩
    exact h w' hw' hR hp
  · intro h w' hw' hR hp
    exact h ⟨w', hw', hR, hp⟩

/-! ### Neg-raising and the excluded-middle premise -/

/-- Neg-raising: the O→E inference `¬Bel(p) → Bel(¬p)` at a world. -/
def NegRaisesAt {W E : Type*} (R : E → W → W → Prop) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) : Prop :=
  ¬ BoxAt R agent w worlds p →
  BoxAt R agent w worlds (λ w' => ¬ p w')

/-- The excluded-middle premise: the agent is *opinionated* about `p`,
believing `p` or believing `¬p` — [gajewski-2007]'s neg-raising
presupposition. -/
def Opinionated {W E : Type*} (R : E → W → W → Prop) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) : Prop :=
  BoxAt R agent w worlds p ∨ BoxAt R agent w worlds (λ w' => ¬ p w')

/-- Opinionatedness about `p` licenses the O→E strengthening by
disjunctive syllogism: neg-raising is this inference run on the
pragmatically presupposed excluded-middle premise, not a semantic
entailment. -/
theorem negRaisesAt_of_opinionated {W E : Type*} (R : E → W → W → Prop) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) :
    Opinionated R agent worlds p w → NegRaisesAt R agent worlds p w :=
  fun hem hnot => hem.resolve_left hnot

/-- The accessible-worlds set at `w`; `BoxAt … p` is `∀ w' ∈ accessibleSet, p w'`. -/
def accessibleSet {W E : Type*} (R : E → W → W → Prop) (agent : E) (worlds : List W)
    (w : W) : Set W :=
  {w' | w' ∈ worlds ∧ R agent w w'}

theorem boxAt_iff_forall_accessibleSet {W E : Type*} (R : E → W → W → Prop) (agent : E)
    (worlds : List W) (p : W → Prop) (w : W) :
    BoxAt R agent w worlds p ↔ ∀ w' ∈ accessibleSet R agent worlds w, p w' := by
  simp only [BoxAt, accessibleSet, Set.mem_ofPred_eq, and_imp]

/-- The agent is opinionated about *every* prejacent — neg-raising
then holds as a validity — iff the accessible state is decided, a
subsingleton: the doxastic instance of the shared `Homogeneity`
core. -/
theorem forall_opinionated_iff_subsingleton {W E : Type*} (R : E → W → W → Prop)
    (agent : E) (worlds : List W) (w : W) :
    (∀ p : W → Prop, Opinionated R agent worlds p w) ↔
      (accessibleSet R agent worlds w).Subsingleton := by
  rw [← Semantics.Homogeneity.excludedMiddle_iff_subsingleton (accessibleSet R agent worlds w)]
  simp only [Opinionated, boxAt_iff_forall_accessibleSet]

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
  | .nonVeridical => true
  | .veridical => false

/-! ### Veridicality and square lemmas -/

/-- Neg-raising availability aligns with non-veridicality. -/
theorem negRaising_iff_nonVeridical (v : Veridicality) :
    negRaisingAvailable v = true ↔ v = .nonVeridical := by
  cases v <;> decide

/-- On the standard templates the availability pattern follows from the
veridicality field: `Doxastic.believeTemplate` and `thinkTemplate` are
non-veridical, `knowTemplate` veridical. -/
example {W E : Type*} (R : E → W → W → Prop) :
    negRaisingAvailable (Doxastic.believeTemplate R).veridicality = true ∧
    negRaisingAvailable (Doxastic.knowTemplate R).veridicality = false :=
  ⟨rfl, rfl⟩

end NegRaising
