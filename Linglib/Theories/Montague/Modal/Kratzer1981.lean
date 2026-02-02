/-
# Kratzer (1981) Modal Semantics - Full Derivation

A comprehensive formalization of Kratzer's "The Notional Category of Modality"
with all key arguments fully derived, not just defined and checked.

## Paper Structure

Kratzer's central innovation is that modal accessibility is DERIVED from
two conversational backgrounds, rather than being primitive:

1. **Modal Base** f: W → ℘(℘(W)) - maps worlds to sets of propositions
2. **Ordering Source** g: W → ℘(℘(W)) - maps worlds to sets of ideal propositions

The ordering source induces a PREORDER on worlds, from which modal force emerges.

## Key Definitions (from paper, p. 31-40)

### Logical Properties (p. 31)
- p **follows from** A iff ∩A ⊆ p
- A is **consistent** iff ∩A ≠ ∅
- p is **compatible with** A iff A ∪ {p} is consistent

### Ordering Relation (p. 39)
For all w, z ∈ W:
  w ≤_A z iff {p ∈ A : z ∈ p} ⊆ {p ∈ A : w ∈ p}

This says: w is at least as close to the ideal A as z iff every ideal
proposition satisfied by z is also satisfied by w.

### Necessity with Ordering (p. 40)
p is a necessity in w w.r.t. f and g iff for all u ∈ ∩f(w):
  ∃v ∈ ∩f(w): v ≤_{g(w)} u ∧ ∀z ∈ ∩f(w): z ≤_{g(w)} v → z ∈ p

This avoids the Limit Assumption!

## What We Derive (not just define)

1. ≤_A is a preorder (reflexive, transitive) [Theorem 1]
2. Empty ordering makes all worlds equivalent [Theorem 2]
3. Empty ordering reduces to simple semantics [Theorem 3]
4. Totally realistic base gives T axiom [Theorem 4]
5. Realistic base gives reflexive accessibility [Theorem 5]
6. Comparative possibility properties [Theorem 6-7]

## References

- Kratzer, A. (1981). The Notional Category of Modality. In Eikmeyer & Rieser (eds.),
  Words, Worlds, and Contexts. de Gruyter. pp. 38-74.
- Kratzer, A. (2012). Modals and Conditionals. Oxford University Press.
  (Updated version used here for clarity)
-/

import Linglib.Theories.Montague.Verb.Attitude.Examples
import Linglib.Theories.Montague.Modal.Basic
import Mathlib.Order.Basic

namespace Montague.Modal.Kratzer1981

open Montague.Verb.Attitude.Examples
open Montague.Modal (ModalTheory ModalForce Proposition allWorlds')

-- ============================================================================
-- PART 1: Foundational Definitions (Kratzer p. 31)
-- ============================================================================

/-- A proposition is a characteristic function on worlds. -/
abbrev Prop' := World → Bool

/-- Convert to list of worlds where proposition holds. -/
def Prop'.extension (p : Prop') : List World :=
  allWorlds.filter p

/-- The intersection of a set of propositions: worlds satisfying ALL. -/
def propIntersection (props : List Prop') : List World :=
  allWorlds.filter fun w => props.all fun p => p w

/-- A proposition p **follows from** a set A iff ∩A ⊆ p (Kratzer p. 31)

In other words: every world satisfying all of A also satisfies p. -/
def followsFrom (p : Prop') (A : List Prop') : Bool :=
  (propIntersection A).all p

/-- A set of propositions is **consistent** iff ∩A ≠ ∅ (Kratzer p. 31) -/
def isConsistent (A : List Prop') : Bool :=
  !(propIntersection A).isEmpty

/-- A proposition p is **compatible with** A iff A ∪ {p} is consistent (Kratzer p. 31) -/
def isCompatibleWith (p : Prop') (A : List Prop') : Bool :=
  isConsistent (p :: A)

-- ============================================================================
-- PART 2: Conversational Backgrounds (Kratzer p. 31-33)
-- ============================================================================

/--
A conversational background maps worlds to sets of propositions.

This is Kratzer's key innovation: the modal base and ordering source are both
conversational backgrounds, but play different roles.
-/
abbrev ConvBackground := World → List Prop'

/-- The modal base: determines which worlds are accessible. -/
abbrev ModalBase := ConvBackground

/-- The ordering source: determines how accessible worlds are ranked. -/
abbrev OrderingSource := ConvBackground

/--
A conversational background is **realistic** iff for all w: w ∈ ∩f(w).

This means the actual world satisfies all propositions in the modal base.
Kratzer (p. 32): "For each world, there is a particular body of facts in w
that has a counterpart in each world in ∩f(w)."
-/
def isRealistic (f : ConvBackground) : Prop :=
  ∀ w : World, (f w).all (fun p => p w) = true

/--
A conversational background is **totally realistic** iff for all w: ∩f(w) = {w}.

This is the strongest form: only the actual world is accessible.
Kratzer (p. 33): "A totally realistic conversational background is a function f
such that for any world w, ∩f(w) = {w}."
-/
def isTotallyRealistic (f : ConvBackground) : Prop :=
  ∀ w : World, propIntersection (f w) = [w]

/--
The **empty** conversational background: f(w) = ∅ for all w.

Kratzer (p. 33): "The empty conversational background is the function f such
that for any w ∈ W, f(w) = ∅. Since ∩f(w) = W if f(w) = ∅, empty
conversational backgrounds are also realistic."
-/
def emptyBackground : ConvBackground := fun _ => []

-- ============================================================================
-- PART 3: The Ordering Relation ≤_A (Kratzer p. 39)
-- ============================================================================

/--
The set of propositions from A that world w satisfies.

This is {p ∈ A : w ∈ p} in Kratzer's notation.
-/
def satisfiedPropositions (A : List Prop') (w : World) : List Prop' :=
  A.filter (fun p => p w)

/--
Kratzer's ordering relation: w ≤_A z

Definition (p. 39): "For all worlds w and z ∈ W:
  w ≤_A z iff {p: p ∈ A and z ∈ p} ⊆ {p: p ∈ A and w ∈ p}"

Intuitively: w is at least as good as z (w.r.t. ideal A) iff every
ideal proposition that z satisfies, w also satisfies.

Note: This is the CORRECT definition using subset inclusion,
NOT counting (which would be incorrect).
-/
def atLeastAsGoodAs (A : List Prop') (w z : World) : Bool :=
  -- Every proposition in A satisfied by z is also satisfied by w
  (satisfiedPropositions A z).all fun p => p w

notation:50 w " ≤[" A "] " z => atLeastAsGoodAs A w z

/--
Strict ordering: w <_A z iff w ≤_A z but not z ≤_A w.

This means w satisfies strictly more ideal propositions than z.
-/
def strictlyBetter (A : List Prop') (w z : World) : Bool :=
  atLeastAsGoodAs A w z && !atLeastAsGoodAs A z w

notation:50 w " <[" A "] " z => strictlyBetter A w z

-- ============================================================================
-- PART 4: Key Theorems About the Ordering (DERIVATIONS)
-- ============================================================================

/--
**Theorem 1a: The ordering ≤_A is reflexive.**

For all w: w ≤_A w.

Proof: Every proposition satisfied by w is satisfied by w. ∎
-/
theorem ordering_reflexive (A : List Prop') (w : World) :
    atLeastAsGoodAs A w w = true := by
  unfold atLeastAsGoodAs satisfiedPropositions
  simp only [List.all_eq_true, List.mem_filter]
  intro p ⟨_, hpw⟩
  exact hpw

/--
**Theorem 1b: The ordering ≤_A is transitive.**

If u ≤_A v and v ≤_A w, then u ≤_A w.

Proof: If every prop satisfied by v is satisfied by u, and every prop
satisfied by w is satisfied by v, then every prop satisfied by w is
satisfied by u (by transitivity of implication). ∎
-/
theorem ordering_transitive (A : List Prop') (u v w : World)
    (huv : atLeastAsGoodAs A u v = true)
    (hvw : atLeastAsGoodAs A v w = true) :
    atLeastAsGoodAs A u w = true := by
  unfold atLeastAsGoodAs at *
  simp only [List.all_eq_true, satisfiedPropositions, List.mem_filter] at *
  intro p ⟨hpA, hpw⟩
  -- w satisfies p, so v must satisfy p (by hvw)
  have hpv : p v = true := hvw p ⟨hpA, hpw⟩
  -- v satisfies p, so u must satisfy p (by huv)
  exact huv p ⟨hpA, hpv⟩

/--
**Corollary: ≤_A is a preorder.**

A preorder is a reflexive and transitive relation.
-/
theorem ordering_is_preorder (A : List Prop') :
    (∀ w, atLeastAsGoodAs A w w = true) ∧
    (∀ u v w, atLeastAsGoodAs A u v = true → atLeastAsGoodAs A v w = true →
              atLeastAsGoodAs A u w = true) :=
  ⟨ordering_reflexive A, ordering_transitive A⟩

-- ============================================================================
-- PART 4b: Mathlib Preorder Instance
-- ============================================================================

/-!
## Mathlib Preorder Instance

We can formalize Kratzer's ordering as a proper mathlib `Preorder` instance.
This gives us access to mathlib's extensive library of order-theoretic lemmas.

Since the ordering depends on a parameter `A : List Prop'`, we define a function
that produces a `Preorder World` for each choice of ordering source.
-/

/-- Convert Boolean ordering to Prop for mathlib compatibility. -/
def atLeastAsGoodAs' (A : List Prop') (w z : World) : Prop :=
  atLeastAsGoodAs A w z = true

/-- Convert Boolean strict ordering to Prop. -/
def strictlyBetter' (A : List Prop') (w z : World) : Prop :=
  atLeastAsGoodAs A w z = true ∧ atLeastAsGoodAs A z w = false

/--
**Kratzer's ordering as a mathlib Preorder.**

Given an ordering source A, this produces a `Preorder World` instance where:
- `w ≤ z` means w is at least as good as z (w satisfies all A-props that z does)
- `w < z` means w is strictly better (derived: w ≤ z ∧ ¬z ≤ w)

This allows using mathlib's preorder lemmas (transitivity, antisymmetry of <, etc.)
-/
def kratzerPreorder (A : List Prop') : Preorder World where
  le := atLeastAsGoodAs' A
  le_refl w := ordering_reflexive A w
  le_trans u v w huv hvw := ordering_transitive A u v w huv hvw

/--
**Using the Preorder: reflexivity via mathlib.**

With the Preorder instance, we get `le_refl` from mathlib.
-/
theorem ordering_reflexive' (A : List Prop') (w : World) :
    (kratzerPreorder A).le w w :=
  (kratzerPreorder A).le_refl w

/--
**Using the Preorder: transitivity via mathlib.**

With the Preorder instance and `letI`, we can use mathlib's `le_trans`.
-/
theorem ordering_transitive' (A : List Prop') (u v w : World)
    (huv : (kratzerPreorder A).le u v)
    (hvw : (kratzerPreorder A).le v w) :
    (kratzerPreorder A).le u w := by
  letI := kratzerPreorder A
  exact le_trans huv hvw

/--
**Equivalence class under the ordering.**

Two worlds are equivalent under ≤_A if they satisfy the same A-propositions.
This is an equivalence relation (reflexive, symmetric, transitive).
-/
def orderingEquiv (A : List Prop') (w z : World) : Prop :=
  (kratzerPreorder A).le w z ∧ (kratzerPreorder A).le z w

/--
**Ordering equivalence is an equivalence relation.**
-/
theorem orderingEquiv_refl (A : List Prop') (w : World) :
    orderingEquiv A w w :=
  ⟨(kratzerPreorder A).le_refl w, (kratzerPreorder A).le_refl w⟩

theorem orderingEquiv_symm (A : List Prop') (w z : World)
    (h : orderingEquiv A w z) : orderingEquiv A z w :=
  ⟨h.2, h.1⟩

theorem orderingEquiv_trans (A : List Prop') (u v w : World)
    (huv : orderingEquiv A u v) (hvw : orderingEquiv A v w) :
    orderingEquiv A u w := by
  letI := kratzerPreorder A
  exact ⟨le_trans huv.1 hvw.1, le_trans hvw.2 huv.2⟩

-- ============================================================================
-- PART 4c: Monotonicity with Mathlib
-- ============================================================================

/-!
## Monotonicity Properties

With the Preorder instance, we can state monotonicity properties using
mathlib's `Monotone` and `Antitone` typeclasses.
-/

/--
**Proposition satisfaction is antitone in worlds.**

If w ≤_A z (w is at least as good as z), then every A-proposition
satisfied by z is also satisfied by w. This is essentially the
definition restated in terms of the preorder.
-/
theorem satisfaction_antitone (A : List Prop') (p : Prop') (hp : p ∈ A)
    (w z : World) (h : (kratzerPreorder A).le w z) (hpz : p z = true) :
    p w = true := by
  unfold kratzerPreorder atLeastAsGoodAs' atLeastAsGoodAs satisfiedPropositions at h
  simp only [List.all_eq_true, List.mem_filter] at h
  exact h p ⟨hp, hpz⟩

/--
**Theorem 2: Empty ordering makes all worlds equivalent.**

If A = ∅, then for all w, z: w ≤_A z and z ≤_A w.

Proof: The set of propositions in ∅ satisfied by any world is ∅.
Vacuously, ∅ ⊆ ∅. ∎
-/
theorem empty_ordering_all_equivalent (w z : World) :
    atLeastAsGoodAs [] w z = true ∧ atLeastAsGoodAs [] z w = true := by
  constructor <;> (unfold atLeastAsGoodAs satisfiedPropositions; simp)

/--
**Empty ordering: all worlds equivalent (preorder version).**

When A = [], the preorder becomes trivial (all pairs related).
-/
theorem empty_ordering_trivial (w z : World) :
    (kratzerPreorder []).le w z :=
  (empty_ordering_all_equivalent w z).1

/--
**Empty ordering gives universal equivalence.**
-/
theorem empty_ordering_universal_equiv (w z : World) :
    orderingEquiv [] w z :=
  ⟨(empty_ordering_all_equivalent w z).1, (empty_ordering_all_equivalent w z).2⟩

-- ============================================================================
-- PART 4d: Galois Connection (Proposition-World Duality)
-- ============================================================================

/-!
## Galois Connection: Semantic Duality

The relationship between propositions and worlds exhibits a **Galois connection**
structure, which is fundamental to possible worlds semantics.

Given:
- A set of propositions A (ordered by reverse inclusion ⊇)
- A set of worlds W (ordered by inclusion ⊆)

We have two functions:
- **Extension**: ext(A) = ∩A = {w : ∀p ∈ A. p(w)} — worlds satisfying all props
- **Intension**: int(W) = {p : ∀w ∈ W. p(w)} — props true at all worlds

These form a Galois connection:
  ext(A) ⊆ W  ↔  A ⊇ int(W)

In Kratzer's framework:
- The modal base f(w) determines accessible worlds via extension: ∩f(w)
- The ordering source g(w) refines these via the preorder
- Necessity (□) and possibility (◇) are adjoint operators

This duality underlies:
- The entailment relation between propositions
- The accessibility relation between worlds
- Modal duality: □p ↔ ¬◇¬p
-/

/--
**Extension**: Given propositions, compute the worlds where all hold.

ext(A) = {w : ∀p ∈ A. p(w)}

This is the "downward" direction of the Galois connection.
-/
def extension (props : List Prop') : List World :=
  propIntersection props

/--
**Intension**: Given worlds, compute propositions true at all of them.

int(W) = {p : ∀w ∈ W. p(w)}

This is the "upward" direction of the Galois connection.
For finite worlds and decidable propositions, we compute this relative to
a given universe of propositions.
-/
def intension (worlds : List World) (props : List Prop') : List Prop' :=
  props.filter fun p => worlds.all p

/--
**Galois connection property (one direction):**

If ext(A) ⊆ W, then int(W) ⊆ A (for props in A).

More precisely: if all worlds satisfying A are in W, then every proposition
true at all of W is a consequence of A.
-/
theorem galois_ext_to_int (A : List Prop') (W : List World)
    (hExt : ∀ w, w ∈ extension A → w ∈ W)
    (p : Prop') (hp : p ∈ intension W A) :
    ∀ w, w ∈ extension A → p w = true := by
  intro w hw
  -- w ∈ extension A means w satisfies all of A
  -- p ∈ intension W A means p is true at all of W
  -- Since w ∈ extension A → w ∈ W, we have w ∈ W
  have hwW : w ∈ W := hExt w hw
  -- intension means p is true at all worlds in W
  unfold intension at hp
  simp only [List.mem_filter, List.all_eq_true] at hp
  exact hp.2 w hwW

/--
**Galois connection property (other direction):**

If int(W) ⊇ A (all of A is true at all of W), then ext(A) ⊇ W.

More precisely: if all propositions in A are true at all worlds in W,
then W ⊆ ext(A).
-/
theorem galois_int_to_ext (A : List Prop') (W : List World)
    (hInt : ∀ p, p ∈ A → ∀ w, w ∈ W → p w = true)
    (w : World) (hw : w ∈ W) :
    w ∈ extension A := by
  unfold extension propIntersection
  simp only [List.mem_filter, List.all_eq_true]
  constructor
  · cases w <;> simp [allWorlds]
  · intro p hp
    exact hInt p hp w hw

/--
**Monotonicity of extension**: More propositions → fewer worlds.

If A ⊆ B (as sets), then ext(B) ⊆ ext(A).
This is the antitonicity in the Galois connection.
-/
theorem extension_antitone (A B : List Prop') (w : World)
    (hSub : ∀ p, p ∈ A → p ∈ B)
    (hw : w ∈ extension B) :
    w ∈ extension A := by
  unfold extension propIntersection at *
  simp only [List.mem_filter, List.all_eq_true] at *
  constructor
  · exact hw.1
  · intro p hp
    exact hw.2 p (hSub p hp)

/--
**Monotonicity of intension**: Fewer worlds → more propositions.

If W ⊆ V (W has fewer worlds), then int(V) ⊆ int(W).
Propositions true at all of V are also true at all of W (since W ⊆ V).
-/
theorem intension_antitone (W V : List World) (A : List Prop') (p : Prop')
    (hSub : ∀ w, w ∈ W → w ∈ V)
    (hp : p ∈ intension V A) :
    p ∈ intension W A := by
  unfold intension at *
  simp only [List.mem_filter, List.all_eq_true] at *
  constructor
  · exact hp.1
  · intro w hw
    exact hp.2 w (hSub w hw)

-- ============================================================================
-- PART 5: Accessible Worlds and Best Worlds
-- ============================================================================

/--
The set of worlds **accessible** from w given modal base f.

These are exactly the worlds in ∩f(w) - worlds compatible with all facts in f(w).
-/
def accessibleWorlds (f : ModalBase) (w : World) : List World :=
  propIntersection (f w)

/--
**Accessible worlds as Galois extension.**

The accessible worlds from w are exactly the extension of the modal base f(w).
This connects Kratzer's accessibility to the Galois connection framework.
-/
theorem accessible_is_extension (f : ModalBase) (w : World) :
    accessibleWorlds f w = extension (f w) := rfl

/--
**Accessibility predicate**: w' is accessible from w iff w' ∈ ∩f(w).

This is the 2-argument predicate version of `accessibleWorlds`.
-/
def accessibleFrom (f : ModalBase) (w w' : World) : Bool :=
  (f w).all (fun p => p w')

/--
The **best** worlds among accessible worlds, according to ordering source g.

These are the accessible worlds that are maximal under ≤_{g(w)}:
worlds w' such that for all accessible w'', w' ≤_{g(w)} w''.

When g(w) = ∅, all accessible worlds are best (by Theorem 2).
-/
def bestWorlds (f : ModalBase) (g : OrderingSource) (w : World) : List World :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  -- Keep worlds that are at least as good as all others
  accessible.filter fun w' =>
    accessible.all fun w'' => atLeastAsGoodAs ordering w' w''

/--
**Theorem 3: Empty ordering source reduces to simple accessibility.**

When g(w) = ∅, bestWorlds = accessibleWorlds.

Proof: By Theorem 2, all worlds are equivalent under empty ordering,
so all accessible worlds are "best". ∎
-/
theorem empty_ordering_simple (f : ModalBase) (w : World) :
    bestWorlds f (fun _ => []) w = accessibleWorlds f w := by
  unfold bestWorlds accessibleWorlds
  simp only [List.filter_eq_self]
  intro w' _
  simp only [List.all_eq_true]
  intro w'' _
  exact (empty_ordering_all_equivalent w' w'').1

-- ============================================================================
-- PART 6: Modal Operators
-- ============================================================================

/--
**Simple f-necessity** (Kratzer p. 32): p is true at ALL accessible worlds.

⟦must⟧_f(p)(w) = ∀w' ∈ ∩f(w). p(w')

This is what you get with an empty ordering source.
-/
def simpleNecessity (f : ModalBase) (p : Prop') (w : World) : Bool :=
  (accessibleWorlds f w).all p

/--
**Simple f-possibility** (Kratzer p. 32): p is true at SOME accessible world.

⟦can⟧_f(p)(w) = ∃w' ∈ ∩f(w). p(w')
-/
def simplePossibility (f : ModalBase) (p : Prop') (w : World) : Bool :=
  (accessibleWorlds f w).any p

/--
**Necessity with ordering** (Kratzer p. 40): p is true at ALL best worlds.

⟦must⟧_{f,g}(p)(w) = ∀w' ∈ Best(f,g,w). p(w')
-/
def necessity (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World) : Bool :=
  (bestWorlds f g w).all p

/--
**Possibility with ordering**: p is true at SOME best world.

⟦can⟧_{f,g}(p)(w) = ∃w' ∈ Best(f,g,w). p(w')
-/
def possibility (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World) : Bool :=
  (bestWorlds f g w).any p

-- ============================================================================
-- PART 7: Duality (DERIVATION)
-- ============================================================================

/-- Helper for list duality proof. -/
private theorem list_all_not_any_not (L : List World) (p : Prop') :
    (L.all p == !L.any fun w => !p w) = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

/--
**Theorem: Modal duality holds.**

□p ↔ ¬◇¬p

Proof: □p means p holds at ALL best worlds.
◇¬p means ¬p holds at SOME best world.
¬◇¬p means ¬p holds at NO best world.
These are logically equivalent. ∎
-/
theorem duality (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World) :
    (necessity f g p w == !possibility f g (fun w' => !p w') w) = true := by
  unfold necessity possibility
  exact list_all_not_any_not (bestWorlds f g w) p

-- ============================================================================
-- PART 8: Background Type Theorems (DERIVATIONS)
-- ============================================================================

/--
**Theorem 4: Totally realistic base gives T axiom.**

If f is totally realistic (∩f(w) = {w}), then □p → p.

Proof: If the only accessible world is w itself, then □p means p(w),
which immediately gives p at w. ∎
-/
theorem totally_realistic_gives_T (f : ModalBase) (g : OrderingSource)
    (hTotal : ∀ w, (accessibleWorlds f w) = [w])
    (p : Prop') (w : World)
    (hNec : necessity f g p w = true) : p w = true := by
  -- The best worlds are a subset of accessible worlds
  -- With totally realistic base, accessible = [w], so best ⊆ [w]
  -- Since necessity holds, p is true at all best worlds
  -- w must be in best worlds (it's the only accessible world)
  unfold necessity at hNec
  have hAcc : accessibleWorlds f w = [w] := hTotal w
  -- Best worlds are a filter of accessible worlds
  unfold bestWorlds at hNec
  simp only [hAcc] at hNec
  -- The only candidate is w, check if it passes the filter
  simp only [List.all_cons, List.all_nil, Bool.and_true] at hNec
  -- If [w].filter _ is non-empty and all p, then p w
  -- Actually, let's check: the filter keeps w iff w ≤ w (reflexive)
  have hRefl : atLeastAsGoodAs (g w) w w = true := ordering_reflexive (g w) w
  simp only [List.filter_cons, hRefl, ↓reduceIte, List.filter_nil,
             List.all_cons, List.all_nil, Bool.and_true] at hNec
  exact hNec

/--
**Theorem 5: Realistic base gives reflexive accessibility.**

If f is realistic (w ∈ ∩f(w) for all w), then the evaluation world
is always accessible from itself.

Proof: If w satisfies all propositions in f(w), then w ∈ ∩f(w). ∎
-/
theorem realistic_gives_reflexive_access (f : ModalBase)
    (hReal : isRealistic f) (w : World) :
    w ∈ accessibleWorlds f w := by
  unfold accessibleWorlds propIntersection
  simp only [List.mem_filter]
  constructor
  · cases w <;> simp [allWorlds]
  · exact hReal w

/--
**Theorem 6: Empty modal base gives universal accessibility.**

If f(w) = ∅ for all w, then ∩f(w) = W (all worlds accessible).

Proof: ∩∅ = W (vacuously, every world satisfies all zero propositions). ∎
-/
theorem empty_base_universal_access (w : World) :
    accessibleWorlds emptyBackground w = allWorlds := by
  unfold accessibleWorlds emptyBackground propIntersection
  simp only [List.filter_eq_self, List.all_eq_true]
  intro _ _ p hp
  simp only [List.not_mem_nil] at hp

-- ============================================================================
-- PART 8: Frame Correspondence Theorems
-- ============================================================================

/-!
## Frame Correspondence (Kripke 1963)

Modal axioms correspond to properties of the accessibility relation.
With Kratzer semantics, these properties apply to the DERIVED accessibility
from the modal base.

| Axiom | Name | Property | Condition |
|-------|------|----------|-----------|
| T | □p → p | Reflexivity | Realistic base |
| D | □p → ◇p | Seriality | Non-empty best worlds |
| 4 | □p → □□p | Transitivity | Transitive accessibility |
| B | p → □◇p | Symmetry | Symmetric accessibility |
| 5 | ◇p → □◇p | Euclidean | Euclidean accessibility |

T is already proven above (`totally_realistic_gives_T`). Here we prove D.
-/

/--
**D Axiom (Seriality)**: □p → ◇p

If necessity holds and the best worlds are non-empty, then possibility holds.

This is the consistency axiom: what is necessary is possible.
Seriality means: ∀w. ∃w'. w' is accessible from w.

Proof: If p holds at ALL best worlds, and there's at least one best world,
then p holds at SOME best world. ∎
-/
theorem D_axiom (f : ModalBase) (g : OrderingSource) (p : Prop') (w : World)
    (hSerial : (bestWorlds f g w).length > 0)
    (hNec : necessity f g p w = true) :
    possibility f g p w = true := by
  unfold necessity possibility at *
  -- hNec: bestWorlds.all p = true
  -- Need: bestWorlds.any p = true
  -- Since bestWorlds is non-empty and all satisfy p, some satisfies p
  have hAll : (bestWorlds f g w).all p = true := hNec
  match hBest : bestWorlds f g w with
  | [] =>
    -- Contradiction: list is empty but length > 0
    simp only [hBest, List.length_nil, gt_iff_lt, Nat.lt_irrefl] at hSerial
  | w' :: ws =>
    -- w' is in bestWorlds and satisfies p
    simp only [List.any_cons]
    have hPw' : p w' = true := by
      simp only [hBest, List.all_cons, Bool.and_eq_true] at hAll
      exact hAll.1
    simp only [hPw', Bool.true_or]

/--
**Seriality of realistic bases.**

If the modal base is realistic, then accessible worlds is non-empty
(contains at least the evaluation world).
-/
theorem realistic_is_serial (f : ModalBase) (hReal : isRealistic f) (w : World) :
    (accessibleWorlds f w).length > 0 := by
  have hw_acc := realistic_gives_reflexive_access f hReal w
  exact List.length_pos_of_mem hw_acc

/--
**D axiom for realistic bases.**

Realistic modal bases satisfy the D axiom (with empty ordering).
-/
theorem D_axiom_realistic (f : ModalBase) (hReal : isRealistic f)
    (p : Prop') (w : World)
    (hNec : necessity f emptyBackground p w = true) :
    possibility f emptyBackground p w = true := by
  -- With empty ordering, bestWorlds = accessibleWorlds
  have hSimple := empty_ordering_simple f w
  -- Accessible worlds is non-empty (contains w)
  have hSerial := realistic_is_serial f hReal w
  -- Apply D axiom: use the general theorem
  have hBestSerial : (bestWorlds f emptyBackground w).length > 0 := by
    unfold emptyBackground at hSimple ⊢
    rw [hSimple]
    exact hSerial
  exact D_axiom f emptyBackground p w hBestSerial hNec

-- ============================================================================
-- PART 8b: Additional Frame Correspondence (4, B, 5 Axioms)
-- ============================================================================

/-!
## Additional Frame Correspondence Theorems

The remaining axioms of modal logic correspond to additional properties
of the accessibility relation. With Kratzer semantics using empty ordering,
accessibility is determined by the modal base: w' accessible from w iff w' ∈ ∩f(w).

| Axiom | Formula | Property | Condition on f |
|-------|---------|----------|----------------|
| 4 | □p → □□p | Transitivity | ∩f(w') ⊆ ∩f(w) for w' ∈ ∩f(w) |
| B | p → □◇p | Symmetry | w ∈ ∩f(w') for w' ∈ ∩f(w) |
| 5 | ◇p → □◇p | Euclidean | ∩f(w') = ∩f(w'') for w',w'' ∈ ∩f(w) |
-/

/--
**Transitive accessibility**: if w' is accessible from w, then all worlds
accessible from w' are also accessible from w.

∀w,w',w''. w' ∈ ∩f(w) ∧ w'' ∈ ∩f(w') → w'' ∈ ∩f(w)

Equivalently: ∩f(w') ⊆ ∩f(w) for all w' ∈ ∩f(w).
-/
def isTransitiveAccess (f : ModalBase) : Prop :=
  ∀ w w' w'' : World,
    w' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w' →
    w'' ∈ accessibleWorlds f w

/--
**Symmetric accessibility**: if w' is accessible from w, then w is accessible from w'.

∀w,w'. w' ∈ ∩f(w) → w ∈ ∩f(w')
-/
def isSymmetricAccess (f : ModalBase) : Prop :=
  ∀ w w' : World,
    w' ∈ accessibleWorlds f w →
    w ∈ accessibleWorlds f w'

/--
**Euclidean accessibility**: if w' and w'' are both accessible from w,
then w'' is accessible from w' (and vice versa).

∀w,w',w''. w' ∈ ∩f(w) ∧ w'' ∈ ∩f(w) → w'' ∈ ∩f(w')

This means all accessible worlds have the same "view" of accessibility.
-/
def isEuclideanAccess (f : ModalBase) : Prop :=
  ∀ w w' w'' : World,
    w' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w →
    w'' ∈ accessibleWorlds f w'

/--
**4 Axiom (Transitivity)**: □p → □□p

If p is necessary at w, then "p is necessary" is necessary at w.

Proof: Assume □p at w and transitive accessibility. For any accessible w',
we need □p at w'. For any w'' accessible from w', by transitivity w'' is
accessible from w. Since □p at w, p holds at w''. Thus p holds at all
worlds accessible from w', so □p at w'. ∎
-/
theorem four_axiom (f : ModalBase) (p : Prop') (w : World)
    (hTrans : isTransitiveAccess f)
    (hNec : necessity f emptyBackground p w = true) :
    necessity f emptyBackground (necessity f emptyBackground p) w = true := by
  -- With empty ordering, bestWorlds = accessibleWorlds
  have hSimple : ∀ v, bestWorlds f emptyBackground v = accessibleWorlds f v :=
    fun v => empty_ordering_simple f v
  -- Unfold the goal
  unfold necessity
  rw [hSimple w]
  apply List.all_eq_true.mpr
  intro w' hw'Acc
  -- Need to show: necessity f emptyBackground p w' = true
  -- Goal is now (bestWorlds f emptyBackground w').all p = true
  -- Rewrite using hSimple w'
  show (bestWorlds f emptyBackground w').all p = true
  rw [hSimple w']
  apply List.all_eq_true.mpr
  intro w'' hw''Acc
  -- w'' is accessible from w' which is accessible from w
  -- By transitivity, w'' is accessible from w
  have hw''AccW : w'' ∈ accessibleWorlds f w := hTrans w w' w'' hw'Acc hw''Acc
  -- Since □p at w, p holds at all worlds accessible from w
  unfold necessity at hNec
  rw [hSimple w] at hNec
  exact List.all_eq_true.mp hNec w'' hw''AccW

/--
**B Axiom (Symmetry)**: p → □◇p

If p holds at w, then "p is possible" is necessary at w.

Proof: Assume p at w and symmetric accessibility. For any accessible w',
we need ◇p at w'. By symmetry, w is accessible from w'. Since p holds at w,
there exists an accessible world from w' (namely w) where p holds. Thus ◇p at w'. ∎
-/
theorem B_axiom (f : ModalBase) (p : Prop') (w : World)
    (hSym : isSymmetricAccess f)
    (hP : p w = true) :
    necessity f emptyBackground (possibility f emptyBackground p) w = true := by
  -- With empty ordering, bestWorlds = accessibleWorlds
  have hSimple : ∀ v, bestWorlds f emptyBackground v = accessibleWorlds f v :=
    fun v => empty_ordering_simple f v
  -- Unfold the goal
  unfold necessity
  rw [hSimple w]
  apply List.all_eq_true.mpr
  intro w' hw'Acc
  -- Need to show: possibility f emptyBackground p w' = true
  unfold possibility
  rw [hSimple w']
  apply List.any_eq_true.mpr
  -- w is accessible from w' by symmetry
  have hwAccW' : w ∈ accessibleWorlds f w' := hSym w w' hw'Acc
  -- p holds at w
  exact ⟨w, hwAccW', hP⟩

/--
**5 Axiom (Euclidean)**: ◇p → □◇p

If p is possible at w, then "p is possible" is necessary at w.

Proof: Assume ◇p at w and Euclidean accessibility. There exists w'' accessible
from w where p holds. For any accessible w', we need ◇p at w'. By Euclidean
property, w'' is accessible from w' (since both w' and w'' are accessible from w).
Since p holds at w'', ◇p holds at w'. ∎
-/
theorem five_axiom (f : ModalBase) (p : Prop') (w : World)
    (hEuc : isEuclideanAccess f)
    (hPoss : possibility f emptyBackground p w = true) :
    necessity f emptyBackground (possibility f emptyBackground p) w = true := by
  -- With empty ordering, bestWorlds = accessibleWorlds
  have hSimple : ∀ v, bestWorlds f emptyBackground v = accessibleWorlds f v :=
    fun v => empty_ordering_simple f v
  -- From ◇p at w, get a witness w'' where p holds
  unfold possibility at hPoss
  rw [hSimple w] at hPoss
  obtain ⟨w'', hw''Acc, hPw''⟩ := List.any_eq_true.mp hPoss
  -- Unfold the goal
  unfold necessity
  rw [hSimple w]
  apply List.all_eq_true.mpr
  intro w' hw'Acc
  -- Need to show: possibility f emptyBackground p w' = true
  unfold possibility
  rw [hSimple w']
  apply List.any_eq_true.mpr
  -- w'' is accessible from w' by Euclidean property
  have hw''AccW' : w'' ∈ accessibleWorlds f w' := hEuc w w' w'' hw'Acc hw''Acc
  exact ⟨w'', hw''AccW', hPw''⟩

/--
**S4 = K + T + 4**: Reflexive and transitive accessibility.

A modal base gives S4 if it is realistic (T) and has transitive accessibility (4).
-/
def isS4Base (f : ModalBase) : Prop :=
  isRealistic f ∧ isTransitiveAccess f

/--
**S5 = K + T + 5**: Reflexive and Euclidean accessibility.

A modal base gives S5 if it is realistic (T) and has Euclidean accessibility (5).

Note: Reflexive + Euclidean implies Symmetric and Transitive.
-/
def isS5Base (f : ModalBase) : Prop :=
  isRealistic f ∧ isEuclideanAccess f

/--
**Euclidean + Reflexive implies Symmetric.**

Proof: Assume w' ∈ ∩f(w). By reflexivity, w ∈ ∩f(w). By Euclidean (w,w',w),
we get w ∈ ∩f(w'). ∎
-/
theorem euclidean_reflexive_implies_symmetric (f : ModalBase)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isSymmetricAccess f := by
  intro w w' hw'Acc
  -- w is accessible from w (reflexivity)
  have hwAcc : w ∈ accessibleWorlds f w := realistic_gives_reflexive_access f hReal w
  -- By Euclidean: w' ∈ ∩f(w) and w ∈ ∩f(w) implies w ∈ ∩f(w')
  exact hEuc w w' w hw'Acc hwAcc

/--
**Euclidean + Reflexive implies Transitive.**

Proof: Assume w' ∈ ∩f(w) and w'' ∈ ∩f(w'). By reflexivity, w' ∈ ∩f(w').
By Euclidean (w', w', w''), we get w'' ∈ ∩f(w'). But we already have that.
Actually, we need a different approach:
By symmetry (derived above), w ∈ ∩f(w'). By Euclidean (w', w, w''),
we get w'' ∈ ∩f(w). ∎
-/
theorem euclidean_reflexive_implies_transitive (f : ModalBase)
    (hReal : isRealistic f) (hEuc : isEuclideanAccess f) :
    isTransitiveAccess f := by
  intro w w' w'' hw'Acc hw''AccW'
  -- By symmetry (derived from Euclidean + reflexive), w ∈ ∩f(w')
  have hSym := euclidean_reflexive_implies_symmetric f hReal hEuc
  have hwAccW' : w ∈ accessibleWorlds f w' := hSym w w' hw'Acc
  -- By Euclidean at w': w ∈ ∩f(w') and w'' ∈ ∩f(w') implies w'' ∈ ∩f(w)
  -- hEuc w' w w'' : w ∈ acc(w') → w'' ∈ acc(w') → w'' ∈ acc(w)
  exact hEuc w' w w'' hwAccW' hw''AccW'

/--
**S5 bases satisfy all axioms: T, D, 4, B, 5.**
-/
theorem S5_satisfies_all (f : ModalBase) (hS5 : isS5Base f) :
    isRealistic f ∧ isSymmetricAccess f ∧ isTransitiveAccess f ∧ isEuclideanAccess f := by
  obtain ⟨hReal, hEuc⟩ := hS5
  exact ⟨hReal,
         euclidean_reflexive_implies_symmetric f hReal hEuc,
         euclidean_reflexive_implies_transitive f hReal hEuc,
         hEuc⟩

-- ============================================================================
-- PART 9: Comparative Possibility (Kratzer p. 41)
-- ============================================================================

/--
p is **at least as good a possibility as** q in w with respect to f and g.

Kratzer (p. 41): p ≥ q iff there's no world in q-p that is better than
all worlds in p-q.

Simplified: every world satisfying q but not p is dominated by some world
satisfying p but not q.
-/
def atLeastAsGoodPossibility (f : ModalBase) (g : OrderingSource)
    (p q : Prop') (w : World) : Bool :=
  let accessible := accessibleWorlds f w
  let ordering := g w
  -- Worlds in q - p (satisfy q but not p)
  let qMinusP := accessible.filter (fun w' => q w' && !p w')
  -- Worlds in p - q (satisfy p but not q)
  let pMinusQ := accessible.filter (fun w' => p w' && !q w')
  -- For each w' in q-p, there exists w'' in p-q with w'' ≤ w'
  qMinusP.all fun w' => pMinusQ.any fun w'' => atLeastAsGoodAs ordering w'' w'

/--
p is a **better possibility** than q: p ≥ q but not q ≥ p.
-/
def betterPossibility (f : ModalBase) (g : OrderingSource)
    (p q : Prop') (w : World) : Bool :=
  atLeastAsGoodPossibility f g p q w && !atLeastAsGoodPossibility f g q p w

/--
**Theorem 7: Comparative possibility is reflexive.**

p is at least as good a possibility as itself.

Proof: p - p = ∅, so the condition is vacuously satisfied. ∎
-/
theorem comparative_poss_reflexive (f : ModalBase) (g : OrderingSource)
    (p : Prop') (w : World) :
    atLeastAsGoodPossibility f g p p w = true := by
  unfold atLeastAsGoodPossibility
  -- p - p is empty since p w && !p w = false for all w
  -- So the condition is vacuously true (all of empty list satisfy predicate)
  -- The filter (fun w' => p w' && !p w') produces [] since p w' && !p w' = false always
  simp only [Bool.and_not_self, List.filter_false, List.all_nil]

-- ============================================================================
-- PART 10: Modal Flavors (Kratzer p. 37-55)
-- ============================================================================

/--
**Epistemic modality**: what is known/believed.

- Modal base: evidence/knowledge
- Ordering source: empty (or stereotypical for "probably")
-/
structure EpistemicFlavor where
  /-- The epistemic modal base (evidence) -/
  evidence : ModalBase
  /-- Typically empty for simple epistemic modals -/
  ordering : OrderingSource := emptyBackground

/--
**Deontic modality**: what is required/permitted by norms.

- Modal base: circumstances
- Ordering source: laws/norms
-/
structure DeonticFlavor where
  /-- Circumstances (realistic modal base) -/
  circumstances : ModalBase
  /-- Laws or norms to be satisfied -/
  norms : OrderingSource

/--
**Bouletic modality**: what is wanted/desired.

- Modal base: circumstances
- Ordering source: desires
-/
structure BouleticFlavor where
  circumstances : ModalBase
  desires : OrderingSource

/--
**Teleological modality**: what leads to goals.

- Modal base: circumstances
- Ordering source: goals
-/
structure TeleologicalFlavor where
  circumstances : ModalBase
  goals : OrderingSource

-- ============================================================================
-- PART 11: K Axiom (Distribution)
-- ============================================================================

/-- Material implication as a proposition. -/
def implies (p q : Prop') : Prop' := fun w => !p w || q w

/--
**Theorem: K Axiom (Distribution) holds.**

□(p → q) → (□p → □q)

This is the fundamental axiom of normal modal logic.

Proof: If (p → q) holds at all best worlds, and p holds at all best worlds,
then q holds at all best worlds (by modus ponens at each world). ∎
-/
theorem K_axiom (f : ModalBase) (g : OrderingSource) (p q : Prop') (w : World)
    (hImpl : necessity f g (implies p q) w = true)
    (hP : necessity f g p w = true) :
    necessity f g q w = true := by
  unfold necessity at hImpl hP ⊢
  apply List.all_eq_true.mpr
  intro w' hW'Best
  have hImplW' : implies p q w' = true := List.all_eq_true.mp hImpl w' hW'Best
  have hPW' : p w' = true := List.all_eq_true.mp hP w' hW'Best
  unfold implies at hImplW'
  cases hp : p w' with
  | false => simp [hp] at hPW'
  | true => simp [hp] at hImplW'; exact hImplW'

-- ============================================================================
-- PART 12: Conditionals (Kratzer p. 64-66)
-- ============================================================================

/--
Conditionals as modal base restrictors.

"If α, (must) β" = must_f+α β

The if-clause adds the antecedent to the modal base.
-/
def restrictedBase (f : ModalBase) (antecedent : Prop') : ModalBase :=
  fun w => antecedent :: f w

/--
**Material implication** emerges from:
- Totally realistic modal base
- Empty ordering source

Kratzer (p. 65-66): When the modal base is totally realistic and the
ordering source is empty, "if p, must q" reduces to material implication.
-/
def materialImplication (p q : Prop') (w : World) : Bool :=
  !p w || q w

/--
**Strict implication** emerges from:
- Empty modal base (all worlds accessible)
- Empty ordering source

"If p, must q" means q is true at all p-worlds.
-/
def strictImplication (p q : Prop') : Bool :=
  allWorlds.all fun w => !p w || q w

-- ============================================================================
-- PART 13: Summary
-- ============================================================================

/-!
## Summary: What We Have DERIVED (not just defined)

### Preorder Properties (Theorem 1)
- `ordering_reflexive`: ∀A,w. w ≤_A w
- `ordering_transitive`: ∀A,u,v,w. u ≤_A v → v ≤_A w → u ≤_A w
- `ordering_is_preorder`: Combines the above
- `kratzerPreorder`: **Mathlib Preorder instance** for ≤_A

### Mathlib Integration
- `kratzerPreorder`: Proper `Preorder World` instance parameterized by A
- `ordering_transitive'`: Uses mathlib's `le_trans`
- `orderingEquiv_trans`: Uses mathlib's transitivity lemmas
- `satisfaction_antitone`: Antitonicity of proposition satisfaction

### Galois Connection (Semantic Duality)
- `extension`: ext(A) = {w : ∀p ∈ A. p(w)} — worlds satisfying all props
- `intension`: int(W) = {p : ∀w ∈ W. p(w)} — props true at all worlds
- `galois_ext_to_int`: ext(A) ⊆ W → int(W) ⊆ A (for A-props)
- `galois_int_to_ext`: A ⊆ int(W) → W ⊆ ext(A)
- `extension_antitone`: More props → fewer worlds
- `intension_antitone`: Fewer worlds → more props
- `accessible_is_extension`: Accessibility = Galois extension

### Empty Ordering (Theorems 2-3)
- `empty_ordering_all_equivalent`: A=∅ implies all worlds equivalent
- `empty_ordering_simple`: g=∅ implies bestWorlds = accessibleWorlds

### Modal Base Properties (Theorems 4-6)
- `totally_realistic_gives_T`: Totally realistic f → (□p → p)
- `realistic_gives_reflexive_access`: Realistic f → w ∈ ∩f(w)
- `empty_base_universal_access`: f=∅ → ∩f(w) = W

### Modal Logic Properties
- `duality`: □p ↔ ¬◇¬p
- `K_axiom`: □(p → q) → (□p → □q)

### Frame Correspondence Theorems
- `D_axiom`: □p → ◇p (seriality)
- `four_axiom`: □p → □□p (transitivity)
- `B_axiom`: p → □◇p (symmetry)
- `five_axiom`: ◇p → □◇p (Euclidean)
- `euclidean_reflexive_implies_symmetric`: T + 5 → B
- `euclidean_reflexive_implies_transitive`: T + 5 → 4
- `S5_satisfies_all`: S5 bases satisfy T, D, 4, B, 5

### Comparative Possibility (Theorem 7)
- `comparative_poss_reflexive`: p is at least as good a possibility as p

### Correspondence to Paper
| Section | Content | Status |
|---------|---------|--------|
| 2.3 | Basic logical notions | ✓ Defined |
| 2.3 | Conversational backgrounds | ✓ Defined |
| 2.4 | Ordering relation | ✓ Defined + Mathlib Preorder |
| 2.4 | Necessity/Possibility | ✓ Defined + Duality PROVEN |
| 2.4 | Comparative possibility | ✓ Defined + Reflexivity PROVEN |
| 2.5-2.7 | Modal flavors | ✓ Structured |
| 2.9 | Conditionals | ✓ Defined |
| Frame | T, D, K axioms | ✓ PROVEN |
| Frame | 4, B, 5 axioms | ✓ PROVEN |
| Galois | Extension/Intension | ✓ PROVEN |

This formalization:
1. Uses Kratzer's CORRECT subset-based ordering (not counting)
2. PROVES preorder properties via **mathlib Preorder instance**
3. DERIVES frame correspondence theorems with full argumentation
4. Establishes **Galois connection** for semantic duality
-/

-- ============================================================================
-- PART 14: ModalTheory Interface
-- ============================================================================

/-!
## ModalTheory Interface

For compatibility with the comparison infrastructure in Compare.lean,
we provide `ModalTheory` instances using the correct definitions.
-/

/--
Parameters for a Kratzer modal theory.
-/
structure KratzerParams where
  /-- Modal base: world → set of propositions (facts) -/
  base : ModalBase
  /-- Ordering source: world → set of propositions (ideals) -/
  ordering : OrderingSource

/--
Construct a Kratzer modal theory from parameters.

Uses the CORRECT subset-based ordering (not the flawed counting approach).
-/
def Kratzer (params : KratzerParams) : ModalTheory where
  name := "Kratzer"
  citation := "Kratzer 1981"
  eval := fun force p w =>
    let best := bestWorlds params.base params.ordering w
    match force with
    | .necessity => best.all p
    | .possibility => best.any p

-- Standard parameter configurations

/-- Empty modal base: all worlds are accessible. -/
def emptyBase' : ModalBase := emptyBackground

/-- Empty ordering source: no ranking among accessible worlds. -/
def emptyOrdering'' : OrderingSource := emptyBackground

/-- Minimal parameters: all worlds accessible, no ordering. -/
def minimalParams : KratzerParams where
  base := emptyBase'
  ordering := emptyOrdering''

/-- Epistemic parameters: modal base from evidence. -/
def epistemicParams (evidence : ModalBase) : KratzerParams where
  base := evidence
  ordering := emptyBackground

/-- Deontic parameters: circumstances + norms. -/
def deonticParams (circumstances : ModalBase) (norms : OrderingSource) : KratzerParams where
  base := circumstances
  ordering := norms

-- Instantiated theories

/-- Minimal Kratzer theory: universal accessibility, no ordering. -/
def KratzerMinimal : ModalTheory := Kratzer minimalParams

-- Concrete epistemic example: knowledge that the ground is wet
-- Using groundWet from Basic.lean

/-- Epistemic modal base: the ground is wet (propositions compatible with knowledge). -/
def concreteEpistemicBase : ModalBase := fun _ => [groundWet]

/-- Concrete epistemic parameters. -/
def concreteEpistemicParams : KratzerParams where
  base := concreteEpistemicBase
  ordering := emptyBackground

/-- Epistemic modal theory: "must" = necessary given what is known. -/
def KratzerEpistemic : ModalTheory := Kratzer concreteEpistemicParams

-- Concrete deontic example: circumstances + norms

/-- Circumstantial modal base: all worlds with consistent circumstances. -/
def concreteCircumstantialBase : ModalBase := fun _ => []  -- All worlds accessible

/-- Deontic ordering: ideals for what the law requires. -/
def concreteDeonticOrdering : OrderingSource := fun _ => [johnHome]  -- John being home is ideal

/-- Concrete deontic parameters. -/
def concreteDeonticParams : KratzerParams where
  base := concreteCircumstantialBase
  ordering := concreteDeonticOrdering

/-- Deontic modal theory: "must" = necessary given the norms. -/
def KratzerDeontic : ModalTheory := Kratzer concreteDeonticParams

-- ============================================================================
-- Duality for ModalTheory Interface
-- ============================================================================

/-- Helper: duality holds for any list. -/
private theorem list_duality_helper (L : List World) (p : Proposition) :
    (L.all p == !L.any fun w' => !p w') = true := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, List.any_cons, Bool.not_or, Bool.not_not]
    cases p x <;> simp [ih]

/--
Kratzer theories (via ModalTheory) satisfy modal duality: □p ↔ ¬◇¬p
-/
theorem kratzer_duality (params : KratzerParams) (p : Proposition) (w : World) :
    (Kratzer params).dualityHolds p w = true := by
  unfold ModalTheory.dualityHolds Kratzer ModalTheory.necessity ModalTheory.possibility
  exact list_duality_helper (bestWorlds params.base params.ordering w) p

/-- All Kratzer theories are normal modal logics. -/
theorem kratzer_isNormal (params : KratzerParams) : (Kratzer params).isNormal :=
  fun p w => kratzer_duality params p w

/-- Corollary: KratzerMinimal is normal. -/
theorem kratzerMinimal_isNormal : KratzerMinimal.isNormal :=
  kratzer_isNormal minimalParams

end Montague.Modal.Kratzer1981
