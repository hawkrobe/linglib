/-
# Common Ground

Formalizes the notion of conversational common ground, following
Stalnaker (1974, 2002). This is fundamental infrastructure used by:

- Presupposition theory (Heim 1983, Schlenker 2009)
- QUD theory (Roberts 2012)
- RSA / pragmatic reasoning
- Dynamic semantics

## Key Concepts

1. **Common Ground (CG)**: The set of propositions mutually believed by
   conversationalists. Represented as a context set (set of possible worlds).

2. **Context Set**: The set of worlds compatible with the common ground.
   A world w is in the context set iff all CG propositions are true at w.

3. **Context Update**: How assertions modify the CG by eliminating worlds
   incompatible with the asserted content.

4. **Entailment**: CG entails P iff P is true at all worlds in context set.

## The Stalnaker Picture

- Context set c = { w : all CG propositions true at w }
- Assert φ: c' = c ∩ { w : φ(w) }
- Presupposition P: utterance felicitous only if c entails P

## References

- Stalnaker (1974). Pragmatic Presuppositions. In Munitz & Unger (eds.)
- Stalnaker (2002). Common Ground. Linguistics and Philosophy 25.
- Lewis (1979). Scorekeeping in a Language Game.
- Roberts (2012). Information Structure in Discourse.
-/

import Linglib.Core.Proposition

namespace Core.CommonGround

open Core.Proposition

-- ============================================================================
-- PART 1: Context Set
-- ============================================================================

/--
A context set is a predicate on worlds — the characteristic function
of the set of worlds compatible with the common ground.

Using `W → Prop` rather than `Set W` for simpler handling.
-/
def ContextSet (W : Type*) := W → Prop

namespace ContextSet

variable {W : Type*}

/--
The trivial context: all worlds possible (nothing established).
-/
def trivial : ContextSet W := fun _ => True

/--
The absurd context: no worlds possible (contradiction established).
-/
def absurd : ContextSet W := fun _ => False

/--
A world is in the context set.
-/
def mem (c : ContextSet W) (w : W) : Prop := c w

/--
The context set is non-empty.
-/
def nonEmpty (c : ContextSet W) : Prop := ∃ w, c w

-- ============================================================================
-- PART 2: Entailment
-- ============================================================================

/--
A context entails a proposition iff the proposition holds at all
worlds in the context.

c ⊧ P iff ∀w ∈ c, P(w)
-/
def entails (c : ContextSet W) (p : BProp W) : Prop :=
  ∀ w, c w → p w = true

notation:50 c " ⊧ " p => entails c p

/--
A proposition is compatible with a context if it holds at some world.
-/
def compatible (c : ContextSet W) (p : BProp W) : Prop :=
  ∃ w, c w ∧ p w = true

/--
Trivial context entails only tautologies.
-/
theorem trivial_entails_iff (p : BProp W) :
    (trivial ⊧ p) ↔ ∀ w, p w = true := by
  unfold entails trivial
  exact ⟨fun h w => h w True.intro, fun h w _ => h w⟩

/--
Absurd context entails everything.
-/
theorem absurd_entails (p : BProp W) : absurd ⊧ p := fun _ hw => hw.elim

-- ============================================================================
-- PART 3: Context Update
-- ============================================================================

/--
Update a context with a proposition: keep only worlds where proposition holds.

c + P = { w ∈ c : P(w) }
-/
def update (c : ContextSet W) (p : BProp W) : ContextSet W :=
  fun w => c w ∧ p w = true

notation:60 c " + " p => update c p

/--
Update restricts the context.
-/
theorem update_restricts (c : ContextSet W) (p : BProp W) (w : W) :
    (c + p) w → c w := And.left

/--
Updated context entails the update proposition.
-/
theorem update_entails (c : ContextSet W) (p : BProp W) :
    (c + p) ⊧ p := fun _ hw => hw.2

/--
Updating with what's already entailed doesn't change the context.
-/
theorem update_entailed (c : ContextSet W) (p : BProp W) (h : c ⊧ p) :
    (c + p) = c := by
  funext w
  unfold update
  exact propext ⟨And.left, fun hw => ⟨hw, h w hw⟩⟩

/--
Sequential updates are associative.
-/
theorem update_assoc (c : ContextSet W) (p q : BProp W) :
    ((c + p) + q) = fun w => c w ∧ p w = true ∧ q w = true := by
  funext w
  simp only [update, and_assoc]

-- ============================================================================
-- PART 4: Intersection and Union of Contexts
-- ============================================================================

/--
Intersection of contexts: worlds in both.
-/
def inter (c₁ c₂ : ContextSet W) : ContextSet W :=
  fun w => c₁ w ∧ c₂ w

/--
Union of contexts: worlds in either.
-/
def union (c₁ c₂ : ContextSet W) : ContextSet W :=
  fun w => c₁ w ∨ c₂ w

instance : Inter (ContextSet W) where
  inter := inter

instance : Union (ContextSet W) where
  union := union

-- ============================================================================
-- PART 5: Context from Proposition
-- ============================================================================

/--
Create a context from a single proposition: worlds where it holds.
-/
def fromProp (p : BProp W) : ContextSet W :=
  fun w => p w = true

/--
Updating trivial context with P gives context from P.
-/
theorem trivial_update (p : BProp W) : (trivial + p) = fromProp p := by
  funext w
  simp only [update, trivial, fromProp, true_and]

-- ============================================================================
-- PART 6: Monotonicity Properties
-- ============================================================================

/--
Entailment is monotonic: smaller context entails more.
-/
theorem entails_mono (c₁ c₂ : ContextSet W) (p : BProp W)
    (h_sub : ∀ w, c₁ w → c₂ w) (h_ent : c₂ ⊧ p) : c₁ ⊧ p :=
  fun w hw => h_ent w (h_sub w hw)

/--
Update is monotonic in the context.
-/
theorem update_mono (c₁ c₂ : ContextSet W) (p : BProp W)
    (h : ∀ w, c₁ w → c₂ w) (w : W) :
    (c₁ + p) w → (c₂ + p) w := fun ⟨hw, hp⟩ => ⟨h w hw, hp⟩

end ContextSet

-- ============================================================================
-- PART 7: Common Ground as Proposition Set (Alternative View)
-- ============================================================================

/--
The common ground can also be viewed as a set of propositions
(those mutually believed). This is the intensional view.

The context set is the intersection of all these propositions.
-/
structure CG (W : Type*) where
  /-- The propositions in the common ground -/
  propositions : List (BProp W)

namespace CG

variable {W : Type*}

/--
The context set determined by a common ground: worlds where
all CG propositions hold.
-/
def contextSet (cg : CG W) : ContextSet W :=
  fun w => cg.propositions.all (fun p => p w)

/--
Add a proposition to the common ground.
-/
def add (cg : CG W) (p : BProp W) : CG W :=
  { propositions := p :: cg.propositions }

/--
Empty common ground (no shared beliefs).
-/
def empty : CG W := { propositions := [] }

/--
Empty CG gives trivial context set.
-/
theorem empty_contextSet : (empty : CG W).contextSet = ContextSet.trivial := by
  funext w
  simp only [contextSet, empty, ContextSet.trivial, List.all_nil]

/--
Adding a proposition restricts the context set.
-/
theorem add_restricts (cg : CG W) (p : BProp W) (w : W) :
    (cg.add p).contextSet w → cg.contextSet w := by
  simp only [contextSet, add, List.all_cons, Bool.and_eq_true]
  exact And.right

end CG

-- ============================================================================
-- SUMMARY
-- ============================================================================

/-
## What This Module Provides

### Context Set
- `ContextSet W`: Predicate on worlds (characteristic function)
- `trivial`, `absurd`: Boundary cases
- `mem`, `nonEmpty`: Membership predicates

### Entailment
- `entails`: Context entails proposition (all worlds satisfy it)
- `compatible`: Proposition compatible with context

### Context Update
- `update`: Stalnaker's update (intersection with proposition)
- `update_entails`: Updated context entails the proposition
- `update_entailed`: Redundant update is identity

### Common Ground (Proposition Set View)
- `CG`: List of shared propositions
- `contextSet`: Derived context set
- `add`: Add proposition to CG

### Connection to Other Modules
- `Core.Proposition`: BProp type
- `Core.QUD`: Questions partition the context set
- `Core.Presupposition`: Presuppositions as felicity conditions
- `Theories.RSA`: Shared beliefs / world priors
-/

end Core.CommonGround
