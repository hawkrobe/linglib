/-
# Propositions as World-Dependent Truth Values

Theory-neutral infrastructure for modeling propositions in formal semantics.

## Two Flavors

1. **Prop' W** — Propositions as sets of worlds (W → Prop)
   - Standard in formal semantics literature (Montague, Heim & Kratzer)
   - Natural for existential/universal statements in proofs
   - Use for: NeoGricean exhaustivity, theoretical semantics

2. **BProp W** — Decidable propositions (W → Bool)
   - Needed for computation (probability, enumeration)
   - Works with `native_decide`, `DecidableEq`
   - Use for: RSA, decidable entailment checking

## Coercion

BProp coerces to Prop' via `p w = true`, so you can use decidable
propositions wherever classical ones are expected.

## References

- Montague (1973). The proper treatment of quantification in ordinary English.
- Lewis (1986). On the Plurality of Worlds.
- Heim & Kratzer (1998). Semantics in Generative Grammar.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Monotone.Basic

namespace Core.Proposition

-- ============================================================================
-- The Two Proposition Types
-- ============================================================================

/-- Classical propositions: sets of worlds (standard formal semantics)

In the formal semantics tradition, a proposition is identified with the
set of possible worlds where it is true. This type captures that:
`Prop' W` is a function assigning to each world `w : W` a truth value
(as a Lean `Prop`).
-/
abbrev Prop' (W : Type*) := W → Prop

/-- Decidable propositions: for computation

Like `Prop'`, but with `Bool` instead of `Prop`. This enables:
- Decidable equality and entailment checking
- Use with `native_decide`
- Probability computations (RSA)
-/
abbrev BProp (W : Type*) := W → Bool

/-- Coercion from decidable to classical propositions -/
instance bpropToProp' (W : Type*) : Coe (BProp W) (Prop' W) where
  coe p := λ w => p w = true

-- ============================================================================
-- Operations on Prop' (Classical)
-- ============================================================================

namespace Classical

/-- Propositional negation -/
def pnot (W : Type*) (p : Prop' W) : Prop' W := λ w => ¬(p w)

/-- Propositional conjunction -/
def pand (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w ∧ q w

/-- Propositional disjunction -/
def por (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w ∨ q w

/-- Propositional implication -/
def pimp (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w → q w

/-- Semantic entailment: p entails q iff q is true whenever p is true -/
def entails (W : Type*) (p q : Prop' W) : Prop := ∀ w, p w → q w

/-- Propositional equivalence -/
def equiv (W : Type*) (p q : Prop' W) : Prop := entails W p q ∧ entails W q p

/-- Grand conjunction: true at w iff all propositions in X are true at w -/
def bigConj (W : Type*) (X : Set (Prop' W)) : Prop' W := λ w => ∀ φ ∈ X, φ w

/-- Grand disjunction: true at w iff some proposition in X is true at w -/
def bigDisj (W : Type*) (X : Set (Prop' W)) : Prop' W := λ w => ∃ φ ∈ X, φ w

/-- Consistency: some world satisfies all propositions in X -/
def consistent (W : Type*) (X : Set (Prop' W)) : Prop := ∃ w, ∀ φ ∈ X, φ w

/-- The always-true proposition -/
def top (W : Type*) : Prop' W := λ _ => True

/-- The always-false proposition -/
def bot (W : Type*) : Prop' W := λ _ => False

-- Basic theorems

theorem entails_refl (W : Type*) (p : Prop' W) : entails W p p := λ_ h => h

theorem entails_trans (W : Type*) (p q r : Prop' W)
    (hpq : entails W p q) (hqr : entails W q r) : entails W p r :=
  λw hp => hqr w (hpq w hp)

theorem equiv_refl (W : Type*) (p : Prop' W) : equiv W p p :=
  ⟨entails_refl W p, entails_refl W p⟩

theorem equiv_symm (W : Type*) (p q : Prop' W) (h : equiv W p q) : equiv W q p :=
  ⟨h.2, h.1⟩

theorem pnot_pnot (W : Type*) (p : Prop' W) : entails W p (pnot W (pnot W p)) :=
  λ_ hp hnp => hnp hp

-- ============================================================================
-- BooleanAlgebra Correspondence
-- ============================================================================

/-
Prop' W = W → Prop inherits BooleanAlgebra from Mathlib's Pi instance:
  Pi.instBooleanAlgebra + Prop.instBooleanAlgebraProp

Our operations correspond exactly to the algebraic operations:
  pand  ↔  ⊓ (inf)
  por   ↔  ⊔ (sup)
  pnot  ↔  ᶜ (compl)
  entails ↔ ≤
-/

/-- Conjunction equals infimum in the lattice -/
theorem pand_eq_inf (W : Type*) (p q : Prop' W) : pand W p q = p ⊓ q := rfl

/-- Disjunction equals supremum in the lattice -/
theorem por_eq_sup (W : Type*) (p q : Prop' W) : por W p q = p ⊔ q := rfl

/-- Negation equals complement in the Boolean algebra -/
theorem pnot_eq_compl (W : Type*) (p : Prop' W) : pnot W p = pᶜ := rfl

/-- Entailment equals the lattice ordering -/
theorem entails_eq_le (W : Type*) (p q : Prop' W) : entails W p q ↔ p ≤ q := Iff.rfl

/-- Top equals lattice top -/
theorem top_eq_latticeTop (W : Type*) : top W = (⊤ : Prop' W) := rfl

/-- Bot equals lattice bot -/
theorem bot_eq_latticeBot (W : Type*) : bot W = (⊥ : Prop' W) := rfl

end Classical

-- ============================================================================
-- Operations on BProp (Decidable)
-- ============================================================================

namespace Decidable

/-- Propositional negation -/
def pnot (W : Type*) (p : BProp W) : BProp W := λ w => !p w

/-- Propositional conjunction -/
def pand (W : Type*) (p q : BProp W) : BProp W := λ w => p w && q w

/-- Propositional disjunction -/
def por (W : Type*) (p q : BProp W) : BProp W := λ w => p w || q w

/-- The always-true proposition -/
def top (W : Type*) : BProp W := λ _ => true

/-- The always-false proposition -/
def bot (W : Type*) : BProp W := λ _ => false

/-- Decidable entailment given explicit world enumeration -/
def entails (W : Type*) (worlds : List W) (p q : BProp W) : Bool :=
  worlds.all λ w => !p w || q w

/-- Decidable equivalence given explicit world enumeration -/
def equiv (W : Type*) (worlds : List W) (p q : BProp W) : Bool :=
  entails W worlds p q && entails W worlds q p

/-- Decidable consistency: is there a world satisfying all propositions? -/
def consistent (W : Type*) (worlds : List W) (ps : List (BProp W)) : Bool :=
  worlds.any λ w => ps.all λp => p w

/-- Count worlds satisfying a proposition -/
def count (W : Type*) (worlds : List W) (p : BProp W) : Nat :=
  worlds.filter p |>.length

/-- Get all worlds satisfying a proposition -/
def filter (W : Type*) (worlds : List W) (p : BProp W) : List W :=
  worlds.filter p

-- ============================================================================
-- BooleanAlgebra Correspondence for Bool
-- ============================================================================

/-
BProp W = W → Bool also inherits BooleanAlgebra from:
  Pi.instBooleanAlgebra + Bool.instBooleanAlgebraBool
-/

/-- Conjunction equals infimum in the Bool lattice -/
theorem pand_eq_inf (W : Type*) (p q : BProp W) : pand W p q = p ⊓ q := rfl

/-- Disjunction equals supremum in the Bool lattice -/
theorem por_eq_sup (W : Type*) (p q : BProp W) : por W p q = p ⊔ q := rfl

/-- Negation equals complement in the Bool Boolean algebra -/
theorem pnot_eq_compl (W : Type*) (p : BProp W) : pnot W p = pᶜ := rfl

/-- Top equals lattice top -/
theorem top_eq_latticeTop (W : Type*) : top W = (⊤ : BProp W) := rfl

/-- Bot equals lattice bot -/
theorem bot_eq_latticeBot (W : Type*) : bot W = (⊥ : BProp W) := rfl

-- ============================================================================
-- Downward Entailing Property of Negation
-- ============================================================================

/--
**Negation reverses entailment (DE property)**.

If P entails Q at all worlds (∀w, P w → Q w), then ¬Q entails ¬P.
This is the defining property of Downward Entailing operators.

This theorem is used by:
- RSA models (HeKaiserIskarous2025) for polarity asymmetries
- NeoGricean implicature computation for DE context detection
- Montague entailment checking
-/
theorem pnot_reverses_entailment {W : Type*} (p q : BProp W)
    (h : ∀ w, p w = true → q w = true) :
    ∀ w, pnot W q w = true → pnot W p w = true := by
  intro w hnq
  simp only [pnot] at *
  cases hp : p w with
  | false => simp
  | true =>
    have hq := h w hp
    simp [hq] at hnq

/-- Double negation elimination for decidable propositions -/
theorem pnot_pnot {W : Type*} (p : BProp W) : pnot W (pnot W p) = p := by
  funext w
  simp [pnot, Bool.not_not]

/-- Negation is antitone (DE): if p ≤ q pointwise, then ¬q ≤ ¬p pointwise -/
theorem pnot_antitone {W : Type*} : Antitone (pnot W) := by
  intro p q hpq w
  simp only [pnot]
  -- Goal: !q w ≤ !p w (in Bool ordering: false ≤ true)
  -- hpq : p ≤ q means ∀w, p w ≤ q w
  have hpq_w := hpq w
  -- In Bool, x ≤ y means x = false ∨ y = true
  cases hp : p w <;> cases hq : q w <;> simp_all

end Decidable

-- ============================================================================
-- Correspondence: Decidable ↔ Classical
-- ============================================================================

/-
The coercion `BProp W → Prop' W` (via `p w = true`) preserves operations.
This means properties proven for `Decidable.pnot` transfer to `Classical.pnot`.
-/

/-- Decidable negation corresponds to Classical negation under coercion.

    (pnot_dec p : BProp W) coerces to (pnot_classical (p : Prop' W))
-/
theorem decidable_pnot_eq_classical {W : Type*} (p : BProp W) :
    (↑(Decidable.pnot W p) : Prop' W) = Classical.pnot W (↑p : Prop' W) := by
  funext w
  simp only [Decidable.pnot, Classical.pnot]
  -- Goal: (!p w = true) = ¬(p w = true)
  cases hp : p w <;> simp [hp]

/-- Decidable conjunction corresponds to Classical conjunction under coercion. -/
theorem decidable_pand_eq_classical {W : Type*} (p q : BProp W) :
    (↑(Decidable.pand W p q) : Prop' W) = Classical.pand W (↑p) (↑q) := by
  funext w
  simp only [Decidable.pand, Classical.pand]
  -- Goal: (p w && q w = true) = (p w = true ∧ q w = true)
  cases hp : p w <;> cases hq : q w <;> simp [hp, hq]

/-- Decidable disjunction corresponds to Classical disjunction under coercion. -/
theorem decidable_por_eq_classical {W : Type*} (p q : BProp W) :
    (↑(Decidable.por W p q) : Prop' W) = Classical.por W (↑p) (↑q) := by
  funext w
  simp only [Decidable.por, Classical.por]
  -- Goal: (p w || q w = true) = (p w = true ∨ q w = true)
  cases hp : p w <;> cases hq : q w <;> simp [hp, hq]

/--
**Transfer theorem**: DE property of `Decidable.pnot` implies DE for `Classical.pnot`.

If negation reverses entailment for decidable propositions,
it also reverses entailment for classical propositions (under the coercion).
-/
theorem classical_pnot_is_de {W : Type*} :
    ∀ (p q : BProp W), (∀ w, (↑p : Prop' W) w → (↑q : Prop' W) w) →
      ∀ w, Classical.pnot W (↑q) w → Classical.pnot W (↑p) w := by
  intro p q hpq w hnq hp
  simp only [Classical.pnot] at *
  have hpq_w := hpq w hp
  exact hnq hpq_w

-- ============================================================================
-- Notation
-- ============================================================================

-- We use scoped notation so users can choose which to import
-- Note: notation needs to work without explicit W parameter

namespace ClassicalNotation
  scoped prefix:75 "∼" => λp => Classical.pnot _ p
  scoped infixl:65 " ∧ₚ " => λp q => Classical.pand _ p q
  scoped infixl:60 " ∨ₚ " => λp q => Classical.por _ p q
  scoped infixr:55 " →ₚ " => λp q => Classical.pimp _ p q
  scoped notation:50 p " ⊆ₚ " q => Classical.entails _ p q
  scoped notation:50 p " ≡ₚ " q => Classical.equiv _ p q
  scoped notation "⋀" => λX => Classical.bigConj _ X
  scoped notation "⋁" => λX => Classical.bigDisj _ X
end ClassicalNotation

namespace DecidableNotation
  scoped prefix:75 "∼ᵇ" => λp => Decidable.pnot _ p
  scoped infixl:65 " ∧ᵇ " => λp q => Decidable.pand _ p q
  scoped infixl:60 " ∨ᵇ " => λp q => Decidable.por _ p q
end DecidableNotation

-- ============================================================================
-- Finite Worlds Typeclass
-- ============================================================================

/-- Typeclass for types with a complete enumeration of all elements.

This enables decidable operations on propositions without
explicitly passing the world list everywhere.
-/
class FiniteWorlds (W : Type*) where
  /-- List of all worlds -/
  worlds : List W
  /-- The list is complete -/
  complete : ∀ w : W, w ∈ worlds

namespace FiniteWorlds

/-- Decidable entailment using the FiniteWorlds instance -/
def entails (W : Type*) [FiniteWorlds W] (p q : BProp W) : Bool :=
  Decidable.entails W (FiniteWorlds.worlds) p q

/-- Decidable equivalence using the FiniteWorlds instance -/
def equiv (W : Type*) [FiniteWorlds W] (p q : BProp W) : Bool :=
  Decidable.equiv W (FiniteWorlds.worlds) p q

/-- Decidable consistency using the FiniteWorlds instance -/
def consistent (W : Type*) [FiniteWorlds W] (ps : List (BProp W)) : Bool :=
  Decidable.consistent W (FiniteWorlds.worlds) ps

/-- Count satisfying worlds -/
def count (W : Type*) [FiniteWorlds W] (p : BProp W) : Nat :=
  Decidable.count W (FiniteWorlds.worlds) p

/-- Filter satisfying worlds -/
def filter (W : Type*) [FiniteWorlds W] (p : BProp W) : List W :=
  Decidable.filter W (FiniteWorlds.worlds) p

end FiniteWorlds

-- ============================================================================
-- Soundness: Decidable operations agree with Classical
-- ============================================================================

/-- Decidable entailment is sound w.r.t. classical entailment -/
theorem entails_sound (W : Type*) [FiniteWorlds W] (p q : BProp W) :
    FiniteWorlds.entails W p q = true → Classical.entails W (↑p : Prop' W) ↑q := by
  intro h w hp
  simp only [FiniteWorlds.entails, Decidable.entails, List.all_eq_true] at h
  have hw := FiniteWorlds.complete w
  have := h w hw
  simp only [Bool.not_eq_true', Bool.or_eq_true] at this
  cases this with
  | inl hpf => simp_all
  | inr hqt => exact hqt

-- ============================================================================
-- Common World Types
-- ============================================================================

/-- A simple 4-world type for basic examples -/
inductive World4 where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds World4 where
  worlds := [.w0, .w1, .w2, .w3]
  complete := λ w => by cases w <;> simp

/-- A simple 2-world type (true/false worlds) -/
inductive World2 where
  | wT | wF
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds World2 where
  worlds := [.wT, .wF]
  complete := λ w => by cases w <;> simp

-- ============================================================================
-- Galois Connection: Proposition-World Semantic Duality
-- ============================================================================

/-!
## Galois Connection: Semantic Duality

The relationship between propositions and worlds exhibits a fundamental
**Galois connection** structure, which is the mathematical foundation of
possible worlds semantics.

Given:
- A set of propositions (ordered by reverse inclusion ⊇)
- A set of worlds (ordered by inclusion ⊆)

We have two antitone functions:
- **Extension**: ext(A) = ∩A = {w : ∀p ∈ A. p(w)} — worlds satisfying all props
- **Intension**: int(W) = {p : ∀w ∈ W. p(w)} — props true at all worlds

These form a Galois connection:
  ext(A) ⊆ W  ↔  A ⊇ int(W)

This duality underlies:
- Modal accessibility (Kratzer's modal base)
- Semantic entailment
- The □/◇ duality in modal logic

### References
- Birkhoff (1967). Lattice Theory.
- Ganter & Wille (1999). Formal Concept Analysis.
- Kratzer (1981). The Notional Category of Modality.
-/

namespace GaloisConnection

/-! ### Set-Based Version (for proofs) -/

/--
**Extension** (Set-based): Given propositions, compute the worlds where all hold.

ext(A) = {w : ∀p ∈ A. p(w)}

This is the "downward" direction of the Galois connection.
Adding more propositions shrinks the extension.
-/
def extension {W : Type*} (props : Set (Prop' W)) : Set W :=
  { w | ∀ p ∈ props, p w }

/--
**Intension** (Set-based): Given worlds, compute propositions true at all of them.

int(W) = {p : ∀w ∈ W. p(w)}

This is the "upward" direction of the Galois connection.
Fewer worlds means more propositions in the intension.
-/
def intension {W : Type*} (worlds : Set W) : Set (Prop' W) :=
  { p | ∀ w ∈ worlds, p w }

/--
**Extension is antitone**: More propositions → fewer worlds.

If A ⊆ B, then ext(B) ⊆ ext(A).
-/
theorem extension_antitone {W : Type*} :
    Antitone (extension (W := W)) := by
  intro A B hAB w hw p hpA
  exact hw p (hAB hpA)

/--
**Intension is antitone**: Fewer worlds → more propositions.

If W ⊆ V, then int(V) ⊆ int(W).
-/
theorem intension_antitone {W : Type*} :
    Antitone (intension (W := W)) := by
  intro V W hVW p hp w hw
  exact hp w (hVW hw)

/--
**Galois connection**: W ⊆ ext(A) ↔ A ⊆ int(W).

This is the fundamental adjunction of possible worlds semantics:
- If every world in W satisfies all propositions in A, then W ⊆ ext(A)
- If W ⊆ ext(A), then every proposition in A is true at every world in W

The two directions are `galois_right` and `galois_left` below.
-/
theorem galois_connection {W : Type*} (A : Set (Prop' W)) (Ws : Set W) :
    Ws ⊆ extension A ↔ A ⊆ intension Ws := by
  constructor
  · -- (→) If W ⊆ ext(A), then A ⊆ int(W)
    intro hWext p hpA w hwW
    exact hWext hwW p hpA
  · -- (←) If A ⊆ int(W), then W ⊆ ext(A)
    intro hAint w hwW p hpA
    exact hAint hpA w hwW

/--
**Galois connection (← direction)**: A ⊆ int(W) implies W ⊆ ext(A).
-/
theorem galois_right {W : Type*} (A : Set (Prop' W)) (Ws : Set W)
    (h : A ⊆ intension Ws) :
    Ws ⊆ extension A :=
  galois_connection A Ws |>.mpr h

/--
**Galois connection (→ direction)**: W ⊆ ext(A) implies A ⊆ int(W).
-/
theorem galois_left {W : Type*} (A : Set (Prop' W)) (Ws : Set W)
    (h : Ws ⊆ extension A) :
    A ⊆ intension Ws :=
  galois_connection A Ws |>.mp h

/--
**Closure property**: ext ∘ int is a closure operator.

ext(int(W)) ⊇ W — applying extension after intension expands the set.
-/
theorem closure_expanding {W : Type*} (Ws : Set W) :
    Ws ⊆ extension (intension Ws) := by
  intro w hw p hp
  exact hp w hw

/--
**Closure property**: int ∘ ext is a closure operator.

int(ext(A)) ⊇ A — applying intension after extension expands the set.
-/
theorem closure_expanding' {W : Type*} (A : Set (Prop' W)) :
    A ⊆ intension (extension A) := by
  intro p hp w hw
  exact hw p hp

/-! ### List-Based Version (for computation) -/

/--
**Extension** (List-based): Given propositions, compute worlds where all hold.

For decidable propositions with finite world enumeration.
-/
def extensionL {W : Type*} (worlds : List W) (props : List (BProp W)) : List W :=
  worlds.filter fun w => props.all fun p => p w

/--
**Intension** (List-based): Given worlds, filter propositions true at all of them.

Takes a universe of propositions to filter from.
-/
def intensionL {W : Type*} (worlds : List W) (props : List (BProp W)) : List (BProp W) :=
  props.filter fun p => worlds.all p

/--
**Extension is antitone** (List version): More propositions → fewer worlds.
-/
theorem extensionL_antitone {W : Type*} (worlds : List W)
    (A B : List (BProp W)) (w : W)
    (hSub : ∀ p, p ∈ A → p ∈ B)
    (hw : w ∈ extensionL worlds B) :
    w ∈ extensionL worlds A := by
  simp only [extensionL, List.mem_filter, List.all_eq_true] at *
  constructor
  · exact hw.1
  · intro p hp
    exact hw.2 p (hSub p hp)

/--
**Intension is antitone** (List version): Fewer worlds → more propositions.
-/
theorem intensionL_antitone {W : Type*} (props : List (BProp W))
    (W1 W2 : List W) (p : BProp W)
    (hSub : ∀ w, w ∈ W1 → w ∈ W2)
    (hp : p ∈ intensionL W2 props) :
    p ∈ intensionL W1 props := by
  simp only [intensionL, List.mem_filter, List.all_eq_true] at *
  constructor
  · exact hp.1
  · intro w hw
    exact hp.2 w (hSub w hw)

/--
**Closure expanding** (List version): W ⊆ ext(int(W, props), props).

Every world in W is in the extension of its intension.
-/
theorem closureL_expanding {W : Type*} (allWorlds : List W) (props : List (BProp W))
    (Ws : List W) (hWs : ∀ w ∈ Ws, w ∈ allWorlds)
    (w : W) (hw : w ∈ Ws) :
    w ∈ extensionL allWorlds (intensionL Ws props) := by
  simp only [extensionL, intensionL, List.mem_filter, List.all_eq_true]
  constructor
  · exact hWs w hw
  · intro p ⟨_, hp_all⟩
    exact hp_all w hw

/--
**FiniteWorlds version of extension**.
-/
def extensionFW (W : Type*) [FiniteWorlds W] (props : List (BProp W)) : List W :=
  extensionL FiniteWorlds.worlds props

/--
**FiniteWorlds version of intension**.
-/
def intensionFW (W : Type*) [FiniteWorlds W] (worlds : List W) (props : List (BProp W)) : List (BProp W) :=
  intensionL worlds props

end GaloisConnection

end Core.Proposition
