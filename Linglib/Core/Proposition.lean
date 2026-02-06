import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Proposition

Theory-neutral infrastructure for modeling propositions in formal semantics.
`Prop' W` is classical (W → Prop); `BProp W` is decidable (W → Bool).
-/

namespace Core.Proposition

/-- Classical propositions: sets of worlds (standard formal semantics). -/
abbrev Prop' (W : Type*) := W → Prop

/-- Decidable propositions: for computation. -/
abbrev BProp (W : Type*) := W → Bool

/-- Coercion from decidable to classical propositions. -/
instance bpropToProp' (W : Type*) : Coe (BProp W) (Prop' W) where
  coe p := λ w => p w = true

namespace Classical

/-- Propositional negation. -/
def pnot (W : Type*) (p : Prop' W) : Prop' W := λ w => ¬(p w)

/-- Propositional conjunction. -/
def pand (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w ∧ q w

/-- Propositional disjunction. -/
def por (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w ∨ q w

/-- Propositional implication. -/
def pimp (W : Type*) (p q : Prop' W) : Prop' W := λ w => p w → q w

/-- Semantic entailment: p entails q iff q is true whenever p is true. -/
def entails (W : Type*) (p q : Prop' W) : Prop := ∀ w, p w → q w

/-- Propositional equivalence. -/
def equiv (W : Type*) (p q : Prop' W) : Prop := entails W p q ∧ entails W q p

/-- Grand conjunction: true at w iff all propositions in X are true at w. -/
def bigConj (W : Type*) (X : Set (Prop' W)) : Prop' W := λ w => ∀ φ ∈ X, φ w

/-- Grand disjunction: true at w iff some proposition in X is true at w. -/
def bigDisj (W : Type*) (X : Set (Prop' W)) : Prop' W := λ w => ∃ φ ∈ X, φ w

/-- Consistency: some world satisfies all propositions in X. -/
def consistent (W : Type*) (X : Set (Prop' W)) : Prop := ∃ w, ∀ φ ∈ X, φ w

/-- The always-true proposition. -/
def top (W : Type*) : Prop' W := λ _ => True

/-- The always-false proposition. -/
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

/-- Conjunction equals infimum in the lattice. -/
theorem pand_eq_inf (W : Type*) (p q : Prop' W) : pand W p q = p ⊓ q := rfl

/-- Disjunction equals supremum in the lattice. -/
theorem por_eq_sup (W : Type*) (p q : Prop' W) : por W p q = p ⊔ q := rfl

/-- Negation equals complement in the Boolean algebra. -/
theorem pnot_eq_compl (W : Type*) (p : Prop' W) : pnot W p = pᶜ := rfl

/-- Entailment equals the lattice ordering. -/
theorem entails_eq_le (W : Type*) (p q : Prop' W) : entails W p q ↔ p ≤ q := Iff.rfl

/-- Top equals lattice top. -/
theorem top_eq_latticeTop (W : Type*) : top W = (⊤ : Prop' W) := rfl

/-- Bot equals lattice bot. -/
theorem bot_eq_latticeBot (W : Type*) : bot W = (⊥ : Prop' W) := rfl

end Classical

namespace Decidable

/-- Propositional negation. -/
def pnot (W : Type*) (p : BProp W) : BProp W := λ w => !p w

/-- Propositional conjunction. -/
def pand (W : Type*) (p q : BProp W) : BProp W := λ w => p w && q w

/-- Propositional disjunction. -/
def por (W : Type*) (p q : BProp W) : BProp W := λ w => p w || q w

/-- The always-true proposition. -/
def top (W : Type*) : BProp W := λ _ => true

/-- The always-false proposition. -/
def bot (W : Type*) : BProp W := λ _ => false

/-- Decidable entailment given explicit world enumeration. -/
def entails (W : Type*) (worlds : List W) (p q : BProp W) : Bool :=
  worlds.all λ w => !p w || q w

/-- Decidable equivalence given explicit world enumeration. -/
def equiv (W : Type*) (worlds : List W) (p q : BProp W) : Bool :=
  entails W worlds p q && entails W worlds q p

/-- Decidable consistency: is there a world satisfying all propositions? -/
def consistent (W : Type*) (worlds : List W) (ps : List (BProp W)) : Bool :=
  worlds.any λ w => ps.all λp => p w

/-- Count worlds satisfying a proposition. -/
def count (W : Type*) (worlds : List W) (p : BProp W) : Nat :=
  worlds.filter p |>.length

/-- Get all worlds satisfying a proposition. -/
def filter (W : Type*) (worlds : List W) (p : BProp W) : List W :=
  worlds.filter p

/-- Conjunction equals infimum in the Bool lattice. -/
theorem pand_eq_inf (W : Type*) (p q : BProp W) : pand W p q = p ⊓ q := rfl

/-- Disjunction equals supremum in the Bool lattice. -/
theorem por_eq_sup (W : Type*) (p q : BProp W) : por W p q = p ⊔ q := rfl

/-- Negation equals complement in the Bool Boolean algebra. -/
theorem pnot_eq_compl (W : Type*) (p : BProp W) : pnot W p = pᶜ := rfl

/-- Top equals lattice top. -/
theorem top_eq_latticeTop (W : Type*) : top W = (⊤ : BProp W) := rfl

/-- Bot equals lattice bot. -/
theorem bot_eq_latticeBot (W : Type*) : bot W = (⊥ : BProp W) := rfl

/-- Negation reverses entailment (DE property). -/
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

/-- Double negation elimination for decidable propositions. -/
theorem pnot_pnot {W : Type*} (p : BProp W) : pnot W (pnot W p) = p := by
  funext w
  simp [pnot, Bool.not_not]

/-- Negation is antitone (DE): if p ≤ q pointwise, then ¬q ≤ ¬p pointwise. -/
theorem pnot_antitone {W : Type*} : Antitone (pnot W) := by
  intro p q hpq w
  simp only [pnot]
  -- Goal: !q w ≤ !p w (in Bool ordering: false ≤ true)
  -- hpq : p ≤ q means ∀w, p w ≤ q w
  have hpq_w := hpq w
  -- In Bool, x ≤ y means x = false ∨ y = true
  cases hp : p w <;> cases hq : q w <;> simp_all

end Decidable

/-- Decidable negation corresponds to Classical negation under coercion. -/
theorem decidable_pnot_eq_classical {W : Type*} (p : BProp W) :
    (↑(Decidable.pnot W p) : Prop' W) = Classical.pnot W (↑p : Prop' W) := by
  funext w
  simp only [Decidable.pnot, Classical.pnot]
  -- Goal: (!p w = true) = ¬(p w = true)
  cases hp : p w <;> simp [hp]

/-- Decidable conjunction corresponds to Classical conjunction. -/
theorem decidable_pand_eq_classical {W : Type*} (p q : BProp W) :
    (↑(Decidable.pand W p q) : Prop' W) = Classical.pand W (↑p) (↑q) := by
  funext w
  simp only [Decidable.pand, Classical.pand]
  -- Goal: (p w && q w = true) = (p w = true ∧ q w = true)
  cases hp : p w <;> cases hq : q w <;> simp [hp, hq]

/-- Decidable disjunction corresponds to Classical disjunction. -/
theorem decidable_por_eq_classical {W : Type*} (p q : BProp W) :
    (↑(Decidable.por W p q) : Prop' W) = Classical.por W (↑p) (↑q) := by
  funext w
  simp only [Decidable.por, Classical.por]
  -- Goal: (p w || q w = true) = (p w = true ∨ q w = true)
  cases hp : p w <;> cases hq : q w <;> simp [hp, hq]

/-- Transfer theorem: DE property of `Decidable.pnot` implies DE for `Classical.pnot`. -/
theorem classical_pnot_is_de {W : Type*} :
    ∀ (p q : BProp W), (∀ w, (↑p : Prop' W) w → (↑q : Prop' W) w) →
      ∀ w, Classical.pnot W (↑q) w → Classical.pnot W (↑p) w := by
  intro p q hpq w hnq hp
  simp only [Classical.pnot] at *
  have hpq_w := hpq w hp
  exact hnq hpq_w

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

/-- Typeclass for types with a complete enumeration of all elements. -/
class FiniteWorlds (W : Type*) where
  /-- List of all worlds -/
  worlds : List W
  /-- The list is complete -/
  complete : ∀ w : W, w ∈ worlds

namespace FiniteWorlds

/-- Decidable entailment using the FiniteWorlds instance. -/
def entails (W : Type*) [FiniteWorlds W] (p q : BProp W) : Bool :=
  Decidable.entails W (FiniteWorlds.worlds) p q

/-- Decidable equivalence using the FiniteWorlds instance. -/
def equiv (W : Type*) [FiniteWorlds W] (p q : BProp W) : Bool :=
  Decidable.equiv W (FiniteWorlds.worlds) p q

/-- Decidable consistency using the FiniteWorlds instance. -/
def consistent (W : Type*) [FiniteWorlds W] (ps : List (BProp W)) : Bool :=
  Decidable.consistent W (FiniteWorlds.worlds) ps

/-- Count satisfying worlds. -/
def count (W : Type*) [FiniteWorlds W] (p : BProp W) : Nat :=
  Decidable.count W (FiniteWorlds.worlds) p

/-- Filter satisfying worlds. -/
def filter (W : Type*) [FiniteWorlds W] (p : BProp W) : List W :=
  Decidable.filter W (FiniteWorlds.worlds) p

/-- Build a `FiniteWorlds` instance from `Fintype` + `DecidableEq`.
Bridges the Mathlib `Fintype` convention (used by 26+ RSA files) to
the linglib `FiniteWorlds` convention (used by 47+ files). -/
noncomputable def ofFintype {W : Type*} [Fintype W] [DecidableEq W] : FiniteWorlds W where
  worlds := Fintype.elems.val.toList.eraseDups
  -- TODO: prove completeness from Fintype.complete + List.mem_eraseDups
  complete := sorry

/-- Convert a `FiniteWorlds` instance to `Fintype`.
Bridges in the other direction: linglib `FiniteWorlds` → Mathlib `Fintype`.
TODO: The `Nodup` obligation requires deduplication; the membership proof
follows from `FiniteWorlds.complete`. -/
noncomputable def toFintype {W : Type*} [fw : FiniteWorlds W] : Fintype W :=
  sorry

end FiniteWorlds

/-- Decidable entailment is sound w.r.t. classical entailment. -/
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

/-- A simple 4-world type for basic examples. -/
inductive World4 where
  | w0 | w1 | w2 | w3
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds World4 where
  worlds := [.w0, .w1, .w2, .w3]
  complete := λ w => by cases w <;> simp

/-- A simple 2-world type (true/false worlds). -/
inductive World2 where
  | wT | wF
  deriving DecidableEq, BEq, Repr, Inhabited

instance : FiniteWorlds World2 where
  worlds := [.wT, .wF]
  complete := λ w => by cases w <;> simp

namespace GaloisConnection

/-- Extension (Set-based): compute the worlds where all propositions hold. -/
def extension {W : Type*} (props : Set (Prop' W)) : Set W :=
  { w | ∀ p ∈ props, p w }

/-- Intension (Set-based): compute propositions true at all given worlds. -/
def intension {W : Type*} (worlds : Set W) : Set (Prop' W) :=
  { p | ∀ w ∈ worlds, p w }

/-- Extension is antitone: more propositions → fewer worlds. -/
theorem extension_antitone {W : Type*} :
    Antitone (extension (W := W)) := by
  intro A B hAB w hw p hpA
  exact hw p (hAB hpA)

/-- Intension is antitone: fewer worlds → more propositions. -/
theorem intension_antitone {W : Type*} :
    Antitone (intension (W := W)) := by
  intro V W hVW p hp w hw
  exact hp w (hVW hw)

/-- Galois connection: W ⊆ ext(A) ↔ A ⊆ int(W). -/
theorem galois_connection {W : Type*} (A : Set (Prop' W)) (Ws : Set W) :
    Ws ⊆ extension A ↔ A ⊆ intension Ws := by
  constructor
  · -- (→) If W ⊆ ext(A), then A ⊆ int(W)
    intro hWext p hpA w hwW
    exact hWext hwW p hpA
  · -- (←) If A ⊆ int(W), then W ⊆ ext(A)
    intro hAint w hwW p hpA
    exact hAint hpA w hwW

/-- Galois connection (← direction): A ⊆ int(W) implies W ⊆ ext(A). -/
theorem galois_right {W : Type*} (A : Set (Prop' W)) (Ws : Set W)
    (h : A ⊆ intension Ws) :
    Ws ⊆ extension A :=
  galois_connection A Ws |>.mpr h

/-- Galois connection (→ direction): W ⊆ ext(A) implies A ⊆ int(W). -/
theorem galois_left {W : Type*} (A : Set (Prop' W)) (Ws : Set W)
    (h : Ws ⊆ extension A) :
    A ⊆ intension Ws :=
  galois_connection A Ws |>.mp h

/-- Closure property: ext(int(W)) ⊇ W. -/
theorem closure_expanding {W : Type*} (Ws : Set W) :
    Ws ⊆ extension (intension Ws) := by
  intro w hw p hp
  exact hp w hw

/-- Closure property: int(ext(A)) ⊇ A. -/
theorem closure_expanding' {W : Type*} (A : Set (Prop' W)) :
    A ⊆ intension (extension A) := by
  intro p hp w hw
  exact hw p hp

/-- Extension (List-based): compute worlds where all propositions hold. -/
def extensionL {W : Type*} (worlds : List W) (props : List (BProp W)) : List W :=
  worlds.filter λ w => props.all λ p => p w

/-- Intension (List-based): filter propositions true at all given worlds. -/
def intensionL {W : Type*} (worlds : List W) (props : List (BProp W)) : List (BProp W) :=
  props.filter λ p => worlds.all p

/-- Extension is antitone (List version). -/
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

/-- Intension is antitone (List version). -/
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

/-- Closure expanding (List version). -/
theorem closureL_expanding {W : Type*} (allWorlds : List W) (props : List (BProp W))
    (Ws : List W) (hWs : ∀ w ∈ Ws, w ∈ allWorlds)
    (w : W) (hw : w ∈ Ws) :
    w ∈ extensionL allWorlds (intensionL Ws props) := by
  simp only [extensionL, intensionL, List.mem_filter, List.all_eq_true]
  constructor
  · exact hWs w hw
  · intro p ⟨_, hp_all⟩
    exact hp_all w hw

/-- FiniteWorlds version of extension. -/
def extensionFW (W : Type*) [FiniteWorlds W] (props : List (BProp W)) : List W :=
  extensionL FiniteWorlds.worlds props

/-- FiniteWorlds version of intension. -/
def intensionFW (W : Type*) [FiniteWorlds W] (worlds : List W) (props : List (BProp W)) : List (BProp W) :=
  intensionL worlds props

end GaloisConnection

end Core.Proposition
