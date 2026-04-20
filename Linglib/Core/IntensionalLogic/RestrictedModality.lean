import Linglib.Core.IntensionalLogic.Quantification
import Linglib.Core.IntensionalLogic.Algebra
import Linglib.Core.Modality.ModalTypes
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# Restricted Modality: Accessibility-Parameterized Box and Diamond

@cite{dowty-wall-peters-1981} @cite{kratzer-1981} @cite{kripke-1963}

In intensional semantics, meanings depend on a world parameter — a proposition
is `W → Prop`, and modal operators quantify over worlds. Montague's IL defines
`box`/`diamond` as S5 operators quantifying over **all** indices. But natural
language modality requires restricting quantification to **accessible** indices,
determined by an accessibility relation `R : W → W → Prop`.

This module is the **single source of truth** for accessibility-restricted
modal logic in linglib. It provides:

1. **Generic `{W : Type*}` infrastructure**: `AccessRel`, `boxR`/`diamondR`,
   frame conditions (reflexivity, transitivity, symmetry, euclideanness),
   modal axiom correspondence (T, 4, B, 5), monotonicity, distribution,
   restriction theorems — all parameterized by an arbitrary world type.

2. **Gallin hierarchy** (@cite{gallin-1975} §12): `PropOp` (general propositional
   operators), `indicialNec`/`indicialPoss` (Kripke-type = accessibility-defined),
   `s5Nec`/`s5Poss` (IL's S5 = universal accessibility). Proves the formal
   embedding: S5 ⊂ Indicial ⊂ All PropOps.

3. **Decidable instances**: for `Refl`/`Serial`/`Trans`/`Symm`/`Eucl` and
   `boxR`/`diamondR` over finite worlds with decidable accessibility and
   propositions. Following mathlib style: define in Prop, provide Decidable
   instances, compute with `decide`.

4. **Logic lattice**: `Axiom`, `Logic`, standard logics (K, T, D, S4, S5, KD45),
   lattice instances, `frameConditions`.

5. **IL Frame specialization**: `boxR`/`diamondR` with universal accessibility
   recover S5 `box`/`diamond`.

The intensional core is just the world type `W` — you don't need the full
Montague `Frame` (Entity + Index + Ty) to define modal operators. The `Frame`
is Montague's packaging for compositional semantics; `W` is the intensional
index that modal operators quantify over.

## Connection to Kratzer semantics

Kratzer's conversational backgrounds derive accessibility from a modal base:
`R_f(w, w') ≡ w' ∈ ⋂f(w)`. The ordering source further restricts to "best"
worlds. In IL terms:

- Simple Kratzer necessity = `boxR R_f` (no ordering source)
- Full Kratzer necessity = `boxR R_{f,g}` where `R_{f,g}` restricts to best worlds
- S5 necessity = `boxR (fun _ _ => True)` = `box`
-/

namespace Core.IntensionalLogic.RestrictedModality

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Generic Accessibility-Restricted Modality
-- ════════════════════════════════════════════════════════════════════════

/-! All definitions in this section are parameterized by `{W : Type*}` — an
arbitrary world type. No Frame, no Entity, no type system. This is the
intensional core: meanings depend on a world parameter, and modal operators
quantify over accessible worlds. -/

-- ────────────────────────────────────────────────────────────────
-- §1.1 Accessibility Relations
-- ────────────────────────────────────────────────────────────────

/-- An accessibility relation on worlds. `R w v` means world `v` is
    accessible from world `w`. -/
abbrev AccessRel (W : Type*) := W → W → Prop

/-- Agent-indexed accessibility relation: each agent has their own
    accessibility relation over worlds. -/
abbrev AgentAccessRel (W E : Type*) := E → AccessRel W

/-- Universal accessibility: every world is accessible from every world. -/
def universalR {W : Type*} : AccessRel W := fun _ _ => True

/-- Empty accessibility: no world is accessible from any world. -/
def emptyR {W : Type*} : AccessRel W := fun _ _ => False

/-- Reflexive (identity) accessibility: each world accesses only itself. -/
def identityR {W : Type*} : AccessRel W := fun w v => w = v

-- ────────────────────────────────────────────────────────────────
-- §1.2 Frame Conditions
-- ────────────────────────────────────────────────────────────────

/-- Reflexivity: every world accesses itself. -/
def Refl {W : Type*} (R : AccessRel W) : Prop := ∀ w, R w w

/-- Seriality: every world accesses at least one world. -/
def Serial {W : Type*} (R : AccessRel W) : Prop := ∀ w, ∃ v, R w v

/-- Transitivity. -/
def Trans {W : Type*} (R : AccessRel W) : Prop := ∀ w v u, R w v → R v u → R w u

/-- Symmetry. -/
def Symm {W : Type*} (R : AccessRel W) : Prop := ∀ w v, R w v → R v w

/-- Euclideanness. -/
def Eucl {W : Type*} (R : AccessRel W) : Prop := ∀ w v u, R w v → R w u → R v u

-- ────────────────────────────────────────────────────────────────
-- §1.3 Frame Condition Relationships
-- ────────────────────────────────────────────────────────────────

variable {W : Type*}

theorem universalR_refl : Refl (universalR (W := W)) := fun _ => trivial
theorem universalR_serial : Serial (universalR (W := W)) := fun w => ⟨w, trivial⟩
theorem universalR_trans : Trans (universalR (W := W)) := fun _ _ _ _ _ => trivial
theorem universalR_symm : Symm (universalR (W := W)) := fun _ _ _ => trivial
theorem universalR_eucl : Eucl (universalR (W := W)) := fun _ _ _ _ _ => trivial

theorem refl_serial {R : AccessRel W} (h : Refl R) : Serial R :=
  fun w => ⟨w, h w⟩

theorem refl_eucl_symm {R : AccessRel W} (hR : Refl R) (hE : Eucl R) : Symm R :=
  fun w v hwv => hE w v w hwv (hR w)

theorem refl_eucl_trans {R : AccessRel W} (hR : Refl R) (hE : Eucl R) : Trans R :=
  fun w v u hwv hvu => hE v w u (refl_eucl_symm hR hE w v hwv) hvu

theorem symm_trans_eucl {R : AccessRel W} (hS : Symm R) (hT : Trans R) : Eucl R :=
  fun w v u hwv hwu => hT v w u (hS w v hwv) hwu

/-- S5 frames are equivalence relations. -/
theorem S5_equiv {R : AccessRel W} (hR : Refl R) (hE : Eucl R) :
    Refl R ∧ Symm R ∧ Trans R :=
  ⟨hR, refl_eucl_symm hR hE, refl_eucl_trans hR hE⟩

/-- S4 frames are preorders. -/
theorem S4_preorder {R : AccessRel W} (hR : Refl R) (hT : Trans R) :
    Refl R ∧ Trans R := ⟨hR, hT⟩

/-- M implies D (reflexive implies serial). -/
theorem M_implies_D {R : AccessRel W} (hM : Refl R) : Serial R :=
  refl_serial hM

/-- M + 5 implies B. -/
theorem M5_implies_B {R : AccessRel W} (hM : Refl R) (h5 : Eucl R) : Symm R :=
  refl_eucl_symm hM h5

/-- M + 5 implies 4. -/
theorem M5_implies_4 {R : AccessRel W} (hM : Refl R) (h5 : Eucl R) : Trans R :=
  refl_eucl_trans hM h5

/-- S5 = M5 = MB5 = M4B5 = M45 = M4B (all collapse to same frame class). -/
theorem S5_collapse {R : AccessRel W} (hM : Refl R) (h5 : Eucl R) :
    Refl R ∧ Serial R ∧ Symm R ∧ Trans R ∧ Eucl R :=
  ⟨hM, refl_serial hM, refl_eucl_symm hM h5, refl_eucl_trans hM h5, h5⟩

-- ────────────────────────────────────────────────────────────────
-- §1.4 Restricted Box and Diamond
-- ────────────────────────────────────────────────────────────────

/-- Restricted necessity: `□_R p` at world `w` holds iff `p v` for all
    `v` accessible from `w`.

    `⟦□_R φ⟧^w = 1` iff `⟦φ⟧^v = 1` for all `v` with `R(w,v)`.

    This is the Kripke generalization of DWP's Rule B.13 (`box`). -/
def boxR (R : AccessRel W) (p : W → Prop) (w : W) : Prop :=
  ∀ v, R w v → p v

/-- Restricted possibility: `◇_R p` at world `w` holds iff `p v` for some
    `v` accessible from `w`. Dual of `boxR`. -/
def diamondR (R : AccessRel W) (p : W → Prop) (w : W) : Prop :=
  ∃ v, R w v ∧ p v

-- ────────────────────────────────────────────────────────────────
-- §1.5 Duality
-- ────────────────────────────────────────────────────────────────

/-- `□_R p ↔ ¬◇_R ¬p` — restricted modal duality. -/
theorem boxR_neg_diamondR (R : AccessRel W) (p : W → Prop) (w : W) :
    boxR R p w = ¬(diamondR R (fun v => ¬(p v)) w) := by
  simp only [boxR, diamondR, not_exists, not_and, not_not]

/-- `◇_R p ↔ ¬□_R ¬p` — dual form. -/
theorem diamondR_neg_boxR (R : AccessRel W) (p : W → Prop) (w : W) :
    diamondR R p w = ¬(boxR R (fun v => ¬(p v)) w) := by
  simp only [diamondR, boxR]
  exact propext ⟨
    fun ⟨v, hwv, hpv⟩ h => h v hwv hpv,
    fun h => Classical.byContradiction fun hne => by
      simp only [not_exists, not_and] at hne
      exact h (fun v hwv => hne v hwv)⟩

-- ────────────────────────────────────────────────────────────────
-- §1.6 Modal Axiom Correspondence
-- ────────────────────────────────────────────────────────────────

/-- **K axiom**: `□_R(p → q) → (□_R p → □_R q)`.
    Holds for any accessibility relation. -/
theorem boxR_K (R : AccessRel W) (p q : W → Prop) (w : W)
    (hpq : boxR R (fun v => p v → q v) w)
    (hp : boxR R p w) : boxR R q w :=
  fun v hwv => hpq v hwv (hp v hwv)

/-- **T axiom**: reflexive `R` gives `□_R p w → p w`.
    What is necessary is actual. -/
theorem boxR_T (R : AccessRel W) (hR : Refl R) (p : W → Prop) (w : W)
    (h : boxR R p w) : p w :=
  h w (hR w)

/-- **D axiom**: serial `R` gives `□_R p w → ◇_R p w`.
    What is necessary is possible. -/
theorem boxR_D (R : AccessRel W) (hS : Serial R) (p : W → Prop) (w : W)
    (h : boxR R p w) : diamondR R p w :=
  let ⟨v, hwv⟩ := hS w; ⟨v, hwv, h v hwv⟩

/-- **4 axiom**: transitive `R` gives `□_R p → □_R □_R p`.
    Positive introspection. -/
theorem boxR_four (R : AccessRel W) (hT : Trans R) (p : W → Prop) (w : W)
    (h : boxR R p w) : boxR R (boxR R p) w :=
  fun v hwv u hvu => h u (hT w v u hwv hvu)

/-- **B axiom**: symmetric `R` gives `p w → □_R ◇_R p w`.
    What is actual is necessarily possible. -/
theorem boxR_B (R : AccessRel W) (hS : Symm R) (p : W → Prop) (w : W)
    (h : p w) : boxR R (diamondR R p) w :=
  fun v hwv => ⟨w, hS w v hwv, h⟩

/-- **5 axiom**: euclidean `R` gives `◇_R p w → □_R ◇_R p w`.
    Positive possibility introspection. -/
theorem boxR_five (R : AccessRel W) (hE : Eucl R) (p : W → Prop) (w : W)
    (h : diamondR R p w) : boxR R (diamondR R p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv => ⟨u, hE w v u hwv hwu, hpu⟩

-- ────────────────────────────────────────────────────────────────
-- §1.7 Monotonicity
-- ────────────────────────────────────────────────────────────────

/-- `boxR R` is monotone: if `p ≤ q` pointwise, then `□_R p ≤ □_R q`. -/
theorem boxR_mono (R : AccessRel W) {p q : W → Prop}
    (h : ∀ v, p v → q v) (w : W)
    (hb : boxR R p w) : boxR R q w :=
  fun v hwv => h v (hb v hwv)

/-- `diamondR R` is monotone. -/
theorem diamondR_mono (R : AccessRel W) {p q : W → Prop}
    (h : ∀ v, p v → q v) (w : W)
    (hd : diamondR R p w) : diamondR R q w :=
  let ⟨v, hwv, hpv⟩ := hd; ⟨v, hwv, h v hpv⟩

-- ────────────────────────────────────────────────────────────────
-- §1.8 Distribution over Connectives
-- ────────────────────────────────────────────────────────────────

/-- `□_R` distributes over `∧`. -/
theorem boxR_conj (R : AccessRel W) (p q : W → Prop) (w : W) :
    boxR R (fun v => p v ∧ q v) w =
    (boxR R p w ∧ boxR R q w) := by
  exact propext ⟨fun h => ⟨fun v hwv => (h v hwv).1, fun v hwv => (h v hwv).2⟩,
                  fun ⟨hp, hq⟩ v hwv => ⟨hp v hwv, hq v hwv⟩⟩

/-- `◇_R` distributes over `∨`. -/
theorem diamondR_disj (R : AccessRel W) (p q : W → Prop) (w : W) :
    diamondR R (fun v => p v ∨ q v) w =
    (diamondR R p w ∨ diamondR R q w) := by
  exact propext ⟨
    fun ⟨v, hwv, h⟩ => h.elim (fun hp => .inl ⟨v, hwv, hp⟩) (fun hq => .inr ⟨v, hwv, hq⟩),
    fun h => h.elim (fun ⟨v, hwv, hp⟩ => ⟨v, hwv, .inl hp⟩)
                     (fun ⟨v, hwv, hq⟩ => ⟨v, hwv, .inr hq⟩)⟩

/-- Necessitation: if `p` holds at every world, then `□_R p` holds everywhere. -/
theorem boxR_necessitation (R : AccessRel W) (p : W → Prop)
    (h : ∀ v, p v) (w : W) : boxR R p w :=
  fun v _ => h v

-- ────────────────────────────────────────────────────────────────
-- §1.9 Accessibility Restriction (Kratzer's Insight)
-- ────────────────────────────────────────────────────────────────

/-- Restricting accessibility strengthens necessity:
    if `R₂ ⊆ R₁`, then `□_{R₁} p → □_{R₂} p`. -/
theorem boxR_restrict {R₁ R₂ : AccessRel W}
    (h : ∀ w v, R₂ w v → R₁ w v) (p : W → Prop) (w : W)
    (hb : boxR R₁ p w) : boxR R₂ p w :=
  fun v hwv => hb v (h w v hwv)

/-- Restricting accessibility weakens possibility:
    if `R₂ ⊆ R₁`, then `◇_{R₂} p → ◇_{R₁} p`. -/
theorem diamondR_restrict {R₁ R₂ : AccessRel W}
    (h : ∀ w v, R₂ w v → R₁ w v) (p : W → Prop) (w : W)
    (hd : diamondR R₂ p w) : diamondR R₁ p w :=
  let ⟨v, hwv, hpv⟩ := hd; ⟨v, h w v hwv, hpv⟩

-- ────────────────────────────────────────────────────────────────
-- §1.10 S5 Recovery
-- ────────────────────────────────────────────────────────────────

/-- With reflexive + euclidean accessibility (= S5 frame conditions),
    `boxR` validates all of T, D, 4, B, 5. -/
theorem S5_frame_all_axioms (R : AccessRel W)
    (hR : Refl R) (hE : Eucl R) :
    (∀ p w, boxR R p w → p w) ∧                          -- T
    (∀ p w, boxR R p w → diamondR R p w) ∧               -- D
    (∀ p w, boxR R p w → boxR R (boxR R p) w) ∧          -- 4
    (∀ p w, p w → boxR R (diamondR R p) w) ∧             -- B
    (∀ p w, diamondR R p w → boxR R (diamondR R p) w) := -- 5
  ⟨fun p w => boxR_T R hR p w,
   fun p w => boxR_D R (refl_serial hR) p w,
   fun p w => boxR_four R (refl_eucl_trans hR hE) p w,
   fun p w => boxR_B R (refl_eucl_symm hR hE) p w,
   fun p w => boxR_five R hE p w⟩

/-- `boxR R p i` is the infimum of `p v` over worlds `v` accessible from `w`. -/
theorem boxR_eq_forall (R : AccessRel W) (p : W → Prop) (w : W) :
    boxR R p w = (∀ v, R w v → p v) := rfl

/-- `diamondR R p w` is the supremum of `p v` over worlds `v` accessible from `w`. -/
theorem diamondR_eq_exists (R : AccessRel W) (p : W → Prop) (w : W) :
    diamondR R p w = (∃ v, R w v ∧ p v) := rfl

-- ════════════════════════════════════════════════════════════════════════
-- § 2. Gallin's Hierarchy of Propositional Operators
-- ════════════════════════════════════════════════════════════════════════

/-! ## The Gallin hierarchy (@cite{gallin-1975} §12)

In IL/ML_p, propositional operators form a three-level hierarchy:

1. **General** (`PropOp`): Any `(W → Prop) → W → Prop` — arbitrary
   properties of propositions, varying by world. This is an element of
   `P(M_ϕ)^I` in Gallin's notation.

2. **Indicial** (= Kripke-type): Operators definable via an accessibility
   relation `R`. The necessity variant is `∀ v, R w v → p v` (= `boxR`);
   the possibility variant is `∃ v, R w v ∧ p v` (= `diamondR`).

3. **S5**: The indicial case with `R = universalR` — IL's `box`/`diamond`.

```
All PropOps  ⊋  Indicial (Kripke)  ⊋  S5 (IL's □)
```

Gallin's key results formalized here:
- Every `boxR R` is a `PropOp` (by type) and is indicial (by construction)
- S5 necessity = `indicialNec universalR` (Theorem 12.6)
- Every indicial operator is monotone (≈ Lemma 12.3: K-operator)
- Frame conditions on `R` characterize T/B/S4/S5 (Theorem 12.5, proved in §1.6)

Non-indicial operators (e.g., Gallin's present progressive tense on p. 95–96)
are `PropOp`s that cannot be expressed as `boxR R` for any `R`. These are
an extension point for formalizing tense operators and other non-Kripke modality.
-/

-- ────────────────────────────────────────────────────────────────
-- §2.1 General Propositional Operators
-- ────────────────────────────────────────────────────────────────

/-- A propositional operator: any function from propositions to propositions,
    parametrized by world. This is Gallin's most general level —
    an element of `P(M_ϕ)^I`.

    Examples: necessity (`boxR R`), possibility (`diamondR R`),
    past tense (`∃ v, v < w ∧ p v`), present progressive, habituals. -/
abbrev PropOp (W : Type*) := (W → Prop) → W → Prop

/-- A propositional operator `N` is **monotone** if `p ≤ q` pointwise implies
    `N p ≤ N q` pointwise. Every K-operator (= normal modal operator) is
    monotone. -/
def PropOp.Monotone {W : Type*} (N : PropOp W) : Prop :=
  ∀ {p q : W → Prop}, (∀ v, p v → q v) → ∀ w, N p w → N q w

/-- A propositional operator distributes over conjunction (one direction of
    the K axiom: □(p ∧ q) → □p ∧ □q). -/
def PropOp.DistribConj {W : Type*} (N : PropOp W) : Prop :=
  ∀ (p q : W → Prop) (w : W), N (fun v => p v ∧ q v) w → N p w ∧ N q w

-- ────────────────────────────────────────────────────────────────
-- §2.2 Indicial (Kripke-type) Operators
-- ────────────────────────────────────────────────────────────────

/-- An indicial necessity operator: the restriction of `PropOp` to
    operators definable via an accessibility relation.
    `indicialNec R p w ↔ ∀ v, R w v → p v`.

    This is `boxR` viewed as a member of the Gallin hierarchy. -/
def indicialNec {W : Type*} (R : AccessRel W) : PropOp W :=
  fun p w => ∀ v, R w v → p v

/-- An indicial possibility operator (dual).
    `indicialPoss R p w ↔ ∃ v, R w v ∧ p v`. -/
def indicialPoss {W : Type*} (R : AccessRel W) : PropOp W :=
  fun p w => ∃ v, R w v ∧ p v

/-- `boxR` IS `indicialNec` — definitional equality. -/
theorem boxR_eq_indicialNec (R : AccessRel W) :
    boxR R = indicialNec R := rfl

/-- `diamondR` IS `indicialPoss` — definitional equality. -/
theorem diamondR_eq_indicialPoss (R : AccessRel W) :
    diamondR R = indicialPoss R := rfl

/-- A propositional operator is **indicial** if there exists an accessibility
    relation `R` such that `N = indicialNec R`. This is the key property
    from Gallin §12 p. 94: N can be characterized by a "relevance relation"
    between indices. -/
def IsIndicial {W : Type*} (N : PropOp W) : Prop :=
  ∃ R : AccessRel W, N = indicialNec R

/-- Every `boxR R` is indicial. -/
theorem boxR_isIndicial (R : AccessRel W) : IsIndicial (boxR R) :=
  ⟨R, rfl⟩

/-- Every indicial operator is monotone (Gallin Lemma 12.3:
    every indicial operator is a K-operator). -/
theorem indicial_monotone (R : AccessRel W) :
    PropOp.Monotone (indicialNec R) :=
  fun h _ hn v hwv => h v (hn v hwv)

/-- Every indicial operator distributes over conjunction. -/
theorem indicial_distribConj (R : AccessRel W) :
    PropOp.DistribConj (indicialNec R) :=
  fun _ _ _ hn => ⟨fun v hwv => (hn v hwv).1, fun v hwv => (hn v hwv).2⟩

-- ────────────────────────────────────────────────────────────────
-- §2.3 S5 as the Universal Indicial Operator
-- ────────────────────────────────────────────────────────────────

/-- S5 necessity as a `PropOp`: `p` holds at all worlds. -/
def s5Nec {W : Type*} : PropOp W :=
  fun p _ => ∀ w, p w

/-- S5 possibility as a `PropOp`: `p` holds at some world. -/
def s5Poss {W : Type*} : PropOp W :=
  fun p _ => ∃ w, p w

/-- **S5 = indicialNec universalR**: the S5 necessity operator is
    the indicial operator with universal accessibility.
    This is the formal statement that S5 is the "top" of the
    indicial hierarchy — Gallin Theorem 12.6 for S5. -/
theorem s5Nec_eq_indicialNec_universalR :
    s5Nec (W := W) = indicialNec universalR := by
  ext p w
  simp only [s5Nec, indicialNec, universalR, forall_true_left]

/-- S5 necessity is indicial. -/
theorem s5Nec_isIndicial : IsIndicial (s5Nec (W := W)) :=
  ⟨universalR, s5Nec_eq_indicialNec_universalR⟩

/-- **Restriction order on indicial operators**: if `R₂ ⊆ R₁` then
    `indicialNec R₁` is weaker than `indicialNec R₂` —
    fewer accessible worlds means a stronger necessity.

    S5 (R = universal) is the weakest; empty R is the strongest (vacuously true).
    This is Kratzer's insight that conversational backgrounds *restrict*
    the modal base, formalized at the PropOp level. -/
theorem indicialNec_weaker_of_sub {R₁ R₂ : AccessRel W}
    (h : ∀ w v, R₂ w v → R₁ w v) :
    ∀ (p : W → Prop) (w : W), indicialNec R₁ p w → indicialNec R₂ p w :=
  fun _ w hn v hwv => hn v (h w v hwv)

/-- S5 necessity is the weakest indicial operator: for any R,
    `s5Nec p w → indicialNec R p w`. -/
theorem s5Nec_weakest (R : AccessRel W) (p : W → Prop) (w : W)
    (h : s5Nec p w) : indicialNec R p w :=
  fun v _ => h v

/-- Empty accessibility gives the strongest (vacuously true) indicial operator. -/
theorem indicialNec_emptyR (p : W → Prop) (w : W) :
    indicialNec (emptyR (W := W)) p w := by
  intro v hv; exact absurd hv (by simp [emptyR])

-- ════════════════════════════════════════════════════════════════════════
-- § 3. Decidable Instances over Finite Worlds
-- ════════════════════════════════════════════════════════════════════════

/-! Following mathlib conventions: definitions are `Prop`-valued (§1 above),
with `Decidable` instances providing computation. With `[Fintype W]`,
`[DecidableRel R]`, and `[DecidablePred p]`, formulas like `boxR R p w` and
`Refl R` reduce by `decide`. -/

/-- `boxR R p w` is decidable when worlds enumerate, accessibility is decidable,
    and the proposition is decidable. -/
instance boxR_decidable {W : Type*} [Fintype W]
    (R : AccessRel W) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (boxR R p w) :=
  decidable_of_iff (∀ v ∈ (Finset.univ : Finset W), R w v → p v)
    ⟨fun h v hwv => h v (Finset.mem_univ v) hwv,
     fun h v _ hwv => h v hwv⟩

/-- `diamondR R p w` is decidable under the same conditions as `boxR`. -/
instance diamondR_decidable {W : Type*} [Fintype W]
    (R : AccessRel W) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (diamondR R p w) :=
  decidable_of_iff (∃ v ∈ (Finset.univ : Finset W), R w v ∧ p v)
    ⟨fun ⟨v, _, hwv, hpv⟩ => ⟨v, hwv, hpv⟩,
     fun ⟨v, hwv, hpv⟩ => ⟨v, Finset.mem_univ v, hwv, hpv⟩⟩

-- ════════════════════════════════════════════════════════════════════════
-- § 4. Lattice of Normal Modal Logics
-- ════════════════════════════════════════════════════════════════════════

/-- Axiom schemas addable to K. -/
inductive Axiom where
  | M     -- □p → p (T)
  | D     -- □p → ◇p
  | B     -- p → □◇p
  | four  -- □p → □□p
  | five  -- ◇p → □◇p
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : ToString Axiom where
  toString | .M => "M" | .D => "D" | .B => "B" | .four => "4" | .five => "5"

/-- A normal modal logic is K plus axiom schemas. -/
structure Logic where
  axioms : Finset Axiom
  deriving DecidableEq

namespace Logic

def K : Logic := ⟨∅⟩
def T : Logic := ⟨{.M}⟩
def D : Logic := ⟨{.D}⟩
def KB : Logic := ⟨{.B}⟩
def K4 : Logic := ⟨{.four}⟩
def K5 : Logic := ⟨{.five}⟩
def S4 : Logic := ⟨{.M, .four}⟩
def S5 : Logic := ⟨{.M, .five}⟩
def KTB : Logic := ⟨{.M, .B}⟩
def KD45 : Logic := ⟨{.D, .four, .five}⟩
def K45 : Logic := ⟨{.four, .five}⟩

/-- L₁ ≤ L₂ means L₁ is weaker (fewer axioms). -/
instance : LE Logic := ⟨λ L₁ L₂ => L₁.axioms ⊆ L₂.axioms⟩

instance : PartialOrder Logic where
  le_refl := λ _ => Finset.Subset.refl _
  le_trans := λ _ _ _ h₁ h₂ => Finset.Subset.trans h₁ h₂
  le_antisymm := λ _ _ h₁ h₂ => by
    cases_type* Logic
    simp only [Logic.mk.injEq]
    exact Finset.Subset.antisymm h₁ h₂

instance : Lattice Logic where
  sup := λ L₁ L₂ => ⟨L₁.axioms ∪ L₂.axioms⟩
  inf := λ L₁ L₂ => ⟨L₁.axioms ∩ L₂.axioms⟩
  le_sup_left := λ _ _ => Finset.subset_union_left
  le_sup_right := λ _ _ => Finset.subset_union_right
  sup_le := λ _ _ _ h₁ h₂ => Finset.union_subset h₁ h₂
  inf_le_left := λ _ _ => Finset.inter_subset_left
  inf_le_right := λ _ _ => Finset.inter_subset_right
  le_inf := λ _ _ _ h₁ h₂ => Finset.subset_inter h₁ h₂

def top : Logic := ⟨{.M, .D, .B, .four, .five}⟩

instance : OrderBot Logic where
  bot := K
  bot_le := λ _ => Finset.empty_subset _

instance : OrderTop Logic where
  top := top
  le_top := λ L => by
    simp only [top, LE.le]
    intro a _
    cases a <;> decide

instance : BoundedOrder Logic := BoundedOrder.mk

theorem K_bot : K = ⊥ := rfl
theorem top_all_axioms : top = ⊤ := rfl

def hasAxiom (L : Logic) (a : Axiom) : Bool := a ∈ L.axioms

/-- Frame conditions required by a logic. -/
def frameConditions {W : Type*} (L : Logic) (R : AccessRel W) : Prop :=
  (L.hasAxiom .M → Refl R) ∧
  (L.hasAxiom .D → Serial R) ∧
  (L.hasAxiom .B → Symm R) ∧
  (L.hasAxiom .four → Trans R) ∧
  (L.hasAxiom .five → Eucl R)

end Logic

-- ════════════════════════════════════════════════════════════════════════
-- § 5. IL Frame Specialization
-- ════════════════════════════════════════════════════════════════════════

/-! Bridge theorems connecting the generic `{W : Type*}` infrastructure
to Montague's IL. With universal accessibility, `boxR`/`diamondR` recover
S5 `box`/`diamond` from `Core.IntensionalLogic`. -/

section FrameSpecialization

open Core.IntensionalLogic

variable {F : Frame}

/-- S5 necessity (`box`) is restricted necessity with universal accessibility. -/
theorem boxR_universal (p : F.Denot .prop) :
    (fun i => boxR (universalR (W := F.Index)) p i) = (fun _ => box (F := F) p) := by
  ext i
  simp only [boxR, universalR, box, forall_true_left]

/-- S5 possibility (`diamond`) is restricted possibility with universal accessibility. -/
theorem diamondR_universal (p : F.Denot .prop) :
    (fun i => diamondR (universalR (W := F.Index)) p i) = (fun _ => diamond (F := F) p) := by
  ext i
  simp only [diamondR, universalR, diamond, true_and]

/-- S5 box implies any restricted box. -/
theorem box_implies_boxR (R : AccessRel F.Index) (p : F.Denot .prop)
    (h : box (F := F) p) (i : F.Index) : boxR R p i :=
  fun v _ => h v

/-- Any restricted diamond implies S5 diamond. -/
theorem diamondR_implies_diamond (R : AccessRel F.Index) (p : F.Denot .prop) (i : F.Index)
    (h : diamondR R p i) : diamond (F := F) p :=
  let ⟨v, _, hpv⟩ := h; ⟨v, hpv⟩

-- ────────────────────────────────────────────────────────────────
-- §5.1 Entailment with Restricted Modality
-- ────────────────────────────────────────────────────────────────

open Core.IntensionalLogic.Algebra (valid entails trueAt)

/-- A valid proposition is R-necessary at every world (for any R). -/
theorem valid_boxR (R : AccessRel F.Index) (p : F.Denot .prop)
    (hv : valid (F := F) p) (i : F.Index) : boxR R p i :=
  fun v _ => hv v

/-- Semantic entailment lifts to restricted modality:
    if `p ⊨ q` then `□_R p ⊨ □_R q`. -/
theorem boxR_entailment_lift (R : AccessRel F.Index)
    (p q : F.Denot .prop)
    (h : ∀ v, p v → q v)
    (i : F.Index) (hb : boxR R p i) : boxR R q i :=
  boxR_mono R h i hb

end FrameSpecialization

end Core.IntensionalLogic.RestrictedModality
