import Linglib.Core.IntensionalLogic.Defs
import Linglib.Core.IntensionalLogic.Quantification
import Linglib.Core.IntensionalLogic.Algebra
import Linglib.Core.Modality.ModalTypes
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# Restricted Modality: Modal Axioms, Decidability, Logic Lattice, Gallin Hierarchy

@cite{dowty-wall-peters-1981} @cite{kratzer-1981} @cite{kripke-1963}

Builds on the polymorphic Kripke foundation in `Defs.lean`. This file adds:

1. **Modal axiom correspondence** (T, D, 4, B, 5): which frame conditions on
   `R` validate which modal axioms when interpreted via `boxR`/`diamondR`.
   The K axiom holds for any `R`.

2. **Monotonicity, distribution, restriction**: standard properties of
   normal modal operators. Restriction (`boxR_restrict`) is Kratzer's
   insight that conversational backgrounds *strengthen* necessity.

3. **Decidable instances**: `boxR R p w`, `diamondR R p w` are decidable
   over finite worlds with decidable accessibility and propositions.

4. **Logic lattice**: `Axiom`, `Logic`, named logics (K, T, D, S4, S5, KD45),
   lattice instances, `frameConditions` predicate.

5. **Gallin hierarchy** (@cite{gallin-1975}): `PropOp` (general propositional
   operators), `indicialNec`/`indicialPoss` (Kripke-type), `s5Nec`/`s5Poss`
   (universal-accessibility = classical IL S5). The architectural anchor
   showing that classical IL S5 = the universal-accessibility special case
   of the polymorphic theory, and that non-Kripke operators (tense,
   progressive) live outside `IsIndicial`.

6. **IL Frame specialization**: with universal accessibility, `boxR`/`diamondR`
   recover S5 `box`/`diamond` from `Quantification.lean` — the formal
   bridge that the polymorphic theory contains classical IL as a special case.

## Connection to Kratzer semantics

Kratzer's conversational backgrounds derive accessibility from a modal base:
`R_f(w, w') ≡ w' ∈ ⋂f(w)`. The ordering source further restricts to "best"
worlds. In IL terms:

- Simple Kratzer necessity = `boxR R_f` (no ordering source)
- Full Kratzer necessity = `boxR R_{f,g}` where `R_{f,g}` restricts to best worlds
- S5 necessity = `boxR (fun _ _ => True)` = `box`
-/

namespace Core.IntensionalLogic

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Modal Axiom Correspondence
-- ════════════════════════════════════════════════════════════════════════

/-- **K axiom**: `□_R(p → q) → (□_R p → □_R q)`.
    Holds for any accessibility relation. -/
theorem boxR_K (R : AccessRel W) (p q : W → Prop) (w : W)
    (hpq : boxR R (fun v => p v → q v) w)
    (hp : boxR R p w) : boxR R q w :=
  fun v hwv => hpq v hwv (hp v hwv)

/-- **T axiom**: reflexive `R` gives `□_R p w → p w`.
    What is necessary is actual. -/
theorem boxR_T (R : AccessRel W) (hR : IsReflexive R) (p : W → Prop) (w : W)
    (h : boxR R p w) : p w :=
  h w (hR w)

/-- **D axiom**: serial `R` gives `□_R p w → ◇_R p w`.
    What is necessary is possible. -/
theorem boxR_D (R : AccessRel W) (hS : IsSerial R) (p : W → Prop) (w : W)
    (h : boxR R p w) : diamondR R p w :=
  let ⟨v, hwv⟩ := hS w; ⟨v, hwv, h v hwv⟩

/-- **4 axiom**: transitive `R` gives `□_R p → □_R □_R p`.
    Positive introspection. -/
theorem boxR_four (R : AccessRel W) (hT : IsTransitive R) (p : W → Prop) (w : W)
    (h : boxR R p w) : boxR R (boxR R p) w :=
  fun v hwv u hvu => h u (hT w v u hwv hvu)

/-- **B axiom**: symmetric `R` gives `p w → □_R ◇_R p w`.
    What is actual is necessarily possible. -/
theorem boxR_B (R : AccessRel W) (hS : IsSymmetric R) (p : W → Prop) (w : W)
    (h : p w) : boxR R (diamondR R p) w :=
  fun v hwv => ⟨w, hS w v hwv, h⟩

/-- **5 axiom**: euclidean `R` gives `◇_R p w → □_R ◇_R p w`.
    Positive possibility introspection. -/
theorem boxR_five (R : AccessRel W) (hE : IsEuclidean R) (p : W → Prop) (w : W)
    (h : diamondR R p w) : boxR R (diamondR R p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv => ⟨u, hE w v u hwv hwu, hpu⟩

-- ════════════════════════════════════════════════════════════════════════
-- § 2. Monotonicity
-- ════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════
-- § 3. Distribution over Connectives
-- ════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════
-- § 4. Accessibility Restriction (Kratzer's Insight)
-- ════════════════════════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════════════════════════
-- § 5. S5 Recovery
-- ════════════════════════════════════════════════════════════════════════

/-- With reflexive + euclidean accessibility (= S5 frame conditions),
    `boxR` validates all of T, D, 4, B, 5. -/
theorem S5_frame_all_axioms (R : AccessRel W)
    (hR : IsReflexive R) (hE : IsEuclidean R) :
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
-- § 6. Gallin's Hierarchy of Propositional Operators
-- ════════════════════════════════════════════════════════════════════════

/-! ## The Gallin hierarchy (@cite{gallin-1975})

In IL/ML_p, propositional operators form a three-level hierarchy:

1. **General** (`PropOp`): Any `(W → Prop) → W → Prop` — arbitrary
   properties of propositions, varying by world.

2. **Indicial** (= Kripke-type): Operators definable via an accessibility
   relation `R`. The necessity variant is `∀ v, R w v → p v` (= `boxR`);
   the possibility variant is `∃ v, R w v ∧ p v` (= `diamondR`).

3. **S5**: The indicial case with `R = universalR` — IL's `box`/`diamond`.

```
All PropOps  ⊋  Indicial (Kripke)  ⊋  S5 (IL's □)
```

**Why this is here even with no current downstream consumer.** These
theorems are the *architectural anchor* for the design choice that
restricted modality lives in `Core/IntensionalLogic/`: they prove that
classical IL S5 is exactly the universal-accessibility special case of
the polymorphic theory, and that every `boxR R` is a normal modal
operator (monotone, distribConj). Non-indicial PropOps (e.g., tense,
present progressive) are the formal extension point for tense /
non-Kripke modal operators that *cannot* be expressed as `boxR R` for
any `R`. Removing this section would erase the formal record of why
the directory layout is what it is.
-/

-- ────────────────────────────────────────────────────────────────
-- §6.1 General Propositional Operators
-- ────────────────────────────────────────────────────────────────

/-- A propositional operator: any function from propositions to propositions,
    parametrized by world. This is Gallin's most general level —
    an arbitrary property of propositions varying by index.

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
-- §6.2 Indicial (Kripke-type) Operators
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
    relation `R` such that `N = indicialNec R`. The non-indicial case is
    where tense and other non-Kripke operators live. -/
def IsIndicial {W : Type*} (N : PropOp W) : Prop :=
  ∃ R : AccessRel W, N = indicialNec R

/-- Every `boxR R` is indicial. -/
theorem boxR_isIndicial (R : AccessRel W) : IsIndicial (boxR R) :=
  ⟨R, rfl⟩

/-- Every indicial operator is monotone (every Kripke operator is a
    K-operator). -/
theorem indicial_monotone (R : AccessRel W) :
    PropOp.Monotone (indicialNec R) :=
  fun h _ hn v hwv => h v (hn v hwv)

/-- Every indicial operator distributes over conjunction. -/
theorem indicial_distribConj (R : AccessRel W) :
    PropOp.DistribConj (indicialNec R) :=
  fun _ _ _ hn => ⟨fun v hwv => (hn v hwv).1, fun v hwv => (hn v hwv).2⟩

-- ────────────────────────────────────────────────────────────────
-- §6.3 S5 as the Universal Indicial Operator
-- ────────────────────────────────────────────────────────────────

/-- S5 necessity as a `PropOp`: `p` holds at all worlds. -/
def s5Nec {W : Type*} : PropOp W :=
  fun p _ => ∀ w, p w

/-- S5 possibility as a `PropOp`: `p` holds at some world. -/
def s5Poss {W : Type*} : PropOp W :=
  fun p _ => ∃ w, p w

/-- **S5 = indicialNec universalR**: the S5 necessity operator is
    the indicial operator with universal accessibility.
    The formal statement that S5 sits at the top of the indicial hierarchy. -/
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
-- § 7. Decidable Instances over Finite Worlds
-- ════════════════════════════════════════════════════════════════════════

/-! Following mathlib conventions: definitions are `Prop`-valued (in `Defs.lean`),
with `Decidable` instances providing computation. With `[Fintype W]`,
`[DecidableRel R]`, and `[DecidablePred p]`, formulas like `boxR R p w` and
`IsReflexive R` reduce by `decide`. -/

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
-- § 8. Lattice of Normal Modal Logics
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
  (L.hasAxiom .M → IsReflexive R) ∧
  (L.hasAxiom .D → IsSerial R) ∧
  (L.hasAxiom .B → IsSymmetric R) ∧
  (L.hasAxiom .four → IsTransitive R) ∧
  (L.hasAxiom .five → IsEuclidean R)

end Logic

-- ════════════════════════════════════════════════════════════════════════
-- § 9. IL Frame Specialization
-- ════════════════════════════════════════════════════════════════════════

/-! Bridge theorems connecting the polymorphic infrastructure to Montague's IL.
With universal accessibility, `boxR`/`diamondR` recover S5 `box`/`diamond`
from `Quantification.lean`. These would all be `rfl` if `box`/`diamond` were
definitionally `boxR universalR ∘ pick-an-index` — see the Quantification module
for the layering question. As stated they're one-step `simp` proofs. -/

section FrameSpecialization

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
-- §9.1 Entailment with Restricted Modality
-- ────────────────────────────────────────────────────────────────

open Algebra (valid entails trueAt)

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

end Core.IntensionalLogic
