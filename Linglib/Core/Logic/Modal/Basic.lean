import Linglib.Core.Logic.Modal.Defs
import Linglib.Core.Logic.Aristotelian.Square
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

/-!
# Modal logic: axioms, the lattice of normal logics, and the modal square

[dowty-wall-peters-1981] [kratzer-1981] [kripke-1963]

Builds on the polymorphic Kripke foundation in `Defs.lean`. This file adds:

1. **Modal axiom correspondence** (T, D, 4, B, 5): which frame conditions on
   `R` validate which modal axioms when interpreted via `box`/`diamond`.
   The K axiom holds for any `R`.

2. **Monotonicity, distribution, restriction**: standard properties of
   normal modal operators. Restriction (`box_restrict`) is Kratzer's
   insight that conversational backgrounds *strengthen* necessity.

3. **Decidable instances**: `box R p w`, `diamond R p w` are decidable
   over finite worlds with decidable accessibility and propositions.

4. **Logic lattice**: `Axiom`, `Logic`, named logics (K, T, D, S4, S5, KD45),
   lattice instances, `frameConditions` predicate.

5. **Gallin hierarchy** ([gallin-1975]): `PropOp` (general propositional
   operators), `indicialNec`/`indicialPoss` (Kripke-type), `s5Nec`/`s5Poss`
   (universal-accessibility = classical IL S5). The architectural anchor
   showing that classical IL S5 = the universal-accessibility special case
   of the polymorphic theory, and that non-Kripke operators (tense,
   progressive) live outside `IsIndicial`.

6. **Modal square of opposition** (`modalSquare`, [carnielli-pizzi-2008]):
   under seriality the `box`/`diamond` corners satisfy all six Aristotelian
   relations — `subalternAI` is the D axiom, `contradEI` the box–diamond duality.

## Connection to Kratzer semantics

Kratzer's conversational backgrounds derive accessibility from a modal base:
`R_f(w, w') ≡ w' ∈ ⋂f(w)`. The ordering source further restricts to "best"
worlds. In IL terms:

- Simple Kratzer necessity = `box R_f` (no ordering source)
- Full Kratzer necessity = `box R_{f,g}` where `R_{f,g}` restricts to best worlds
- S5 necessity = `box universalR`
-/

namespace Core.Logic.Modal

variable {W : Type*}

-- ════════════════════════════════════════════════════════════════════════
-- § 1. Modal Axiom Correspondence
-- ════════════════════════════════════════════════════════════════════════

/-- **K axiom**: `□_R(p → q) → (□_R p → □_R q)`.
    Holds for any accessibility relation. -/
theorem box_K (R : AccessRel W) (p q : W → Prop) (w : W)
    (hpq : box R (fun v => p v → q v) w)
    (hp : box R p w) : box R q w :=
  fun v hwv => hpq v hwv (hp v hwv)

/-- **T axiom**: reflexive `R` gives `□_R p w → p w`.
    What is necessary is actual. -/
theorem box_T (R : AccessRel W) [Std.Refl R] (p : W → Prop) (w : W)
    (h : box R p w) : p w :=
  h w (Std.Refl.refl w)

/-- **D axiom**: serial `R` gives `□_R p w → ◇_R p w`.
    What is necessary is possible. -/
theorem box_D (R : AccessRel W) [hS : IsSerial R] (p : W → Prop) (w : W)
    (h : box R p w) : diamond R p w :=
  let ⟨v, hwv⟩ := hS.serial w; ⟨v, hwv, h v hwv⟩

/-- **4 axiom**: transitive `R` gives `□_R p → □_R □_R p`.
    Positive introspection. -/
theorem box_four (R : AccessRel W) [IsTrans W R] (p : W → Prop) (w : W)
    (h : box R p w) : box R (box R p) w :=
  fun v hwv u hvu => h u (IsTrans.trans w v u hwv hvu)

/-- **B axiom**: symmetric `R` gives `p w → □_R ◇_R p w`.
    What is actual is necessarily possible. -/
theorem box_B (R : AccessRel W) [Std.Symm R] (p : W → Prop) (w : W)
    (h : p w) : box R (diamond R p) w :=
  fun v hwv => ⟨w, Std.Symm.symm w v hwv, h⟩

/-- **5 axiom**: euclidean `R` gives `◇_R p w → □_R ◇_R p w`.
    Positive possibility introspection. -/
theorem box_five (R : AccessRel W) [hE : IsEuclidean R] (p : W → Prop) (w : W)
    (h : diamond R p w) : box R (diamond R p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv => ⟨u, hE.eucl w v u hwv hwu, hpu⟩

/-- **Moore reductio for KD4**: no world satisfies `□_R (p ∧ ¬□_R p)` when
    `R` is serial and transitive. The content `p ∧ ¬□_R p` is itself
    satisfiable; what fails is *boxing* it. Specialise to belief
    ([hintikka-1962]), knowledge, or any other KD4 modality. -/
theorem box_not_moore (R : AccessRel W) [hS : IsSerial R] [IsTrans W R]
    (p : W → Prop) (w : W) :
    ¬ box R (fun v => p v ∧ ¬ box R p v) w := by
  intro h
  have hbp : box R p w := fun v hwv => (h v hwv).1
  have hbbp : box R (box R p) w := box_four R p w hbp
  obtain ⟨v, hv⟩ := hS.serial w
  exact (h v hv).2 (hbbp v hv)

/-! ### Modal square of opposition

[carnielli-pizzi-2008]. The `□`/`◇` pair forms an Aristotelian square
(`A = □p`, `E = □¬p`, `I = ◇p`, `O = ¬□p`). Under seriality — the modal D axiom
(`box_D`) — it satisfies all six relations of the square of opposition, so every
serial modality (epistemic, deontic, temporal, doxastic) inherits the square. -/

/-- Under seriality, `□p` and `□¬p` are incompatible: no world satisfies both. -/
theorem box_disjoint_compl (R : AccessRel W) [hS : IsSerial R] (p : W → Prop) :
    Disjoint (box R p) (box R pᶜ) := by
  rw [Pi.disjoint_iff]
  intro w
  rw [disjoint_iff_inf_le]
  rintro ⟨hp, hnp⟩
  obtain ⟨v, hwv⟩ := hS.serial w
  exact hnp v hwv (hp v hwv)

/-- Box–diamond duality as an equation of predicates: `◇p = ¬□¬p`. -/
theorem diamond_eq_compl_box_compl (R : AccessRel W) (p : W → Prop) :
    diamond R p = (box R pᶜ)ᶜ := by
  funext w
  apply propext
  constructor
  · rintro ⟨v, hv, hpv⟩ hbox
    exact hbox v hv hpv
  · intro h
    by_contra hne
    exact h (fun v hv hpv => hne ⟨v, hv, hpv⟩)

/-- The **modal square of opposition** over an accessibility relation `R`
([carnielli-pizzi-2008]): `A = □p`, `E = □¬p`, `I = ◇p`, `O = ¬□p`. -/
def modalSquare (R : AccessRel W) (p : W → Prop) : Aristotelian.Square (W → Prop) where
  A := box R p
  E := box R pᶜ
  I := diamond R p
  O := (box R p)ᶜ

/-- The modal square satisfies all six Aristotelian relations whenever `R` is
**serial**. `subalternAI` is exactly the D axiom (`box_D` : `□p → ◇p`); the two
contradiction diagonals combine `isCompl_compl` with box–diamond duality; and
contrariety/subcontrariety reduce to `box_disjoint_compl`. -/
theorem modalSquare_relations (R : AccessRel W) [IsSerial R] (p : W → Prop) :
    Aristotelian.SquareRelations (modalSquare R p) where
  subalternAI := by rw [Pi.le_def]; exact fun w => box_D R p w
  subalternEO := le_compl_iff_disjoint_right.mpr (box_disjoint_compl R p).symm
  contradAO := isCompl_compl
  contradEI := by
    show IsCompl (box R pᶜ) (diamond R p)
    rw [diamond_eq_compl_box_compl]; exact isCompl_compl
  contraryAE := box_disjoint_compl R p
  subcontrIO := by
    show Codisjoint (diamond R p) ((box R p)ᶜ)
    rw [diamond_eq_compl_box_compl, codisjoint_iff, ← compl_inf,
        disjoint_iff.mp (box_disjoint_compl R p).symm, compl_bot]

-- ════════════════════════════════════════════════════════════════════════
-- § 2. Monotonicity
-- ════════════════════════════════════════════════════════════════════════

/-- `box R` is monotone: if `p ≤ q` pointwise, then `□_R p ≤ □_R q`. -/
theorem box_mono (R : AccessRel W) {p q : W → Prop}
    (h : ∀ v, p v → q v) (w : W)
    (hb : box R p w) : box R q w :=
  fun v hwv => h v (hb v hwv)

/-- `diamond R` is monotone. -/
theorem diamond_mono (R : AccessRel W) {p q : W → Prop}
    (h : ∀ v, p v → q v) (w : W)
    (hd : diamond R p w) : diamond R q w :=
  let ⟨v, hwv, hpv⟩ := hd; ⟨v, hwv, h v hpv⟩

-- ════════════════════════════════════════════════════════════════════════
-- § 3. Distribution over Connectives
-- ════════════════════════════════════════════════════════════════════════

/-- `□_R` distributes over `∧`. -/
theorem box_conj (R : AccessRel W) (p q : W → Prop) (w : W) :
    box R (fun v => p v ∧ q v) w =
    (box R p w ∧ box R q w) := by
  exact propext ⟨fun h => ⟨fun v hwv => (h v hwv).1, fun v hwv => (h v hwv).2⟩,
                  fun ⟨hp, hq⟩ v hwv => ⟨hp v hwv, hq v hwv⟩⟩

/-- `◇_R` distributes over `∨`. -/
theorem diamond_disj (R : AccessRel W) (p q : W → Prop) (w : W) :
    diamond R (fun v => p v ∨ q v) w =
    (diamond R p w ∨ diamond R q w) := by
  exact propext ⟨
    fun ⟨v, hwv, h⟩ => h.elim (fun hp => .inl ⟨v, hwv, hp⟩) (fun hq => .inr ⟨v, hwv, hq⟩),
    fun h => h.elim (fun ⟨v, hwv, hp⟩ => ⟨v, hwv, .inl hp⟩)
                     (fun ⟨v, hwv, hq⟩ => ⟨v, hwv, .inr hq⟩)⟩

/-- Necessitation: if `p` holds at every world, then `□_R p` holds everywhere. -/
theorem box_necessitation (R : AccessRel W) (p : W → Prop)
    (h : ∀ v, p v) (w : W) : box R p w :=
  fun v _ => h v

-- ════════════════════════════════════════════════════════════════════════
-- § 4. Accessibility Restriction (Kratzer's Insight)
-- ════════════════════════════════════════════════════════════════════════

/-- Restricting accessibility strengthens necessity:
    if `R₂ ⊆ R₁`, then `□_{R₁} p → □_{R₂} p`. -/
theorem box_restrict {R₁ R₂ : AccessRel W}
    (h : ∀ w v, R₂ w v → R₁ w v) (p : W → Prop) (w : W)
    (hb : box R₁ p w) : box R₂ p w :=
  fun v hwv => hb v (h w v hwv)

/-- Restricting accessibility weakens possibility:
    if `R₂ ⊆ R₁`, then `◇_{R₂} p → ◇_{R₁} p`. -/
theorem diamond_restrict {R₁ R₂ : AccessRel W}
    (h : ∀ w v, R₂ w v → R₁ w v) (p : W → Prop) (w : W)
    (hd : diamond R₂ p w) : diamond R₁ p w :=
  let ⟨v, hwv, hpv⟩ := hd; ⟨v, h w v hwv, hpv⟩

-- ════════════════════════════════════════════════════════════════════════
-- § 5. S5 Recovery
-- ════════════════════════════════════════════════════════════════════════

/-- With reflexive + euclidean accessibility (= S5 frame conditions),
    `box` validates all of T, D, 4, B, 5. -/
theorem S5_frame_all_axioms (R : AccessRel W) [Std.Refl R] [IsEuclidean R] :
    (∀ p w, box R p w → p w) ∧                          -- T
    (∀ p w, box R p w → diamond R p w) ∧               -- D
    (∀ p w, box R p w → box R (box R p) w) ∧          -- 4
    (∀ p w, p w → box R (diamond R p) w) ∧             -- B
    (∀ p w, diamond R p w → box R (diamond R p) w) := -- 5
  ⟨box_T R, box_D R, box_four R, box_B R, box_five R⟩

/-- KD45 frame conditions validate all three KD45 axioms (D, 4, 5). -/
theorem KD45_frame_all_axioms (R : AccessRel W) [IsKD45Frame R] :
    (∀ p w, box R p w → diamond R p w) ∧               -- D
    (∀ p w, box R p w → box R (box R p) w) ∧          -- 4
    (∀ p w, diamond R p w → box R (diamond R p) w) := -- 5
  ⟨box_D R, box_four R, box_five R⟩

/-- `box R p i` is the infimum of `p v` over worlds `v` accessible from `w`. -/
theorem box_eq_forall (R : AccessRel W) (p : W → Prop) (w : W) :
    box R p w = (∀ v, R w v → p v) := rfl

/-- `diamond R p w` is the supremum of `p v` over worlds `v` accessible from `w`. -/
theorem diamond_eq_exists (R : AccessRel W) (p : W → Prop) (w : W) :
    diamond R p w = (∃ v, R w v ∧ p v) := rfl

-- ════════════════════════════════════════════════════════════════════════
-- § 6. Gallin's Hierarchy of Propositional Operators
-- ════════════════════════════════════════════════════════════════════════

/-! ## The Gallin hierarchy ([gallin-1975])

In IL/ML_p, propositional operators form a three-level hierarchy:

1. **General** (`PropOp`): Any `(W → Prop) → W → Prop` — arbitrary
   properties of propositions, varying by world.

2. **Indicial** (= Kripke-type): Operators definable via an accessibility
   relation `R`. The necessity variant is `∀ v, R w v → p v` (= `box`);
   the possibility variant is `∃ v, R w v ∧ p v` (= `diamond`).

3. **S5**: The indicial case with `R = universalR` — IL's `box`/`diamond`.

```
All PropOps  ⊋  Indicial (Kripke)  ⊋  S5 (IL's □)
```

**Why this is here even with no current downstream consumer.** These
theorems are the *architectural anchor* for the design choice that
restricted modality lives in `Core/Logic/Intensional/`: they prove that
classical IL S5 is exactly the universal-accessibility special case of
the polymorphic theory, and that every `box R` is a normal modal
operator (monotone, distribConj). Non-indicial PropOps (e.g., tense,
present progressive) are the formal extension point for tense /
non-Kripke modal operators that *cannot* be expressed as `box R` for
any `R`. Removing this section would erase the formal record of why
the directory layout is what it is.
-/

-- ────────────────────────────────────────────────────────────────
-- §6.1 General Propositional Operators
-- ────────────────────────────────────────────────────────────────

/-- A propositional operator: any function from propositions to propositions,
    parametrized by world. This is Gallin's most general level —
    an arbitrary property of propositions varying by index.

    Examples: necessity (`box R`), possibility (`diamond R`),
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

    This is `box` viewed as a member of the Gallin hierarchy. -/
def indicialNec {W : Type*} (R : AccessRel W) : PropOp W :=
  fun p w => ∀ v, R w v → p v

/-- An indicial possibility operator (dual).
    `indicialPoss R p w ↔ ∃ v, R w v ∧ p v`. -/
def indicialPoss {W : Type*} (R : AccessRel W) : PropOp W :=
  fun p w => ∃ v, R w v ∧ p v

/-- `box` IS `indicialNec` — definitional equality. -/
theorem box_eq_indicialNec (R : AccessRel W) :
    box R = indicialNec R := rfl

/-- `diamond` IS `indicialPoss` — definitional equality. -/
theorem diamond_eq_indicialPoss (R : AccessRel W) :
    diamond R = indicialPoss R := rfl

/-- A propositional operator is **indicial** if there exists an accessibility
    relation `R` such that `N = indicialNec R`. The non-indicial case is
    where tense and other non-Kripke operators live. -/
def IsIndicial {W : Type*} (N : PropOp W) : Prop :=
  ∃ R : AccessRel W, N = indicialNec R

/-- Every `box R` is indicial. -/
theorem box_isIndicial (R : AccessRel W) : IsIndicial (box R) :=
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

/-! ### Decidability over finite worlds -/

/-- `box R p w` is decidable when worlds enumerate, accessibility is decidable,
    and the proposition is decidable. -/
instance box_decidable {W : Type*} [Fintype W]
    (R : AccessRel W) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (box R p w) :=
  decidable_of_iff (∀ v ∈ (Finset.univ : Finset W), R w v → p v)
    ⟨fun h v hwv => h v (Finset.mem_univ v) hwv,
     fun h v _ hwv => h v hwv⟩

/-- `diamond R p w` is decidable under the same conditions as `box`. -/
instance diamond_decidable {W : Type*} [Fintype W]
    (R : AccessRel W) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (diamond R p w) :=
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
  (L.hasAxiom .M → Std.Refl R) ∧
  (L.hasAxiom .D → IsSerial R) ∧
  (L.hasAxiom .B → Std.Symm R) ∧
  (L.hasAxiom .four → IsTrans W R) ∧
  (L.hasAxiom .five → IsEuclidean R)

/-- The syntactic-semantic bridge for `S5`: `frameConditions Logic.S5 R`
    iff `R` is an S5 frame. -/
@[simp] theorem frameConditions_S5_iff {W : Type*} (R : AccessRel W) :
    frameConditions S5 R ↔ Std.Refl R ∧ IsEuclidean R := by
  unfold frameConditions S5 hasAxiom
  simp

/-- The syntactic-semantic bridge for `KD45`. -/
@[simp] theorem frameConditions_KD45_iff {W : Type*} (R : AccessRel W) :
    frameConditions KD45 R ↔ IsSerial R ∧ IsTrans W R ∧ IsEuclidean R := by
  unfold frameConditions KD45 hasAxiom
  simp

/-- The syntactic-semantic bridge for `KTB`. -/
@[simp] theorem frameConditions_KTB_iff {W : Type*} (R : AccessRel W) :
    frameConditions KTB R ↔ Std.Refl R ∧ Std.Symm R := by
  unfold frameConditions KTB hasAxiom
  simp

end Logic

end Core.Logic.Modal
