import Linglib.Logic.Modal.Defs
import Linglib.Logic.Aristotelian.Square
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Lattice

/-!
# Modal logic over accessibility relations

Axiom correspondence, normality, and the operator hierarchy for the
relational `box`/`diamond` of `Defs.lean` ([kripke-1963]): which frame
conditions validate the T, D, 4, B, and 5 schemas; monotonicity and
distribution; restriction — [kratzer-1981]'s insight that conversational
backgrounds strengthen necessity by shrinking accessibility; the modal
square of opposition ([carnielli-pizzi-2008]); [gallin-1975]'s hierarchy
of propositional operators, placing Montague's S5 `box`/`diamond`
([dowty-wall-peters-1981]) as the universal-accessibility case; and the
lattice of normal modal logics as axiom sets over K.

## Main declarations

* `box_K` … `box_five` — per-axiom frame correspondences; `box_not_moore`
  is the Moore-sentence reductio for any KD4 modality ([hintikka-1962]).
* `modalSquare`, `modalSquare_relations` — the `□`/`◇` Aristotelian
  square, satisfying all six relations under seriality.
* `PropOp`, `IsIndicial`, `s5Nec`, `poss`/`nec` — the Gallin hierarchy:
  arbitrary operators ⊋ Kripke-definable (`∃ R, N = box R`) ⊋ S5.
* `ModalLogic.frameConditions` — frame conditions for a normal modal
  logic, identified with its axiom set over K and ordered by the
  `Finset` lattice (named logics `ModalLogic.K` … `ModalLogic.KD45`);
  `frameConditions_iff_valid` is the correspondence theorem: the
  conditions hold iff every schema of the logic is valid.

## Connection to Kratzer semantics

Kratzer's conversational backgrounds derive accessibility from a modal
base: `R_f(w, w') ≡ w' ∈ ⋂f(w)`, with the ordering source further
restricting to best worlds. Simple Kratzer necessity is `box R_f`, full
Kratzer necessity is `box` of the best-world restriction, and S5
necessity is `box ⊤` — see `box_restrict` for why restriction
strengthens.
-/

namespace ModalLogic

variable {W : Type*} {R : W → W → Prop} {p q : W → Prop} {w : W}

/-! ### Axiom correspondence -/

/-- **K**: `□(p → q) → □p → □q`, over any relation. -/
theorem box_K (hpq : □[R] (fun v => p v → q v) w) (hp : □[R] p w) : □[R] q w :=
  fun v hwv => hpq v hwv (hp v hwv)

/-- **T**: over a reflexive relation, `□p → p`. -/
theorem box_T [Std.Refl R] (h : □[R] p w) : p w :=
  h w (Std.Refl.refl w)

/-- **D**: over a serial relation, `□p → ◇p`. -/
theorem box_D [hS : IsSerial R] (h : □[R] p w) : ◇[R] p w :=
  let ⟨v, hwv⟩ := hS.serial w; ⟨v, hwv, h v hwv⟩

/-- **4**: over a transitive relation, `□p → □□p`. -/
theorem box_four [IsTrans W R] (h : □[R] p w) : □[R] (□[R] p) w :=
  fun v hwv u hvu => h u (IsTrans.trans w v u hwv hvu)

/-- **B**: over a symmetric relation, `p → □◇p`. -/
theorem box_B [Std.Symm R] (h : p w) : □[R] (◇[R] p) w :=
  fun v hwv => ⟨w, Std.Symm.symm w v hwv, h⟩

/-- **5**: over a Euclidean relation, `◇p → □◇p`. -/
theorem box_five [hE : IsEuclidean R] (h : ◇[R] p w) : □[R] (◇[R] p) w :=
  let ⟨u, hwu, hpu⟩ := h
  fun v hwv => ⟨u, hE.eucl w v u hwv hwu, hpu⟩

/-- **Moore reductio for KD4**: no world satisfies `□(p ∧ ¬□p)` over a
    serial transitive relation — the content is satisfiable; boxing it
    is not. -/
theorem box_not_moore [hS : IsSerial R] [IsTrans W R] :
    ¬ □[R] (fun v => p v ∧ ¬ □[R] p v) w := fun h =>
  have ⟨v, hv⟩ := hS.serial w
  (h v hv).2 (box_four (fun u hu => (h u hu).1) v hv)

/-! ### Modal square of opposition

The `□`/`◇` pair forms an Aristotelian square (`A = □p`, `E = □¬p`,
`I = ◇p`, `O = ¬□p`). Under seriality — the D axiom (`box_D`) — it
satisfies all six relations of the square of opposition, so every serial
modality (epistemic, deontic, temporal, doxastic) inherits the square. -/

/-- Under seriality, `□p` and `□¬p` are incompatible: no world satisfies both. -/
theorem box_disjoint_compl (R : W → W → Prop) [hS : IsSerial R] (p : W → Prop) :
    Disjoint (box R p) (box R pᶜ) := by
  rw [Pi.disjoint_iff]
  intro w
  rw [disjoint_iff_inf_le]
  rintro ⟨hp, hnp⟩
  obtain ⟨v, hwv⟩ := hS.serial w
  exact hnp v hwv (hp v hwv)

/-- Box–diamond duality as an equation of predicates: `◇p = ¬□¬p`. -/
theorem diamond_eq_compl_box_compl (R : W → W → Prop) (p : W → Prop) :
    diamond R p = (box R pᶜ)ᶜ := by
  funext w
  apply propext
  constructor
  · rintro ⟨v, hv, hpv⟩ hbox
    exact hbox v hv hpv
  · intro h
    by_contra hne
    exact h (fun v hv hpv => hne ⟨v, hv, hpv⟩)

/-- The **modal square of opposition** over an accessibility relation `R`:
    `A = □p`, `E = □¬p`, `I = ◇p`, `O = ¬□p`. -/
def modalSquare (R : W → W → Prop) (p : W → Prop) : Aristotelian.Square (W → Prop) where
  A := box R p
  E := box R pᶜ
  I := diamond R p
  O := (box R p)ᶜ

/-- The modal square satisfies all six Aristotelian relations whenever `R` is
**serial**. `subalternAI` is exactly the D axiom (`box_D` : `□p → ◇p`); the two
contradiction diagonals combine `isCompl_compl` with box–diamond duality; and
contrariety/subcontrariety reduce to `box_disjoint_compl`. -/
theorem modalSquare_relations (R : W → W → Prop) [IsSerial R] (p : W → Prop) :
    Aristotelian.SquareRelations (modalSquare R p) where
  subalternAI := by rw [Pi.le_def]; exact fun _ => box_D
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

/-! ### Monotonicity and distribution -/

/-- `box R` is monotone: if `p ≤ q` pointwise, then `□_R p ≤ □_R q`. -/
theorem box_mono (R : W → W → Prop) {p q : W → Prop}
    (h : ∀ v, p v → q v) (w : W)
    (hb : box R p w) : box R q w :=
  fun v hwv => h v (hb v hwv)

/-- `diamond R` is monotone. -/
theorem diamond_mono (R : W → W → Prop) {p q : W → Prop}
    (h : ∀ v, p v → q v) (w : W)
    (hd : diamond R p w) : diamond R q w :=
  let ⟨v, hwv, hpv⟩ := hd; ⟨v, hwv, h v hpv⟩

/-- `□_R` distributes over `∧`. -/
theorem box_conj (R : W → W → Prop) (p q : W → Prop) (w : W) :
    box R (fun v => p v ∧ q v) w ↔ box R p w ∧ box R q w :=
  ⟨fun h => ⟨fun v hwv => (h v hwv).1, fun v hwv => (h v hwv).2⟩,
   fun ⟨hp, hq⟩ v hwv => ⟨hp v hwv, hq v hwv⟩⟩

/-- `◇_R` distributes over `∨`. -/
theorem diamond_disj (R : W → W → Prop) (p q : W → Prop) (w : W) :
    diamond R (fun v => p v ∨ q v) w ↔ diamond R p w ∨ diamond R q w :=
  ⟨fun ⟨v, hwv, h⟩ => h.elim (fun hp => .inl ⟨v, hwv, hp⟩) (fun hq => .inr ⟨v, hwv, hq⟩),
   fun h => h.elim (fun ⟨v, hwv, hp⟩ => ⟨v, hwv, .inl hp⟩)
                   (fun ⟨v, hwv, hq⟩ => ⟨v, hwv, .inr hq⟩)⟩

/-- Necessitation: if `p` holds at every world, then `□_R p` holds everywhere. -/
theorem box_necessitation (R : W → W → Prop) (p : W → Prop)
    (h : ∀ v, p v) (w : W) : box R p w :=
  fun v _ => h v

/-! ### Accessibility restriction -/

/-- Restricting accessibility strengthens necessity:
    if `R₂ ⊆ R₁`, then `□_{R₁} p → □_{R₂} p`. -/
theorem box_restrict {R₁ R₂ : W → W → Prop}
    (h : ∀ w v, R₂ w v → R₁ w v) (p : W → Prop) (w : W)
    (hb : box R₁ p w) : box R₂ p w :=
  fun v hwv => hb v (h w v hwv)

/-- Restricting accessibility weakens possibility:
    if `R₂ ⊆ R₁`, then `◇_{R₂} p → ◇_{R₁} p`. -/
theorem diamond_restrict {R₁ R₂ : W → W → Prop}
    (h : ∀ w v, R₂ w v → R₁ w v) (p : W → Prop) (w : W)
    (hd : diamond R₂ p w) : diamond R₁ p w :=
  let ⟨v, hwv, hpv⟩ := hd; ⟨v, h w v hwv, hpv⟩

/-- **Conversion** (Prior's tense axiom `A ⊃ G P A` / `A ⊃ H F A`): for `R` and its converse
    `flip R`, `p w → □_{flip R} ◇_R p w`. The correspondence fact that two modalities over a
    relation and its converse are temporally adjoint (holds for *any* `R`). -/
theorem self_imp_box_flip_diamond (R : W → W → Prop) (p : W → Prop) (w : W)
    (h : p w) : box (flip R) (diamond R p) w :=
  fun _ hv => ⟨w, hv, h⟩

/-! ### Bundled frame classes

Named frame classes for the logics of `ModalLogic.frameConditions`; the
per-logic correspondence theorems (`frameConditions_S5_iff`, …) live with
the lattice below. -/

/-- S5 frame: reflexive + euclidean (implies symmetric + transitive). -/
class IsS5Frame {W : Type*} (R : W → W → Prop) : Prop extends Std.Refl R, IsEuclidean R

/-- KD45 frame for textbook belief: serial + transitive + euclidean. -/
class IsKD45Frame {W : Type*} (R : W → W → Prop) : Prop
  extends IsSerial R, IsTrans W R, IsEuclidean R

/-- K45 frame: transitive + euclidean, NOT serial. The frame condition
    for commitment in [stalnaker-1984]-style discourse models, where
    commitment violations (no accessible compliance world) must be
    expressible. -/
class IsK45Frame {W : Type*} (R : W → W → Prop) : Prop
  extends IsTrans W R, IsEuclidean R

/-- KTB frame: reflexive + symmetric. The natural setting for tolerance
    semantics ([cobreros-etal-2012]) where each predicate's
    similarity relation is reflexive and symmetric but possibly
    non-transitive. -/
class IsKTBFrame {W : Type*} (R : W → W → Prop) : Prop
  extends Std.Refl R, Std.Symm R

/-! ### The Gallin hierarchy

Propositional operators form a three-level hierarchy: **general**
(`PropOp` — arbitrary properties of propositions, varying by world),
**indicial** (Kripke-definable: `N = box R` for some accessibility `R`),
and **S5** (the indicial case with `R = ⊤`). Non-indicial
operators (tense, present progressive) live outside `IsIndicial`;
`Logic/Temporal/Basic.lean` consumes this boundary. -/

/-- A propositional operator: any function from propositions to propositions,
    parametrized by world — Gallin's most general level.

    Examples: necessity (`box R`), possibility (`diamond R`),
    past tense (`∃ v, v < w ∧ p v`), present progressive, habituals. -/
abbrev PropOp (W : Type*) := (W → Prop) → W → Prop

/-- A propositional operator `N` is **monotone** if `p ≤ q` pointwise implies
    `N p ≤ N q` pointwise. Every normal (K-)operator is monotone. -/
def PropOp.Monotone {W : Type*} (N : PropOp W) : Prop :=
  ∀ ⦃p q : W → Prop⦄, (∀ v, p v → q v) → ∀ w, N p w → N q w

/-- A propositional operator distributes over conjunction (one direction of
    the K axiom: `□(p ∧ q) → □p ∧ □q`). -/
def PropOp.DistribConj {W : Type*} (N : PropOp W) : Prop :=
  ∀ (p q : W → Prop) (w : W), N (fun v => p v ∧ q v) w → N p w ∧ N q w

/-- A propositional operator is **indicial** (Kripke-definable) if it is
    `box R` for some accessibility relation `R`. The non-indicial case is
    where tense and other non-Kripke operators live. -/
def IsIndicial {W : Type*} (N : PropOp W) : Prop :=
  ∃ R : W → W → Prop, N = box R

/-- Every `box R` is indicial. -/
theorem box_isIndicial (R : W → W → Prop) : IsIndicial (box R) :=
  ⟨R, rfl⟩

/-- Every indicial operator is monotone (every Kripke operator is a
    K-operator). -/
theorem monotone_box (R : W → W → Prop) : PropOp.Monotone (box R) :=
  fun _ _ h w hb => box_mono R h w hb

/-- Every indicial operator distributes over conjunction. -/
theorem distribConj_box (R : W → W → Prop) : PropOp.DistribConj (box R) :=
  fun p q w h => (box_conj R p q w).mp h

/-- S5 necessity as a `PropOp`: `p` holds at all worlds. -/
def s5Nec {W : Type*} : PropOp W :=
  fun p _ => ∀ w, p w

/-- S5 possibility as a `PropOp`: `p` holds at some world. -/
def s5Poss {W : Type*} : PropOp W :=
  fun p _ => ∃ w, p w

/-- **S5 = box over the universal relation**: the S5 necessity operator is
    the indicial operator with universal accessibility — S5 sits at the top
    of the indicial hierarchy. -/
theorem s5Nec_eq_box_top : s5Nec (W := W) = box ⊤ := by
  ext p w
  exact ⟨fun h v _ => h v, fun h v => h v trivial⟩

/-- S5 necessity is indicial. -/
theorem s5Nec_isIndicial : IsIndicial (s5Nec (W := W)) :=
  ⟨⊤, s5Nec_eq_box_top⟩

/-- S5 necessity is the weakest indicial operator: for any `R`,
    `s5Nec p w → box R p w`. Fewer accessible worlds means a stronger
    necessity — Kratzer restriction at the `PropOp` level (`box_restrict`). -/
theorem s5Nec_weakest (R : W → W → Prop) (p : W → Prop) (w : W)
    (h : s5Nec p w) : box R p w :=
  fun v _ => h v

/-- The empty relation gives the strongest (vacuously true) necessity. -/
theorem box_bot (p : W → Prop) (w : W) : box (⊥ : W → W → Prop) p w :=
  fun _ hv => False.elim hv

/-! ### Flat S5 operators

`poss`/`nec` are the genuinely flat existential/universal modals (`∃ w` / `∀ w`),
the world-collapsed projection of `s5Poss`/`s5Nec`, whose evaluation world is
vestigial. These are the canonical flat modals consumed by the implicature
calculus (`Exhaustification.FreeChoice`) and free-choice scope theory, which do
not track an evaluation world; `s5Poss_apply`/`s5Nec_apply` connect them back to
the `PropOp` hierarchy. -/

/-- Flat S5 possibility: `◇p = ∃ w, p w` (no evaluation world). -/
def poss (p : W → Prop) : Prop := ∃ w, p w

/-- Flat S5 necessity: `□p = ∀ w, p w` (no evaluation world). -/
def nec (p : W → Prop) : Prop := ∀ w, p w

@[simp] theorem s5Poss_apply (p : W → Prop) (w : W) : s5Poss p w = poss p := rfl
@[simp] theorem s5Nec_apply (p : W → Prop) (w : W) : s5Nec p w = nec p := rfl

/-- ◇ distributes over ∨ (flat): `◇(p ∨ q) = ◇p ∨ ◇q`. -/
theorem poss_or (p q : W → Prop) : poss (fun w => p w ∨ q w) = (poss p ∨ poss q) :=
  propext exists_or

/-- □ distributes over ∧ (flat): `□(p ∧ q) = □p ∧ □q`. -/
theorem nec_and (p q : W → Prop) : nec (fun w => p w ∧ q w) = (nec p ∧ nec q) :=
  propext forall_and

/-- ◇ is monotone. -/
theorem poss_mono {p q : W → Prop} (h : ∀ w, p w → q w) : poss p → poss q :=
  fun ⟨w, hw⟩ => ⟨w, h w hw⟩

/-- □ is monotone. -/
theorem nec_mono {p q : W → Prop} (h : ∀ w, p w → q w) : nec p → nec q :=
  fun hn w => h w (hn w)

/-! ### Decidability over finite worlds -/

instance box_decidable {W : Type*} [Fintype W]
    (R : W → W → Prop) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (box R p w) :=
  inferInstanceAs (Decidable (∀ v, R w v → p v))

instance diamond_decidable {W : Type*} [Fintype W]
    (R : W → W → Prop) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (diamond R p w) :=
  inferInstanceAs (Decidable (∃ v, R w v ∧ p v))

/-! ### The lattice of normal modal logics

A normal modal logic is identified with its set of axiom schemas over K;
the `Finset` lattice (`⊆`, `∪`, `∩`, `⊥ = ∅ = K`) is the lattice of
normal logics. -/

/-- Axiom schemas addable to the base logic K. -/
inductive Axiom where
  /-- `□p → p` (T; von Wright's M). -/
  | M
  /-- `□p → ◇p`. -/
  | D
  /-- `p → □◇p`. -/
  | B
  /-- `□p → □□p`. -/
  | four
  /-- `◇p → □◇p`. -/
  | five
  deriving DecidableEq, Repr, Inhabited

instance : ToString Axiom where
  toString | .M => "M" | .D => "D" | .B => "B" | .four => "4" | .five => "5"


/-- The base logic `K`: no additional axioms. -/
def K : Finset Axiom := ∅

/-- `T = K + M`. -/
def T : Finset Axiom := {.M}

/-- `D = K + D`. -/
def D : Finset Axiom := {.D}

/-- `KB = K + B`. -/
def KB : Finset Axiom := {.B}

/-- `K4 = K + 4`. -/
def K4 : Finset Axiom := {.four}

/-- `K5 = K + 5`. -/
def K5 : Finset Axiom := {.five}

/-- `S4 = K + M + 4`. -/
def S4 : Finset Axiom := {.M, .four}

/-- `S5 = K + M + 5`. -/
def S5 : Finset Axiom := {.M, .five}

/-- `KTB = K + M + B`. -/
def KTB : Finset Axiom := {.M, .B}

/-- `KD45 = K + D + 4 + 5` (the doxastic logic). -/
def KD45 : Finset Axiom := {.D, .four, .five}

/-- `K45 = K + 4 + 5`. -/
def K45 : Finset Axiom := {.four, .five}

/-- `K` is the bottom of the lattice of normal logics. -/
theorem K_bot : K = ⊥ := rfl

/-- Frame conditions required by a logic: for each axiom schema present,
    the corresponding condition on `R`. -/
def frameConditions {W : Type*} (L : Finset Axiom) (R : W → W → Prop) : Prop :=
  (.M ∈ L → Std.Refl R) ∧
  (.D ∈ L → IsSerial R) ∧
  (.B ∈ L → Std.Symm R) ∧
  (.four ∈ L → IsTrans W R) ∧
  (.five ∈ L → IsEuclidean R)

/-- Validity of an axiom schema over an accessibility relation: the schema
    holds for all propositions at all worlds. -/
def Axiom.Valid {W : Type*} : Axiom → (W → W → Prop) → Prop
  | .M, R => ∀ (p : W → Prop) (w : W), box R p w → p w
  | .D, R => ∀ (p : W → Prop) (w : W), box R p w → diamond R p w
  | .B, R => ∀ (p : W → Prop) (w : W), p w → box R (diamond R p) w
  | .four, R => ∀ (p : W → Prop) (w : W), box R p w → box R (box R p) w
  | .five, R => ∀ (p : W → Prop) (w : W), diamond R p w → box R (diamond R p) w

/-- **Correspondence for M (= T)**: `□p → p` is valid over `R` iff `R` is
    reflexive. -/
theorem Axiom.valid_M_iff {W : Type*} {R : W → W → Prop} :
    (Axiom.M).Valid R ↔ Std.Refl R :=
  ⟨fun h => ⟨fun w => h (R w) w (fun _ hv => hv)⟩,
   fun hR => haveI := hR; fun _ _ => box_T⟩

/-- **Correspondence for D**: `□p → ◇p` is valid over `R` iff `R` is serial. -/
theorem Axiom.valid_D_iff {W : Type*} {R : W → W → Prop} :
    (Axiom.D).Valid R ↔ IsSerial R :=
  ⟨fun h => ⟨fun w => let ⟨v, hv, _⟩ := h (fun _ => True) w (fun _ _ => trivial); ⟨v, hv⟩⟩,
   fun hR => haveI := hR; fun _ _ => box_D⟩

/-- **Correspondence for B**: `p → □◇p` is valid over `R` iff `R` is
    symmetric. -/
theorem Axiom.valid_B_iff {W : Type*} {R : W → W → Prop} :
    (Axiom.B).Valid R ↔ Std.Symm R :=
  ⟨fun h => ⟨fun w v hwv => match h (· = w) w rfl v hwv with | ⟨_, hvw, rfl⟩ => hvw⟩,
   fun hR => haveI := hR; fun _ _ => box_B⟩

/-- **Correspondence for 4**: `□p → □□p` is valid over `R` iff `R` is
    transitive. -/
theorem Axiom.valid_four_iff {W : Type*} {R : W → W → Prop} :
    (Axiom.four).Valid R ↔ IsTrans W R :=
  ⟨fun h => ⟨fun w v u hwv hvu => h (R w) w (fun _ hv => hv) v hwv u hvu⟩,
   fun hR => haveI := hR; fun _ _ => box_four⟩

/-- **Correspondence for 5**: `◇p → □◇p` is valid over `R` iff `R` is
    euclidean. -/
theorem Axiom.valid_five_iff {W : Type*} {R : W → W → Prop} :
    (Axiom.five).Valid R ↔ IsEuclidean R :=
  ⟨fun h => ⟨fun w v u hwv hwu =>
     match h (· = u) w ⟨u, hwu, rfl⟩ v hwv with | ⟨_, hvu, rfl⟩ => hvu⟩,
   fun hR => haveI := hR; fun _ _ => box_five⟩

/-- **The correspondence theorem**: `R` satisfies the frame conditions of `L`
    iff every axiom schema of `L` is valid over `R`. Left to right is
    soundness (`box_T` … `box_five`); the converse holds because each schema
    elementarily defines its frame condition (`Axiom.valid_M_iff`, …). -/
theorem frameConditions_iff_valid {W : Type*} {L : Finset Axiom}
    {R : W → W → Prop} :
    frameConditions L R ↔ ∀ a ∈ L, a.Valid R := by
  constructor
  · intro h a ha
    cases a with
    | M => exact Axiom.valid_M_iff.mpr (h.1 ha)
    | D => exact Axiom.valid_D_iff.mpr (h.2.1 ha)
    | B => exact Axiom.valid_B_iff.mpr (h.2.2.1 ha)
    | four => exact Axiom.valid_four_iff.mpr (h.2.2.2.1 ha)
    | five => exact Axiom.valid_five_iff.mpr (h.2.2.2.2 ha)
  · intro h
    exact ⟨fun hm => Axiom.valid_M_iff.mp (h _ hm),
           fun hm => Axiom.valid_D_iff.mp (h _ hm),
           fun hm => Axiom.valid_B_iff.mp (h _ hm),
           fun hm => Axiom.valid_four_iff.mp (h _ hm),
           fun hm => Axiom.valid_five_iff.mp (h _ hm)⟩

/-- The syntactic-semantic bridge for `S5`: `frameConditions ModalLogic.S5 R`
    iff `R` is an S5 frame. -/
@[simp] theorem frameConditions_S5_iff {W : Type*} (R : W → W → Prop) :
    frameConditions S5 R ↔ IsS5Frame R :=
  ⟨fun h => haveI := h.1 (by decide); haveI := h.2.2.2.2 (by decide); ⟨⟩,
   fun h => ⟨fun _ => h.toRefl, fun hm => absurd hm (by decide),
             fun hm => absurd hm (by decide), fun hm => absurd hm (by decide),
             fun _ => h.toIsEuclidean⟩⟩

/-- The syntactic-semantic bridge for `KD45`. -/
@[simp] theorem frameConditions_KD45_iff {W : Type*} (R : W → W → Prop) :
    frameConditions KD45 R ↔ IsKD45Frame R :=
  ⟨fun h => haveI := h.2.1 (by decide); haveI := h.2.2.2.1 (by decide);
     haveI := h.2.2.2.2 (by decide); ⟨⟩,
   fun h => ⟨fun hm => absurd hm (by decide), fun _ => h.toIsSerial,
             fun hm => absurd hm (by decide), fun _ => h.toIsTrans,
             fun _ => h.toIsEuclidean⟩⟩

/-- The syntactic-semantic bridge for `K45`. -/
@[simp] theorem frameConditions_K45_iff {W : Type*} (R : W → W → Prop) :
    frameConditions K45 R ↔ IsK45Frame R :=
  ⟨fun h => haveI := h.2.2.2.1 (by decide); haveI := h.2.2.2.2 (by decide); ⟨⟩,
   fun h => ⟨fun hm => absurd hm (by decide), fun hm => absurd hm (by decide),
             fun hm => absurd hm (by decide), fun _ => h.toIsTrans,
             fun _ => h.toIsEuclidean⟩⟩

/-- The syntactic-semantic bridge for `KTB`. -/
@[simp] theorem frameConditions_KTB_iff {W : Type*} (R : W → W → Prop) :
    frameConditions KTB R ↔ IsKTBFrame R :=
  ⟨fun h => haveI := h.1 (by decide); haveI := h.2.2.1 (by decide); ⟨⟩,
   fun h => ⟨fun _ => h.toRefl, fun hm => absurd hm (by decide),
             fun _ => h.toSymm, fun hm => absurd hm (by decide),
             fun hm => absurd hm (by decide)⟩⟩

end ModalLogic
