import Linglib.Logic.Modal.Defs
import Linglib.Logic.Aristotelian.Square
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Lattice

/-!
# Modal logic over accessibility relations

Normality and the operator hierarchy for the relational `box`/`diamond`
of `Defs.lean`: monotonicity and distribution; restriction —
[kratzer-1981]'s insight that conversational backgrounds strengthen
necessity by shrinking accessibility; the modal square of opposition
([carnielli-pizzi-2008]); [gallin-1975]'s hierarchy of propositional
operators, placing Montague's S5 `box`/`diamond`
([dowty-wall-peters-1981]) as the universal-accessibility case; and the
lattice of normal modal logics as axiom sets over K.

-/

namespace ModalLogic

variable {W : Type*}

/-! ### Modal square of opposition -/

variable {R : W → W → Prop} {p : W → Prop}

/-- Over a serial relation, `□p` and `□¬p` are incompatible. -/
theorem box_disjoint_compl [hS : IsSerial R] : Disjoint (□[R] p) (□[R] pᶜ) :=
  Pi.disjoint_iff.mpr fun w => Prop.disjoint_iff.mpr fun ⟨hp, hnp⟩ =>
    let ⟨v, hwv⟩ := hS.serial w
    hnp v hwv (hp v hwv)

/-- Box–diamond duality as an equation of predicates: `¬□¬p = ◇p`. -/
theorem compl_box_compl (R : W → W → Prop) (p : W → Prop) :
    (□[R] pᶜ)ᶜ = ◇[R] p := by
  funext w
  simp [not_box]

/-- The **modal square of opposition** over `R`: `A = □p`, `E = □¬p`,
    `I = ◇p`, `O = ¬□p`. -/
def modalSquare (R : W → W → Prop) (p : W → Prop) : Aristotelian.Square (W → Prop) where
  A := □[R] p
  E := □[R] pᶜ
  I := ◇[R] p
  O := (□[R] p)ᶜ

/-- Over a serial relation the modal square satisfies all six Aristotelian
    relations. -/
theorem modalSquare_relations (R : W → W → Prop) [IsSerial R] (p : W → Prop) :
    Aristotelian.SquareRelations (modalSquare R p) :=
  .of_disjoint (compl_box_compl R p).symm rfl box_disjoint_compl

/-! ### The Galois connection and normality -/

variable (R) {q : W → Prop}

/-- `◇` along `R` is left adjoint to `□` along the converse relation —
    the characteristic adjunction of relational modality. -/
theorem diamond_box_gc : GaloisConnection ◇[R] □[flip R] :=
  fun _ _ =>
    ⟨fun h v hp w hwv => h w ⟨v, hwv, hp⟩,
     fun h w => fun ⟨v, hwv, hp⟩ => h v hp w hwv⟩

theorem box_mono : Monotone □[R] :=
  (diamond_box_gc (flip R)).monotone_u

theorem diamond_mono : Monotone ◇[R] :=
  (diamond_box_gc R).monotone_l

theorem box_inf : □[R] (p ⊓ q) = □[R] p ⊓ □[R] q :=
  (diamond_box_gc (flip R)).u_inf

theorem diamond_sup : ◇[R] (p ⊔ q) = ◇[R] p ⊔ ◇[R] q :=
  (diamond_box_gc R).l_sup

/-- Necessitation: `□⊤ = ⊤`. -/
theorem box_top : □[R] ⊤ = ⊤ :=
  (diamond_box_gc (flip R)).u_top

/-- **Conversion** (Prior's tense axiom `A ⊃ G P A`): the unit of the
    adjunction — over any relation, `p ≤ □_{flip R} ◇_R p`. -/
theorem self_imp_box_flip_diamond (p : W → Prop) : p ≤ □[flip R] (◇[R] p) :=
  (diamond_box_gc R).le_u_l p

/-! ### Accessibility restriction -/

/-- Restricting accessibility strengthens necessity: `box` is antitone
    in the relation. -/
theorem box_restrict {R₁ R₂ : W → W → Prop} (h : R₂ ≤ R₁) (p : W → Prop) :
    □[R₁] p ≤ □[R₂] p :=
  fun _ hb v hwv => hb v (h _ _ hwv)

/-- Restricting accessibility weakens possibility: `diamond` is monotone
    in the relation. -/
theorem diamond_restrict {R₁ R₂ : W → W → Prop} (h : R₂ ≤ R₁) (p : W → Prop) :
    ◇[R₂] p ≤ ◇[R₁] p :=
  fun _ hd => let ⟨v, hwv, hpv⟩ := hd; ⟨v, h _ _ hwv, hpv⟩

/-! ### Bundled frame classes -/

/-- S5 frame: reflexive + euclidean (implies symmetric + transitive). -/
class IsS5Frame : Prop extends Std.Refl R, IsEuclidean R

/-- KD45 frame for textbook belief: serial + transitive + euclidean. -/
class IsKD45Frame : Prop extends IsSerial R, IsTrans W R, IsEuclidean R

/-- K45 frame: transitive + euclidean, NOT serial. The frame condition
    for commitment in [stalnaker-1984]-style discourse models, where
    commitment violations (no accessible compliance world) must be
    expressible. -/
class IsK45Frame : Prop extends IsTrans W R, IsEuclidean R

/-- KTB frame: reflexive + symmetric. The natural setting for tolerance
    semantics ([cobreros-etal-2012]) where each predicate's
    similarity relation is reflexive and symmetric but possibly
    non-transitive. -/
class IsKTBFrame : Prop extends Std.Refl R, Std.Symm R

/-! ### The Gallin hierarchy

Operators `(W → Prop) → W → Prop` form a three-level hierarchy
([gallin-1975]): arbitrary operators, the **indicial** (Kripke-definable)
ones — `box R` for some accessibility relation — and S5, the indicial
case `R = ⊤`. Tense and other non-Kripke operators live outside
`IsIndicial`. -/

/-- An operator on world-propositions is **indicial** (Kripke-definable)
    if it is `box R` for some accessibility relation `R`. -/
def IsIndicial (N : (W → Prop) → W → Prop) : Prop :=
  ∃ R : W → W → Prop, N = box R

/-- Every `box R` is indicial. -/
theorem box_isIndicial : IsIndicial □[R] := ⟨R, rfl⟩

/-! ### Flat S5 operators

`poss`/`nec` are the flat existential/universal modals (`∃ w` / `∀ w`) —
the S5 operators `□[⊤]`/`◇[⊤]` with their vestigial evaluation world
dropped. -/

/-- Flat S5 possibility: `poss p` iff `p` holds at some world. -/
def poss (p : W → Prop) : Prop := ∃ w, p w

/-- Flat S5 necessity: `nec p` iff `p` holds at every world. -/
def nec (p : W → Prop) : Prop := ∀ w, p w

theorem nec_mono : Monotone (nec (W := W)) :=
  fun _ q h hn w => h w (hn w)

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
