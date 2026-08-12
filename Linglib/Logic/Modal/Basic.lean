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

/-- Restricting accessibility strengthens necessity. -/
theorem box_restrict (p : W → Prop) : Antitone fun R : W → W → Prop => □[R] p :=
  fun _ _ h _ hb v hwv => hb v (h _ _ hwv)

/-- Restricting accessibility weakens possibility. -/
theorem diamond_restrict (p : W → Prop) : Monotone fun R : W → W → Prop => ◇[R] p :=
  fun _ _ h _ hd => let ⟨v, hwv, hpv⟩ := hd; ⟨v, h _ _ hwv, hpv⟩

/-! ### Bundled frame classes -/

/-- `R` is an **S5 frame** if it is reflexive and Euclidean. -/
class IsS5Frame : Prop extends Std.Refl R, IsEuclidean R

/-- `R` is a **KD45 frame** — the doxastic frame — if it is serial,
    transitive, and Euclidean. -/
class IsKD45Frame : Prop extends IsSerial R, IsTrans W R, IsEuclidean R

/-- `R` is a **K45 frame** if it is transitive and Euclidean. -/
class IsK45Frame : Prop extends IsTrans W R, IsEuclidean R

/-- `R` is a **KTB frame** if it is reflexive and symmetric. -/
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
  fun _ _ h hn w => h w (hn w)

/-! ### Decidability over finite worlds -/

instance [Fintype W] (R : W → W → Prop) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (box R p w) :=
  inferInstanceAs (Decidable (∀ v, R w v → p v))

instance [Fintype W] (R : W → W → Prop) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (diamond R p w) :=
  inferInstanceAs (Decidable (∃ v, R w v ∧ p v))

/-! ### The lattice of normal modal logics

A normal modal logic is identified with its set of axiom schemas over K;
the `Finset` lattice (`⊆`, `∪`, `∩`, `⊥ = ∅ = K`) is the lattice of
normal logics. The named logics below follow the textbook scheme — the
name lists the axioms added to `K` — plus the historical names `T`,
`S4`, `S5`. -/

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

def K : Finset Axiom := ∅
def T : Finset Axiom := {.M}
def D : Finset Axiom := {.D}
def KB : Finset Axiom := {.B}
def K4 : Finset Axiom := {.four}
def K5 : Finset Axiom := {.five}
def S4 : Finset Axiom := {.M, .four}
def S5 : Finset Axiom := {.M, .five}
def KTB : Finset Axiom := {.M, .B}
def KD45 : Finset Axiom := {.D, .four, .five}
def K45 : Finset Axiom := {.four, .five}

/-- The frame condition of an axiom schema. -/
def Axiom.FrameCondition : Axiom → (W → W → Prop) → Prop
  | .M => Std.Refl
  | .D => IsSerial
  | .B => Std.Symm
  | .four => IsTrans W
  | .five => IsEuclidean

/-- Validity of an axiom schema over an accessibility relation. -/
def Axiom.Valid : Axiom → (W → W → Prop) → Prop
  | .M, R => ∀ p, □[R] p ≤ p
  | .D, R => ∀ p, □[R] p ≤ ◇[R] p
  | .B, R => ∀ p, p ≤ □[R] (◇[R] p)
  | .four, R => ∀ p, □[R] p ≤ □[R] (□[R] p)
  | .five, R => ∀ p, ◇[R] p ≤ □[R] (◇[R] p)

/-- **Correspondence, per axiom**: a schema is valid over `R` iff `R`
    satisfies its frame condition. -/
theorem Axiom.valid_iff {R : W → W → Prop} :
    ∀ a : Axiom, a.Valid R ↔ a.FrameCondition R
  | .M => ⟨fun h => ⟨fun w => h (R w) w fun _ hv => hv⟩,
           fun hR => haveI : Std.Refl R := hR; fun _ _ h => box_T h⟩
  | .D => ⟨fun h => ⟨fun w =>
             let ⟨v, hv, _⟩ := h (fun _ => True) w fun _ _ => trivial; ⟨v, hv⟩⟩,
           fun hR => haveI : IsSerial R := hR; fun _ _ h => box_D h⟩
  | .B => ⟨fun h => ⟨fun w v hwv =>
             match h (· = w) w rfl v hwv with | ⟨_, hvw, rfl⟩ => hvw⟩,
           fun hR => haveI : Std.Symm R := hR; fun _ _ h => box_B h⟩
  | .four => ⟨fun h => ⟨fun w v u hwv hvu => h (R w) w (fun _ hv => hv) v hwv u hvu⟩,
              fun hR => haveI : IsTrans W R := hR; fun _ _ h => box_four h⟩
  | .five => ⟨fun h => ⟨fun w v u hwv hwu =>
               match h (· = u) w ⟨u, hwu, rfl⟩ v hwv with | ⟨_, hvu, rfl⟩ => hvu⟩,
              fun hR => haveI : IsEuclidean R := hR; fun _ _ h => box_five h⟩

/-- Frame conditions of a logic: every axiom schema present imposes its
    condition on `R`. -/
def frameConditions (L : Finset Axiom) (R : W → W → Prop) : Prop :=
  ∀ a ∈ L, a.FrameCondition R

/-- **The correspondence theorem**: `R` satisfies the frame conditions of
    `L` iff every axiom schema of `L` is valid over `R`. -/
theorem frameConditions_iff_valid {L : Finset Axiom} {R : W → W → Prop} :
    frameConditions L R ↔ ∀ a ∈ L, a.Valid R :=
  forall₂_congr fun a _ => (Axiom.valid_iff a).symm

/-- The syntactic-semantic bridge for `S5`. -/
@[simp] theorem frameConditions_S5_iff (R : W → W → Prop) :
    frameConditions S5 R ↔ IsS5Frame R := by
  simp only [frameConditions, S5, Axiom.FrameCondition, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨h1, h2⟩ => haveI := h1; haveI := h2; ⟨⟩,
         fun h => ⟨h.toRefl, h.toIsEuclidean⟩⟩

/-- The syntactic-semantic bridge for `KD45`. -/
@[simp] theorem frameConditions_KD45_iff (R : W → W → Prop) :
    frameConditions KD45 R ↔ IsKD45Frame R := by
  simp only [frameConditions, KD45, Axiom.FrameCondition, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨h1, h2, h3⟩ => haveI := h1; haveI := h2; haveI := h3; ⟨⟩,
         fun h => ⟨h.toIsSerial, h.toIsTrans, h.toIsEuclidean⟩⟩

/-- The syntactic-semantic bridge for `K45`. -/
@[simp] theorem frameConditions_K45_iff (R : W → W → Prop) :
    frameConditions K45 R ↔ IsK45Frame R := by
  simp only [frameConditions, K45, Axiom.FrameCondition, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨h1, h2⟩ => haveI := h1; haveI := h2; ⟨⟩,
         fun h => ⟨h.toIsTrans, h.toIsEuclidean⟩⟩

/-- The syntactic-semantic bridge for `KTB`. -/
@[simp] theorem frameConditions_KTB_iff (R : W → W → Prop) :
    frameConditions KTB R ↔ IsKTBFrame R := by
  simp only [frameConditions, KTB, Axiom.FrameCondition, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq]
  exact ⟨fun ⟨h1, h2⟩ => haveI := h1; haveI := h2; ⟨⟩,
         fun h => ⟨h.toRefl, h.toSymm⟩⟩

end ModalLogic
