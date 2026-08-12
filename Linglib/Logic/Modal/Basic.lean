import Linglib.Logic.Modal.Defs
import Linglib.Logic.Aristotelian.Square
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
([dowty-wall-peters-1981]) as the universal-accessibility case.

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

end ModalLogic
