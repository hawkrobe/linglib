module

public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Aristotelian.Square
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Order.GaloisConnection.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Relation

/-!
# Modal logic over accessibility relations

This file proves the order theory of `box` and `diamond`: the Galois
connection `◇[R] ⊣ □[flip R]` and the normality laws it yields,
antitonicity in the relation (conversational backgrounds strengthen
necessity by shrinking accessibility), and the modal square of
opposition. It also defines the bundled frame classes `IsS5Frame`,
`IsKD45Frame`, `IsK45Frame`, `IsKTBFrame`, and the indicial operators,
with Montague's S5 `box`/`diamond` as the universal-accessibility case
`R = ⊤`, and lifts `box` and `diamond` to propositions as sets: `nec R p`
and `poss R p` are the `SetRel.core` and `SetRel.preimage` of the
accessibility relation.

## References

* [kratzer-1981] — necessity strengthened by restricting accessibility
* [carnielli-pizzi-2008] — the modal square of opposition
* [gallin-1975] — the indicial operator hierarchy
* [dowty-wall-peters-1981] — Montague's S5 operators

-/

@[expose] public section


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

/-! ### Transitive closure

Necessity along the transitive closure of `R` is the infinite conjunction of iterated
necessity along `R`: `□[R⁺] p = □[R] p ∧ □[R] (□[R] p) ∧ ⋯`. -/

theorem box_iterate_succ_of_box_transGen :
    ∀ (n : ℕ) {p : W → Prop} {w : W}, □[Relation.TransGen R] p w → (□[R])^[n + 1] p w
  | 0, _, _, h => fun v hv => h v (Relation.TransGen.single hv)
  | n + 1, _, _, h => by
    rw [Function.iterate_succ_apply']
    exact fun v hv =>
      box_iterate_succ_of_box_transGen n fun u hu => h u (Relation.TransGen.head hv hu)

theorem exists_box_iterate_imp_of_transGen {w v : W} (h : Relation.TransGen R w v) :
    ∃ n, ∀ q : W → Prop, (□[R])^[n + 1] q w → q v := by
  induction h with
  | single hwv => exact ⟨0, fun _ hq => hq _ hwv⟩
  | tail _ huv ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, fun q hq => hn (□[R] q) (by rwa [Function.iterate_succ_apply] at hq) _ huv⟩

theorem box_transGen_iff {p : W → Prop} {w : W} :
    □[Relation.TransGen R] p w ↔ ∀ n, (□[R])^[n + 1] p w :=
  ⟨fun h n => box_iterate_succ_of_box_transGen R n h,
   fun h _ hv => let ⟨n, hn⟩ := exists_box_iterate_imp_of_transGen R hv; hn p (h n)⟩

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

/-- Over a KD45 frame the modalities collapse: `◇□p ↔ □p`. An agent introspective about her
own beliefs considers it possible that she must do something exactly when she must. -/
theorem diamond_box_iff [IsKD45Frame R] {p : W → Prop} {w : W} :
    ◇[R] (□[R] p) w ↔ □[R] p w :=
  ⟨box_of_diamond_box, diamond_box_of_box⟩

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

/-! ### Necessity and possibility of propositions as sets

A proposition as a set `p : Set W` carries `box` and `diamond` through membership: `nec R p`
is the `SetRel.core` and `poss R p` the `SetRel.preimage` of the accessibility relation. The
relation may run between different world types, as when a modal base pairs an evaluation world
with the worlds of a prejacent. -/

section Sets

variable {W' : Type*} (R : W' → W → Prop) {p q : Set W} {x : W'}

/-- The worlds all of whose accessible worlds lie in `p`: `□[R]` on a proposition as a set. -/
def nec (p : Set W) : Set W' := {x | ∀ v, R x v → v ∈ p}

/-- The worlds with an accessible world in `p`: `◇[R]` on a proposition as a set. -/
def poss (p : Set W) : Set W' := {x | ∃ v, R x v ∧ v ∈ p}

@[simp] theorem mem_nec : x ∈ nec R p ↔ ∀ v, R x v → v ∈ p := Iff.rfl

@[simp] theorem mem_poss : x ∈ poss R p ↔ ∃ v, R x v ∧ v ∈ p := Iff.rfl

theorem mem_nec_iff_box {R : W → W → Prop} {w : W} : w ∈ nec R p ↔ □[R] (· ∈ p) w :=
  Iff.rfl

theorem mem_poss_iff_diamond {R : W → W → Prop} {w : W} :
    w ∈ poss R p ↔ ◇[R] (· ∈ p) w :=
  Iff.rfl

variable {R}

theorem nec_mono : Monotone (nec R) := fun _ _ h _ hx v hv => h (hx v hv)

theorem poss_mono : Monotone (poss R) := fun _ _ h _ ⟨v, hv, hp⟩ => ⟨v, hv, h hp⟩

@[simp] theorem compl_nec : (nec R p)ᶜ = poss R pᶜ := by
  ext; simp [not_forall]

@[simp] theorem compl_poss : (poss R p)ᶜ = nec R pᶜ := by
  ext; simp [not_exists, not_and]

theorem nec_inter : nec R (p ∩ q) = nec R p ∩ nec R q := by
  ext; simp [forall_and]

theorem poss_union : poss R (p ∪ q) = poss R p ∪ poss R q := by
  ext; simp [exists_or, and_or_left]

theorem poss_inter_subset : poss R (p ∩ q) ⊆ poss R p ∩ poss R q :=
  fun _ ⟨v, hv, h⟩ => ⟨⟨v, hv, h.1⟩, ⟨v, hv, h.2⟩⟩

theorem nec_union_subset : nec R p ∪ nec R q ⊆ nec R (p ∪ q) :=
  fun _ h v hv => h.elim (fun h => Or.inl (h v hv)) (fun h => Or.inr (h v hv))

@[simp] theorem nec_univ : nec R (Set.univ : Set W) = Set.univ := by simp [Set.eq_univ_iff_forall]

@[simp] theorem poss_empty : poss R (∅ : Set W) = ∅ := by simp [Set.eq_empty_iff_forall_notMem]

/-- Over the identity relation both operators are the identity. -/
@[simp] theorem nec_eq (p : Set W) : nec Eq p = p := by ext; simp

@[simp] theorem poss_eq (p : Set W) : poss Eq p = p := by ext; simp

end Sets

/-! ### Decidability over finite worlds -/

instance [Fintype W] (R : W → W → Prop) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (box R p w) :=
  inferInstanceAs (Decidable (∀ v, R w v → p v))

instance [Fintype W] (R : W → W → Prop) (p : W → Prop) (w : W)
    [∀ v, Decidable (R w v)] [DecidablePred p] :
    Decidable (diamond R p w) :=
  inferInstanceAs (Decidable (∃ v, R w v ∧ p v))

instance {W' : Type*} [Fintype W] (R : W' → W → Prop) (p : Set W) (x : W')
    [∀ v, Decidable (R x v)] [DecidablePred (· ∈ p)] :
    Decidable (x ∈ nec R p) :=
  inferInstanceAs (Decidable (∀ v, R x v → v ∈ p))

instance {W' : Type*} [Fintype W] (R : W' → W → Prop) (p : Set W) (x : W')
    [∀ v, Decidable (R x v)] [DecidablePred (· ∈ p)] :
    Decidable (x ∈ poss R p) :=
  inferInstanceAs (Decidable (∃ v, R x v ∧ v ∈ p))

end ModalLogic
