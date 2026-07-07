import Mathlib.Data.Setoid.Basic
import Linglib.Semantics.Mood.POSW

/-!
# POSW with Inquiry Partition (POSWQ)
[portner-2018] [groenendijk-stokhof-1984] [roberts-2012]

This file is **our extension** of the POSW substrate
(`Semantics/Mood/POSW.lean`: [veltman-1996]'s `ExpState` under
[portner-2018]'s modal reading) to interrogative force, by way of a
third component recording the open question: `info` and `order` stay
intact and `inquiry : Setoid W` is a separate third coordinate, so
`assert`, `promote`, `inquire` each touch one component and the
inquiry partition composes orthogonally with the other two
refinements. [portner-2018]'s verbal-mood unification itself is
stated over the two POSW components only; the separate question
coordinate follows the architecture of [portner-2004]'s discourse
model, which keeps the Question Set apart from the Common Ground and
the To-Do Lists.

The third-component idea is grounded in the dynamic-question tradition:
[groenendijk-stokhof-1984]'s partition theory takes the meaning of
a question to be an equivalence relation on worlds; [roberts-2012]
maintains a QUD stack alongside the common ground; inquisitive
semantics ([ciardelli-groenendijk-roelofsen-2018]) folds it into a
single informative/inquisitive content. The Setoid representation
makes the partition view directly available via mathlib's
`CompleteLattice (Setoid W)`.

## The 3×3 Portner-style unification

| layer            | declarative      | imperative       | interrogative      |
|------------------|------------------|------------------|--------------------|
| sentence mood    | `assert` (`+`)   | `promote` (`⋆`)  | `inquire` (`?`)    |
| modal necessity  | `boxCs`          | `boxLe`          | `boxAns`           |
| verbal mood      | `.indicative`    | (no analogue)    | `.interrogative`   |

The columns are the three components (`info`, `order`, `inquiry`); the
rows are the operations on each component (refining update,
quantification). Refinement of the inquiry partition (`?`-update),
the modal `boxAns`, and the third column entries are this library's
extensions; they do not appear in [portner-2018]. Each update is meet
in its component's lattice (`Pi` over `Prop` for `info`; the preorder
lattice via `Normality.refine` for `order`; `Setoid.completeLattice`
for `inquiry`), so commutativity and idempotency are one-line
`inf`-facts throughout.

## Support vs necessity, inquiry column

Acceptance-as-fixpoint extends to the third coordinate: the state
supports `inquire q` iff its inquiry already refines `q`
(`le_inquire_iff`). Routing a proposition through `polarSetoid`,
support implies answerhood (`boxAns_of_inquiry_le_polarSetoid`), and
the two coincide when `info = Set.univ`
(`inquiry_le_polarSetoid_iff_boxAns_of_univ`) — `boxAns` is
`info`-relativized while the inquiry coordinate is not.

## Architectural note: Setoid vs. InquisitiveContent

We commit `inquiry : Setoid W` (partition-based questions). The
state-of-the-art generalization is the algebraic / inquisitive-
semantics frame of [puncochar-2016] (lattice-of-logics
characterization, with inquisitive logic as the strongest "G-logic"),
[puncochar-2019] (information models on substructural bases;
declarative propositions as principal ideals), and
[ciardelli-groenendijk-roelofsen-2018] (the textbook), in which
inquiry would be a downward-closed nonempty set of information states
rather than a partition. That generalization handles non-partition
inquiry — mention-some, intermediate-exhaustive, and conditional
question phenomena — that `Setoid W` provably cannot represent
(partition cells are disjoint and exhaustive).

We do not lift to `InquisitiveContent W` here. Following mathlib
discipline, the lift should be triggered by a forcing phenomenon
study, not built speculatively. The clearest forcing candidate is
[theiler-etal-2018]'s uniform semantics for declarative and
interrogative complements, which derives mention-some and
intermediate-exhaustive readings as theorems and shows that
[groenendijk-stokhof-1984]'s partition theory provably cannot.
When that study is formalized in `Studies/`, the
`InquisitiveContent W` type becomes load-bearing; until then, every
existing POSWQ use case is partition-based and `Setoid W` is the
right structure (mathlib already provides its `CompleteLattice`).

The lift, when it happens, should be a **sibling** structure (parallel
to Setoid, with `Setoid → InquisitiveContent` as a faithful embedding)
rather than a replacement — mirroring how mathlib keeps `Set`/`Finset`
and `Filter`/`Ultrafilter` parallel rather than collapsing them.
-/

namespace Semantics.Mood

open Semantics.Dynamic.Default

/-- A **POSW with an inquiry partition** (POSWQ): the POSW substrate
    (an `ExpState`) enriched with a third component recording the open
    question. The `inquiry : Setoid W` partitions worlds into
    "answers"; its `⊤` element is "no question". The three-coordinate
    packaging is ours; the separate question coordinate follows
    [portner-2004]'s Question Set (kept apart from the Common Ground),
    while [portner-2018]'s verbal-mood unification is stated over the
    two POSW components only. -/
structure POSWQ (W : Type*) extends ExpState W where
  /-- The inquiry partition: `inquiry.r w v` means worlds `w` and `v`
      are indistinguishable answers to the open question. -/
  inquiry : Setoid W

namespace POSWQ

variable {W : Type*}

/-! ### Constructors -/

/-- Lift an expectation state to a POSWQ with no question under
    discussion (trivial inquiry partition: every world is in the same
    cell). -/
def ofExpState (σ : ExpState W) : POSWQ W :=
  { σ with inquiry := ⊤ }

@[simp] theorem ofExpState_toExpState (σ : ExpState W) :
    (ofExpState σ).toExpState = σ := rfl

@[simp] theorem ofExpState_inquiry (σ : ExpState W) :
    (ofExpState σ).inquiry = (⊤ : Setoid W) := rfl

/-- The **polar Setoid** of a proposition `q : W → Prop`: two worlds
    are equivalent iff they agree on `q`. The smallest piece of
    partition structure a single proposition can contribute to an
    inquiry. The `Setoid` lattice's `⊤` is the trivial inquiry
    (`q = ⊤`), and meeting two polar Setoids gives the polar
    Setoid for the conjunction (up to logical equivalence).

    Distinct from mathlib's `Setoid.ker q`, which uses `=` on
    propositions rather than `↔`; we keep `↔` to make
    `polarSetoid_r` definitionally `Iff.rfl`. -/
def polarSetoid (q : W → Prop) : Setoid W where
  r w v := q w ↔ q v
  iseqv :=
    { refl := fun _ => Iff.rfl
      symm := fun h => h.symm
      trans := fun h₁ h₂ => h₁.trans h₂ }

@[simp] theorem polarSetoid_r (q : W → Prop) (w v : W) :
    (polarSetoid q).r w v ↔ (q w ↔ q v) := Iff.rfl

@[simp] theorem polarSetoid_top : polarSetoid (W := W) (fun _ => True) = ⊤ := by
  ext w v
  simp

/-! ### The third update: `?` (inquiry refinement) -/

/-- **`?`-update** (our extension; not in [portner-2018]): refine
    the inquiry partition by meet with `q`. The partition-side
    analogue of `assert` on `info` and `promote` on `order`: it
    constrains the third component without touching the other two.

    The meet of two equivalence relations on `W` is "agree on both";
    refining the inquiry by `q` shrinks each cell down to its
    intersection with `q`'s cells (jointly-finer partition). -/
def inquire (c : POSWQ W) (q : Setoid W) : POSWQ W :=
  { c with inquiry := c.inquiry ⊓ q }

@[simp] theorem inquire_toExpState (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).toExpState = c.toExpState := rfl

@[simp] theorem inquire_info (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).info = c.info := rfl

@[simp] theorem inquire_order (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).order = c.order := rfl

/-- `?`-update is meet in `Setoid.completeLattice W` — the inquiry-side
    analogue of `assert` (meet in `W → Prop`) and `promote` (meet with
    the criterion preorder, `Normality.refine`). Definitional. -/
@[simp] theorem inquire_inquiry_eq_inf (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).inquiry = c.inquiry ⊓ q := rfl

/-! ### The third modal: `boxAns` (informational answerhood) -/

/-- **Informational answerhood** (our extension): `p` is *settled by the
    question* at `c` iff `p` has a constant truth value within every
    cell of `c.inquiry` (restricted to the information state). The
    answerhood counterpart of `boxCs` (truth throughout `info`) and
    `boxLe` (truth at every best world); the formulation is closest in
    spirit to [groenendijk-stokhof-1984] answerhood.

    Unlike `boxCs` and `boxLe`, `boxAns` is *not* upward-monotone in
    `p`: a strengthening of `p` can break the constant-truth property
    on a cell. The natural monotonicity for `boxAns` is *anti*-monotone
    in the inquiry partition (`boxAns_anti` below). -/
def boxAns (c : POSWQ W) (p : W → Prop) : Prop :=
  ∀ w v, w ∈ c.info → v ∈ c.info → c.inquiry.r w v → (p w ↔ p v)

/-! ### Refinement preorder

`POSWQ W` inherits a refinement preorder componentwise from the
`ExpState` refinement preorder and the `Setoid W` lattice:
`c₁ ≤ c₂` iff `c₁.toExpState ≤ c₂.toExpState` and
`c₁.inquiry ≤ c₂.inquiry`. All components agree on "finer ≤
coarser". -/

instance : Preorder (POSWQ W) where
  le c₁ c₂ := c₁.toExpState ≤ c₂.toExpState ∧ c₁.inquiry ≤ c₂.inquiry
  le_refl c := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

theorem le_iff (c₁ c₂ : POSWQ W) :
    c₁ ≤ c₂ ↔ c₁.toExpState ≤ c₂.toExpState ∧ c₁.inquiry ≤ c₂.inquiry :=
  Iff.rfl

/-- `?`-update lands below the input: refining `inquiry` by meet with
    `q` can only constrain the POSWQ further. The third-component
    analogue of `ExpState.assert_le_self` and
    `ExpState.promote_le_self`. -/
theorem inquire_le_self (c : POSWQ W) (q : Setoid W) : c.inquire q ≤ c :=
  ⟨le_refl _, inf_le_left⟩

/-- `?`-update is monotone in the underlying POSWQ. -/
theorem inquire_mono {c₁ c₂ : POSWQ W} (h : c₁ ≤ c₂) (q : Setoid W) :
    c₁.inquire q ≤ c₂.inquire q :=
  ⟨h.1, inf_le_inf_right q h.2⟩

/-- **Acceptance fixpoint for `inquire`**: the input refines its own
    `?`-update iff its inquiry already refines the question. The
    third-coordinate instance of [veltman-1996]'s acceptance
    (`ExpState.le_assert_iff`, `ExpState.le_promote_iff`). -/
theorem le_inquire_iff (c : POSWQ W) (q : Setoid W) :
    c ≤ c.inquire q ↔ c.inquiry ≤ q :=
  ⟨fun h => le_trans h.2 inf_le_right,
   fun h => ⟨le_refl _, le_inf (le_refl _) h⟩⟩

/-- Support implies answerhood: if the inquiry already refines `p`'s
    polar partition, `p` is settled by the question. -/
theorem boxAns_of_inquiry_le_polarSetoid (c : POSWQ W) (p : W → Prop)
    (h : c.inquiry ≤ polarSetoid p) : c.boxAns p :=
  fun _ _ _ _ hwv => h hwv

/-- On states with total information (`info = Set.univ`), answerhood
    *is* inquiry-support for the polar partition: the `info`-guards in
    `boxAns` are the only gap between the two. -/
theorem inquiry_le_polarSetoid_iff_boxAns_of_univ (c : POSWQ W)
    (p : W → Prop) (h : c.info = Set.univ) :
    c.inquiry ≤ polarSetoid p ↔ c.boxAns p :=
  ⟨fun hle => c.boxAns_of_inquiry_le_polarSetoid p hle,
   fun hbox w v hwv =>
     hbox w v (h ▸ Set.mem_univ w) (h ▸ Set.mem_univ v) hwv⟩

/-- Refining the POSWQ *strengthens* informational answerhood: if
    `c₁` is more refined than `c₂` and `p` is settled by the question
    at `c₂`, then `p` is settled at `c₁` too. The answerhood
    counterpart of `ExpState.boxCs_anti`. -/
theorem boxAns_anti (c₁ c₂ : POSWQ W) (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxAns p → c₁.boxAns p :=
  fun hbox w v hw hv hwv =>
    hbox w v (h.1.1 hw) (h.1.1 hv) (h.2 hwv)

/-! ### Closure properties of `boxAns`

`boxAns p` says "`p` is constant on each inquiry cell within `info`".
This class of propositions is closed under the standard logical
operations — answers to a question can be combined like ordinary
propositions. -/

/-- Negation preserves answerhood. -/
theorem boxAns_not (c : POSWQ W) (p : W → Prop) :
    c.boxAns p → c.boxAns (fun w => ¬ p w) :=
  fun hp w v hw hv hwv =>
    ⟨fun hnpw hpv => hnpw ((hp w v hw hv hwv).mpr hpv),
     fun hnpv hpw => hnpv ((hp w v hw hv hwv).mp hpw)⟩

/-- Conjunction preserves answerhood. -/
theorem boxAns_and (c : POSWQ W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w => p w ∧ q w) :=
  fun hp hq w v hw hv hwv =>
    ⟨fun ⟨hpw, hqw⟩ => ⟨(hp w v hw hv hwv).mp hpw, (hq w v hw hv hwv).mp hqw⟩,
     fun ⟨hpv, hqv⟩ => ⟨(hp w v hw hv hwv).mpr hpv, (hq w v hw hv hwv).mpr hqv⟩⟩

/-- Disjunction preserves answerhood. -/
theorem boxAns_or (c : POSWQ W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w => p w ∨ q w) :=
  fun hp hq w v hw hv hwv =>
    ⟨fun hpqw => hpqw.elim
      (fun hpw => Or.inl ((hp w v hw hv hwv).mp hpw))
      (fun hqw => Or.inr ((hq w v hw hv hwv).mp hqw)),
     fun hpqv => hpqv.elim
      (fun hpv => Or.inl ((hp w v hw hv hwv).mpr hpv))
      (fun hqv => Or.inr ((hq w v hw hv hwv).mpr hqv))⟩

/-- Material implication preserves answerhood. Follows from the
    Boolean-algebra closure of constant-on-cell propositions. -/
theorem boxAns_imp (c : POSWQ W) (p q : W → Prop) :
    c.boxAns p → c.boxAns q → c.boxAns (fun w => p w → q w) :=
  fun hp hq w v hw hv hwv =>
    ⟨fun himp hpv => (hq w v hw hv hwv).mp (himp ((hp w v hw hv hwv).mpr hpv)),
     fun himp hpw => (hq w v hw hv hwv).mpr (himp ((hp w v hw hv hwv).mp hpw))⟩

/-! ### Three-component update disjointness

The three updates `assert`, `promote`, `inquire` touch disjoint POSWQ
components, so they pairwise commute when lifted to act on `POSWQ`.
The lifts are defined here because `ExpState.assert` and
`ExpState.promote` strip the inquiry field; `POSWQ.assert` and
`POSWQ.promote` are the inquiry-preserving counterparts. -/

/-- POSWQ-side `+`-update: refine `info` while preserving the inquiry
    partition. The inquiry-preserving lift of `ExpState.assert`. -/
def assert (c : POSWQ W) (p : W → Prop) : POSWQ W :=
  { c.toExpState.assert p with inquiry := c.inquiry }

/-- POSWQ-side `⋆`-update: refine `order` while preserving the inquiry
    partition. The inquiry-preserving lift of `ExpState.promote`. -/
def promote (c : POSWQ W) (p : W → Prop) : POSWQ W :=
  { c.toExpState.promote p with inquiry := c.inquiry }

@[simp] theorem assert_toExpState (c : POSWQ W) (p : W → Prop) :
    (c.assert p).toExpState = c.toExpState.assert p := rfl

@[simp] theorem assert_inquiry (c : POSWQ W) (p : W → Prop) :
    (c.assert p).inquiry = c.inquiry := rfl

@[simp] theorem promote_toExpState (c : POSWQ W) (p : W → Prop) :
    (c.promote p).toExpState = c.toExpState.promote p := rfl

@[simp] theorem promote_inquiry (c : POSWQ W) (p : W → Prop) :
    (c.promote p).inquiry = c.inquiry := rfl

/-- `assert` and `promote` commute on POSWQ: the components never
    interact. -/
@[simp] theorem assert_promote_comm (c : POSWQ W) (p q : W → Prop) :
    (c.assert p).promote q = (c.promote q).assert p := rfl

/-- `assert` and `inquire` commute on POSWQ: each touches a different
    component. -/
@[simp] theorem assert_inquire_comm (c : POSWQ W) (p : W → Prop) (s : Setoid W) :
    (c.assert p).inquire s = (c.inquire s).assert p := rfl

/-- `promote` and `inquire` commute on POSWQ: each touches a different
    component. -/
@[simp] theorem promote_inquire_comm (c : POSWQ W) (p : W → Prop) (s : Setoid W) :
    (c.promote p).inquire s = (c.inquire s).promote p := rfl

/-- `?`-update is idempotent on the same partition: refining inquiry
    by `s` twice equals refining once. The Setoid-meet is idempotent
    in the `CompleteLattice (Setoid W)`. -/
theorem inquire_inquire_self (c : POSWQ W) (s : Setoid W) :
    ((c.inquire s).inquire s).inquiry = (c.inquire s).inquiry := by
  show (c.inquiry ⊓ s) ⊓ s = c.inquiry ⊓ s
  rw [inf_assoc, inf_idem]

/-! ### Distinctness witness: `boxAns` ≠ `boxCs` ∘ projection

The third modal genuinely differs from `boxCs`. We exhibit a POSWQ
where some `p` is settled by the question (`boxAns p`) but is *not*
informationally necessary (`¬ boxCs p`). The witness is a non-trivial
inquiry partition with two cells, where `p` is true on one cell and
false on the other: it has a constant truth value per cell (so
`boxAns`), but is not uniformly true on `info` (so not `boxCs`). -/

/-- Two-cell inquiry POSWQ: `info = Set.univ` over `Bool`, `order`
    total, with `inquiry` the identity Setoid (each Bool in its own
    cell). -/
def sepPOSWQ : POSWQ Bool where
  info := Set.univ
  order := Core.Order.Normality.total
  inquiry := { r := fun w v => w = v, iseqv :=
    ⟨fun _ => rfl, fun {_ _} h => h.symm, fun {_ _ _} h₁ h₂ => h₁.trans h₂⟩ }

/-- Separation proposition: only `false` satisfies it. -/
def sepProp : Bool → Prop := fun w => w = false

/-- The separation proposition is settled by the question at
    `sepPOSWQ`: within each (singleton) cell, its truth value is
    constant. -/
theorem boxAns_sepPOSWQ_sepProp : sepPOSWQ.boxAns sepProp := by
  intro w v _ _ hwv
  rw [show w = v from hwv]

/-- The separation proposition is *not* informationally necessary at
    `sepPOSWQ.toExpState`: `true` is in `info` but does not satisfy
    `p`. -/
theorem not_boxCs_sepPOSWQ_sepProp : ¬ sepPOSWQ.toExpState.boxCs sepProp := by
  intro h
  exact Bool.noConfusion (h true trivial)

/-- **`boxAns` and `boxCs` are not interderivable** on the POSW substrate
    alone: there exists a POSWQ and a proposition where `boxAns` holds
    and `boxCs` fails. The inquiry component is doing genuine work. -/
theorem boxAns_not_reducible_to_boxCs :
    ∃ (c : POSWQ Bool) (p : Bool → Prop),
      c.boxAns p ∧ ¬ c.toExpState.boxCs p :=
  ⟨sepPOSWQ, sepProp, boxAns_sepPOSWQ_sepProp, not_boxCs_sepPOSWQ_sepProp⟩

end POSWQ
end Semantics.Mood
