import Mathlib.Data.Setoid.Basic
import Linglib.Core.Mood.POSW

/-!
# POSW with Inquiry Partition (POSWQ)
@cite{portner-2018} @cite{groenendijk-stokhof-1984} @cite{roberts-2012}

This file is **our extension** of @cite{portner-2018}'s POSW substrate
to interrogative force, by way of a third component recording the open
question. It is not the extension Portner himself works out.
Portner's interrogative variant — **PPOSW** — replaces `cs` with a
*partition* of `cs`, so the "informational" and "inquisitive"
components are fused. We instead keep `cs` intact and add `inquiry :
Setoid W` as a separate third coordinate; this preserves Portner's
disjoint-target story (`+`, `⋆`, `?` each touch one component) and
lets the inquiry partition compose orthogonally with `cs`-refinement
and `≤`-refinement.

The third-component idea is grounded in the dynamic-question tradition:
@cite{groenendijk-stokhof-1984}'s partition theory takes the meaning of
a question to be an equivalence relation on worlds; @cite{roberts-2012}
maintains a QUD stack alongside the common ground; inquisitive
semantics (Ciardelli et al. 2013) folds it into a single
informative/inquisitive content. The Setoid representation makes the
partition view directly available via mathlib's `CompleteLattice
(Setoid W)`.

## The 3×3 Portner-style unification

| layer            | declarative      | imperative       | interrogative      |
|------------------|------------------|------------------|--------------------|
| sentence mood    | assertion (`+`)  | direction (`⋆`)  | inquiry (`?`)      |
| modal necessity  | `boxCs`          | `boxLe`          | `boxAns`           |
| verbal mood      | `.indicative`    | (no analogue)    | `.interrogative`   |

The columns are the three POSW components (`cs`, `le`, `inquiry`); the
rows are the operations on each component (refining update,
quantification). Refinement of the inquiry partition (`?`-update),
the modal `boxAns`, and the third column entries are this library's
extensions; they do not appear in @cite{portner-2018}.

## Mathlib alignment

- `inquiry : Setoid W` uses mathlib's `CompleteLattice (Setoid W)`
  instance directly: `⊓` for partition meet (jointly-finer), `≤` for
  refinement (finer ≤ coarser).
- The Setoid `≤` convention (`r ≤ s ↔ ∀ x y, r x y → s x y`) coincides
  with the POSW refinement preorder convention from
  `Linglib/Core/Mood/POSW.lean` §4: finer ≤ coarser, more
  discriminating ≤ less discriminating.
- `extends POSW W` mirrors `Group extends Monoid`: a POSWQ *is* a POSW
  (via the auto-generated `POSWQ.toPOSW`) plus extra structure.
-/

namespace Core.Mood

universe u

/-- A **POSW with an inquiry partition** (POSWQ): the @cite{portner-2018}
    POSW substrate enriched with a third component recording the open
    question. The `inquiry : Setoid W` partitions worlds into
    "answers"; its `⊤` element is "no question". This three-coordinate
    extension is ours and is distinct from @cite{portner-2018}'s own
    PPOSW (which replaces `cs` with a partition rather than adding a
    third field). -/
structure POSWQ (W : Type u) extends POSW W where
  /-- The inquiry partition: `inquiry.r w v` means worlds `w` and `v`
      are indistinguishable answers to the open question. -/
  inquiry : Setoid W

namespace POSWQ

variable {W : Type u}

/-! ## §1. Constructors -/

/-- Lift a POSW to a POSWQ with no question under discussion (trivial
    inquiry partition: every world is in the same cell). -/
def ofPOSW (c : POSW W) : POSWQ W :=
  { c with inquiry := ⊤ }

@[simp] theorem ofPOSW_toPOSW (c : POSW W) : (ofPOSW c).toPOSW = c := rfl

@[simp] theorem ofPOSW_inquiry (c : POSW W) :
    (ofPOSW c).inquiry = (⊤ : Setoid W) := rfl

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

/-! ## §2. The third update: `?` (inquiry refinement) -/

/-- **`?`-update** (our extension; not in @cite{portner-2018}): refine
    the inquiry partition by meet with `q`. The partition-side
    analogue of `+`-update on `cs` and `⋆`-update on `le`: it
    constrains the third POSW component without touching the other
    two.

    The meet of two equivalence relations on `W` is "agree on both";
    refining the inquiry by `q` shrinks each cell down to its
    intersection with `q`'s cells (jointly-finer partition). -/
def inquire (c : POSWQ W) (q : Setoid W) : POSWQ W :=
  { c with inquiry := c.inquiry ⊓ q }

@[simp] theorem inquire_toPOSW (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).toPOSW = c.toPOSW := rfl

@[simp] theorem inquire_cs (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).cs = c.cs := rfl

@[simp] theorem inquire_le (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).le = c.le := rfl

theorem inquire_inquiry (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).inquiry = c.inquiry ⊓ q := rfl

/-! ## §3. The third modal: `boxAns` (informational answerhood) -/

/-- **Informational answerhood** (our extension): `p` is *settled by the
    question* at `c` iff `p` has a constant truth value within every
    cell of `c.inquiry` (restricted to the context set). The
    answerhood counterpart of @cite{portner-2018}'s `boxCs` (truth
    throughout `cs`) and `boxLe` (truth at every best world); the
    formulation is closest in spirit to @cite{groenendijk-stokhof-1984}
    answerhood.

    Unlike `boxCs` and `boxLe`, `boxAns` is *not* upward-monotone in
    `p`: a strengthening of `p` can break the constant-truth property
    on a cell. The natural monotonicity for `boxAns` is *anti*-monotone
    in the inquiry partition (`boxAns_anti` below). -/
def boxAns (c : POSWQ W) (p : W → Prop) : Prop :=
  ∀ w v, c.cs w → c.cs v → c.inquiry.r w v → (p w ↔ p v)

/-! ## §4. Disjointness of components

The `+`-, `⋆`-, and `?`-updates target *disjoint* components of the
POSWQ. The first two leave `inquiry` alone (vacuously, since they're
defined on the underlying POSW), and `?`-update leaves both `cs` and
`le` alone. The Portner unification thesis extends to three columns. -/

theorem inquire_targets_disjoint_components (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).cs = c.cs ∧ (c.inquire q).le = c.le :=
  ⟨rfl, rfl⟩

/-! ## §5. Refinement preorder

`POSWQ W` inherits a refinement preorder componentwise from `POSW W`'s
refinement preorder (Mood/POSW.lean §4) and the `Setoid W` lattice:
`c₁ ≤ c₂` iff `c₁.toPOSW ≤ c₂.toPOSW` and `c₁.inquiry ≤ c₂.inquiry`.
Both directions agree on "finer ≤ coarser". -/

instance : Preorder (POSWQ W) where
  le c₁ c₂ := c₁.toPOSW ≤ c₂.toPOSW ∧ c₁.inquiry ≤ c₂.inquiry
  le_refl c := ⟨le_refl _, le_refl _⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2 h₂₃.2⟩

theorem le_iff (c₁ c₂ : POSWQ W) :
    c₁ ≤ c₂ ↔ c₁.toPOSW ≤ c₂.toPOSW ∧ c₁.inquiry ≤ c₂.inquiry :=
  Iff.rfl

/-- `?`-update lands below the input: refining `inquiry` by meet with
    `q` can only constrain the POSWQ further. The third-component
    analogue of `POSW.plus_le_self` and `POSW.star_le_self`. -/
theorem inquire_le_self (c : POSWQ W) (q : Setoid W) : c.inquire q ≤ c :=
  ⟨le_refl _, inf_le_left⟩

/-- `?`-update is monotone in the underlying POSWQ. -/
theorem inquire_mono {c₁ c₂ : POSWQ W} (h : c₁ ≤ c₂) (q : Setoid W) :
    c₁.inquire q ≤ c₂.inquire q :=
  ⟨h.1, inf_le_inf_right q h.2⟩

/-- Refining the POSWQ *strengthens* informational answerhood: if
    `c₁` is more refined than `c₂` and `p` is settled by the question
    at `c₂`, then `p` is settled at `c₁` too. The answerhood
    counterpart of `POSW.boxCs_anti`. -/
theorem boxAns_anti (c₁ c₂ : POSWQ W) (h : c₁ ≤ c₂) (p : W → Prop) :
    c₂.boxAns p → c₁.boxAns p :=
  fun hbox w v hw hv hwv =>
    hbox w v (h.1.1 w hw) (h.1.1 v hv) (h.2 hwv)

/-! ## §6. Closure properties of `boxAns`

`boxAns p` says "`p` is constant on each inquiry cell within `cs`".
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

/-! ## §7. Three-component update disjointness

The three updates `+`, `⋆`, `?` touch disjoint POSWQ components, so
they pairwise commute when lifted to act on `POSWQ`. The lifts are
defined here because `POSW.plus` and `POSW.star` strip the inquiry
field; `POSWQ.plus` and `POSWQ.star` are the inquiry-preserving
counterparts. -/

/-- POSWQ-side `+`-update: refine `cs` while preserving the inquiry
    partition. The inquiry-preserving lift of `POSW.plus`. -/
def plus (c : POSWQ W) (p : W → Prop) : POSWQ W :=
  { c.toPOSW.plus p with inquiry := c.inquiry }

/-- POSWQ-side `⋆`-update: refine `le` while preserving the inquiry
    partition. The inquiry-preserving lift of `POSW.star`. -/
def star (c : POSWQ W) (p : W → Prop) : POSWQ W :=
  { c.toPOSW.star p with inquiry := c.inquiry }

@[simp] theorem plus_toPOSW (c : POSWQ W) (p : W → Prop) :
    (c.plus p).toPOSW = c.toPOSW.plus p := rfl

@[simp] theorem plus_inquiry (c : POSWQ W) (p : W → Prop) :
    (c.plus p).inquiry = c.inquiry := rfl

@[simp] theorem star_toPOSW (c : POSWQ W) (p : W → Prop) :
    (c.star p).toPOSW = c.toPOSW.star p := rfl

@[simp] theorem star_inquiry (c : POSWQ W) (p : W → Prop) :
    (c.star p).inquiry = c.inquiry := rfl

/-- `+` and `⋆` commute on POSWQ: applying `+`-then-`⋆` and `⋆`-then-`+`
    produces the same POSWQ. The components never interact. -/
@[simp] theorem plus_star_comm (c : POSWQ W) (p q : W → Prop) :
    (c.plus p).star q = (c.star q).plus p := rfl

/-- `+` and `?` commute on POSWQ: each touches a different component. -/
@[simp] theorem plus_inquire_comm (c : POSWQ W) (p : W → Prop) (s : Setoid W) :
    (c.plus p).inquire s = (c.inquire s).plus p := rfl

/-- `⋆` and `?` commute on POSWQ: each touches a different component. -/
@[simp] theorem star_inquire_comm (c : POSWQ W) (p : W → Prop) (s : Setoid W) :
    (c.star p).inquire s = (c.inquire s).star p := rfl

/-- `?`-update is idempotent on the same partition: refining inquiry
    by `s` twice equals refining once. The Setoid-meet is idempotent
    in the `CompleteLattice (Setoid W)`. -/
theorem inquire_inquire_self (c : POSWQ W) (s : Setoid W) :
    ((c.inquire s).inquire s).inquiry = (c.inquire s).inquiry := by
  show (c.inquiry ⊓ s) ⊓ s = c.inquiry ⊓ s
  rw [inf_assoc, inf_idem]

/-! ## §8. Distinctness witness: `boxAns` ≠ `boxCs` ∘ projection

The third modal genuinely differs from `boxCs`. We exhibit a POSWQ
where some `p` is settled by the question (`boxAns p`) but is *not*
informationally necessary (`¬ boxCs p`). The witness is a non-trivial
inquiry partition with two cells, where `p` is true on one cell and
false on the other: it has a constant truth value per cell (so
`boxAns`), but is not uniformly true on `cs` (so not `boxCs`). -/

/-- Two-cell inquiry POSWQ: `cs = ⊤` over `Bool`, `le = ⊤`, with
    `inquiry` the identity Setoid (each Bool in its own cell). -/
def sepPOSWQ : POSWQ Bool where
  cs := fun _ => True
  le := fun _ _ => True
  le_refl  := fun _ _ => trivial
  le_trans := fun _ _ _ _ _ _ _ _ => trivial
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
    `sepPOSWQ.toPOSW`: `true` is in `cs` but does not satisfy `p`. -/
theorem not_boxCs_sepPOSWQ_sepProp : ¬ sepPOSWQ.toPOSW.boxCs sepProp := by
  intro h
  exact Bool.noConfusion (h true trivial)

/-- **`boxAns` and `boxCs` are not interderivable** on the POSW substrate
    alone: there exists a POSWQ and a proposition where `boxAns` holds
    and `boxCs` fails. The inquiry component is doing genuine work. -/
theorem boxAns_not_reducible_to_boxCs :
    ∃ (c : POSWQ Bool) (p : Bool → Prop),
      c.boxAns p ∧ ¬ c.toPOSW.boxCs p :=
  ⟨sepPOSWQ, sepProp, boxAns_sepPOSWQ_sepProp, not_boxCs_sepPOSWQ_sepProp⟩

end POSWQ
end Core.Mood
