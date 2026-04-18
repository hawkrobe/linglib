import Mathlib.Data.Setoid.Basic
import Linglib.Core.Mood.POSW

/-!
# POSW with Inquiry Partition (POSWQ)
@cite{portner-2018} @cite{groenendijk-stokhof-1984} @cite{roberts-2012}

@cite{portner-2018} (Ch. 3) shows that the same POSW substrate that
unifies declarative/imperative force and indicative/subjunctive
selection extends to **interrogative** force as well. The dynamic
treatment of questions adds a third component to the discourse object
— an **inquiry partition** on the context set whose cells are "what
counts as the same answer". @cite{groenendijk-stokhof-1984}'s
partition theory makes this component explicit (eq. 66: `∀ w ∈ p,
Q(w) = p`); @cite{roberts-2012}'s QUD architecture treats it as a
separate stack alongside the common ground (eq. 71); inquisitive
semantics (Ciardelli et al. 2013) folds it into a single
informative/inquisitive content.

This file takes the partition route. A `POSWQ W` is a `POSW W` (the
@cite{portner-2018} substrate) extended with an `inquiry : Setoid W`
whose equivalence classes are the open question's possible answers.
The trivial inquiry (`⊤` in the `Setoid` lattice) is "no question
under discussion".

## The 3×3 Portner unification

| layer            | declarative      | imperative       | interrogative      |
|------------------|------------------|------------------|--------------------|
| sentence mood    | assertion (`+`)  | direction (`⋆`)  | inquiry (`?`)      |
| modal necessity  | `boxCs`          | `boxLt`          | `boxAns`           |
| verbal mood      | `.indicative`    | (no analogue)    | `.interrogative`   |

The columns are the three POSW components (`cs`, `lt`, `inquiry`); the
rows are the operations on each component (refining update,
quantification). Refinement of the inquiry partition (`?`-update) is
the partition-side analogue of `+`/`⋆`-update.

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
    substrate enriched with a third component recording the open
    question. The `inquiry : Setoid W` partitions worlds into
    "answers"; its `⊤` element is "no question". -/
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

/-! ## §2. The third update: `?` (inquiry refinement) -/

/-- **`?`-update**: refine the inquiry partition by meet with `q`.
    The partition-side analogue of `+`-update on `cs` and `⋆`-update
    on `lt`: it constrains the third POSW component without touching
    the other two.

    The meet of two equivalence relations on `W` is "agree on both";
    refining the inquiry by `q` shrinks each cell down to its
    intersection with `q`'s cells (jointly-finer partition). -/
def inquire (c : POSWQ W) (q : Setoid W) : POSWQ W :=
  { c with inquiry := c.inquiry ⊓ q }

@[simp] theorem inquire_toPOSW (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).toPOSW = c.toPOSW := rfl

@[simp] theorem inquire_cs (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).cs = c.cs := rfl

@[simp] theorem inquire_lt (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).lt = c.lt := rfl

theorem inquire_inquiry (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).inquiry = c.inquiry ⊓ q := rfl

/-! ## §3. The third modal: `boxAns` (informational answerhood) -/

/-- **Informational answerhood**: `p` is *settled by the question* at
    `c` iff `p` has a constant truth value within every cell of
    `c.inquiry` (restricted to the context set). The answerhood
    counterpart of @cite{portner-2018}'s `boxCs` (truth throughout
    `cs`) and `boxLt` (truth at every best world).

    Unlike `boxCs` and `boxLt`, `boxAns` is *not* upward-monotone in
    `p`: a strengthening of `p` can break the constant-truth property
    on a cell. The natural monotonicity for `boxAns` is *anti*-monotone
    in the inquiry partition (`boxAns_anti_inquiry` below). -/
def boxAns (c : POSWQ W) (p : W → Prop) : Prop :=
  ∀ w v, c.cs w → c.cs v → c.inquiry.r w v → (p w ↔ p v)

/-! ## §4. Disjointness of components

The `+`-, `⋆`-, and `?`-updates target *disjoint* components of the
POSWQ. The first two leave `inquiry` alone (vacuously, since they're
defined on the underlying POSW), and `?`-update leaves both `cs` and
`lt` alone. The Portner unification thesis extends to three columns. -/

theorem inquire_targets_disjoint_components (c : POSWQ W) (q : Setoid W) :
    (c.inquire q).cs = c.cs ∧ (c.inquire q).lt = c.lt :=
  ⟨rfl, rfl⟩

/-! ## §5. Refinement preorder

`POSWQ W` inherits a refinement preorder componentwise from `POSW W`'s
refinement preorder (Mood/POSW.lean §4) and the `Setoid W` lattice:
`c₁ ≤ c₂` iff `c₁.toPOSW ≤ c₂.toPOSW` and `c₁.inquiry ≤ c₂.inquiry`.
Both directions agree on "finer ≤ coarser". -/

instance instPreorder : Preorder (POSWQ W) where
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

/-! ## §7. Distinctness witness: `boxAns` ≠ `boxCs` ∘ projection

The third modal genuinely differs from `boxCs`. We exhibit a POSWQ
where some `p` is settled by the question (`boxAns p`) but is *not*
informationally necessary (`¬ boxCs p`). The witness is a non-trivial
inquiry partition with two cells, where `p` is true on one cell and
false on the other: it has a constant truth value per cell (so
`boxAns`), but is not uniformly true on `cs` (so not `boxCs`). -/

/-- Two-cell inquiry POSWQ: `cs = ⊤` over `Bool`, `lt = ⊤`, with
    `inquiry` the identity Setoid (each Bool in its own cell). -/
def sepPOSWQ : POSWQ Bool where
  cs := fun _ => True
  lt := fun _ _ => True
  lt_refl  := fun _ _ => trivial
  lt_trans := fun _ _ _ _ _ _ _ _ => trivial
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
