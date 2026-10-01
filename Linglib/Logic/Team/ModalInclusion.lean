module

public import Linglib.Logic.Team.Kripke
public import Linglib.Logic.Modal.Defs
public import Linglib.Logic.Team.Operations
public import Linglib.Logic.Team.Closure
public import Linglib.Logic.Team.Definability
public import Linglib.Logic.Team.Atoms

/-!
# Modal Inclusion Logic (MIL)

[anttila-haggblom-yang-2024] [anttila-2025]

Modal inclusion logic ML(⊆) extends classical modal logic with an
**inclusion atom** `x⃗ ⊆ y⃗` meaning: for every tuple of `x⃗`-truth-values
realised at some world in the team, the same tuple is realised as a
tuple of `y⃗`-truth-values at some world in the team. Introduced for
team semantics by Galliani; the modal variant ML(⊆) is axiomatised in
[anttila-haggblom-yang-2024] (*Archive for Mathematical Logic*
2025; arXiv:2312.02285), which is also [anttila-2025] Chapter 5.

Unlike BSML / MDL, **MIL is unilateral**: there is only a support
relation, no separate anti-support. Negation is restricted to classical
sub-formulas and defined by pointwise team-extension of classical
Kripke negation. This file follows AHY 2024's exact Definition 2.2 and
provides single-polarity `eval`.

## Closure profile

| Property            | BSML (with NE) | MDL              | MIL              |
|---------------------|----------------|------------------|------------------|
| `IsLowerSet`        | broken by NE   | ✓                | broken by `incl` |
| `SupClosed`         | ✓              | broken by `dep`  | ✓                |
| `∅ ∈ support`       | ✓              | ✓                | ✓                |

MIL shares its closure profile cell (— ✓ ✓) with BSML-with-NE and
BSMLEmpty — same closure cell, different syntactic mechanism (the
inclusion atom rather than NE breaks DC; UC is preserved because two
teams that each witness an inclusion provide a superset of witnesses
in the union).

## Main declarations

* `Formula` — MIL syntax (AHY 2024 Definition 2.1).
* `eval` — single-polarity team-semantic evaluation (AHY 2024
  Definition 2.2).
* `support` — alias for `eval`.
* `Formula.modalDepth` — depth of nested ◇/□.
* `supClosed_support` — every MIL formula has sup-closed support
  (AHY 2024 §2, "Union closure").
* `support_empty` — every formula is supported on the empty team
  (AHY 2024 §2, "Empty Team Property").
* `not_isLowerSet_incl_of_witness` — constructive witness that the
  inclusion atom breaks downward closure.
* `Formula.InclFree`, `Realize`, `support_iff_forall_realize` — without
  inclusion atoms MIL is classical modal logic: support is pointwise Kripke
  truth.

## Implementation notes

The `eval` clauses are the operations of `Team/Operations.lean` — `Team.flat`
for atoms and negation, `Team.tensor` for disjunction, the lax modality
`Team.possLax` and the image modality `Team.necImage` — and the inclusion atom
`Team.incl` of `Team/Atoms.lean` read through the valuation, so union closure and
the empty-team property are folds over their per-case lemmas.

The paper's inclusion atom takes equal-length lists of *classical
formulas* `α₁...αₙ ⊆ β₁...βₙ`. We simplify to lists of *atoms* — each
pair encoded as `(Atom × Atom)`. This loses some expressive power but
matches concrete instances and avoids mutual recursion with a separate
classical-formula type.

The paper allows `¬α` only when `α` is a classical formula. We allow
`neg` syntactically over any MIL formula and define its semantics by
the same pointwise team-extension as the paper. Under the paper's
syntactic restriction this case is unreachable for non-classical
sub-formulas; we extend the definition uniformly because team-extended
pointwise classical negation is well-defined regardless.

The ◇ clause uses AHY 2024's **lax semantics** (Definition 2.2): a
successor team `S` must satisfy both `S ⊆ R[T]` (the reach constraint)
and `T ⊆ R⁻¹[S]` (the back constraint). The paper's footnote 1 notes
that with the **strict semantics** (functional successor selection),
MIL would lose union closure. We follow the paper in using lax.

## Todo

* AHY 2024 §3 — expressive completeness and normal forms for MIL.
* AHY 2024 §4 — natural deduction axiomatisation + completeness proof.
* AHY 2024 §5 — the variant logics ML(▽) and ML(▽) (might-operator
  and singular might-operator). Should each get its own file once
  the substrate proves itself.
* Bisim invariance for MIL — same shape as BSML's; AHY 2024 §3.1 uses
  this for the expressive completeness proof.
-/

@[expose] public section

namespace ModalLogic.Inclusion

variable {W : Type*} {Atom : Type*}

open ModalLogic (KripkeModel)

/-! ### Syntax (AHY 2024 Definition 2.1) -/

/-- MIL syntax. The paper's `α₁...αₙ ⊆ β₁...βₙ` is encoded as a list of
    pairs `[(α₁, β₁), ..., (αₙ, βₙ)]`. Both ◇ and □ are primitives. -/
inductive Formula (Atom : Type*) where
  /-- Atomic proposition. -/
  | atom (p : Atom)
  /-- Weak contradiction `⊥`. -/
  | bot
  /-- Inclusion atom `x⃗ ⊆ y⃗`. -/
  | incl (xys : List (Atom × Atom))
  /-- Classical negation (restricted to classical formulas in the paper;
      we allow on any formula for uniform recursion). -/
  | neg (φ : Formula Atom)
  /-- Conjunction. -/
  | conj (φ ψ : Formula Atom)
  /-- Tensor disjunction. -/
  | disj (φ ψ : Formula Atom)
  /-- Possibility modal `◇` (lax semantics). -/
  | poss (φ : Formula Atom)
  /-- Necessity modal `□`. -/
  | nec (φ : Formula Atom)
  deriving Repr

/-! ### Classical truth

Without inclusion atoms MIL is classical modal logic ([anttila-2021]'s Proposition 2.2.16
for the lax and image modalities, `support_iff_forall_realize` below). -/

/-- `Formula.InclFree φ` holds when `φ` contains no inclusion atom. -/
def Formula.InclFree : Formula Atom → Prop
  | .atom _ | .bot => True
  | .incl _ => False
  | .neg φ | .poss φ | .nec φ => φ.InclFree
  | .conj φ ψ | .disj φ ψ => φ.InclFree ∧ ψ.InclFree

open scoped ModalLogic in
/-- Classical Kripke truth of a MIL formula at a world, with `◇` and `□` the shared
    `ModalLogic.Diamond` and `ModalLogic.Box`; an inclusion atom is true at every world. -/
def Realize (M : KripkeModel W Atom) : Formula Atom → W → Prop
  | .atom p, w => M.val p w = true
  | .bot, _ => False
  | .incl _, _ => True
  | .neg ψ, w => ¬ Realize M ψ w
  | .conj ψ₁ ψ₂, w => Realize M ψ₁ w ∧ Realize M ψ₂ w
  | .disj ψ₁ ψ₂, w => Realize M ψ₁ w ∨ Realize M ψ₂ w
  | .poss ψ, w => ◇[M.accessible] (Realize M ψ) w
  | .nec ψ, w => □[M.accessible] (Realize M ψ) w

theorem realize_poss {M : KripkeModel W Atom} {ψ : Formula Atom} {w : W} :
    Realize M (.poss ψ) w ↔ ∃ v ∈ M.access w, Realize M ψ v := Iff.rfl

theorem realize_nec {M : KripkeModel W Atom} {ψ : Formula Atom} {w : W} :
    Realize M (.nec ψ) w ↔ ∀ v ∈ M.access w, Realize M ψ v := Iff.rfl

variable [DecidableEq W]

/-! ### Semantics (AHY 2024 Definition 2.2) -/

/-- Single-polarity team-semantic evaluation. -/
def eval (M : KripkeModel W Atom) : Formula Atom → Finset W → Prop
  | .atom p,        t => t ∈ Team.flat fun w ↦ M.val p w = true
  | .bot,           t => t ∈ ({∅} : Team.TeamProperty W)
  | .incl xys,      t =>
      t ∈ Team.incl (fun w ↦ xys.map (M.val ·.1 w)) (fun w ↦ xys.map (M.val ·.2 w))
  | .neg ψ,         t => t ∈ Team.flat fun w ↦ ¬ eval M ψ {w}
  | .conj ψ₁ ψ₂,    t => eval M ψ₁ t ∧ eval M ψ₂ t
  | .disj ψ₁ ψ₂,    t => t ∈ Team.tensor {s | eval M ψ₁ s} {s | eval M ψ₂ s}
  | .poss ψ,        t => t ∈ Team.possLax M.access {s | eval M ψ s}
  | .nec ψ,         t => t ∈ Team.necImage M.access {s | eval M ψ s}

/-- Support: alias for `eval`. MIL is unilateral (no separate
    anti-support), but the name `support` is the conventional one
    in team semantics. -/
abbrev support (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) : Prop :=
  eval M φ t

@[simp] lemma support_atom (M : KripkeModel W Atom) (p : Atom) (t : Finset W) :
    support M (.atom p) t ↔ ∀ w ∈ t, M.val p w = true := Iff.rfl

@[simp] lemma support_bot (M : KripkeModel W Atom) (t : Finset W) :
    support M (.bot : Formula Atom) t ↔ t = ∅ := Iff.rfl

@[simp] lemma support_incl (M : KripkeModel W Atom) (xys : List (Atom × Atom))
    (t : Finset W) :
    support M (.incl xys) t ↔
      ∀ w₁ ∈ t, ∃ w₂ ∈ t, ∀ xy ∈ xys, M.val xy.1 w₁ = M.val xy.2 w₂ := by
  simp only [support, eval, Team.mem_incl, List.map_inj_left]

@[simp] lemma support_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ ∀ w ∈ t, ¬ support M φ {w} := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma support_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.disj φ ψ) t ↔
      ∃ t₁, support M φ t₁ ∧ ∃ t₂, support M ψ t₂ ∧ t₁ ∪ t₂ = t := Iff.rfl

@[simp] lemma support_poss (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.poss φ) t ↔
      ∃ S : Finset W, S ⊆ t.biUnion M.access ∧
        (∀ w ∈ t, ∃ s ∈ S, s ∈ M.access w) ∧ support M φ S := Iff.rfl

@[simp] lemma support_nec (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.nec φ) t ↔ support M φ (t.biUnion M.access) := Iff.rfl

/-! ### Modal depth -/

/-- Modal depth of a MIL formula. -/
def Formula.modalDepth : Formula Atom → ℕ
  | .atom _ => 0
  | .bot => 0
  | .incl _ => 0
  | .neg ψ => ψ.modalDepth
  | .conj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .disj ψ₁ ψ₂ => max ψ₁.modalDepth ψ₂.modalDepth
  | .poss ψ => ψ.modalDepth + 1
  | .nec ψ => ψ.modalDepth + 1

/-! ### Sup-closure: the defining property of the inclusion family
    (AHY 2024 §2 — "Union closure: if M, Tᵢ ⊨ φ for all i ∈ I ≠ ∅,
    then M, ⋃_{i ∈ I} Tᵢ ⊨ φ") -/

/-- Every MIL formula has sup-closed support: each case is the closure lemma of its
    connective in `Team/Operations.lean`; a world's inclusion witness in either team is a
    witness in the union. -/
theorem supClosed_support (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed { t : Finset W | support M φ t } := by
  induction φ with
  | atom p => exact Team.supClosed_flat _
  | bot => exact Team.supClosed_singleton_empty
  | incl xys => exact Team.supClosed_incl _ _
  | neg ψ _ => exact Team.supClosed_flat _
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ih₁.inter ih₂
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact ih₁.tensor ih₂
  | poss ψ ih => exact ih.possLax
  | nec ψ ih => exact ih.necImage

/-! ### Empty team property (AHY 2024 §2) -/

theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ := by
  induction φ with
  | atom p => exact Team.empty_mem_flat _
  | bot => rfl
  | incl xys => exact Team.empty_mem_incl _ _
  | neg ψ _ => exact Team.empty_mem_flat _
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ => exact Team.empty_mem_tensor ih₁ ih₂
  | poss ψ ih => exact Team.empty_mem_possLax ih
  | nec ψ ih => exact Team.empty_mem_necImage ih

/-! ### Inclusion breaks downward closure (the defining feature) -/

/-- **The inclusion atom breaks downward closure** (`Team.not_isLowerSet_incl`): if `w₂`
    supplies the `b`-value matching both its own and `w₁`'s `a`-value, but `w₁` does not match
    itself, then `{w₁, w₂}` supports `a ⊆ b` and `{w₁}` does not. -/
theorem not_isLowerSet_incl_of_witness {a b : Atom} {w₁ w₂ : W} {M : KripkeModel W Atom}
    (hpair : M.val a w₁ = M.val b w₂) (hself : M.val a w₂ = M.val b w₂)
    (hwit : M.val a w₁ ≠ M.val b w₁) :
    ¬ IsLowerSet { t : Finset W | support M (.incl [(a, b)]) t } := by
  simpa only [support, eval, Set.ofPred_mem_eq] using
    Team.not_isLowerSet_incl (f := fun w ↦ [(a, b)].map (M.val ·.1 w))
      (g := fun w ↦ [(a, b)].map (M.val ·.2 w)) (a := w₁) (b := w₂) (by simp [hpair])
      (by simp [hself]) (by simp [hwit])

/-! ### Soundness for the closure cell (Definability bridge) -/

open Team in
/-- **MIL is sound for its closure cell**: every MIL-definable team property is
    union-closed and has the empty-team property. This is the soundness half of
    the expressive-completeness theorem for ML(⊆) ([anttila-haggblom-yang-2024];
    [anttila-2025] Ch 5 shows ML(⊆) is complete for the union-closed modal
    properties with the empty-team property, modulo bounded bisimulation).

    Composes `supClosed_support` and `support_empty` through the
    `Team/Definability.lean` bridge — the first consumer of that substrate. The
    converse (every such property is MIL-definable, via the inclusion normal
    form) is the open half. -/
theorem definableClass_support_subset (M : KripkeModel W Atom) :
    definableClass (support M) ⊆ {P | SupClosed P ∧ ∅ ∈ P} :=
  definableClass_subset fun φ ↦ ⟨supClosed_support M φ, support_empty M φ⟩

/-! ### The classical fragment

On `incl`-free formulas support is pointwise classical truth: the lax and image modalities
agree with the flat ones on flat properties (`Team.possLax_flat`, `Team.necImage_flat`). -/

section Classical

variable {M : KripkeModel W Atom} {φ : Formula Atom} {w : W} {t : Finset W}

/-- On `incl`-free formulas, support is pointwise classical truth. -/
theorem support_iff_forall_realize (hI : φ.InclFree) (t : Finset W) :
    support M φ t ↔ ∀ w ∈ t, Realize M φ w := by
  induction φ generalizing t with
  | atom p => simp [support, eval, Realize]
  | bot => simp [support, eval, Realize, Finset.eq_empty_iff_forall_notMem]
  | incl xys => exact hI.elim
  | neg ψ ih =>
    simp only [support, eval, Team.mem_flat, Realize]
    exact forall₂_congr fun w _ ↦ not_congr ((ih hI {w}).trans (by simp))
  | conj ψ₁ ψ₂ ih₁ ih₂ => simp [support, eval, ih₁ hI.1, ih₂ hI.2, Realize, forall_and]
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    simp only [support, eval, ih₁ hI.1, ih₂ hI.2]
    exact Team.mem_tensor_flat.trans (by simp [Realize])
  | poss ψ ih =>
    simp only [support, eval, ih hI]
    exact Team.mem_possLax_flat.trans (by simp [realize_poss])
  | nec ψ ih =>
    simp only [support, eval, ih hI]
    exact Team.mem_necImage_flat.trans (by simp [realize_nec])

theorem support_singleton_iff_realize (hI : φ.InclFree) : support M φ {w} ↔ Realize M φ w := by
  simp [support_iff_forall_realize hI]

end Classical

end ModalLogic.Inclusion
