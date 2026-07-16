import Linglib.Semantics.Dynamic.Partial
import Linglib.Semantics.Dynamic.State

/-!
# File Change Semantics
[heim-1982] [heim-1983]

[heim-1982]'s file change potentials over referential information
states: `FCP W V M` is `CCP.Partial` at the possibility type — the
partiality effect of `Dynamic/Partial.lean` over the root states of
`Dynamic/State.lean`. A file *is* an information state: its cards are
the familiar referents, `Dom(F)` the shared domain of a uniform file.
Presupposition is `Part`-definedness (`CCP.Partial.admits`, Heim's
"F admits φ"), so the Novelty and Familiarity Conditions are genuine
definedness conditions; sequencing and its monoid laws are `PFun.comp`'s
(`PFun.comp_assoc`, `PFun.id_comp`, `PFun.comp_id`).

Negation keeps the points of `F` that do not *subsist* (`≺`) in the
scope's update — the no-verifying-extension clause, generalizing
[heim-1983]'s world-only `s \ s[φ]` (`CCP.Partial.neg`): on a uniform
stratum the two coincide (`neg_eq_partial_neg`), so the 1983 clauses are
the referent-free shadow of the 1982 ones.

## Main definitions

- `FCP`: file change potentials —
  `CCP.Partial (Possibility W V (Option M))`.
- `FCP.atomW`, `FCP.atomVar`, `FCP.atomVar2`: atomic updates,
  familiarity-guarded.
- `FCP.neg`, `FCP.cond`: negation as non-subsistence; *if* as `¬(φ ∧ ¬ψ)`.
- `FCP.indef`, `FCP.def_`: the Novelty and Familiarity Conditions as
  `Part.assert` guards on `State.randomAssign` and identity.
- `FCP.trueIn`, `FCP.falseIn`, `FCP.supports`, `FCP.fcpEntails`: truth
  criterion (C) (Ch. III §3.2) and dynamic entailment.

## Main results

- `admits_atomVar`: the Familiarity Condition is exactly definedness.
- `neg_eq_partial_neg`: on a uniform stratum, non-subsistence negation
  is [heim-1983]'s set-difference negation.
- `atomW_eliminative`, `atomVar_eliminative`, `neg_eliminative`:
  Principle (A) — file change only eliminates (closure under sequencing
  is `CCP.Partial.seq_eliminative`).
-/

namespace DynamicSemantics

/-- A file change potential ([heim-1982], Ch. III): a partial update of
referential information states — `CCP.Partial` at the possibility type.
Partiality is presupposition (`CCP.Partial.admits`); Heim's files number
their cards, `V := ℕ`. -/
abbrev FCP (W V M : Type*) := CCP.Partial (Possibility W V (Option M))

namespace FCP

variable {W V M : Type*}

/-- Card `x` in `F` refers to `m`: every point assigns `m` to `x`
(Ch. III §2.3). -/
def refersTo (F : State W V M) (x : V) (m : M) : Prop :=
  ∀ p ∈ F, p.assignment x = some m

/-- Atomic predicate on the world: filter the points. -/
def atomW (pred : W → Prop) : FCP W V M :=
  fun F => Part.some {p ∈ F | pred p.world}

/-- Atomic predicate at card `x`: filter the points by the value at `x`.
Defined only if `x` is familiar — Heim's "every variable mentioned has
been introduced", as a genuine definedness condition. -/
def atomVar (pred : M → Prop) (x : V) : FCP W V M :=
  fun F => Part.assert (Familiar F x) fun _ =>
    Part.some {p ∈ F | ∃ m, p.assignment x = some m ∧ pred m}

/-- Binary atomic predicate at `x` and `y`; both must be familiar. -/
def atomVar2 (pred : M → M → Prop) (x y : V) : FCP W V M :=
  fun F => Part.assert (Familiar F x ∧ Familiar F y) fun _ =>
    Part.some {p ∈ F | ∃ m m', p.assignment x = some m ∧
      p.assignment y = some m' ∧ pred m m'}

/-- Negation: keep the points of `F` that do not subsist in the scope's
update — the no-verifying-extension clause, as non-subsistence.
Referents introduced inside the scope are trapped. Undefined when the
scope is. -/
def neg (φ : FCP W V M) : FCP W V M :=
  fun F => (φ F).map fun F' => {p ∈ F | ¬ p ≺ F'}

/-- Conditional: `F + [if φ then ψ] = F + [¬(φ ∧ ¬ψ)]` — Heim's analysis
of conditionals as negated conjunctions. -/
def cond (φ ψ : FCP W V M) : FCP W V M :=
  neg (φ.seq (neg ψ))

/-- Indefinite introduction: defined only if `x` is novel (the Novelty
Condition — no point defines it); then introduce `x` by random
assignment and update with the body. Indefinites don't quantify — they
open a new file card. -/
def indef [DecidableEq V] (x : V) (body : FCP W V M) : FCP W V M :=
  fun F => Part.assert (∀ p ∈ F, p.assignment x = none) fun _ =>
    body (State.randomAssign F x)

/-- Definite reference: defined only if `x` is familiar (the Familiarity
Condition); the card is already established, so the file passes through
to the body. -/
def def_ (x : V) (body : FCP W V M) : FCP W V M :=
  fun F => Part.assert (Familiar F x) fun _ => body F

/-! ### Truth and entailment (Ch. III §3) -/

/-- Truth criterion (C) (Ch. III §3.2): `φ` is true w.r.t. `F` iff
`F + φ` is defined and consistent. Existential quantification is built
into truth itself — indefinites need no existential closure. -/
def trueIn (F : State W V M) (φ : FCP W V M) : Prop :=
  ∃ F' ∈ φ F, F'.Nonempty

/-- `φ` is false w.r.t. `F` iff `F + φ` is defined but absurd. -/
def falseIn (F : State W V M) (φ : FCP W V M) : Prop :=
  ∃ F' ∈ φ F, ¬F'.Nonempty

/-- `F` supports `φ` iff updating changes nothing — the dynamic notion
of entailment, stronger than `trueIn`. -/
def supports (F : State W V M) (φ : FCP W V M) : Prop :=
  φ F = Part.some F

/-- `φ` semantically entails `ψ` iff every defined update with `φ`
supports `ψ`. -/
def fcpEntails (φ ψ : FCP W V M) : Prop :=
  ∀ F : State W V M, ∀ F' ∈ φ F, supports F' ψ

/-- Truth implies definedness. -/
theorem trueIn_admits {F : State W V M} {φ : FCP W V M}
    (h : trueIn F φ) : φ.admits F :=
  let ⟨F', hF', _⟩ := h
  Part.dom_iff_mem.mpr ⟨F', hF'⟩

/-- Support implies truth for consistent files. -/
theorem supports_trueIn {F : State W V M} {φ : FCP W V M}
    (hsup : supports F φ) (hcons : F.Nonempty) : trueIn F φ :=
  ⟨F, by rw [hsup]; exact Part.mem_some F, hcons⟩

/-- Support is idempotent: if `F` supports `φ`, updating twice is the
same as once. -/
theorem supports_idempotent {F : State W V M} {φ : FCP W V M}
    (h : supports F φ) : φ.seq φ F = φ F := by
  show (φ F).bind φ = φ F
  rw [h, Part.bind_some, h]

/-! ### Admittance -/

/-- **The Familiarity Condition is definedness**: variable atoms are
defined exactly on files where the variable is familiar. -/
theorem admits_atomVar (pred : M → Prop) (x : V) (F : State W V M) :
    (atomVar pred x).admits F ↔ Familiar F x :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

/-- The Novelty Condition is definedness: an indefinite is defined iff
its card is novel and the body is defined on the extended file. -/
theorem admits_indef [DecidableEq V] (x : V) (body : FCP W V M)
    (F : State W V M) :
    (indef x body).admits F ↔
      ∃ _ : ∀ p ∈ F, p.assignment x = none,
        (body (F.randomAssign x)).Dom := by
  exact Iff.rfl

/-- A definite is defined iff its card is familiar and the body is
defined. -/
theorem admits_def_ (x : V) (body : FCP W V M) (F : State W V M) :
    (def_ x body).admits F ↔ ∃ _ : Familiar F x, (body F).Dom := by
  exact Iff.rfl

/-! ### Eliminativity (Principle (A)) -/

/-- World atoms are eliminative: file change only eliminates points. -/
theorem atomW_eliminative (pred : W → Prop) {F F' : State W V M}
    (h : F' ∈ atomW pred F) : F' ⊆ F := by
  obtain rfl := Part.mem_some_iff.mp h
  exact fun p hp => hp.1

/-- Variable atoms are eliminative. -/
theorem atomVar_eliminative (pred : M → Prop) (x : V) {F F' : State W V M}
    (h : F' ∈ atomVar pred x F) : F' ⊆ F := by
  obtain ⟨hdom, hval⟩ := Part.mem_assert_iff.mp h
  obtain rfl := Part.mem_some_iff.mp hval
  exact fun p hp => hp.1

/-- Negation is eliminative. -/
theorem neg_eliminative (φ : FCP W V M) {F F' : State W V M}
    (h : F' ∈ neg φ F) : F' ⊆ F := by
  obtain ⟨G, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact fun p hp => hp.1

/-! ### The referent-free shadow -/

/-- On a uniform stratum, non-subsistence negation is [heim-1983]'s
set-difference negation (`CCP.Partial.neg`): with every referent shared,
a point subsists in the update exactly when it survives into it. The
1983 clauses are the referent-free shadow of the 1982 ones. -/
theorem neg_eq_partial_neg [DecidableEq V] {X : Finset V}
    {φ : FCP W V M} {F : State W V M} (hF : State.UniformAt X F)
    (hφ : ∀ F' ∈ φ F, State.UniformAt X F') :
    neg φ F = CCP.Partial.neg φ F := by
  refine Part.ext' Iff.rfl fun h₁ h₂ => ?_
  show {p ∈ F | ¬ p ≺ (φ F).get h₁} = F \ (φ F).get h₁
  ext p
  simp only [Set.mem_sep_iff, Set.mem_sdiff]
  exact and_congr_right fun hp => not_congr
    (State.subsists_iff_mem (hφ _ (Part.get_mem _)) (hF p hp))

end FCP

end DynamicSemantics
