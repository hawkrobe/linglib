import Linglib.Semantics.Dynamic.State
import Mathlib.Data.PFun

/-!
# File Change Semantics
[heim-1982] [heim-1983]

Heim's File Change Semantics: sentence meanings are *file change
potentials* (FCPs), partial functions from files to files. A file *is* an
information state (`Semantics/Dynamic/State.lean`): its cards are the
defined referents of its points, `Dom(F)` the shared domain of a uniform
file, `Sat(F)` the state itself. Partiality of FCPs models
presupposition as definedness — and since the Novelty and Familiarity
Conditions are genuinely propositional over base-free states, the
partiality is `Part`'s, the module's own partial column
(`Dynamic/Partial.lean`): `(φ F).Dom` is Heim's "F admits φ".

Heim's clauses land on the root vocabulary: familiarity is `Familiar`,
negation keeps the points of `F` that do *not subsist* (`≺`) in the
scope's update — the no-verifying-extension clause is non-subsistence,
the same repair [groenendijk-stokhof-veltman-1996] Def. 3.1 makes.

## Main definitions

- `FCP`: partial functions `State W ℕ E →. State W ℕ E`.
- `FCP.atomW`, `atomVar`, `atomVar2`: atomic updates (filter the points).
- `FCP.seq`, `neg`, `cond`: conjunction as sequencing, negation as
  non-subsistence, conditionals as `¬(φ ∧ ¬ψ)`.
- `FCP.indef`, `def_`: novelty-guarded introduction (via
  `State.randomAssign`) and familiarity-guarded definite update.
- `trueIn`, `falseIn` (truth criterion (C), Ch III §3.2), `supports`,
  `fcpEntails`, `definedOn`.

## Main results

- `atomVar_definedOn_iff`: Heim's Familiarity Condition is exactly
  definedness of the atomic update — stated with `Familiar` itself.
- `atomW_eliminative`, `atomVar_eliminative`, `neg_eliminative`,
  `seq_eliminative`: Principle (A) — file change only eliminates points.
- `seq_assoc`, `id_seq`, `seq_id`: the FCP monoid.
-/

namespace FileChangeSemantics

open DynamicSemantics

variable {W E : Type*}

/-- A File Change Potential: a partial function from files to files.
`Part`-partiality captures presupposition-as-definedness: when a novelty
or familiarity precondition fails, the FCP is undefined rather than
absurd. -/
def FCP (W : Type*) (E : Type*) := State W ℕ E →. State W ℕ E

/-- Card `i` in `F` refers to entity `x` iff every point assigns `x` to
position `i` (Ch III §2.3). -/
def refersTo (F : State W ℕ E) (i : ℕ) (x : E) : Prop :=
  ∀ p ∈ F, p.assignment i = some x

namespace FCP

/-- Atomic predicate on the world: filter the points. -/
def atomW (pred : W → Prop) : FCP W E :=
  fun F => Part.some {p ∈ F | pred p.world}

/-- Atomic predicate on the variable `x`: filter the points by the value
at `x`. Defined only if `x` is familiar — Heim's "every variable
mentioned has been introduced", as a genuine definedness condition. -/
def atomVar (pred : E → Prop) (x : ℕ) : FCP W E :=
  fun F => Part.assert (Familiar F x) fun _ =>
    Part.some {p ∈ F | ∃ e, p.assignment x = some e ∧ pred e}

/-- Binary atomic predicate on `x` and `y`; both must be familiar. -/
def atomVar2 (pred : E → E → Prop) (x y : ℕ) : FCP W E :=
  fun F => Part.assert (Familiar F x ∧ Familiar F y) fun _ =>
    Part.some {p ∈ F | ∃ e e', p.assignment x = some e ∧
      p.assignment y = some e' ∧ pred e e'}

/-- Sequential composition (conjunction): `F + [φ ∧ ψ] = (F + φ) + ψ`.
If either step is undefined (presupposition failure), the whole is. -/
def seq (φ ψ : FCP W E) : FCP W E :=
  fun F => (φ F).bind ψ

@[inherit_doc] infixl:70 " +> " => seq

/-- Negation: keep the points of `F` that do not subsist in the scope's
update — the no-verifying-extension clause, as non-subsistence.
Referents introduced inside the scope are trapped. Undefined when the
scope is. -/
def neg (φ : FCP W E) : FCP W E :=
  fun F => (φ F).map fun F' => {p ∈ F | ¬ p ≺ F'}

/-- Conditional: `F + [if φ then ψ] = F + [¬(φ ∧ ¬ψ)]` — Heim's analysis
of conditionals as negated conjunctions. -/
def cond (φ ψ : FCP W E) : FCP W E :=
  neg (seq φ (neg ψ))

/-- Indefinite introduction: defined only if `x` is novel (the Novelty
Condition — no point defines it); then introduce `x` by random
assignment and update with the body. Indefinites don't quantify — they
open a new file card. -/
def indef [DecidableEq ℕ] (x : ℕ) (body : FCP W E) : FCP W E :=
  fun F => Part.assert (∀ p ∈ F, p.assignment x = none) fun _ =>
    body (F.randomAssign x)

/-- Definite reference: defined only if `x` is familiar (the Familiarity
Condition); the dref is already established, so the file is untouched
before the body applies. -/
def def_ (x : ℕ) (body : FCP W E) : FCP W E :=
  fun F => Part.assert (Familiar F x) fun _ => body F

/-- Identity FCP: no change. -/
def id : FCP W E := fun F => Part.some F

/-- Absurd FCP: always undefined (total presupposition failure). -/
def fail : FCP W E := fun _ => Part.none

end FCP

/-! ### Truth and entailment (Ch III §3) -/

/-- Truth criterion (C) (Ch III §3.2): `φ` is true w.r.t. `F` iff `F + φ`
is defined and consistent. Existential quantification is built into
truth itself — indefinites need no existential closure. -/
def trueIn (F : State W ℕ E) (φ : FCP W E) : Prop :=
  ∃ F' ∈ φ F, F'.Nonempty

/-- `φ` is false w.r.t. `F` iff `F + φ` is defined but absurd. -/
def falseIn (F : State W ℕ E) (φ : FCP W E) : Prop :=
  ∃ F' ∈ φ F, ¬F'.Nonempty

/-- `F` supports `φ` iff updating changes nothing — the dynamic notion of
entailment/support, stronger than `trueIn`. -/
def supports (F : State W ℕ E) (φ : FCP W E) : Prop :=
  φ F = Part.some F

/-- `F` entails `φ` iff `F` supports it. -/
def fileEntails (F : State W ℕ E) (φ : FCP W E) : Prop :=
  supports F φ

/-- `φ` semantically entails `ψ` iff every defined update with `φ`
supports `ψ`. -/
def fcpEntails (φ ψ : FCP W E) : Prop :=
  ∀ F : State W ℕ E, ∀ F' ∈ φ F, supports F' ψ

/-- `φ` is defined on `F` — Heim's "F admits φ", `Part.Dom` as in
`Dynamic/Partial.lean`. -/
def definedOn (F : State W ℕ E) (φ : FCP W E) : Prop :=
  (φ F).Dom

/-- Truth implies definedness. -/
theorem trueIn_definedOn (F : State W ℕ E) (φ : FCP W E)
    (h : trueIn F φ) : definedOn F φ := by
  obtain ⟨F', hF', -⟩ := h
  exact Part.dom_iff_mem.mpr ⟨F', hF'⟩

/-- Support implies truth for consistent files. -/
theorem supports_trueIn (F : State W ℕ E) (φ : FCP W E)
    (hsup : supports F φ) (hcons : F.Nonempty) : trueIn F φ :=
  ⟨F, by rw [hsup]; exact Part.mem_some F, hcons⟩

/-! ### Theorems -/

section Theorems

/-- Sequential composition is associative. -/
theorem seq_assoc (φ ψ χ : FCP W E) :
    FCP.seq (FCP.seq φ ψ) χ = FCP.seq φ (FCP.seq ψ χ) := by
  funext F
  exact Part.bind_assoc ..

/-- Identity is left unit for sequential composition. -/
theorem id_seq (φ : FCP W E) : FCP.seq FCP.id φ = φ := by
  funext F
  exact Part.bind_some ..

/-- Identity is right unit for sequential composition. -/
theorem seq_id (φ : FCP W E) : FCP.seq φ FCP.id = φ := by
  funext F
  exact Part.bind_some_right _

/-- **The Familiarity Condition is definedness**: variable atoms are
defined exactly on files where the variable is familiar. -/
theorem atomVar_definedOn_iff (pred : E → Prop) (x : ℕ) (F : State W ℕ E) :
    definedOn F (FCP.atomVar pred x) ↔ Familiar F x :=
  ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩

/-- World atoms are eliminative: `Sat(F + P) ⊆ Sat(F)` — Principle (A):
file change only eliminates. -/
theorem atomW_eliminative (pred : W → Prop) {F F' : State W ℕ E}
    (h : F' ∈ FCP.atomW pred F) : F' ⊆ F := by
  obtain rfl := Part.mem_some_iff.mp h
  exact fun p hp => hp.1

/-- Variable atoms are eliminative. -/
theorem atomVar_eliminative (pred : E → Prop) (x : ℕ) {F F' : State W ℕ E}
    (h : F' ∈ FCP.atomVar pred x F) : F' ⊆ F := by
  obtain ⟨hdom, hval⟩ := Part.mem_assert_iff.mp h
  obtain rfl := Part.mem_some_iff.mp hval
  exact fun p hp => hp.1

/-- Negation is eliminative: `Sat(F + ¬φ) ⊆ Sat(F)`. -/
theorem neg_eliminative (φ : FCP W E) {F F' : State W ℕ E}
    (h : F' ∈ FCP.neg φ F) : F' ⊆ F := by
  obtain ⟨G, -, rfl⟩ := (Part.mem_map_iff _).mp h
  exact fun p hp => hp.1

/-- Sequential composition of eliminative FCPs is eliminative. -/
theorem seq_eliminative (φ ψ : FCP W E)
    (hφ : ∀ F : State W ℕ E, ∀ F' ∈ φ F, F' ⊆ F)
    (hψ : ∀ F : State W ℕ E, ∀ F' ∈ ψ F, F' ⊆ F)
    {F F' : State W ℕ E} (h : F' ∈ FCP.seq φ ψ F) : F' ⊆ F := by
  obtain ⟨F₁, hF₁, hF'⟩ := Part.mem_bind_iff.mp h
  exact (hψ F₁ F' hF').trans (hφ F F₁ hF₁)

/-- Indefinite is undefined when the variable is not novel. -/
theorem indef_not_novel_not_definedOn (x : ℕ) (body : FCP W E)
    (F : State W ℕ E) (h : ¬ ∀ p ∈ F, p.assignment x = none) :
    ¬ definedOn F (FCP.indef x body) := by
  simp only [definedOn, FCP.indef, Part.assert]
  rintro ⟨hnovel, -⟩
  exact h hnovel

/-- Definite is undefined when the variable is unfamiliar. -/
theorem def_not_familiar_not_definedOn (x : ℕ) (body : FCP W E)
    (F : State W ℕ E) (h : ¬ Familiar F x) :
    ¬ definedOn F (FCP.def_ x body) := by
  simp only [definedOn, FCP.def_, Part.assert]
  rintro ⟨hfam, -⟩
  exact h hfam

/-- Support is idempotent: if `F` supports `φ`, updating twice is the same
as once. -/
theorem supports_idempotent (F : State W ℕ E) (φ : FCP W E)
    (h : supports F φ) : FCP.seq φ φ F = φ F := by
  simp only [FCP.seq, supports] at *
  rw [h, Part.bind_some, h]

end Theorems

end FileChangeSemantics
