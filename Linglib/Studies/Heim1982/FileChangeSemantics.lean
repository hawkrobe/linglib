import Linglib.Semantics.Dynamic.State

/-!
# File Change Semantics
[heim-1982] [heim-1983]

Heim's File Change Semantics: sentence meanings are *file change
potentials* (FCPs), partial functions from files to files. A file
`⟨Dom(F), Sat(F)⟩` *is* a based information state: `Dom(F)` is
`State.base` (the open file cards) and `Sat(F)` is `State.carrier`, whose
support invariant renders the partiality of Heim's satisfaction sequences
— they carry information exactly at the file's cards. Partiality of FCPs
(`Option`) models presupposition as definedness: the Novelty Condition for
indefinites, the Familiarity Condition for definites.

## Main definitions

- `FCP`: partial functions `State W ℕ E → Option (State W ℕ E)`.
- `FCP.atomW`, `atomVar`, `atomVar2`: atomic updates (filter the carrier).
- `FCP.seq`, `neg`, `cond`: conjunction as sequencing, negation as the
  no-verifying-extension test, conditionals as `¬(φ ∧ ¬ψ)`.
- `FCP.indef`, `def_`: novelty-guarded introduction (via
  `State.randomAssign`) and familiarity-guarded definite update.
- `trueIn`, `falseIn` (truth criterion (C), Ch III §3.2), `supports`,
  `fcpEntails`.

## Main results

- `atomVar_definedOn_iff`: familiarity of the variable is exactly
  definedness of the atomic update.
- `neg_preserves_base`, `neg_blocks_dref` (in `Basic.lean`): negation
  traps discourse referents.
- `atomW_eliminative`, `neg_eliminative`, `seq_eliminative`:
  Principle (A) — file change only eliminates possibilities.

## Implementation notes

Negation keeps the possibilities of `F` with *no verifying extension* in
the scope's update (the negation clause familiar from DRT,
[kamp-reyle-1993]): membership in the update restricted back to `F.base`
(`State.restrict`) says exactly "some extension survives". A raw
non-membership clause over total assignments would let a possibility
survive `¬∃x φ` whenever its own irrelevant `x`-value fails `φ`.

[heim-1982]'s rule (i'') lets atomic updates expand the domain by the
mentioned variables. We follow the modern convention (shared by DRT and
DPL) where domain growth is the indefinite's job — and the support
discipline turns the convention's proviso ("every variable mentioned has
already been introduced") into a genuine definedness condition on
`atomVar`/`atomVar2`.
-/

namespace FileChangeSemantics

open DynamicSemantics

variable {W E : Type*}

/-- A File Change Potential: a partial function from files to files.
Partiality (`Option`) captures presupposition-as-definedness: when a
novelty or familiarity precondition fails, the FCP returns `none` rather
than an empty file. -/
def FCP (W : Type*) (E : Type*) := State W ℕ E → Option (State W ℕ E)

/-- Card `i` in `F` refers to entity `x` iff every satisfying possibility
assigns `x` to position `i` (Ch III §2.3, p. 207). -/
def refersTo (F : State W ℕ E) (i : ℕ) (x : E) : Prop :=
  ∀ p ∈ F.carrier, p.assignment i = x

namespace FCP

/-- Atomic predicate on the world: filter the carrier, keep the base. -/
def atomW (pred : W → Prop) : FCP W E :=
  λ F => some
    { base := F.base
      carrier := {p ∈ F.carrier | pred p.world}
      supported := baseSupported_of_iff fun _ _ _ hfg =>
        and_congr (F.supported.mem_iff hfg) Iff.rfl }

/-- Atomic predicate on the variable `x`: filter the carrier by the value
at `x`. Defined only if `x` is familiar — the support discipline makes
"every variable mentioned has been introduced" a definedness condition. -/
def atomVar (pred : E → Prop) (x : ℕ) : FCP W E :=
  λ F => if hx : x ∈ F.base then
    some
      { base := F.base
        carrier := {p ∈ F.carrier | pred (p.assignment x)}
        supported := baseSupported_of_iff fun _ f g hfg =>
          and_congr (F.supported.mem_iff hfg)
            (by show pred (f x) ↔ pred (g x)
                rw [hfg (Finset.mem_coe.mpr hx)]) }
  else none

/-- Binary atomic predicate on `x` and `y`; both must be familiar. -/
def atomVar2 (pred : E → E → Prop) (x y : ℕ) : FCP W E :=
  λ F => if hxy : x ∈ F.base ∧ y ∈ F.base then
    some
      { base := F.base
        carrier := {p ∈ F.carrier | pred (p.assignment x) (p.assignment y)}
        supported := baseSupported_of_iff fun _ f g hfg =>
          and_congr (F.supported.mem_iff hfg)
            (by show pred (f x) (f y) ↔ pred (g x) (g y)
                rw [hfg (Finset.mem_coe.mpr hxy.1),
                  hfg (Finset.mem_coe.mpr hxy.2)]) }
  else none

/-- Sequential composition (conjunction): `F + [φ ∧ ψ] = (F + φ) + ψ`.
If either step is undefined (presupposition failure), the whole is. -/
def seq (φ ψ : FCP W E) : FCP W E :=
  λ F => (φ F).bind ψ

@[inherit_doc] infixl:70 " +> " => seq

/-- Negation: keep the possibilities of `F` with no verifying extension in
the scope's update — membership in the update restricted back to `F.base`
says "some extension survives". The base is preserved: negation traps
discourse referents. Undefined when the scope is. -/
def neg (φ : FCP W E) : FCP W E :=
  λ F => (φ F).map fun F' =>
    { base := F.base
      carrier := {p ∈ F.carrier | p ∉ F'.restrict F.base}
      supported := baseSupported_of_iff fun _ _ _ hfg =>
        and_congr (F.supported.mem_iff hfg)
          (not_congr ((F'.restrict F.base).supported.mem_iff hfg)) }

/-- Conditional: `F + [if φ then ψ] = F + [¬(φ ∧ ¬ψ)]` — Heim's analysis
of conditionals as negated conjunctions. -/
def cond (φ ψ : FCP W E) : FCP W E :=
  neg (seq φ (neg ψ))

/-- Indefinite introduction: defined only if `x` is novel (the Novelty
Condition); then introduce `x` by random assignment and update with the
body. Indefinites don't quantify — they open a new file card. -/
def indef (x : ℕ) (body : FCP W E) : FCP W E :=
  λ F => if x ∈ F.base then none else body (F.randomAssign x)

/-- Definite reference: defined only if `x` is familiar (the Familiarity
Condition); the dref is already established, so the file structure is
untouched before the body applies. -/
def def_ (x : ℕ) (body : FCP W E) : FCP W E :=
  λ F => if x ∈ F.base then body F else none

/-- Identity FCP: no change. -/
def id : FCP W E := λ F => some F

/-- Absurd FCP: always undefined (total presupposition failure). -/
def fail : FCP W E := λ _ => none

end FCP

/-! ### Truth and entailment (Ch III §3) -/

/-- Truth criterion (C) (Ch III §3.2, p. 214): `φ` is true w.r.t. `F` iff
`F + φ` is defined and consistent. Existential quantification is built
into truth itself — indefinites need no existential closure. -/
def trueIn (F : State W ℕ E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F' ∧ F'.carrier.Nonempty

/-- `φ` is false w.r.t. `F` iff `F + φ` is defined but absurd. -/
def falseIn (F : State W ℕ E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F' ∧ ¬F'.carrier.Nonempty

/-- `F` supports `φ` iff updating changes nothing — the dynamic notion of
entailment/support, stronger than `trueIn`. -/
def supports (F : State W ℕ E) (φ : FCP W E) : Prop :=
  φ F = some F

/-- `F` entails `φ` iff `F` supports it. -/
def fileEntails (F : State W ℕ E) (φ : FCP W E) : Prop :=
  supports F φ

/-- `φ` semantically entails `ψ` iff every defined update with `φ`
supports `ψ`. -/
def fcpEntails (φ ψ : FCP W E) : Prop :=
  ∀ F F' : State W ℕ E, φ F = some F' → supports F' ψ

/-- `φ` is defined on `F` (no presupposition failure). -/
def definedOn (F : State W ℕ E) (φ : FCP W E) : Prop :=
  ∃ F', φ F = some F'

/-- Truth implies definedness. -/
theorem trueIn_definedOn (F : State W ℕ E) (φ : FCP W E)
    (h : trueIn F φ) : definedOn F φ :=
  ⟨h.choose, h.choose_spec.1⟩

/-- Support implies truth for consistent files. -/
theorem supports_trueIn (F : State W ℕ E) (φ : FCP W E)
    (hsup : supports F φ) (hcons : F.carrier.Nonempty) : trueIn F φ :=
  ⟨F, hsup, hcons⟩

/-! ### Theorems -/

section Theorems

/-- Sequential composition is associative. -/
theorem seq_assoc (φ ψ χ : FCP W E) :
    FCP.seq (FCP.seq φ ψ) χ = FCP.seq φ (FCP.seq ψ χ) := by
  funext F
  simp only [FCP.seq]
  cases φ F <;> rfl

/-- Identity is left unit for sequential composition. -/
theorem id_seq (φ : FCP W E) : FCP.seq FCP.id φ = φ := by
  funext F; simp [FCP.seq, FCP.id, Option.bind]

/-- Identity is right unit for sequential composition. -/
theorem seq_id (φ : FCP W E) : FCP.seq φ FCP.id = φ := by
  funext F; simp [FCP.seq]
  cases φ F <;> rfl

/-- Familiarity is exactly definedness for variable atoms. -/
theorem atomVar_definedOn_iff (pred : E → Prop) (x : ℕ) (F : State W ℕ E) :
    definedOn F (FCP.atomVar pred x) ↔ x ∈ F.base := by
  simp only [definedOn, FCP.atomVar]
  split
  · exact iff_of_true ⟨_, rfl⟩ ‹_›
  · exact iff_of_false (by simp) ‹_›

/-- World atoms preserve the base. -/
theorem atomW_preserves_base (pred : W → Prop) (F : State W ℕ E) :
    (FCP.atomW pred F).map (·.base) = some F.base := rfl

/-- Negation preserves the base. -/
theorem neg_preserves_base (φ : FCP W E) (F F' : State W ℕ E)
    (h : FCP.neg φ F = some F') : F'.base = F.base := by
  simp only [FCP.neg, Option.map_eq_some_iff] at h
  obtain ⟨G, -, rfl⟩ := h
  rfl

/-- Indefinite is undefined when the variable is familiar (not novel). -/
theorem indef_familiar_none (x : ℕ) (body : FCP W E) (F : State W ℕ E)
    (h : x ∈ F.base) : FCP.indef x body F = none :=
  if_pos h

/-- Definite is undefined when the variable is novel (not familiar). -/
theorem def_novel_none (x : ℕ) (body : FCP W E) (F : State W ℕ E)
    (h : x ∉ F.base) : FCP.def_ x body F = none :=
  if_neg h

/-- World atoms are eliminative: Sat(F + P) ⊆ Sat(F) — Principle (A):
information only grows. -/
theorem atomW_eliminative (pred : W → Prop) (F F' : State W ℕ E)
    (h : FCP.atomW pred F = some F') : F'.carrier ⊆ F.carrier := by
  obtain rfl : _ = F' := Option.some.inj h
  exact fun p hp => hp.1

/-- Variable atoms are eliminative. -/
theorem atomVar_eliminative (pred : E → Prop) (x : ℕ) (F F' : State W ℕ E)
    (h : FCP.atomVar pred x F = some F') : F'.carrier ⊆ F.carrier := by
  simp only [FCP.atomVar] at h
  split at h
  · obtain rfl : _ = F' := Option.some.inj h
    exact fun p hp => hp.1
  · exact absurd h (by simp)

/-- Negation is eliminative: Sat(F + ¬φ) ⊆ Sat(F). -/
theorem neg_eliminative (φ : FCP W E) (F F' : State W ℕ E)
    (h : FCP.neg φ F = some F') : F'.carrier ⊆ F.carrier := by
  simp only [FCP.neg, Option.map_eq_some_iff] at h
  obtain ⟨G, -, rfl⟩ := h
  exact fun p hp => hp.1

/-- Sequential composition of eliminative FCPs is eliminative. -/
theorem seq_eliminative (φ ψ : FCP W E)
    (hφ : ∀ F F', φ F = some F' → F'.carrier ⊆ F.carrier)
    (hψ : ∀ F F', ψ F = some F' → F'.carrier ⊆ F.carrier)
    (F F' : State W ℕ E) (h : FCP.seq φ ψ F = some F') :
    F'.carrier ⊆ F.carrier := by
  simp only [FCP.seq, Option.bind] at h
  cases hφF : φ F with
  | none => rw [hφF] at h; exact absurd h (by simp)
  | some F₁ =>
    rw [hφF] at h
    simp at h
    intro p hp
    exact hφ F F₁ hφF (hψ F₁ F' h hp)

/-- Base monotonicity for definite updates: when the body preserves the
base, so does the definite FCP. -/
theorem def_preserves_base (x : ℕ) (body : FCP W E)
    (hbody : ∀ G G', body G = some G' → G'.base = G.base)
    (F F' : State W ℕ E) (h : FCP.def_ x body F = some F') :
    F'.base = F.base := by
  simp only [FCP.def_] at h
  split at h
  · exact hbody F F' h
  · exact absurd h (by simp)

/-- Support is idempotent: if `F` supports `φ`, updating twice is the same
as once. -/
theorem supports_idempotent (F : State W ℕ E) (φ : FCP W E)
    (h : supports F φ) : FCP.seq φ φ F = φ F := by
  simp only [FCP.seq, supports] at *
  rw [h]
  simp [h]

end Theorems

end FileChangeSemantics
