import Linglib.Core.Logic.Modal.Kripke
import Linglib.Core.Logic.Team.Algebra
import Linglib.Core.Logic.Team.Closure
import Linglib.Core.Logic.Team.ClosureProfile

/-!
# Modal Inclusion Logic (MIL)

@cite{anttila-haggblom-yang-2024} @cite{anttila-2025}

Modal inclusion logic ML(⊆) extends classical modal logic with an
**inclusion atom** `x⃗ ⊆ y⃗` meaning: for every tuple of `x⃗`-truth-values
realised at some world in the team, the same tuple is realised as a
tuple of `y⃗`-truth-values at some world in the team. Introduced for
team semantics by Galliani; the modal variant ML(⊆) is axiomatised in
@cite{anttila-haggblom-yang-2024} (*Archive for Mathematical Logic*
2025; arXiv:2312.02285), which is also @cite{anttila-2025} Chapter 5.

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

## Implementation notes

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

## Sibling logics in `Core/Logic/Modal/`

* `Modal/Kripke.lean` — the carrier type.
* `Modal/Dependence.lean` — MDL (Väänänen 2008), bilateral, dep atoms.
* `Modal/Inclusion.lean` (this file) — MIL, unilateral, inclusion atoms.
* `Modal/Independence.lean` (future) — modal independence logic.

## Todo

* AHY 2024 §3 — expressive completeness and normal forms for MIL.
* AHY 2024 §4 — natural deduction axiomatisation + completeness proof.
* AHY 2024 §5 — the variant logics ML(▽) and ML(▽) (might-operator
  and singular might-operator). Should each get its own file once
  the substrate proves itself.
* Bisim invariance for MIL — same shape as BSML's; AHY 2024 §3.1 uses
  this for the expressive completeness proof.
-/

namespace Core.Logic.Modal.Inclusion

variable {W : Type*} [DecidableEq W] [Fintype W] {Atom : Type*}

open Core.Logic.Modal (KripkeModel)

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

/-! ### Semantics (AHY 2024 Definition 2.2) -/

/-- Single-polarity team-semantic evaluation. -/
def eval (M : KripkeModel W Atom) : Formula Atom → Finset W → Prop
  | .atom p,        t => ∀ w ∈ t, M.val p w = true
  | .bot,           t => t = ∅
  | .incl xys,      t =>
      ∀ w₁ ∈ t, ∃ w₂ ∈ t,
        ∀ xy ∈ xys, M.val (Prod.fst xy) w₁ = true ↔ M.val (Prod.snd xy) w₂ = true
  | .neg ψ,         t => ∀ w ∈ t, ¬ eval M ψ {w}
  | .conj ψ₁ ψ₂,    t => eval M ψ₁ t ∧ eval M ψ₂ t
  | .disj ψ₁ ψ₂,    t => ∃ t₁ t₂ : Finset W,
                          Core.Logic.Team.splitsAs t t₁ t₂ ∧
                          eval M ψ₁ t₁ ∧ eval M ψ₂ t₂
  | .poss ψ,        t => ∃ S : Finset W,
                          S ⊆ t.biUnion M.access ∧
                          (∀ w ∈ t, ∃ s ∈ S, s ∈ M.access w) ∧
                          eval M ψ S
  | .nec ψ,         t => eval M ψ (t.biUnion M.access)

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
      ∀ w₁ ∈ t, ∃ w₂ ∈ t,
        ∀ xy ∈ xys, M.val (Prod.fst xy) w₁ = true ↔ M.val (Prod.snd xy) w₂ = true :=
  Iff.rfl

@[simp] lemma support_neg (M : KripkeModel W Atom) (φ : Formula Atom) (t : Finset W) :
    support M (.neg φ) t ↔ ∀ w ∈ t, ¬ support M φ {w} := Iff.rfl

@[simp] lemma support_conj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.conj φ ψ) t ↔ support M φ t ∧ support M ψ t := Iff.rfl

@[simp] lemma support_disj (M : KripkeModel W Atom) (φ ψ : Formula Atom) (t : Finset W) :
    support M (.disj φ ψ) t ↔
      ∃ t₁ t₂ : Finset W, Core.Logic.Team.splitsAs t t₁ t₂ ∧
        support M φ t₁ ∧ support M ψ t₂ := Iff.rfl

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

/-- Every MIL formula has sup-closed support. Single-polarity induction
    is cleaner than BSML's joint-bilateral form because there's no
    antiSupport to track. -/
theorem support_supClosed (M : KripkeModel W Atom) (φ : Formula Atom) :
    SupClosed { t : Finset W | support M φ t } := by
  induction φ with
  | atom p =>
    intro s hs t ht w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact hs w h
    · exact ht w h
  | bot =>
    intro s hs t ht
    show s ∪ t = ∅
    rw [hs, ht]; simp
  | incl xys =>
    -- support .incl: every w in t has a witness w' in t with matching truth-values.
    -- Under union: a world in s ∪ t is in s or t; its witness from the
    -- corresponding side lifts to s ∪ t.
    intro s hs t ht w₁ hw₁
    rcases Finset.mem_union.mp hw₁ with hw₁s | hw₁t
    · obtain ⟨w₂, hw₂, hagree⟩ := hs w₁ hw₁s
      exact ⟨w₂, Finset.mem_union.mpr (Or.inl hw₂), hagree⟩
    · obtain ⟨w₂, hw₂, hagree⟩ := ht w₁ hw₁t
      exact ⟨w₂, Finset.mem_union.mpr (Or.inr hw₂), hagree⟩
  | neg ψ _ih =>
    -- support .neg ψ t = ∀ w ∈ t, ¬ support ψ {w}. Union-closed:
    -- the condition holds for each w ∈ s ∪ t via the corresponding side.
    intro s hs t ht w hw
    rcases Finset.mem_union.mp hw with h | h
    · exact hs w h
    · exact ht w h
  | conj ψ₁ ψ₂ ih₁ ih₂ =>
    intro s ⟨hs₁, hs₂⟩ t ⟨ht₁, ht₂⟩
    exact ⟨ih₁ hs₁ ht₁, ih₂ hs₂ ht₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    intro s ⟨s₁, s₂, hsplit_s, hs_s₁, hs_s₂⟩ t ⟨t₁, t₂, hsplit_t, hs_t₁, hs_t₂⟩
    refine ⟨s₁ ∪ t₁, s₂ ∪ t₂, ?_, ih₁ hs_s₁ hs_t₁, ih₂ hs_s₂ hs_t₂⟩
    show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = s ∪ t
    have h1 : s₁ ∪ s₂ = s := hsplit_s
    have h2 : t₁ ∪ t₂ = t := hsplit_t
    rw [show (s₁ ∪ t₁) ∪ (s₂ ∪ t₂) = (s₁ ∪ s₂) ∪ (t₁ ∪ t₂) from by
      ext x; simp [Finset.mem_union]; tauto]
    rw [h1, h2]
  | poss ψ ih =>
    -- support .poss ψ t: ∃ S ⊆ t.biUnion R, ... ∧ support ψ S.
    -- Under union: take S = S_s ∪ S_t (witnesses from each side).
    intro s ⟨S_s, hS_s_sub, hS_s_wit, hS_s_supp⟩ t ⟨S_t, hS_t_sub, hS_t_wit, hS_t_supp⟩
    refine ⟨S_s ∪ S_t, ?_, ?_, ih hS_s_supp hS_t_supp⟩
    · -- S_s ∪ S_t ⊆ (s ∪ t).biUnion R
      intro x hx
      rcases Finset.mem_union.mp hx with hx_s | hx_t
      · have := hS_s_sub hx_s
        rw [Finset.mem_biUnion] at this ⊢
        obtain ⟨w, hw, hxw⟩ := this
        exact ⟨w, Finset.mem_union.mpr (Or.inl hw), hxw⟩
      · have := hS_t_sub hx_t
        rw [Finset.mem_biUnion] at this ⊢
        obtain ⟨w, hw, hxw⟩ := this
        exact ⟨w, Finset.mem_union.mpr (Or.inr hw), hxw⟩
    · -- Every w in s ∪ t has a witness in S_s ∪ S_t
      intro w hw
      rcases Finset.mem_union.mp hw with hws | hwt
      · obtain ⟨s', hs', hacc⟩ := hS_s_wit w hws
        exact ⟨s', Finset.mem_union.mpr (Or.inl hs'), hacc⟩
      · obtain ⟨s', hs', hacc⟩ := hS_t_wit w hwt
        exact ⟨s', Finset.mem_union.mpr (Or.inr hs'), hacc⟩
  | nec ψ ih =>
    -- support .nec ψ t = support ψ (t.biUnion R).
    -- (s ∪ t).biUnion R = s.biUnion R ∪ t.biUnion R; UC of support of ψ.
    intro s hs t ht
    show support M ψ ((s ∪ t).biUnion M.access)
    rw [Finset.union_biUnion]
    exact ih hs ht

/-! ### Empty team property (AHY 2024 §2) -/

theorem support_empty (M : KripkeModel W Atom) (φ : Formula Atom) :
    support M φ ∅ := by
  induction φ with
  | atom p => intro w hw; exact absurd hw (Finset.notMem_empty w)
  | bot => rfl
  | incl xys => intro w₁ hw₁; exact absurd hw₁ (Finset.notMem_empty w₁)
  | neg ψ _ih => intro w hw; exact absurd hw (Finset.notMem_empty w)
  | conj ψ₁ ψ₂ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | disj ψ₁ ψ₂ ih₁ ih₂ =>
    refine ⟨∅, ∅, ?_, ih₁, ih₂⟩
    show ∅ ∪ ∅ = ∅
    simp
  | poss ψ ih =>
    refine ⟨∅, ?_, ?_, ih⟩
    · intro x hx; exact absurd hx (Finset.notMem_empty x)
    · intro w hw; exact absurd hw (Finset.notMem_empty w)
  | nec ψ ih =>
    show support M ψ ((∅ : Finset W).biUnion M.access)
    rw [Finset.biUnion_empty]
    exact ih

/-- **MIL has the upward closure profile**: every formula's support is
    sup-closed and contains the empty team
    (`Core.Logic.Team.IsUpwardProfile`). Bundles `support_supClosed`
    and `support_empty` into the named profile, placing MIL alongside
    BSML-with-NE and BSMLEmpty in the `IsUpwardProfile` cell of the
    closure-property lattice. -/
theorem support_isUpwardProfile (M : KripkeModel W Atom) (φ : Formula Atom) :
    Core.Logic.Team.IsUpwardProfile { t : Finset W | support M φ t } :=
  ⟨support_supClosed M φ, support_empty M φ⟩

/-! ### Inclusion breaks downward closure (the defining feature) -/

/-- **The inclusion atom breaks downward closure**: a constructive
    counterexample. With two distinct worlds `w₁, w₂` where:
    * `M.val a w₁ = M.val b w₂` (so w₂ witnesses w₁'s a-as-b in {w₁,w₂})
    * `M.val a w₂ = M.val b w₂` (so w₂ self-witnesses)
    * `M.val a w₁ ≠ M.val b w₁` (so {w₁} alone fails)
    the team `{w₁, w₂}` supports `a ⊆ b` but the subteam `{w₁}` does not.

    This shows MIL's inclusion atom violates downward closure (the
    defining negative property of the inclusion family — Anttila Ch 5
    contrasts MIL with dependence logic on exactly this axis). -/
theorem not_isLowerSet_incl_of_witness {a b : Atom} {w₁ w₂ : W}
    {M : KripkeModel W Atom}
    (hne : w₁ ≠ w₂)
    (hpair : M.val a w₁ = true ↔ M.val b w₂ = true)
    (hself : M.val a w₂ = true ↔ M.val b w₂ = true)
    (hwit : ¬ (M.val a w₁ = true ↔ M.val b w₁ = true)) :
    ¬ IsLowerSet { t : Finset W | support M (.incl [(a, b)]) t } := by
  intro hLS
  -- {w₁, w₂} supports a ⊆ b: w₂ witnesses both w₁'s and w₂'s a-values
  have h_full : support M (.incl [(a, b)]) ({w₁, w₂} : Finset W) := by
    intro w hw
    refine ⟨w₂, Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl), ?_⟩
    intro xy hxy
    rw [List.mem_singleton] at hxy
    subst hxy
    rcases Finset.mem_insert.mp hw with hw1 | hw2
    · subst hw1; exact hpair
    · rw [Finset.mem_singleton] at hw2
      subst hw2; exact hself
  -- {w₁} ⊆ {w₁, w₂}, so IsLowerSet gives support on {w₁}
  have hsub : ({w₁} : Finset W) ⊆ ({w₁, w₂} : Finset W) := by
    intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]; exact Finset.mem_insert_self w₁ {w₂}
  have h_small : support M (.incl [(a, b)]) ({w₁} : Finset W) :=
    hLS hsub h_full
  -- But {w₁}'s a-witness must be in {w₁}, and {w₁}'s own values don't agree
  obtain ⟨w', hw', hagree⟩ := h_small w₁ (Finset.mem_singleton.mpr rfl)
  rw [Finset.mem_singleton] at hw'
  have hag := hagree (a, b) (List.mem_singleton.mpr rfl)
  simp only at hag
  rw [hw'] at hag
  exact hwit hag

end Core.Logic.Modal.Inclusion
