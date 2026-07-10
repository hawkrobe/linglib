import Linglib.Semantics.Dynamic.PPCDRT.Defs

/-!
# PPCDRT — Anaphoric Relations and Maximize Anaphora
[haug-dalrymple-2020] [dotlacil-2013] [murray-2008]
[langendoen-1978]

The anaphoric-relation conditions on top of the PPCDRT substrate, plus
the `R_u` set construction and the Maximize Anaphora principle.

Three relations distinguished by [higginbotham-1985], [williams-1991]
and formalized in [haug-dalrymple-2020]:

- **Binding** (`u_anaph = u_ant`): pointwise equality of dref values
  across the plural state. Requires c-command in the syntax.
  [haug-dalrymple-2020] eq 30.

- **Group identity** (`∪u_anaph = ∪u_ant`): the *summed* set of values
  across the plural state is identical. The pronoun denotes the same
  plurality as its antecedent. No c-command required.
  [haug-dalrymple-2020] §2.3.

- **Reciprocity** (group identity + `∂(u ≠ u')`): same plurality, plus
  per-state distinctness. The semantic core of *each other*.
  [haug-dalrymple-2020] eq 41.

- **Underspecified** (group identity, no distinctness): German *sich*,
  Czech *se*, Cheyenne REFL/RECIP affix. Permits reflexive, reciprocal,
  and mixed readings ([murray-2008], [cable-2014]).

The reciprocity-as-cumulativity link asserted by [langendoen-1978]
shows up as a structural theorem in `Cumulativity.lean`: `groupIdentityCond`
is the bidirectional-coverage shape that `Plurality.Cumulativity.cumulativeOp`
expresses for plural arguments.

§6 of [haug-dalrymple-2020] adds the **Maximize Anaphora** principle
(eq 128): when interpreting a discourse referent introduced by a reciprocal
with antecedent and relation φ, maximize the set `R_u` of pairs in the
relation, subject to consistency with world knowledge. The substrate-level
statement is given here; the §6.1/§6.2/§6.3 applications (the SMH contrast,
the multi-reciprocal pairwise prediction, the Tracy/Matty/Chris case) live
in `Studies/HaugDalrymple2020.lean`.
-/

namespace Semantics.Dynamic.PPCDRT

open Core

universe u

variable {E : Type u}

-- ════════════════════════════════════════════════════════════════
-- § 1: Binding (=) — [haug-dalrymple-2020] eq 30
-- ════════════════════════════════════════════════════════════════

/-- Binding (`u_anaph = u_ant`): pointwise dref equality across the plural
    state. The two drefs hold the same `Option E` value at every state —
    either both defined and equal, or both undefined.

    Per [haug-dalrymple-2020] eq 30: `u_anaph = u_ant ≡ ∀ s ∈ S.
    v(s)(u_anaph) = v(s)(u_ant)`. The pointwise `Option` equality matches
    this — both drefs hold the same value (defined or undefined) at every
    state. Stronger than the *coreference* presupposition (the eq-29 `→`
    abbreviation), which only requires defined-and-equal where both are
    defined. -/
def bindingCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S _Δ =>
  ∀ s ∈ S, s uAnaph = s uAnt

-- ════════════════════════════════════════════════════════════════
-- § 2: Group Identity (∪) — [haug-dalrymple-2020] §2.3
-- ════════════════════════════════════════════════════════════════

/-- One-direction sum-dref coverage: every value `uAnaph` takes across
    the plural state is also a value `uAnt` takes.

    *Note*: this is NOT [haug-dalrymple-2020] eq 29 (the asymmetric
    `→`). Paper eq 29 is `λS.λΔ.∀s ∈ S. u_anaph(s,[s]_Δ) = u_ant(s,S)` —
    an *equation* between two evaluations, not a subset relation. At
    Δ = ∅ paper eq 29 reduces to pointwise `bindingCond`, not to
    `coverCond`. The closer paper match is the SUM-dref equality of
    eq 37 (p. 16), but eq 37 is also bidirectional.

    `coverCond` is a derived auxiliary used solely by the bidirectional
    bridge `groupIdentityCond_iff_bidir_coverCond` below — it spells
    out one direction of the value-set equality so consumers can reason
    about it directly. It is not itself paper-stipulated. -/
def coverCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S _Δ =>
  Core.PluralAssign.sumDref S uAnaph ⊆ Core.PluralAssign.sumDref S uAnt

/-- Group identity (`∪u_anaph = ∪u_ant`): the value-sets of the two
    drefs across the plural state are equal.

    [haug-dalrymple-2020] eq 41 stipulates `∂(∪u = ∪𝒜(u))` for *each
    other* — exactly this symmetric equality on sum-drefs. Bidirectional
    `coverCond` is an alternative formulation provable via
    `groupIdentityCond_iff_bidir_coverCond` below. -/
def groupIdentityCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S _Δ =>
  Core.PluralAssign.sumDref S uAnaph = Core.PluralAssign.sumDref S uAnt

/-- Group identity is the bidirectional version of `coverCond`. -/
theorem groupIdentityCond_iff_bidir_coverCond (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat) :
    groupIdentityCond uAnaph uAnt S Δ ↔
    coverCond uAnaph uAnt S Δ ∧ coverCond uAnt uAnaph S Δ := by
  unfold groupIdentityCond coverCond
  exact ⟨fun h => ⟨h.le, h.ge⟩, fun ⟨h₁, h₂⟩ => Set.Subset.antisymm h₁ h₂⟩

-- ════════════════════════════════════════════════════════════════
-- § 3: Reciprocity (R) — [haug-dalrymple-2020] eq 41
-- ════════════════════════════════════════════════════════════════

/-- Reciprocity (`∂(∪u = ∪u') ∧ ∂(u ≠ u')`): group identity plus
    per-state distinctness. The presupposition wrappers are realized
    semantically when consumers project to `Truth`. -/
def reciprocityCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S Δ =>
  groupIdentityCond uAnaph uAnt S Δ ∧
  ∀ s ∈ S, ∀ d_a d_b, s uAnaph = some d_a → s uAnt = some d_b → d_a ≠ d_b

-- ════════════════════════════════════════════════════════════════
-- § 4: Underspecified — [haug-dalrymple-2020] §4.2 + [murray-2008]
-- ════════════════════════════════════════════════════════════════

/-- Underspecified reflexive/reciprocal: group identity with no
    distinctness. Permits reflexive, reciprocal, and mixed readings.
    [murray-2008] (Cheyenne), [cable-2014] (German *sich*). -/
def underspecifiedCond (uAnaph uAnt : Nat) : PPDRSCond E :=
  groupIdentityCond uAnaph uAnt

-- ════════════════════════════════════════════════════════════════
-- § 5: Implication Lattice — derives the cumulativity / underspec / etc.
-- relationships from the substrate definitions
-- ════════════════════════════════════════════════════════════════

/-- Binding implies group identity: pointwise `Option` equality of dref
    values yields equality of value-sets. [haug-dalrymple-2020] fig 1. -/
theorem binding_implies_groupIdentity (uAnaph uAnt : Nat) (S : PluralAssign E) (Δ : Set Nat)
    (h : bindingCond uAnaph uAnt S Δ) : groupIdentityCond uAnaph uAnt S Δ := by
  unfold groupIdentityCond
  ext d
  constructor
  · rintro ⟨g, hgS, hgu⟩
    exact ⟨g, hgS, by rw [← h g hgS]; exact hgu⟩
  · rintro ⟨g, hgS, hgu⟩
    exact ⟨g, hgS, by rw [h g hgS]; exact hgu⟩

/-- Reciprocity excludes binding *when there is some state where both
    drefs are defined*: per-state distinctness then contradicts pointwise
    equality. The `hdef` hypothesis is necessary because PPCDRT allows
    both drefs to be undefined at a state, in which case binding (Option
    `none = none`) and reciprocity (vacuous distinctness) trivially
    co-exist. -/
theorem reciprocity_excludes_binding (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat)
    (hdef : ∃ s ∈ S, ∃ d, s uAnaph = some d)
    (h : reciprocityCond uAnaph uAnt S Δ) :
    ¬ bindingCond uAnaph uAnt S Δ := by
  intro hb
  obtain ⟨g, hgS, d, hAnaph⟩ := hdef
  have hEq := hb g hgS
  rw [hAnaph] at hEq
  -- hEq : some d = g uAnt; so g uAnt = some d
  have hAnt : g uAnt = some d := hEq.symm
  exact h.2 g hgS d d hAnaph hAnt rfl

/-- Reciprocity strengthens underspecified: reciprocity = underspecified
    + per-state distinctness, so reciprocity implies underspecified. -/
theorem reciprocity_strengthens_underspecified (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat)
    (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ := h.1

-- ════════════════════════════════════════════════════════════════
-- § 6: R_u ([haug-dalrymple-2020] eq 127)
-- ════════════════════════════════════════════════════════════════

/-- The set of (anaphor-value, antecedent-value) pairs across the plural
    state. [haug-dalrymple-2020] eq 127:
    `R_u = {⟨v(s)(u_anaph), v(s)(u_ant)⟩ : s ∈ S}`. -/
def R_u (uAnaph uAnt : Nat) (S : PluralAssign E) : Set (E × E) :=
  { p | ∃ s ∈ S, s uAnaph = some p.1 ∧ s uAnt = some p.2 }

/-- A bigger plural state yields a (weakly) bigger R_u. -/
theorem R_u_mono (uAnaph uAnt : Nat) {S₁ S₂ : PluralAssign E}
    (h : ∀ g, g ∈ S₁ → g ∈ S₂) :
    R_u uAnaph uAnt S₁ ⊆ R_u uAnaph uAnt S₂ := by
  rintro ⟨a, b⟩ ⟨g, hg, hAnaph, hAnt⟩
  exact ⟨g, h g hg, hAnaph, hAnt⟩

-- ════════════════════════════════════════════════════════════════
-- § 7: Maximize Anaphora ([haug-dalrymple-2020] eq 128)
-- ════════════════════════════════════════════════════════════════

/-- **Maximize Anaphora** ([haug-dalrymple-2020] eq 128). In
    interpreting a DRS containing a discourse referent `u` introduced by
    a reciprocal with antecedent `u'` and relation `φ`, maximize the set
    `R_u` of pairs standing in `φ`, subject to the constraint that `φ`
    holds in the local DRS given world knowledge.

    The substrate-level statement: for the chosen plural state `S`, no
    proper extension of `S` (in the lifted-Set sense on `R_u`) also
    satisfies `φ`. Per [haug-dalrymple-2020] §6, this is a
    *generation principle*, not a decidable predicate — concrete examples
    supply per-instance `decide`-checks.

    Note: the principle replaces the Strongest Meaning Hypothesis of
    [dalrymple-et-al-1998]; §6.1 of [haug-dalrymple-2020]
    discusses the empirical contrast (paper eq 132–133). -/
def maximizeAnaphora (φ : Nat → Nat → PPDRSCond E) (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat) : Prop :=
  φ uAnaph uAnt S Δ ∧
  ∀ S', φ uAnaph uAnt S' Δ →
    R_u uAnaph uAnt S' ⊆ R_u uAnaph uAnt S

/-- Maximize Anaphora implies the chosen state satisfies the relation. -/
theorem maximizeAnaphora_implies_relation (φ : Nat → Nat → PPDRSCond E)
    (uAnaph uAnt : Nat) (S : PluralAssign E) (Δ : Set Nat)
    (h : maximizeAnaphora φ uAnaph uAnt S Δ) :
    φ uAnaph uAnt S Δ := h.1

end Semantics.Dynamic.PPCDRT
