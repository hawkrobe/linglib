import Linglib.Theories.Semantics.Dynamic.PPCDRT.Defs

/-!
# PPCDRT — Anaphoric Relations and Maximize Anaphora
@cite{haug-dalrymple-2020} @cite{dotlacil-2013} @cite{murray-2008}
@cite{langendoen-1978}

The anaphoric-relation conditions on top of the PPCDRT substrate, plus
the `R_u` set construction and the Maximize Anaphora principle.

Three relations distinguished by @cite{higginbotham-1985}, @cite{williams-1991}
and formalized in @cite{haug-dalrymple-2020}:

- **Binding** (`u_anaph = u_ant`): pointwise equality of dref values
  across the plural state. Requires c-command in the syntax.
  @cite{haug-dalrymple-2020} eq 30.

- **Group identity** (`∪u_anaph = ∪u_ant`): the *summed* set of values
  across the plural state is identical. The pronoun denotes the same
  plurality as its antecedent. No c-command required.
  @cite{haug-dalrymple-2020} §2.3.

- **Reciprocity** (group identity + `∂(u ≠ u')`): same plurality, plus
  per-state distinctness. The semantic core of *each other*.
  @cite{haug-dalrymple-2020} eq 41.

- **Underspecified** (group identity, no distinctness): German *sich*,
  Czech *se*, Cheyenne REFL/RECIP affix. Permits reflexive, reciprocal,
  and mixed readings (@cite{murray-2008}, @cite{cable-2014}).

The reciprocity-as-cumulativity link asserted by @cite{langendoen-1978}
shows up as a structural theorem in `Cumulativity.lean`: `groupIdentityCond`
is the bidirectional-coverage shape that `Plurality.Cumulativity.cumulativeOp`
expresses for plural arguments.

§6 of @cite{haug-dalrymple-2020} adds the **Maximize Anaphora** principle
(eq 128): when interpreting a discourse referent introduced by a reciprocal
with antecedent and relation φ, maximize the set `R_u` of pairs in the
relation, subject to consistency with world knowledge. The substrate-level
statement is given here; the §6.1/§6.2/§6.3 applications (the SMH contrast,
the multi-reciprocal pairwise prediction, the Tracy/Matty/Chris case) live
in `Phenomena/Anaphora/Studies/HaugDalrymple2020.lean`.
-/

namespace Theories.Semantics.Dynamic.PPCDRT

open Core

universe u

variable {E : Type u}

-- ════════════════════════════════════════════════════════════════
-- § 1: Binding (=) — @cite{haug-dalrymple-2020} eq 30
-- ════════════════════════════════════════════════════════════════

/-- Binding (`u_anaph = u_ant`): pointwise dref equality across the plural
    state. Both must be defined (with the same value) at every state. -/
def bindingCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S _Δ =>
  ∀ s ∈ S, ∃ d, s uAnaph = some d ∧ s uAnt = some d

-- ════════════════════════════════════════════════════════════════
-- § 2: Group Identity (∪) — @cite{haug-dalrymple-2020} §2.3
-- ════════════════════════════════════════════════════════════════

/-- Group identity (`∪u_anaph = ∪u_ant`): the value-sets of the two drefs
    across the plural state are identical. -/
def groupIdentityCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S _Δ =>
  Core.PluralAssign.sumDref S uAnaph = Core.PluralAssign.sumDref S uAnt

-- ════════════════════════════════════════════════════════════════
-- § 3: Reciprocity (R) — @cite{haug-dalrymple-2020} eq 41
-- ════════════════════════════════════════════════════════════════

/-- Reciprocity (`∂(∪u = ∪u') ∧ ∂(u ≠ u')`): group identity plus
    per-state distinctness. The presupposition wrappers are realized
    semantically when consumers project to `Truth3`. -/
def reciprocityCond (uAnaph uAnt : Nat) : PPDRSCond E := λ S Δ =>
  groupIdentityCond uAnaph uAnt S Δ ∧
  ∀ s ∈ S, ∀ d_a d_b, s uAnaph = some d_a → s uAnt = some d_b → d_a ≠ d_b

-- ════════════════════════════════════════════════════════════════
-- § 4: Underspecified — @cite{haug-dalrymple-2020} §4.2 + @cite{murray-2008}
-- ════════════════════════════════════════════════════════════════

/-- Underspecified reflexive/reciprocal: group identity with no
    distinctness. Permits reflexive, reciprocal, and mixed readings.
    @cite{murray-2008} (Cheyenne), @cite{cable-2014} (German *sich*). -/
def underspecifiedCond (uAnaph uAnt : Nat) : PPDRSCond E :=
  groupIdentityCond uAnaph uAnt

-- ════════════════════════════════════════════════════════════════
-- § 5: Implication Lattice — derives the cumulativity / underspec / etc.
-- relationships from the substrate definitions
-- ════════════════════════════════════════════════════════════════

/-- Binding implies group identity: pointwise equality of values yields
    range equality. @cite{haug-dalrymple-2020} fig 1. -/
theorem binding_implies_groupIdentity (uAnaph uAnt : Nat) (S : PluralAssign E) (Δ : Set Nat)
    (h : bindingCond uAnaph uAnt S Δ) : groupIdentityCond uAnaph uAnt S Δ := by
  ext d
  constructor
  · rintro ⟨g, hgS, hgEq⟩
    obtain ⟨d', hAnaph, hAnt⟩ := h g hgS
    refine ⟨g, hgS, ?_⟩
    rw [hgEq] at hAnaph
    rw [hAnt]; exact hAnaph.symm
  · rintro ⟨g, hgS, hgEq⟩
    obtain ⟨d', hAnaph, hAnt⟩ := h g hgS
    refine ⟨g, hgS, ?_⟩
    rw [hgEq] at hAnt
    rw [hAnaph]; exact hAnt.symm

/-- Reciprocity excludes binding: per-state distinctness contradicts
    pointwise equality, so any nonempty plural state cannot satisfy both. -/
theorem reciprocity_excludes_binding (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat) (hne : S.IsNonempty)
    (h : reciprocityCond uAnaph uAnt S Δ) :
    ¬ bindingCond uAnaph uAnt S Δ := by
  intro hb
  obtain ⟨g, hgS⟩ := hne
  obtain ⟨d, hAnaph, hAnt⟩ := hb g hgS
  exact h.2 g hgS d d hAnaph hAnt rfl

/-- Reciprocity strengthens underspecified: reciprocity = underspecified
    + per-state distinctness, so reciprocity implies underspecified. -/
theorem reciprocity_strengthens_underspecified (uAnaph uAnt : Nat)
    (S : PluralAssign E) (Δ : Set Nat)
    (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ := h.1

-- ════════════════════════════════════════════════════════════════
-- § 6: R_u (@cite{haug-dalrymple-2020} eq 127)
-- ════════════════════════════════════════════════════════════════

/-- The set of (anaphor-value, antecedent-value) pairs across the plural
    state. @cite{haug-dalrymple-2020} eq 127:
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
-- § 7: Maximize Anaphora (@cite{haug-dalrymple-2020} eq 128)
-- ════════════════════════════════════════════════════════════════

/-- **Maximize Anaphora** (@cite{haug-dalrymple-2020} eq 128). In
    interpreting a DRS containing a discourse referent `u` introduced by
    a reciprocal with antecedent `u'` and relation `φ`, maximize the set
    `R_u` of pairs standing in `φ`, subject to the constraint that `φ`
    holds in the local DRS given world knowledge.

    The substrate-level statement: for the chosen plural state `S`, no
    proper extension of `S` (in the lifted-Set sense on `R_u`) also
    satisfies `φ`. Per @cite{haug-dalrymple-2020} §6, this is a
    *generation principle*, not a decidable predicate — concrete examples
    supply per-instance `decide`-checks.

    Note: the principle replaces the Strongest Meaning Hypothesis of
    @cite{dalrymple-et-al-1998}; §6.1 of @cite{haug-dalrymple-2020}
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

end Theories.Semantics.Dynamic.PPCDRT
