import Linglib.Semantics.Dynamic.PPCDRT.Defs

/-!
# PPCDRT — Anaphoric Relations
[haug-dalrymple-2020] [dotlacil-2013] [murray-2008]
[langendoen-1978]

The anaphoric-relation conditions on top of the PPCDRT substrate, plus
the `R_u` set construction.

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
is the bidirectional-coverage shape that `Plurality.Cumulativity.Cumulative`
expresses for plural arguments.

§6 of [haug-dalrymple-2020] builds its Maximize Anaphora principle
(eq 128) over the set `R_u` of anaphor-antecedent value pairs (eq 127),
defined here; the §6.1/§6.2/§6.3 applications (the SMH contrast, the
multi-reciprocal pairwise prediction, the Tracy/Matty/Chris case) live in
`Studies/HaugDalrymple2020.lean`.
-/

namespace PPCDRT

open Core

variable {E : Type*}
variable (uAnaph uAnt : Nat) (S : PluralAssign E) (Δ : Set Nat)

/-! ### Binding -/

/-- Binding (`u_anaph = u_ant`): pointwise dref equality across the plural
    state. The two drefs hold the same `Option E` value at every state —
    either both defined and equal, or both undefined.

    Per [haug-dalrymple-2020] eq 30: `u_anaph = u_ant ≡ ∀ s ∈ S.
    v(s)(u_anaph) = v(s)(u_ant)`. The pointwise `Option` equality matches
    this — both drefs hold the same value (defined or undefined) at every
    state. Stronger than the *coreference* presupposition (the eq-29 `→`
    abbreviation), which only requires defined-and-equal where both are
    defined. -/
def bindingCond : PPDRSCond E := λ S _Δ =>
  ∀ s ∈ S, s uAnaph = s uAnt

/-! ### Group identity -/

/-- Group identity (`∪u_anaph = ∪u_ant`): the value-sets of the two
    drefs across the plural state are equal.

    [haug-dalrymple-2020] eq 41 stipulates `∂(∪u = ∪𝒜(u))` for *each
    other* — exactly this symmetric equality on sum-drefs. -/
def groupIdentityCond : PPDRSCond E := λ S _Δ =>
  Core.PluralAssign.sumDref S uAnaph = Core.PluralAssign.sumDref S uAnt

/-! ### Reciprocity -/

/-- Reciprocity (`∂(∪u = ∪u') ∧ ∂(u ≠ u')`): group identity plus
    per-state distinctness. The presupposition wrappers are realized
    semantically when consumers project to `Truth`. -/
def reciprocityCond : PPDRSCond E := λ S Δ =>
  groupIdentityCond uAnaph uAnt S Δ ∧
  ∀ s ∈ S, ∀ d_a d_b, s uAnaph = some d_a → s uAnt = some d_b → d_a ≠ d_b

/-! ### Underspecified reflexive/reciprocal -/

/-- Underspecified reflexive/reciprocal: group identity with no
    distinctness. Permits reflexive, reciprocal, and mixed readings.
    [murray-2008] (Cheyenne), [cable-2014] (German *sich*). -/
def underspecifiedCond : PPDRSCond E :=
  groupIdentityCond uAnaph uAnt

/-! ### Implication lattice -/

/-- Binding implies group identity: pointwise `Option` equality of dref
    values yields equality of value-sets. [haug-dalrymple-2020] fig 1. -/
theorem binding_implies_groupIdentity (h : bindingCond uAnaph uAnt S Δ) :
    groupIdentityCond uAnaph uAnt S Δ :=
  Set.ext λ _ => exists_congr λ g => and_congr_right λ hgS => by rw [h g hgS]

/-- Reciprocity excludes binding *when there is some state where both
    drefs are defined*: per-state distinctness then contradicts pointwise
    equality. The `hdef` hypothesis is necessary because PPCDRT allows
    both drefs to be undefined at a state, in which case binding (Option
    `none = none`) and reciprocity (vacuous distinctness) trivially
    co-exist. -/
theorem reciprocity_excludes_binding
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
theorem reciprocity_strengthens_underspecified
    (h : reciprocityCond uAnaph uAnt S Δ) :
    underspecifiedCond uAnaph uAnt S Δ := h.1

/-! ### The relation set `R_u` -/

/-- The set of (anaphor-value, antecedent-value) pairs across the plural
    state. [haug-dalrymple-2020] eq 127:
    `R_u = {⟨v(s)(u_anaph), v(s)(u_ant)⟩ : s ∈ S}`. -/
def R_u : Set (E × E) :=
  { p | ∃ s ∈ S, s uAnaph = some p.1 ∧ s uAnt = some p.2 }

/-- A bigger plural state yields a (weakly) bigger R_u. -/
theorem R_u_mono {S₁ S₂ : PluralAssign E}
    (h : ∀ g, g ∈ S₁ → g ∈ S₂) :
    R_u uAnaph uAnt S₁ ⊆ R_u uAnaph uAnt S₂ := by
  rintro ⟨a, b⟩ ⟨g, hg, hAnaph, hAnt⟩
  exact ⟨g, h g hg, hAnaph, hAnt⟩

end PPCDRT
