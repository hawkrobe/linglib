import Mathlib.Data.List.Basic

/-!
# Mixed Consequence Relations
@cite{cobreros-etal-2012}

Abstract framework for mixed notions of logical consequence, where
premises and conclusions may be evaluated under different standards
of satisfaction.

## Motivation

Given multiple notions of satisfaction for a logic (e.g., tolerant,
classical, strict), we can form *mixed* consequence relations by
requiring premises to be satisfied under one standard and conclusions
under another. This generates a lattice of consequence relations
whose structural properties (strength ordering, duality, deduction
theorem) depend only on the relationships between the satisfaction
notions — not on the specific logic.

## Key Definitions

- `MixedConsequence`: Γ ⊨ᵐⁿ φ iff every model m-satisfying all
  of Γ also n-satisfies φ
- `SatImplies`: one satisfaction notion implies another
- `SatDuality`: satisfaction duality via negation and mode-swapping

## Key Results

- **Premise monotonicity**: stronger premises → more things follow
- **Conclusion monotonicity**: weaker conclusions → more things follow
- **Duality**: ⊨ᵐⁿ dualizes to ⊨^{d(n)d(m)} on negated formulas
-/

namespace Core.Logic.Consequence

section MixedConsequence

variable {Model Formula Mode : Type*}

/-- Mixed consequence relation. Γ ⊨ᵐⁿ φ iff every model that
    m-satisfies all premises also n-satisfies the conclusion.

    When m = n, this is standard (unmixed) consequence.
    When m ≠ n, the standard for premises differs from that for
    conclusions — a key feature of @cite{cobreros-etal-2012}'s
    framework for vagueness.

    Definition 15/17 of @cite{cobreros-etal-2012}, specialized
    to single-conclusion. -/
def MixedConsequence (sat : Model → Mode → Formula → Prop)
    (m n : Mode) (Γ : List Formula) (φ : Formula) : Prop :=
  ∀ M : Model, (∀ γ ∈ Γ, sat M m γ) → sat M n φ

/-- mn-validity: φ is valid when it holds with empty premises.
    The premise mode m is vacuously satisfied and thus irrelevant. -/
def mnValid (sat : Model → Mode → Formula → Prop)
    (n : Mode) (φ : Formula) : Prop :=
  ∀ M : Model, sat M n φ

/-- mn-validity is just n-validity: the premise mode is irrelevant
    when there are no premises. -/
theorem mnValid_iff_emptyPremise (sat : Model → Mode → Formula → Prop)
    (m n : Mode) (φ : Formula) :
    MixedConsequence sat m n [] φ ↔ mnValid sat n φ := by
  simp [MixedConsequence, mnValid]

end MixedConsequence

-- ════════════════════════════════════════════════════
-- § 2. Strength Ordering
-- ════════════════════════════════════════════════════

section Strength

variable {Model Formula Mode : Type*}

/-- One satisfaction notion implies another: m-satisfaction entails
    m'-satisfaction for all models and formulas. -/
def SatImplies (sat : Model → Mode → Formula → Prop)
    (m m' : Mode) : Prop :=
  ∀ (M : Model) (φ : Formula), sat M m φ → sat M m' φ

/-- `SatImplies` is reflexive. -/
theorem SatImplies.refl (sat : Model → Mode → Formula → Prop)
    (m : Mode) : SatImplies sat m m :=
  fun _ _ h => h

/-- `SatImplies` is transitive. -/
theorem SatImplies.trans {sat : Model → Mode → Formula → Prop}
    {m₁ m₂ m₃ : Mode}
    (h₁₂ : SatImplies sat m₁ m₂) (h₂₃ : SatImplies sat m₂ m₃) :
    SatImplies sat m₁ m₃ :=
  fun M φ h => h₂₃ M φ (h₁₂ M φ h)

/-- **Premise strength monotonicity** (Lemma 7, first part of
    @cite{cobreros-etal-2012}).

    If m' implies m (m' is at least as strong), then
    mn-consequence is at least as inclusive as m'n-consequence.
    Rationale: stronger premises exclude more models, so fewer
    models need to verify the conclusion, making more arguments
    valid. -/
theorem premise_monotone {sat : Model → Mode → Formula → Prop}
    {m m' n : Mode} (h : SatImplies sat m' m)
    {Γ : List Formula} {φ : Formula}
    (hc : MixedConsequence sat m n Γ φ) :
    MixedConsequence sat m' n Γ φ :=
  fun M hp => hc M (fun γ hγ => h M γ (hp γ hγ))

/-- **Conclusion strength monotonicity** (Lemma 7, second part).

    If n implies n' (n' is at least as weak), then
    mn-consequence is at least as inclusive as mn'-consequence.
    Rationale: weaker conclusions are easier to satisfy. -/
theorem conclusion_monotone {sat : Model → Mode → Formula → Prop}
    {m n n' : Mode} (h : SatImplies sat n n')
    {Γ : List Formula} {φ : Formula}
    (hc : MixedConsequence sat m n Γ φ) :
    MixedConsequence sat m n' Γ φ :=
  fun M hp => h M φ (hc M hp)

/-- **Combined monotonicity**: if m' ⟹ m and n ⟹ n', then
    mn-consequence ⊆ m'n'-consequence. -/
theorem mixed_monotone {sat : Model → Mode → Formula → Prop}
    {m m' n n' : Mode}
    (hm : SatImplies sat m' m) (hn : SatImplies sat n n')
    {Γ : List Formula} {φ : Formula}
    (hc : MixedConsequence sat m n Γ φ) :
    MixedConsequence sat m' n' Γ φ :=
  conclusion_monotone hn (premise_monotone hm hc)

end Strength

-- ════════════════════════════════════════════════════
-- § 3. Duality
-- ════════════════════════════════════════════════════

section Duality

variable {Model Formula Mode : Type*}

/-- Satisfaction duality: a negation operation on formulas and a
    dual operation on modes such that:
    - `dual` is an involution (d(d(m)) = m)
    - `neg` is an involution (¬¬φ = φ)
    - Negation swaps modes: M ⊨ᵐ ¬φ ↔ M ⊭^{d(m)} φ

    In TCS, d(t) = s, d(s) = t, d(c) = c, and negation is
    formula negation. -/
structure SatDuality (sat : Model → Mode → Formula → Prop)
    (neg : Formula → Formula) (dual : Mode → Mode) : Prop where
  dual_invol : ∀ m : Mode, dual (dual m) = m
  neg_invol : ∀ φ : Formula, neg (neg φ) = φ
  neg_swap : ∀ (M : Model) (m : Mode) (φ : Formula),
    sat M m (neg φ) ↔ ¬sat M (dual m) φ

/-- **Consequence duality** (Lemma 6 of @cite{cobreros-etal-2012}).

    If φ ⊨ᵐⁿ ψ, then ¬ψ ⊨^{d(n)d(m)} ¬φ.
    Duality swaps premise/conclusion modes and negates formulas. -/
theorem consequence_dual {sat : Model → Mode → Formula → Prop}
    {neg : Formula → Formula} {dual : Mode → Mode}
    (hd : SatDuality sat neg dual)
    {m n : Mode} {φ ψ : Formula}
    (hc : MixedConsequence sat m n [φ] ψ) :
    MixedConsequence sat (dual n) (dual m) [neg ψ] (neg φ) := by
  intro M hprem
  have hnψ : ¬sat M n ψ := by
    have := hprem (neg ψ) (List.mem_singleton.mpr rfl)
    rwa [hd.neg_swap, hd.dual_invol] at this
  rw [hd.neg_swap, hd.dual_invol]
  intro hφ
  exact hnψ (hc M (fun γ hγ => by
    rw [List.mem_singleton.mp hγ]; exact hφ))

end Duality

-- ════════════════════════════════════════════════════
-- § 4. Self-Duality
-- ════════════════════════════════════════════════════

section SelfDuality

variable {Mode : Type*}

/-- A mixed consequence relation ⊨ᵐⁿ is **self-dual** when
    m = d(n) and n = d(m). Self-dual relations are exactly
    those satisfying the deduction theorem (Lemma 10 of
    @cite{cobreros-etal-2012}).

    The three self-dual relations in TCS are: st, cc, and ts. -/
def IsSelfDual (dual : Mode → Mode) (m n : Mode) : Prop :=
  dual n = m

/-- Self-duality is symmetric when `dual` is an involution. -/
theorem selfDual_symm {dual : Mode → Mode}
    (hinv : ∀ m : Mode, dual (dual m) = m)
    {m n : Mode} (h : IsSelfDual dual m n) :
    IsSelfDual dual n m := by
  unfold IsSelfDual at *
  rw [← h, hinv]

end SelfDuality

end Core.Logic.Consequence
