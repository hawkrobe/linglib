import Linglib.Core.Semantics.Proposition
import Linglib.Core.Scales.EpistemicScale.Conditional
import Linglib.Core.Order.Normality

/-!
# Belief Revision and Preferential Reasoning

@cite{halpern-2003} @cite{alchourrn-makinson-1985} @cite{kraus-magidor-1990}@cite{halpern-2003} connects three frameworks — default reasoning @cite{kratzer-1981} @cite{kratzer-2012}
(System P), AGM belief revision, and conditional plausibility measures —
showing they are algebraically equivalent. This file formalizes:

1. **AGM revision postulates** (K*1–K*5): the rational constraints on
   how a belief set should change when new evidence arrives.
2. **Preferential structures** (System P): the axioms for "normally A
   implies B" that underlie default reasoning.
3. **Bridge to Kratzer**: Kratzer's ordering source IS a preferential
   structure, connecting modal semantics to belief revision.

## The Connection

```
Kratzer ordering source (Theories/Semantics/Modality/Kratzer.lean)
    ↓
Preferential structure (this file: System P axioms)
    ↓
Conditional plausibility (EpistemicScale/Conditional.lean)
    ↓
AGM revision operator (this file: K*1–K*5)
```

-/

namespace Core.Logic.BeliefRevision

open Core.Proposition (Prop' BProp)

-- ══════════════════════════════════════════════════════════════════════
-- § 1. AGM Belief Revision (Alchourrón, @cite{alchourrn-makinson-1985})
-- ══════════════════════════════════════════════════════════════════════

/-- A belief set: a deductively closed set of propositions.
    Represented as a predicate on propositions (K is a theory). -/
abbrev BeliefSet (W : Type*) := Set (Prop' W)

/-- An AGM revision operator with fixed prior beliefs.

    The prior belief set K is determined by the measure (the probability-1
    propositions), not freely chosen. This matches @cite{halpern-2003}'s representation theorem, where the AGM postulates hold for the specific
    K induced by the conditional plausibility measure.

    K*3 (inclusion) is stated in logical-consequence form: K*φ ⊆ Cn(K ∪ {φ}),
    meaning every revised belief is entailed by the prior beliefs together
    with φ. This is the standard semantic formulation that avoids requiring
    explicit deductive closure infrastructure. -/
structure AGMRevision (W : Type*) where
  /-- The prior belief set, determined by the measure -/
  beliefs : BeliefSet W

  /-- The revision operation: φ ↦ K * φ -/
  revise : Prop' W → BeliefSet W

  /-- K*2 (success): φ ∈ K * φ (when φ is satisfiable) -/
  success : ∀ φ, (∃ w, φ w) → φ ∈ revise φ

  /-- K*3 (inclusion): K * φ ⊆ Cn(K ∪ {φ}).
      Every revised belief follows from the prior beliefs plus φ.
      Stated semantically: if w satisfies all prior beliefs and φ,
      then w satisfies every ψ ∈ K * φ. -/
  inclusion : ∀ φ ψ,
    ψ ∈ revise φ → ∀ w, (∀ χ ∈ beliefs, χ w) → φ w → ψ w

  /-- K*4 (vacuity): if ¬φ ∉ K, then Cn(K ∪ {φ}) ⊆ K * φ.
      If φ is consistent with the prior beliefs, everything entailed
      by beliefs + φ is in the revised set. Together with K*3, this gives
      K * φ = Cn(K ∪ {φ}) when φ is consistent with K. -/
  vacuity : ∀ φ ψ,
    (fun w => ¬φ w) ∉ beliefs →
    (∀ w, (∀ χ ∈ beliefs, χ w) → φ w → ψ w) → ψ ∈ revise φ

  /-- K*5 (consistency): K * φ is consistent when φ is satisfiable -/
  consistency : ∀ φ,
    (∃ w, φ w) → ∃ w, ∀ ψ ∈ revise φ, ψ w


-- ══════════════════════════════════════════════════════════════════════
-- § 2. Preferential Structures (System P)
-- ══════════════════════════════════════════════════════════════════════

/-- A preferential consequence relation: `φ |~ ψ` reads "normally, if φ then ψ".

    System P axiomatizes the minimal
    properties of default reasoning. @cite{halpern-2003} shows that
    System P is sound and complete for preferential models — structures
    where worlds are ordered by plausibility, and `φ |~ ψ` iff ψ holds
    at all most-plausible φ-worlds. -/
structure PreferentialConsequence (W : Type*) where
  /-- The default consequence relation: `default φ ψ` means φ |~ ψ -/
  default : Prop' W → Prop' W → Prop

  /-- Reflexivity: φ |~ φ -/
  refl : ∀ φ, default φ φ

  /-- Left Logical Equivalence: if φ ↔ ψ then (φ |~ χ ↔ ψ |~ χ) -/
  leftEquiv : ∀ φ ψ χ,
    (∀ w, φ w ↔ ψ w) → (default φ χ ↔ default ψ χ)

  /-- Right Weakening: if φ |~ ψ and ψ → χ, then φ |~ χ -/
  rightWeaken : ∀ φ ψ χ,
    default φ ψ → (∀ w, ψ w → χ w) → default φ χ

  /-- And: if φ |~ ψ and φ |~ χ, then φ |~ (ψ ∧ χ) -/
  and_ : ∀ φ ψ χ,
    default φ ψ → default φ χ → default φ (fun w => ψ w ∧ χ w)

  /-- Or: if φ |~ χ and ψ |~ χ, then (φ ∨ ψ) |~ χ -/
  or_ : ∀ φ ψ χ,
    default φ χ → default ψ χ →
    default (fun w => φ w ∨ ψ w) χ

  /-- Cautious Monotonicity: if φ |~ ψ and φ |~ χ, then (φ ∧ ψ) |~ χ -/
  cautiousMono : ∀ φ ψ χ,
    default φ ψ → default φ χ →
    default (fun w => φ w ∧ ψ w) χ

/-- Rational Monotonicity: if φ |~ χ and ¬(φ |~ ¬ψ), then (φ ∧ ψ) |~ χ.

    This is strictly stronger than System P. @cite{halpern-2003} shows
    it corresponds to ranked (well-ordered) plausibility models, not
    merely preferential ones. -/
def rationalMonotonicity {W : Type*} (pc : PreferentialConsequence W) : Prop :=
  ∀ φ ψ χ : Prop' W,
    pc.default φ χ → ¬pc.default φ (fun w => ¬ψ w) →
    pc.default (fun w => φ w ∧ ψ w) χ

-- ══════════════════════════════════════════════════════════════════════
-- § 3. Plausibility Ordering → Preferential Consequence
-- ══════════════════════════════════════════════════════════════════════

/-- A plausibility ordering on worlds: w₁ ≤ w₂ means w₁ is at least
    as plausible as w₂. The minimal elements of a proposition A are
    the most plausible A-worlds.

    Extends `NormalityOrder` with the **smoothness condition** (also
    called "limit assumption"): every satisfiable proposition has
    minimal elements. This is automatic for finite W; for infinite W
    it rules out infinite descending chains. @cite{kraus-magidor-1990} call this
    "stopperedness". -/
structure PlausibilityOrder (W : Type*) extends Core.Order.NormalityOrder W where
  /-- Smoothness: every satisfiable φ has a minimal element -/
  smooth : ∀ (φ : Prop' W) (w : W), φ w →
    ∃ v, φ v ∧ le v w ∧ ∀ u, φ u → le u v → le v u

/-- The most plausible worlds satisfying φ: those with no strictly
    more plausible φ-world.

    This is the same as `NormalityOrder.optimal` applied to the set
    `{w | φ w}`, but stated with `Prop'` for the System P interface. -/
def PlausibilityOrder.minimal {W : Type*} (po : PlausibilityOrder W)
    (φ : Prop' W) : Prop' W :=
  fun w => φ w ∧ ∀ v, φ v → po.le v w → po.le w v

/-- A plausibility ordering induces a preferential consequence relation:
    φ |~ ψ iff all minimal φ-worlds satisfy ψ.

    @cite{halpern-2003}, Theorem 8.1.1: System P is sound and complete for
    this semantics. -/
def PlausibilityOrder.toPreferential {W : Type*}
    (po : PlausibilityOrder W) : PreferentialConsequence W where
  default := fun φ ψ => ∀ w, po.minimal φ w → ψ w
  refl := fun φ w ⟨hφ, _⟩ => hφ
  leftEquiv := fun φ ψ χ hEquiv => by
    constructor
    · intro h w ⟨hψ, hmin⟩
      exact h w ⟨(hEquiv w).mpr hψ, fun v hv hle => hmin v ((hEquiv v).mp hv) hle⟩
    · intro h w ⟨hφ, hmin⟩
      exact h w ⟨(hEquiv w).mp hφ, fun v hv hle => hmin v ((hEquiv v).mpr hv) hle⟩
  rightWeaken := fun φ ψ χ hdef hent w hmin => hent w (hdef w hmin)
  and_ := fun φ ψ χ hψ hχ w hmin => ⟨hψ w hmin, hχ w hmin⟩
  or_ := fun φ ψ χ hφχ hψχ w ⟨hφψ, hmin⟩ =>
    hφψ.elim
      (fun hφ => hφχ w ⟨hφ, fun v hv hle => hmin v (Or.inl hv) hle⟩)
      (fun hψ => hψχ w ⟨hψ, fun v hv hle => hmin v (Or.inr hv) hle⟩)
  cautiousMono := fun φ ψ χ hψ hχ w ⟨⟨hφ, hψw⟩, hmin⟩ => by
    obtain ⟨v, hφv, hvw, hmin_v⟩ := po.smooth φ w hφ
    have hψv : ψ v := hψ v ⟨hφv, hmin_v⟩
    have hwv := hmin v ⟨hφv, hψv⟩ hvw
    have hmin_w : ∀ u, φ u → po.le u w → po.le w u := by
      intro u hφu huw
      have huv := po.le_trans u w v huw hwv
      have hvu := hmin_v u hφu huv
      exact po.le_trans w v u hwv hvu
    exact hχ w ⟨hφ, hmin_w⟩

-- ══════════════════════════════════════════════════════════════════════
-- § 4. Bridge: Kratzer Ordering Source → Preferential Structure
-- ══════════════════════════════════════════════════════════════════════

/-- Kratzer's ordering source induces a plausibility ordering on worlds.

    Given propositions A₁,..., Aₙ in the ordering source, world w is
    at least as plausible as v iff every Aᵢ satisfied by v is also
    satisfied by w.

    This is exactly Kratzer's `atLeastAsGoodAs`, repackaged as a
    `PlausibilityOrder`. The bridge connects:
    - Kratzer modal semantics (Theories/Semantics/Modality/Kratzer.lean)
    - Preferential reasoning (System P axioms above)
    - Epistemic likelihood (Core/Scales/EpistemicScale/ via halpernLift) -/
private lemma filter_sublist_of_imp {α : Type*} (l : List α)
    (p q : α → Bool) (h : ∀ x ∈ l, p x = true → q x = true) :
    (l.filter p).Sublist (l.filter q) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a t ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    simp only [List.filter_cons]
    by_cases hpa : p a = true
    · rw [if_pos hpa, if_pos (h a List.mem_cons_self hpa)]
      exact ih'.cons₂ a
    · rw [if_neg hpa]
      by_cases hqa : q a = true
      · rw [if_pos hqa]; exact ih'.cons a
      · rw [if_neg hqa]; exact ih'

private lemma sublist_length_lt_of_mem {α : Type*} {l₁ l₂ : List α}
    (hsub : l₁.Sublist l₂) {x : α} (hx : x ∈ l₂) (hnx : x ∉ l₁) :
    l₁.length < l₂.length := by
  rcases Nat.lt_or_eq_of_le hsub.length_le with h | h
  · exact h
  · exact absurd (hsub.eq_of_length h ▸ hx) hnx

def kratzerPlausibility {W : Type*} [Fintype W] [DecidableEq W]
    (orderingSource : List (BProp W)) : PlausibilityOrder W where
  toNormalityOrder := Core.Order.NormalityOrder.fromProps orderingSource
  smooth := fun φ w hφw => by
    classical
    let sat := fun (v : W) => (orderingSource.filter (fun p => p v)).length
    let cands := Finset.univ.filter
      (fun v => φ v ∧ ∀ p ∈ orderingSource, p w = true → p v = true)
    have hw : w ∈ cands := by
      simp only [cands, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hφw, fun _ _ h => h⟩
    obtain ⟨v, hv_mem, hv_eq⟩ := cands.exists_mem_eq_sup' ⟨w, hw⟩ sat
    have hv_max : ∀ y ∈ cands, sat y ≤ sat v := fun y hy =>
      hv_eq ▸ Finset.le_sup' sat hy
    simp only [cands, Finset.mem_filter, Finset.mem_univ, true_and] at hv_mem
    refine ⟨v, hv_mem.1, hv_mem.2, ?_⟩
    intro u hφu huv p hp hpu
    by_contra hpv
    simp only [Bool.not_eq_true] at hpv
    have hu_mem : u ∈ cands := by
      simp only [cands, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hφu, fun q hq hqw => huv q hq (hv_mem.2 q hq hqw)⟩
    have hfilt : (orderingSource.filter (fun q => q v)).Sublist
                 (orderingSource.filter (fun q => q u)) :=
      filter_sublist_of_imp orderingSource _ _ (fun q hq hqv => huv q hq hqv)
    have hp_in_u : p ∈ orderingSource.filter (fun q => q u) :=
      List.mem_filter.mpr ⟨hp, hpu⟩
    have hp_not_v : p ∉ orderingSource.filter (fun q => q v) := fun h => by
      rw [List.mem_filter] at h; exact absurd h.2 (by simp [hpv])
    have : sat v < sat u := sublist_length_lt_of_mem hfilt hp_in_u hp_not_v
    linarith [hv_max u hu_mem]

/-- The preferential consequence relation induced by Kratzer's ordering
    source: φ |~ ψ iff all most-plausible φ-worlds (given the ordering
    source) satisfy ψ. This is the formal content of Kratzer's claim that
    "modal base + ordering source = conditional". -/
def kratzerDefault {W : Type*} [Fintype W] [DecidableEq W]
    (orderingSource : List (BProp W)) : PreferentialConsequence W :=
  (kratzerPlausibility orderingSource).toPreferential

-- ══════════════════════════════════════════════════════════════════════
-- § 5. FinAddMeasure Helpers
-- ══════════════════════════════════════════════════════════════════════

open Core.Scale in
/-- The empty set has measure 0. -/
private theorem mu_empty {W : Type*} (m : FinAddMeasure W) :
    m.mu ∅ = 0 := by
  have h := m.additive ∅ Set.univ (fun x hx _ => hx.elim)
  simp [m.total] at h
  linarith [m.nonneg ∅]

open Core.Scale in
/-- Subset monotonicity: A ⊆ B → μ(A) ≤ μ(B). -/
private theorem mu_mono {W : Type*} (m : FinAddMeasure W)
    (A B : Set W) (h : A ⊆ B) : m.mu A ≤ m.mu B := by
  have hdisj : ∀ x, x ∈ A → x ∉ B \ A := fun x hx ⟨_, hna⟩ => hna hx
  have hunion := m.additive A (B \ A) hdisj
  rw [Set.union_diff_cancel h] at hunion
  linarith [m.nonneg (B \ A)]

open Core.Scale in
/-- Complement measure: μ(A) + μ(Aᶜ) = 1. -/
private theorem mu_compl {W : Type*} (m : FinAddMeasure W)
    (A : Set W) : m.mu A + m.mu Aᶜ = 1 := by
  have hdisj : ∀ x, x ∈ A → x ∉ Aᶜ := fun x hx hxc => hxc hx
  have hunion := m.additive A Aᶜ hdisj
  rw [Set.union_compl_self] at hunion
  linarith [m.total]

open Core.Scale in
/-- In finite W, if every singleton in A has measure 0, then μ(A) = 0. -/
private theorem mu_eq_zero_of_singletons {W : Type*} [Fintype W] [DecidableEq W]
    (m : FinAddMeasure W) (A : Set W)
    (h : ∀ w ∈ A, m.mu {w} = 0) : m.mu A = 0 := by
  classical
  suffices key : ∀ (s : Finset W), (∀ w ∈ s, m.mu {w} = 0) → m.mu ↑s = 0 by
    have hA : A = ↑(Finset.univ.filter (· ∈ A)) := by ext x; simp
    rw [hA]
    exact key _ (fun w hw => by simp [Finset.mem_filter] at hw; exact h w hw)
  intro s
  induction s using Finset.cons_induction with
  | empty => intro _; simp [Finset.coe_empty, mu_empty m]
  | cons a t ha ih =>
    intro hall
    rw [Finset.coe_cons, Set.insert_eq a ↑t]
    have hdisj : ∀ x, x ∈ ({a} : Set W) → x ∉ (↑t : Set W) :=
      fun x hx hxt => ha (Set.mem_singleton_iff.mp hx ▸ Finset.mem_coe.mp hxt)
    rw [m.additive {a} ↑t hdisj,
        hall a (Finset.mem_cons_self a t),
        ih (fun w hw => hall w (Finset.mem_cons.mpr (Or.inr hw))),
        zero_add]

-- ══════════════════════════════════════════════════════════════════════
-- § 6. Bridge: Conditional Plausibility → AGM Revision
-- ══════════════════════════════════════════════════════════════════════

open Core.Scale in
/-- P(φ|φ) = P(⊤|φ) when φ is normal (the common case). -/
private theorem condMu_self_eq_univ {W : Type*}
    (m : CondMeasure W) (φ : Set W) (hn : m.condMu φ φ ≠ 0) :
    m.condMu φ φ = m.condMu Set.univ φ := by
  have hchain := m.cond_chain Set.univ φ φ
  simp only [Set.univ_inter, Set.inter_self] at hchain
  have hnorm := m.cond_norm φ hn
  rw [hnorm] at hchain ⊢; linarith

open Core.Scale in
/-- P(ψ|φ) + P(ψᶜ|φ) = P(⊤|φ) by conditional additivity. -/
private theorem condMu_compl {W : Type*}
    (m : CondMeasure W) (ψ φ : Set W) :
    m.condMu ψ φ + m.condMu ψᶜ φ = m.condMu Set.univ φ := by
  have := m.cond_additive ψ ψᶜ φ (fun x hx hxc => hxc hx)
  rw [Set.union_compl_self] at this
  exact this.symm

open Core.Scale in
/-- Key lemma: if P(ψ|φ) = P(⊤|φ) and φ is normal, then μ(φ \ ψ) = 0.
    This is the algebraic core shared by the K*3, K*4, and K*5 proofs. -/
private theorem mu_diff_eq_zero_of_condMu {W : Type*}
    (m : CondMeasure W) (ψ φ : Set W)
    (hreg : m.condMu φ φ ≠ 0) (hcond : m.condMu ψ φ = m.condMu Set.univ φ) :
    m.mu (φ \ ψ) = 0 := by
  have hnorm := m.cond_norm φ hreg
  have htop := (condMu_self_eq_univ m φ hreg).symm
  rw [hnorm] at htop
  rw [htop] at hcond
  have hcompl := condMu_compl m ψ φ
  rw [hcond, htop] at hcompl
  have hpsic : m.condMu ψᶜ φ = 0 := by linarith [m.cond_nonneg ψᶜ φ]
  have hchain := m.cond_chain ψᶜ φ Set.univ
  simp only [Set.inter_univ] at hchain
  rw [m.cond_univ, m.cond_univ] at hchain
  rw [hpsic, zero_mul] at hchain
  have : φ \ ψ = ψᶜ ∩ φ := by
    ext x; simp [Set.mem_diff, Set.mem_compl_iff, Set.mem_inter_iff, and_comm]
  rw [this]; exact hchain

open Core.Scale in
/-- If μ({w}) > 0 and μ(A) = 1, then w ∈ A.
    Worlds with positive measure satisfy all probability-1 beliefs. -/
private theorem mem_of_mu_singleton_pos {W : Type*}
    (m : FinAddMeasure W) (w : W) (A : Set W)
    (hw : 0 < m.mu {w}) (hA : m.mu A = 1) : w ∈ A := by
  by_contra hw_not
  have hAc : m.mu Aᶜ = 0 := by have := mu_compl m A; linarith
  have hsub : ({w} : Set W) ⊆ Aᶜ := fun v hv => by
    rw [Set.mem_singleton_iff.mp hv]; exact hw_not
  linarith [mu_mono m {w} Aᶜ hsub]

open Core.Scale in
/-- A **regular** conditional measure: every satisfiable proposition is
    normal (P(φ|φ) ≠ 0 when φ ≠ ∅), and every satisfiable set has
    positive unconditional measure. The latter ("full support") ensures
    consistency of revised beliefs in finite W.

    For the ratio construction `FinAddMeasure.toCondMeasure`, regularity
    is equivalent to: every singleton has positive measure.

    @cite{halpern-2003}'s regularity condition. -/
structure Core.Scale.RegularCondMeasure (W : Type*) extends Core.Scale.CondMeasure W where
  regular : ∀ (φ : Set W), (∃ w, w ∈ φ) → condMu φ φ ≠ 0
  muPositive : ∀ (φ : Set W), (∃ w, w ∈ φ) → 0 < mu φ

open Core.Scale in
/-- The core inclusion argument, factored as a helper for reuse by K*5.
    If P(ψ|φ) = P(⊤|φ) and w satisfies all probability-1 beliefs and φ,
    then w satisfies ψ. -/
private theorem revised_entails {W : Type*}
    (m : Core.Scale.RegularCondMeasure W) (ψ φ : Prop' W)
    (hrev : m.condMu (fun w => ψ w : Set W) (fun w => φ w : Set W) =
            m.condMu Set.univ (fun w => φ w : Set W))
    (w : W) (hbeliefs : ∀ (χ : Prop' W), m.mu (fun w => χ w : Set W) = 1 → χ w)
    (hφ : φ w) : ψ w := by
  by_contra hnψ
  have hsat : ∃ v, φ v := ⟨w, hφ⟩
  have hdiff := mu_diff_eq_zero_of_condMu m.toCondMeasure
    (fun w => ψ w) (fun w => φ w) (m.regular _ hsat) hrev
  -- w ∈ φ \ ψ, so {w} ⊆ φ \ ψ, so μ({w}) ≤ μ(φ \ ψ) = 0
  have hsub : ({w} : Set W) ⊆ (fun w => φ w : Set W) \ (fun w => ψ w : Set W) :=
    fun v hv => by rw [Set.mem_singleton_iff.mp hv]; exact ⟨hφ, hnψ⟩
  have hw_zero : m.mu ({w} : Set W) = 0 :=
    le_antisymm (by linarith [mu_mono m.toFinAddMeasure _ _ hsub]) (m.nonneg _)
  -- μ({w}ᶜ) = 1, so by hbeliefs, w ∈ {w}ᶜ — contradiction
  have hcompl : m.mu ({w} : Set W)ᶜ = 1 := by
    have := mu_compl m.toFinAddMeasure ({w} : Set W); linarith
  exact absurd (hbeliefs (fun v => v ≠ w) hcompl) (not_not.mpr rfl)

open Core.Scale in
/-- **Theorem**: every regular conditional plausibility
    measure induces an AGM revision operator on finite W.

    Construction:
    - K (beliefs) = {ψ | μ(ψ) = 1} — the probability-1 propositions
    - K * φ = {ψ | P(ψ | φ) = P(⊤ | φ)} — the conditional probability-1
      propositions

    The AGM postulates K*2–K*5 are verified:
    - K*2 (success): P(φ|φ) = P(⊤|φ) by regularity + cond_norm
    - K*3 (inclusion): P(ψ|φ) = 1 → μ(φ \ ψ) = 0 → (ψ ∪ φᶜ) ∈ K → ψ
      follows from beliefs + φ
    - K*4 (vacuity): if ¬φ ∉ K (i.e., μ(φ) > 0), then beliefs + φ entailing
      ψ implies P(ψ|φ) = 1 (by finite decomposition: every φ \ ψ world has
      measure 0, so μ(φ \ ψ) = 0)
    - K*5 (consistency): finite W has a positive-measure φ-world satisfying
      all beliefs, which satisfies all of K*φ by K*3 -/
noncomputable def Core.Scale.RegularCondMeasure.toAGM {W : Type*}
    [Fintype W] [DecidableEq W]
    (m : Core.Scale.RegularCondMeasure W) : AGMRevision W where
  beliefs := { ψ | m.mu (fun w => ψ w : Set W) = 1 }
  revise := fun φ =>
    { ψ | m.condMu (fun w => ψ w : Set W) (fun w => φ w : Set W) =
           m.condMu Set.univ (fun w => φ w : Set W) }
  success := fun φ hsat => by
    show m.condMu (fun w => φ w) (fun w => φ w) =
         m.condMu Set.univ (fun w => φ w)
    exact condMu_self_eq_univ m.toCondMeasure _ (m.regular _ hsat)
  inclusion := fun φ ψ hrev w hbeliefs hφ =>
    revised_entails m ψ φ hrev w hbeliefs hφ
  vacuity := fun φ ψ hnot_neg hent => by
    show m.condMu (fun w => ψ w) (fun w => φ w) = m.condMu Set.univ (fun w => φ w)
    -- ¬φ ∉ beliefs ↔ μ(φᶜ) ≠ 1 ↔ μ(φ) > 0
    have hmu_phi_pos : 0 < m.mu (fun w => φ w : Set W) := by
      have hcompl := mu_compl m.toFinAddMeasure (fun w => φ w : Set W)
      by_contra h; push_neg at h
      have h0 := le_antisymm h (m.nonneg _)
      have hone : m.mu (fun w => φ w : Set W)ᶜ = 1 := by linarith
      exact hnot_neg hone
    have hsat : ∃ w, φ w := by
      by_contra hall; push_neg at hall
      linarith [mu_eq_zero_of_singletons m.toFinAddMeasure (fun w => φ w : Set W)
        (fun w hw => absurd hw (hall w))]
    -- P(⊤|φ) = 1
    have htop : m.condMu Set.univ (fun w => φ w) = 1 := by
      have := condMu_self_eq_univ m.toCondMeasure (fun w => φ w) (m.regular _ hsat)
      rw [m.toCondMeasure.cond_norm _ (m.regular _ hsat)] at this; exact this.symm
    rw [htop]
    -- Need P(ψ|φ) = 1. Suffices: P(ψᶜ|φ) = 0.
    have hcompl_cond := condMu_compl m.toCondMeasure (fun w => ψ w) (fun w => φ w)
    rw [htop] at hcompl_cond
    suffices hpsic : m.condMu (fun w => ψ w : Set W)ᶜ (fun w => φ w) = 0 by linarith
    -- By chain rule: P(ψᶜ|φ) · μ(φ) = μ(ψᶜ ∩ φ)
    have hchain := m.toCondMeasure.cond_chain (fun w => ψ w : Set W)ᶜ (fun w => φ w) Set.univ
    simp only [Set.inter_univ] at hchain
    rw [m.toCondMeasure.cond_univ, m.toCondMeasure.cond_univ] at hchain
    -- Show μ(ψᶜ ∩ φ) = 0: every w ∈ ψᶜ ∩ φ has μ({w}) = 0
    have hdiff_zero : m.mu ((fun w => ψ w : Set W)ᶜ ∩ (fun w => φ w : Set W)) = 0 := by
      apply mu_eq_zero_of_singletons m.toFinAddMeasure
      intro w ⟨hnψ, hφ⟩
      by_contra h_pos; push_neg at h_pos
      have h_pos' : 0 < m.mu ({w} : Set W) :=
        lt_of_le_of_ne (m.nonneg _) (Ne.symm h_pos)
      have hbeliefs : ∀ (χ : Prop' W), m.mu (fun w => χ w : Set W) = 1 → χ w :=
        fun χ hχ => mem_of_mu_singleton_pos m.toFinAddMeasure w _ h_pos' hχ
      exact hnψ (hent w hbeliefs hφ)
    rw [hdiff_zero] at hchain
    rcases mul_eq_zero.mp hchain.symm with h | h
    · exact h
    · linarith
  consistency := fun φ hsat => by
    -- Find w ∈ φ with μ({w}) > 0, then w satisfies all of K*φ.
    have hmu_pos := m.muPositive _ hsat
    -- If all singletons in φ had measure 0, μ(φ) = 0, contradiction.
    by_contra hall; push_neg at hall
    -- hall : ∀ w, ∃ ψ ∈ revise φ, ¬ψ w
    have hzero : ∀ w, φ w → m.mu ({w} : Set W) = 0 := by
      intro w hw
      by_contra h_pos; push_neg at h_pos
      have h_pos' : 0 < m.mu ({w} : Set W) :=
        lt_of_le_of_ne (m.nonneg _) (Ne.symm h_pos)
      have hbeliefs : ∀ (χ : Prop' W), m.mu (fun w => χ w : Set W) = 1 → χ w :=
        fun χ hχ => mem_of_mu_singleton_pos m.toFinAddMeasure w _ h_pos' hχ
      obtain ⟨ψ, hψ, hnψ⟩ := hall w
      exact hnψ (revised_entails m ψ φ hψ w hbeliefs hw)
    linarith [mu_eq_zero_of_singletons m.toFinAddMeasure _ hzero]

end Core.Logic.BeliefRevision
