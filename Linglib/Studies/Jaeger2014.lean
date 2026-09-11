import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Linglib.Core.Order.Argmax
import Linglib.Data.Examples.Jaeger2014

/-!
# Jäger (2014): Rationalizable Signaling

This file formalizes [jaeger-2014], the iterated cautious response model of game-theoretic
pragmatics. A semantic game equips a signaling game with contexts, the players' uncertainty about
each other's preferences, an interpretation function and cost-separable sender utilities
(`SemanticGame`). Following Pearce's rationalizability, a cautious response to a set of the
opponent's strategies is a best response to some belief giving every member of the set positive
probability, Definitions 2 and 3; the iterated cautious response sequence, Definition 4, starts
from the credulous receiver, who acts on the literal meaning of each signal, and alternates
cautious responses, the receiver reading an unexpected signal as true under some revised belief.
The pragmatically rationalizable strategies are those recurring arbitrarily late in the sequence,
Definition 5. Theorem 1, `prs_rationalizable`: they are rationalizable in the classical sense,
Definition 6, since the sequence is a deterministic dynamical system on a finite space and so
eventually periodic, its late stages lying inside the recurrence sets that witness
rationalizability. The best responses of Definition 2 reduce to pointwise argmaxes
(`mem_senderBR_iff`, `mem_receiverBR_iff`), the form in which Section 5 computes the examples,
and at a fixed point the recurrence sets are the fixed stage (`prsR_eq_of_fixed`). Example 6,
Horn's division of pragmatic labor, (4): with two synonymous signals, the costlier by one unit,
and a 3:1 prior, the sequence reaches its fixed point at the convention that the cheap form marks
the frequent world and the costly form the rare one (`Horn.division_of_pragmatic_labor`), the
costly form being read as the rare world although, in the sense of Rabin's credibility recast in
Section 7, it is not credible.

## Implementation notes

* Beliefs are functions to `ℝ`; `Δ(M)` is mathlib's `stdSimplex ℝ M`, and the full-support and
  support-restricted variants `int(Δ(M))` and `Δ(P)` are stated locally, the relative interior of
  the simplex having no lightweight mathlib form.
* Examples 1 to 5 and 7 to 10, including the comparison with [franke-2011]'s iterated best
  response in Section 6, are not formalized; Section 5's linguistic examples are rows.

## References

* [jaeger-2014]
* [jaeger-ebert-2009]
* [franke-2011]
-/

namespace Jaeger2014

noncomputable section

/-! ### Beliefs

Probability distributions and full-support ("cautious") distributions,
including versions supported on a given strategy set — Jäger's `Δ(M)` and
`int(Δ(M))`. -/

variable {M : Type*}

/-- Jäger's `Δ(M)` is mathlib's standard simplex, `stdSimplex ℝ M`; the
full-support and support-restricted variants below have no mathlib
counterpart and are stated relative to it. A full-support probability
distribution: Jäger's `int(Δ(M))`. -/
def IsFullDist [Fintype M] (q : M → ℝ) : Prop :=
  (∀ x, 0 < q x) ∧ ∑ x, q x = 1

/-- A distribution supported inside `P`: Jäger's `Δ(P)` for `P ⊆ M`. -/
def IsDistOn [Fintype M] (P : Set M) (q : M → ℝ) : Prop :=
  q ∈ stdSimplex ℝ M ∧ ∀ x ∉ P, q x = 0

/-- A distribution with support exactly `P`: Jäger's `int(Δ(P)))` for
`P ⊆ M` — positive on `P`, zero off it. -/
def IsFullDistOn [Fintype M] (P : Set M) (q : M → ℝ) : Prop :=
  (∀ x ∈ P, 0 < q x) ∧ (∀ x ∉ P, q x = 0) ∧ ∑ x, q x = 1

theorem IsFullDist.mem_stdSimplex [Fintype M] {q : M → ℝ} (h : IsFullDist q) :
    q ∈ stdSimplex ℝ M :=
  ⟨λ x => (h.1 x).le, h.2⟩

/-- A full-support-on-`P` distribution is supported inside any superset. -/
theorem IsFullDistOn.isDistOn [Fintype M] {P P' : Set M} {q : M → ℝ}
    (h : IsFullDistOn P q) (hPP' : P ⊆ P') : IsDistOn P' q :=
  ⟨⟨λ x => (em (x ∈ P)).elim (λ hx => (h.1 x hx).le) (λ hx => (h.2.1 x hx).ge),
    h.2.2⟩,
   λ x hx => h.2.1 x (λ hxP => hx (hPP' hxP))⟩

/-! ### Semantic games -/

/-- A semantic game ([jaeger-2014] §4): contexts `C` (higher-order
uncertainty about preferences), worlds `W`, signals `F`, actions `A`; a
positive prior over worlds; an exogenous interpretation function
(`meaning`); receiver utilities, and cost-separable sender utilities
(`uS c w f a = vS c w a - cost f`). -/
structure SemanticGame (C W F A : Type*) [Fintype W] where
  /-- The receiver's prior probability over worlds (`p*`). -/
  prior : W → ℝ
  /-- All worlds have positive prior probability. -/
  prior_pos : ∀ w, 0 < prior w
  /-- The prior is a probability distribution. -/
  prior_sum : ∑ w, prior w = 1
  /-- The interpretation function `⟦·⟧`: is signal `f` true at world `w`? -/
  meaning : F → W → Prop
  /-- Context/outcome utilities of the sender. -/
  vS : C → W → A → ℝ
  /-- Signalling costs. -/
  cost : F → ℝ
  /-- The receiver's utility function. -/
  uR : C → W → A → ℝ
  [meaningDecidable : ∀ f, DecidablePred (meaning f)]

attribute [instance] SemanticGame.meaningDecidable

namespace SemanticGame

variable {C W F A : Type*} [Fintype C] [Fintype W] [Fintype F] [Fintype A]
  [DecidableEq C] [DecidableEq W] [DecidableEq F]
  (g : SemanticGame C W F A)

/-- The sender's utility function: outcome utility minus signalling cost. -/
def uS (c : C) (w : W) (f : F) (a : A) : ℝ :=
  g.vS c w a - g.cost f

/-- The extension of a signal: the worlds at which it is true. -/
def extension (f : F) : Finset W :=
  Finset.univ.filter (g.meaning f)

/-- Def. 1: the receiver-optimal actions in context `c` when the belief `p`
is updated with the proposition `φ` — the argmax of `p`-expected receiver
utility over `φ`. -/
def optimalActions (c : C) (φ : Finset W) (p : W → ℝ) : Finset A :=
  Finset.univ.argmax (λ a => ∑ w ∈ φ, p w * g.uR c w a)

/-! ### Best responses and cautious responses

Pure sender strategies are `C → W → F`, pure receiver strategies
`C → F → A`. A receiver belief is a distribution over sender strategies
plus a distribution over (sender) contexts; symmetrically for the sender.
Cautious responses (Def. 3, after Pearce) are best responses to *some*
full-support belief. -/

/-- Def. 2 (receiver): `r'` is a best response to the belief `(σ, q)` iff
in every own-context `c` it maximizes expected utility against the sender
strategy distribution `σ`, context distribution `q`, and the prior. -/
def receiverBR (σ : (C → W → F) → ℝ) (q : C → ℝ) : Set (C → F → A) :=
  {r' | ∀ c, r' ∈ Finset.univ.argmax (λ r : C → F → A =>
    ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w)))}

/-- Def. 2 (sender): `s'` is a best response to the belief `(ρ, q)` iff at
every context/world pair it maximizes expected utility against the
receiver strategy distribution `ρ` and context distribution `q`. -/
def senderBR (ρ : (C → F → A) → ℝ) (q : C → ℝ) : Set (C → W → F) :=
  {s' | ∀ c w, s' ∈ Finset.univ.argmax (λ s : C → W → F =>
    ∑ r, ρ r * ∑ c', q c' * g.uS c w (s c w) (r c' (s c w)))}

/-- Def. 3: cautious responses of the sender to a set `R` of receiver
strategies — best responses to some belief with support exactly `R` and
full-support context beliefs. -/
def senderCR (R : Set (C → F → A)) : Set (C → W → F) :=
  {s | ∃ ρ q, IsFullDistOn R ρ ∧ IsFullDist q ∧ s ∈ g.senderBR ρ q}

/-- Def. 3: cautious responses of the receiver to a set `S` of sender
strategies. -/
def receiverCR (S : Set (C → W → F)) : Set (C → F → A) :=
  {r | ∃ σ q, IsFullDistOn S σ ∧ IsFullDist q ∧ r ∈ g.receiverBR σ q}

/-! ### The iterated cautious response sequence -/

/-- A signal is unexpected for a set `S` of sender strategies if no
strategy in `S` ever uses it. -/
def Unexpected (S : Set (C → W → F)) (f : F) : Prop :=
  ∀ s ∈ S, ∀ c w, s c w ≠ f

/-- The receiver side of the ICR sequence (Def. 4). `icrR 0` is the set of
*credulous* strategies — pointwise optimal against the prior updated with
the literal meaning. `icrR (n+1)` consists of the cautious responses to
`icrS n` that moreover interpret unexpected signals as literally true
under *some* consistent belief revision (a full-support prior updated with
the signal's extension). -/
def icrR : ℕ → Set (C → F → A)
  | 0 => {r | ∀ c f, r c f ∈ g.optimalActions c (g.extension f) g.prior}
  | n + 1 =>
    {r ∈ g.receiverCR (g.senderCR (icrR n)) |
      ∀ f, Unexpected (g.senderCR (icrR n)) f →
        ∀ c, ∃ p, IsFullDist p ∧ r c f ∈ g.optimalActions c (g.extension f) p}

/-- The sender side of the ICR sequence (Def. 4): cautious responses to
the receiver's current stage. -/
def icrS (n : ℕ) : Set (C → W → F) :=
  g.senderCR (g.icrR n)

/-- Def. 5: pragmatically rationalizable sender strategies — those
recurring arbitrarily late in the ICR sequence. -/
def prsS : Set (C → W → F) :=
  {s | ∀ n, ∃ m > n, s ∈ g.icrS m}

/-- Def. 5: pragmatically rationalizable receiver strategies. -/
def prsR : Set (C → F → A) :=
  {r | ∀ n, ∃ m > n, r ∈ g.icrR m}

/-- Def. 6 (after Osborne): a strategy pair is rationalizable iff it
belongs to a pair of sets each of whose members is a best response to some
belief supported inside the other set. -/
def IsRationalizable (s : C → W → F) (r : C → F → A) : Prop :=
  ∃ (S : Set (C → W → F)) (R : Set (C → F → A)),
    (∀ s' ∈ S, ∃ ρ q, IsDistOn R ρ ∧ q ∈ stdSimplex ℝ C ∧ s' ∈ g.senderBR ρ q) ∧
    (∀ r' ∈ R, ∃ σ q, IsDistOn S σ ∧ q ∈ stdSimplex ℝ C ∧ r' ∈ g.receiverBR σ q) ∧
    s ∈ S ∧ r ∈ R

/-! ### Theorem 1: pragmatic rationalizability implies rationalizability

The ICR sequence is a deterministic dynamical system on the finite space
of strategy-set pairs, hence eventually periodic; beyond the periodic
threshold every stage lies inside the recurrence sets `prsS`/`prsR`, which
therefore witness rationalizability for every pragmatically rationalizable
pair. -/

private theorem icrR_shift {a b : ℕ} (h : g.icrR a = g.icrR b) (k : ℕ) :
    g.icrR (a + k) = g.icrR (b + k) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    show g.icrR (a + k + 1) = g.icrR (b + k + 1)
    simp only [icrR]
    rw [ih]

/-- The ICR sequence eventually repeats: there are `a < b` with
`icrR a = icrR b`. -/
private theorem icrR_repeats : ∃ a b, a < b ∧ g.icrR a = g.icrR b := by
  obtain ⟨a, b, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite g.icrR
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact ⟨a, b, h, heq⟩
  · exact ⟨b, a, h, heq.symm⟩

/-- Beyond the repeat point the ICR receiver sequence is periodic with
period `b - a`. -/
private theorem icrR_periodic {a b : ℕ} (hab : a < b)
    (heq : g.icrR a = g.icrR b) {n : ℕ} (han : a ≤ n) (t : ℕ) :
    g.icrR n = g.icrR (n + (b - a) * t) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hstep : g.icrR (n + (b - a) * t) = g.icrR (n + (b - a) * t + (b - a)) := by
      have := g.icrR_shift heq ((n + (b - a) * t) - a)
      rwa [Nat.add_sub_cancel' (le_trans han (Nat.le_add_right _ _)),
        show b + (n + (b - a) * t - a) = n + (b - a) * t + (b - a) by omega] at this
    rw [ih, hstep, Nat.mul_succ]
    ring_nf

/-- Arbitrarily late indices along the period. -/
private theorem exists_period_gt {a b : ℕ} (hab : a < b) (n N : ℕ) :
    ∃ t, N < n + (b - a) * t :=
  ⟨N + 1, by have : 1 ≤ b - a := by omega
             nlinarith⟩

/-- Beyond the repeat point, every ICR receiver stage recurs arbitrarily
late, i.e. lies inside `prsR`. -/
private theorem icrR_subset_prsR {a b : ℕ} (hab : a < b)
    (heq : g.icrR a = g.icrR b) {n : ℕ} (han : a ≤ n) :
    g.icrR n ⊆ g.prsR := by
  intro r hr N
  obtain ⟨t, ht⟩ := exists_period_gt hab n N
  exact ⟨n + (b - a) * t, ht, (g.icrR_periodic hab heq han t) ▸ hr⟩

/-- Beyond the repeat point, every ICR sender stage lies inside `prsS`. -/
private theorem icrS_subset_prsS {a b : ℕ} (hab : a < b)
    (heq : g.icrR a = g.icrR b) {n : ℕ} (han : a ≤ n) :
    g.icrS n ⊆ g.prsS := by
  intro s hs N
  obtain ⟨t, ht⟩ := exists_period_gt hab n N
  refine ⟨n + (b - a) * t, ht, ?_⟩
  show s ∈ g.senderCR (g.icrR (n + (b - a) * t))
  rw [← g.icrR_periodic hab heq han t]
  exact hs

/-- **[jaeger-2014], Theorem 1**: pragmatically rationalizable strategy
pairs are rationalizable. The recurrence sets themselves are the witness:
every recurring sender strategy is a cautious (hence best) response to a
belief supported on a late ICR receiver stage, which lies inside `prsR`;
symmetrically for the receiver, whose late stages are cautious responses
to late sender stages inside `prsS`. -/
theorem prs_rationalizable {s : C → W → F} {r : C → F → A}
    (hs : s ∈ g.prsS) (hr : r ∈ g.prsR) :
    g.IsRationalizable s r := by
  obtain ⟨a, b, hab, heq⟩ := g.icrR_repeats
  refine ⟨g.prsS, g.prsR, ?_, ?_, hs, hr⟩
  · -- every recurring sender strategy is a BR to a belief inside prsR
    intro s' hs'
    obtain ⟨m, hm, hs'm⟩ := hs' a
    obtain ⟨ρ, q, hρ, hq, hBR⟩ := hs'm
    exact ⟨ρ, q, hρ.isDistOn (g.icrR_subset_prsR hab heq hm.le),
      hq.mem_stdSimplex, hBR⟩
  · -- every recurring receiver strategy is a BR to a belief inside prsS
    intro r' hr'
    obtain ⟨m, hm, hr'm⟩ := hr' (a + 1)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk : a ≤ k := by omega
    obtain ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩ := hr'm
    exact ⟨σ, q, hσ.isDistOn (g.icrS_subset_prsS hab heq hk),
      hq.mem_stdSimplex, hBR⟩


/-! ### Best-response characterizations

Def. 2's argmaxes range over whole strategy spaces, but the objectives are
additively separable: the sender's depends only on the signal chosen at the
quantified context/world, the receiver's is a sum of per-signal terms
against posterior-weighted world masses. `Finset.mem_argmax_comp_surjective`
and `Finset.mem_argmax_pi_sum` reduce both to pointwise argmaxes — the
form in which the §5 examples are actually computed. -/

/-- The sender's expected utility of sending `f` at `(c, w)` under the
belief `(ρ, q)`. -/
def senderEU (ρ : (C → F → A) → ℝ) (q : C → ℝ) (c : C) (w : W) (f : F) : ℝ :=
  ∑ r, ρ r * ∑ c', q c' * g.uS c w f (r c' f)

/-- Sender best responses, pointwise: `s'` is a best response iff at every
context/world it picks a signal maximizing expected utility. -/
theorem mem_senderBR_iff (ρ : (C → F → A) → ℝ) (q : C → ℝ) (s' : C → W → F) :
    s' ∈ g.senderBR ρ q ↔
      ∀ c w, s' c w ∈ Finset.univ.argmax (g.senderEU ρ q c w) := by
  have he : ∀ (c : C) (w : W), Function.Surjective (λ s : C → W → F => s c w) :=
    λ c w f₀ => ⟨λ _ _ => f₀, rfl⟩
  constructor <;> intro h c w
  · exact (Finset.mem_argmax_comp_surjective (he c w) (g.senderEU ρ q c w)).mp (h c w)
  · exact (Finset.mem_argmax_comp_surjective (he c w) (g.senderEU ρ q c w)).mpr (h c w)

/-- The receiver's per-signal objective: expected utility of playing `a`
on signal `f`, against the belief `(σ, q)` — the prior-weighted utility
restricted to the occasions on which `f` is actually sent. -/
def receiverEU (σ : (C → W → F) → ℝ) (q : C → ℝ) (c : C) (f : F) (a : A) : ℝ :=
  ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * (if s c' w = f then g.uR c w a else 0)

omit [Fintype A] in
private theorem receiverBR_objective_eq (σ : (C → W → F) → ℝ) (q : C → ℝ)
    (c : C) (r : C → F → A) :
    (∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
      ∑ f, g.receiverEU σ q c f (r c f) := by
  unfold receiverEU
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl λ s _ => ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl λ c' _ => ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl λ w _ => ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  exact ((Finset.sum_ite_eq Finset.univ (s c' w)
    (λ f => g.uR c w (r c f))).trans (if_pos (Finset.mem_univ _))).symm

/-- Receiver best responses, pointwise: `r'` is a best response iff at
every context and signal it picks an action maximizing posterior-weighted
expected utility. -/
theorem mem_receiverBR_iff (σ : (C → W → F) → ℝ) (q : C → ℝ) (r' : C → F → A) :
    r' ∈ g.receiverBR σ q ↔
      ∀ c f, r' c f ∈ Finset.univ.argmax (g.receiverEU σ q c f) := by
  have he : ∀ c : C, Function.Surjective (λ r : C → F → A => r c) :=
    λ c ρ₀ => ⟨λ _ => ρ₀, rfl⟩
  have hobj : ∀ c, (λ r : C → F → A =>
      ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
      (λ ρ : F → A => ∑ f, g.receiverEU σ q c f (ρ f)) ∘ (λ r => r c) := by
    intro c; funext r; exact g.receiverBR_objective_eq σ q c r
  constructor <;> intro h
  · intro c f
    have h1 := h c
    rw [show (λ r : C → F → A =>
        ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
        (λ ρ : F → A => ∑ f, g.receiverEU σ q c f (ρ f)) ∘ (λ r => r c)
      from hobj c] at h1
    exact (Finset.mem_argmax_pi_sum _).mp
      ((Finset.mem_argmax_comp_surjective (he c) _).mp h1) f
  · intro c
    rw [show (λ r : C → F → A =>
        ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
        (λ ρ : F → A => ∑ f, g.receiverEU σ q c f (ρ f)) ∘ (λ r => r c)
      from hobj c]
    exact (Finset.mem_argmax_comp_surjective (he c) _).mpr
      ((Finset.mem_argmax_pi_sum _).mpr (h c))

/-! ### Fixed points collapse the recurrence sets -/

private theorem icrR_const_of_fixed {n : ℕ} (hfix : g.icrR (n + 1) = g.icrR n) :
    ∀ k, g.icrR (n + k) = g.icrR n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have : g.icrR (n + k + 1) = g.icrR (n + 1) := by
      simp only [icrR]; rw [ih]
    exact this.trans hfix

/-- At a fixed point of the ICR step, the pragmatically rationalizable
receiver strategies are exactly the fixed stage. -/
theorem prsR_eq_of_fixed {n : ℕ} (hfix : g.icrR (n + 1) = g.icrR n) :
    g.prsR = g.icrR n := by
  ext r
  constructor
  · intro h
    obtain ⟨m, hm, hr⟩ := h n
    obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    rwa [g.icrR_const_of_fixed hfix k] at hr
  · intro h N
    exact ⟨n + (N + 1), by omega, by rw [g.icrR_const_of_fixed hfix (N + 1)]; exact h⟩

/-- At a fixed point of the ICR step, the pragmatically rationalizable
sender strategies are exactly the fixed sender stage. -/
theorem prsS_eq_of_fixed {n : ℕ} (hfix : g.icrR (n + 1) = g.icrR n) :
    g.prsS = g.icrS n := by
  ext s
  constructor
  · intro h
    obtain ⟨m, hm, hs⟩ := h n
    obtain ⟨k, rfl⟩ : ∃ k, m = n + k := ⟨m - n, by omega⟩
    show s ∈ g.senderCR (g.icrR n)
    rw [← g.icrR_const_of_fixed hfix k]
    exact hs
  · intro h N
    refine ⟨n + (N + 1), by omega, ?_⟩
    show s ∈ g.senderCR (g.icrR (n + (N + 1)))
    rw [g.icrR_const_of_fixed hfix (N + 1)]
    exact h

/-! ### Message credibility -/

/-- Rabin's message credibility recast in Section 7: a signal is credible iff at every stage every
sender strategy uses it wherever it is true, `⟦f⟧ ⊆ s⁻¹(f)`. -/
def Credible (f : F) : Prop :=
  ∀ n, ∀ s ∈ g.icrS n, ∀ c w, g.meaning f w → s c w = f

end SemanticGame

end

noncomputable section

/-! ### Beliefs on a singleton and on a pair

A full-support belief on one strategy is its point mass, and on a pair of strategies a mixture
with weights `t` and `1 - t` for some `0 < t < 1`; sums against such beliefs collapse to the
support. -/

section Support

variable {M : Type*} [Fintype M] [DecidableEq M] {a b : M} {ρ : M → ℝ}

/-- The mixture of two point masses with weight `t` on `a`. -/
def mix (a b : M) (t : ℝ) : M → ℝ := λ r => if r = a then t else if r = b then 1 - t else 0

theorem isFullDistOn_singleton_iff : IsFullDistOn {a} ρ ↔ ρ = Pi.single a 1 := by
  constructor
  · rintro ⟨hpos, hzero, hsum⟩
    have h1 : ρ a = 1 := by
      rwa [Finset.sum_eq_single a (λ b _ hb => hzero b hb) (λ h => absurd (Finset.mem_univ _) h)]
        at hsum
    funext r
    by_cases hr : r = a
    · subst hr; simp [h1]
    · simp [hr, hzero r hr]
  · rintro rfl
    refine ⟨λ x hx => ?_, λ x hx => ?_, ?_⟩
    · rw [Set.mem_singleton_iff.1 hx]; simp
    · simp [Set.mem_singleton_iff.not.1 hx]
    · simp

theorem isFullDistOn_pair_iff (hab : a ≠ b) :
    IsFullDistOn {a, b} ρ ↔ ∃ t, 0 < t ∧ t < 1 ∧ ρ = mix a b t := by
  constructor
  · rintro ⟨hpos, hzero, hsum⟩
    have ha := hpos a (by simp)
    have hb := hpos b (by simp)
    rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset M))
      (λ x _ hx => hzero x (by simpa using hx)), Finset.sum_pair hab] at hsum
    refine ⟨ρ a, ha, by linarith, funext λ r => ?_⟩
    simp only [mix]
    split_ifs with h₁ h₂
    · rw [h₁]
    · rw [h₂]; linarith
    · exact hzero r (by simp [h₁, h₂])
  · rintro ⟨t, h0, h1, rfl⟩
    refine ⟨λ x hx => ?_, λ x hx => ?_, ?_⟩
    · rcases hx with rfl | hx
      · simp [mix, h0]
      · rw [Set.mem_singleton_iff.1 hx]; simp [mix, Ne.symm hab]; linarith
    · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      simp [mix, hx.1, hx.2]
    · rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset M))
        (λ x _ hx => by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
                        simp [mix, hx.1, hx.2]),
        Finset.sum_pair hab]
      simp [mix, Ne.symm hab]

theorem sum_mul_single (X : M → ℝ) : ∑ r, (Pi.single a 1 : M → ℝ) r * X r = X a := by
  simp [Pi.single_apply]

theorem sum_mul_mix (hab : a ≠ b) (t : ℝ) (X : M → ℝ) :
    ∑ r, mix a b t r * X r = t * X a + (1 - t) * X b := by
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset M))
    (λ x _ hx => by simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
                    simp [mix, hx.1, hx.2]),
    Finset.sum_pair hab]
  simp [mix, Ne.symm hab]

end Support

/-- Over a single context the only full-support belief is certainty. -/
theorem isFullDist_unit_iff {q : Unit → ℝ} : IsFullDist q ↔ q = λ _ => 1 := by
  constructor
  · rintro ⟨-, h⟩; funext u; cases u; simpa using h
  · rintro rfl; exact ⟨λ _ => one_pos, by simp⟩

namespace SemanticGame

variable {C W F A : Type*} [Fintype C] [Fintype W] [Fintype F] [Fintype A]
  [DecidableEq C] [DecidableEq W] [DecidableEq F] (g : SemanticGame C W F A)

/-- Cautious responses of the sender, pointwise. -/
theorem mem_senderCR_iff {R : Set (C → F → A)} {s : C → W → F} :
    s ∈ g.senderCR R ↔ ∃ ρ q, IsFullDistOn R ρ ∧ IsFullDist q ∧
      ∀ c w, s c w ∈ Finset.univ.argmax (g.senderEU ρ q c w) := by
  simp only [senderCR, Set.mem_ofPred_eq, mem_senderBR_iff]

/-- Cautious responses of the receiver, pointwise. -/
theorem mem_receiverCR_iff {S : Set (C → W → F)} {r : C → F → A} :
    r ∈ g.receiverCR S ↔ ∃ σ q, IsFullDistOn S σ ∧ IsFullDist q ∧
      ∀ c f, r c f ∈ Finset.univ.argmax (g.receiverEU σ q c f) := by
  simp only [receiverCR, Set.mem_ofPred_eq, mem_receiverBR_iff]

omit [DecidableEq W] in
/-- The sender's expected utility against a single receiver strategy. -/
theorem senderEU_single [DecidableEq A] (r₀ : C → F → A) (q : C → ℝ) (c : C) (w : W) (f : F) :
    g.senderEU (Pi.single r₀ 1) q c w f = ∑ c', q c' * g.uS c w f (r₀ c' f) :=
  sum_mul_single _

omit [DecidableEq W] in
/-- The sender's expected utility against a mixture of two receiver strategies. -/
theorem senderEU_mix [DecidableEq A] {r₀ r₁ : C → F → A} (h : r₀ ≠ r₁) (t : ℝ) (q : C → ℝ)
    (c : C) (w : W) (f : F) :
    g.senderEU (mix r₀ r₁ t) q c w f =
      t * ∑ c', q c' * g.uS c w f (r₀ c' f) + (1 - t) * ∑ c', q c' * g.uS c w f (r₁ c' f) :=
  sum_mul_mix h t _

omit [Fintype A] in
/-- The receiver's expected utility against a single sender strategy. -/
theorem receiverEU_single (s₀ : C → W → F) (q : C → ℝ) (c : C) (f : F) (a : A) :
    g.receiverEU (Pi.single s₀ 1) q c f a =
      ∑ c', q c' * ∑ w, g.prior w * (if s₀ c' w = f then g.uR c w a else 0) :=
  sum_mul_single _

omit [Fintype A] in
/-- The receiver's expected utility against a mixture of two sender strategies. -/
theorem receiverEU_mix {s₀ s₁ : C → W → F} (h : s₀ ≠ s₁) (t : ℝ) (q : C → ℝ) (c : C) (f : F)
    (a : A) :
    g.receiverEU (mix s₀ s₁ t) q c f a =
      t * ∑ c', q c' * ∑ w, g.prior w * (if s₀ c' w = f then g.uR c w a else 0) +
        (1 - t) * ∑ c', q c' * ∑ w, g.prior w * (if s₁ c' w = f then g.uR c w a else 0) :=
  sum_mul_mix h t _

end SemanticGame

/-! ### Horn's division of pragmatic labor (Section 5, Example 6)

Two worlds, the first three times as likely as the second, two synonymous signals, both
tautologies, the second costing one unit more, matching utilities of 5, one context. The
sequence runs `R₀ = {0}`, `S₀ = {0}`, `R₁ = {r | r 0 = 0}`, `S₁ = {s | s 0 = 0}`,
`R₂ = S₂ = {id}` and stays there; each stage is an argmax over `Fin 2` against a belief on the
one or two strategies of the previous stage. -/

namespace Horn

open Data.Examples

/-- Example 6's semantic game, Table 10. -/
def game : SemanticGame Unit (Fin 2) (Fin 2) (Fin 2) where
  prior := λ w => if w = 0 then 3/4 else 1/4
  prior_pos := by intro w; fin_cases w <;> norm_num
  prior_sum := by rw [Fin.sum_univ_two]; norm_num
  meaning := λ _ _ => True
  vS := λ _ w a => if w = a then 5 else 0
  cost := λ f => if f = 0 then 0 else 1
  uR := λ _ w a => if w = a then 5 else 0

/-- The constant strategy and the identity: the only strategies the sequence visits. -/
private theorem zero_ne_id : (λ _ _ => 0 : Unit → Fin 2 → Fin 2) ≠ (λ _ x => x) := λ h =>
  absurd (congrFun (congrFun h ()) 1) (by decide)

/-- The strategies fixing coordinate `0` are the constant and the identity. -/
private theorem pair_eq :
    {h : Unit → Fin 2 → Fin 2 | h () 0 = 0} = {(λ _ _ => 0), (λ _ x => x)} := by
  ext h
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h0
    rcases (by omega : h () 1 = 0 ∨ h () 1 = 1) with h1 | h1
    · left; funext c x; cases c; fin_cases x <;> assumption
    · right; funext c x; cases c; fin_cases x <;> simp_all
  · rintro (rfl | rfl) <;> rfl

/-- An argmax over `Fin 2` is the index of the strictly larger value, or everything on a tie. -/
private theorem argmax_fin2_zero {V : Fin 2 → ℝ} (h : V 1 < V 0) :
    Finset.univ.argmax V = {0} := by
  ext x; fin_cases x <;> simp [Finset.mem_argmax, Fin.forall_fin_two] <;> linarith

private theorem argmax_fin2_one {V : Fin 2 → ℝ} (h : V 0 < V 1) :
    Finset.univ.argmax V = {1} := by
  ext x; fin_cases x <;> simp [Finset.mem_argmax, Fin.forall_fin_two] <;> linarith

private theorem argmax_fin2_univ {V : Fin 2 → ℝ} (h : V 0 = V 1) :
    Finset.univ.argmax V = Finset.univ := by
  ext x; fin_cases x <;> simp [Finset.mem_argmax, Fin.forall_fin_two, h.le, h.ge]

/-- The stage-`n + 1` receiver set, unfolded. -/
private theorem icrR_succ (n : ℕ) :
    game.icrR (n + 1) = {r ∈ game.receiverCR (game.senderCR (game.icrR n)) |
      ∀ f, SemanticGame.Unexpected (game.senderCR (game.icrR n)) f →
        ∀ c, ∃ p, IsFullDist p ∧ r c f ∈ game.optimalActions c (game.extension f) p} :=
  rfl

private theorem extension_eq (f : Fin 2) : game.extension f = Finset.univ := by
  simp [SemanticGame.extension, game]

/-- The credulous stage: both signals are tautologies, so the receiver plays the frequent
world's action on either. -/
private theorem icrR_zero : game.icrR 0 = {λ _ _ => 0} := by
  have h : ∀ (c : Unit) (f : Fin 2),
      game.optimalActions c (game.extension f) game.prior = {0} := λ c f => by
    rw [SemanticGame.optimalActions, extension_eq]
    exact argmax_fin2_zero (by simp [game]; norm_num)
  ext r
  simp only [SemanticGame.icrR, Set.mem_ofPred_eq, Set.mem_singleton_iff, h,
    Finset.mem_singleton]
  exact ⟨λ hr => funext λ c => funext (hr c), λ hr c f => by subst hr; rfl⟩

/-- `S₀`: against the credulous receiver the cheap form is uniquely optimal at both worlds. -/
private theorem icrS_zero : game.icrS 0 = {λ _ _ => 0} := by
  have e : ∀ w : Fin 2,
      Finset.univ.argmax (game.senderEU (Pi.single (λ _ _ => 0) 1) (λ _ => 1) () w) = {0} :=
    λ w => argmax_fin2_zero (by
      fin_cases w <;> simp [SemanticGame.senderEU_single, game, SemanticGame.uS])
  ext s
  rw [SemanticGame.icrS, icrR_zero, SemanticGame.mem_senderCR_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, q, hρ, hq, hBR⟩
    rw [isFullDistOn_singleton_iff] at hρ
    rw [isFullDist_unit_iff] at hq
    subst hρ hq
    funext c w; cases c
    simpa [e] using hBR () w
  · rintro rfl
    exact ⟨_, _, isFullDistOn_singleton_iff.2 rfl, isFullDist_unit_iff.2 rfl,
      λ c w => by cases c; simp [e]⟩

/-- Either action is optimal on a tautologous signal under a belief skewed to its world. -/
private theorem optimalActions_witness (x : Fin 2) :
    ∃ p, IsFullDist p ∧ x ∈ game.optimalActions () Finset.univ p := by
  refine ⟨λ w => if w = x then 2/3 else 1/3,
    ⟨λ w => by dsimp only; split_ifs <;> norm_num, by
      rw [Fin.sum_univ_two]; fin_cases x <;> simp <;> norm_num⟩, ?_⟩
  rw [SemanticGame.optimalActions]
  fin_cases x
  · rw [argmax_fin2_zero (by simp [game]; norm_num)]; simp
  · rw [argmax_fin2_one (by simp [game]; norm_num)]; simp

/-- `R₁`: the cheap form, the only one sent, is read as the frequent world; the costly form is
unexpected, so any action survives on it and some skewed belief makes it optimal. -/
private theorem icrR_one : game.icrR 1 = {r | r () 0 = 0} := by
  have e0 : Finset.univ.argmax
      (game.receiverEU (Pi.single (λ _ _ => 0) 1) (λ _ => 1) () 0) = {0} :=
    argmax_fin2_zero (by simp [SemanticGame.receiverEU_single, game]; norm_num)
  have e1 : Finset.univ.argmax
      (game.receiverEU (Pi.single (λ _ _ => 0) 1) (λ _ => 1) () 1) = Finset.univ :=
    argmax_fin2_univ (by simp [SemanticGame.receiverEU_single, game])
  ext r
  rw [icrR_succ, show game.senderCR (game.icrR 0) = {λ _ _ => 0} from icrS_zero, Set.mem_ofPred_eq,
    Set.mem_ofPred_eq, SemanticGame.mem_receiverCR_iff]
  constructor
  · rintro ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩
    rw [isFullDistOn_singleton_iff] at hσ
    rw [isFullDist_unit_iff] at hq
    subst hσ hq
    simpa [e0] using hBR () 0
  · intro hr
    refine ⟨⟨_, _, isFullDistOn_singleton_iff.2 rfl, isFullDist_unit_iff.2 rfl,
      λ c => ?_⟩, λ f _ c => ?_⟩
    · cases c; rw [Fin.forall_fin_two]
      exact ⟨by rw [e0]; simp [hr], by rw [e1]; simp⟩
    · cases c; rw [extension_eq]; exact optimalActions_witness _

/-- `S₁`: against a mixture of the two receivers the frequent world still takes the cheap form,
while the rare world takes the costly form exactly when the literal receiver weighs at least
`1/5`, so both signals survive there. -/
private theorem icrS_one : game.icrS 1 = {s | s () 0 = 0} := by
  have e0 : ∀ t : ℝ, 0 < t → t < 1 → Finset.univ.argmax
      (game.senderEU (mix (λ _ _ => 0) (λ _ x => x) t) (λ _ => 1) () 0) = {0} :=
    λ t _ _ => argmax_fin2_zero (by
      simp only [game.senderEU_mix zero_ne_id]; simp [game, SemanticGame.uS]; linarith)
  have e1 : ∀ t : ℝ, t < 4/5 → Finset.univ.argmax
      (game.senderEU (mix (λ _ _ => 0) (λ _ x => x) t) (λ _ => 1) () 1) = {1} :=
    λ t h => argmax_fin2_one (by
      simp only [game.senderEU_mix zero_ne_id]; simp [game, SemanticGame.uS]; linarith)
  have e1' : ∀ t : ℝ, 4/5 < t → Finset.univ.argmax
      (game.senderEU (mix (λ _ _ => 0) (λ _ x => x) t) (λ _ => 1) () 1) = {0} :=
    λ t h => argmax_fin2_zero (by
      simp only [game.senderEU_mix zero_ne_id]; simp [game, SemanticGame.uS]; linarith)
  ext s
  rw [SemanticGame.icrS, icrR_one.trans pair_eq, SemanticGame.mem_senderCR_iff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ρ, q, hρ, hq, hBR⟩
    rw [isFullDistOn_pair_iff zero_ne_id] at hρ
    rw [isFullDist_unit_iff] at hq
    obtain ⟨t, h0, h1, rfl⟩ := hρ
    subst hq
    simpa [e0 t h0 h1] using hBR () 0
  · intro hs
    rcases (by omega : s () 1 = 0 ∨ s () 1 = 1) with h1 | h1
    · refine ⟨mix _ _ (9/10), _, (isFullDistOn_pair_iff zero_ne_id).2 ⟨9/10, by norm_num,
        by norm_num, rfl⟩, isFullDist_unit_iff.2 rfl, λ c => ?_⟩
      cases c; rw [Fin.forall_fin_two]
      exact ⟨by rw [e0 (9/10) (by norm_num) (by norm_num)]; simp [hs],
        by rw [e1' (9/10) (by norm_num)]; simp [h1]⟩
    · refine ⟨mix _ _ (1/2), _, (isFullDistOn_pair_iff zero_ne_id).2 ⟨1/2, by norm_num,
        by norm_num, rfl⟩, isFullDist_unit_iff.2 rfl, λ c => ?_⟩
      cases c; rw [Fin.forall_fin_two]
      exact ⟨by rw [e0 (1/2) (by norm_num) (by norm_num)]; simp [hs],
        by rw [e1 (1/2) (by norm_num)]; simp [h1]⟩

/-- `R₂`: once the sender separates the worlds, each form is read literally, and no signal is
unexpected. -/
private theorem icrR_two : game.icrR 2 = {λ _ f => f} := by
  have e0 : ∀ t : ℝ, t < 1 → Finset.univ.argmax
      (game.receiverEU (mix (λ _ _ => 0) (λ _ x => x) t) (λ _ => 1) () 0) = {0} :=
    λ t h => argmax_fin2_zero (by
      simp only [game.receiverEU_mix zero_ne_id]; simp [game]; linarith)
  have e1 : ∀ t : ℝ, t < 1 → Finset.univ.argmax
      (game.receiverEU (mix (λ _ _ => 0) (λ _ x => x) t) (λ _ => 1) () 1) = {1} :=
    λ t h => argmax_fin2_one (by
      simp only [game.receiverEU_mix zero_ne_id]; simp [game]; linarith)
  ext r
  rw [icrR_succ, show game.senderCR (game.icrR 1) = {(λ _ _ => 0), (λ _ x => x)} from
    icrS_one.trans pair_eq, Set.mem_ofPred_eq, SemanticGame.mem_receiverCR_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩
    rw [isFullDistOn_pair_iff zero_ne_id] at hσ
    rw [isFullDist_unit_iff] at hq
    obtain ⟨t, -, h1, rfl⟩ := hσ
    subst hq
    funext c f; cases c; revert f; rw [Fin.forall_fin_two]
    exact ⟨by simpa [e0 t h1] using hBR () 0, by simpa [e1 t h1] using hBR () 1⟩
  · rintro rfl
    refine ⟨⟨mix _ _ (1/2), _, (isFullDistOn_pair_iff zero_ne_id).2 ⟨1/2, by norm_num,
      by norm_num, rfl⟩, isFullDist_unit_iff.2 rfl, λ c => ?_⟩, λ f hf c => ?_⟩
    · cases c; rw [Fin.forall_fin_two]
      exact ⟨by rw [e0 (1/2) (by norm_num)]; simp, by rw [e1 (1/2) (by norm_num)]; simp⟩
    · exact absurd rfl (hf (λ _ x => x) (Set.mem_insert_of_mem _ rfl) () f)

/-- `S₂`: against the literal receiver the sender matches signal to world. -/
private theorem icrS_two : game.icrS 2 = {λ _ w => w} := by
  have e : ∀ w : Fin 2,
      Finset.univ.argmax (game.senderEU (Pi.single (λ _ x => x) 1) (λ _ => 1) () w) = {w} := by
    rw [Fin.forall_fin_two]
    exact ⟨argmax_fin2_zero (by
        simp [SemanticGame.senderEU_single, game, SemanticGame.uS]; norm_num),
      argmax_fin2_one (by simp [SemanticGame.senderEU_single, game, SemanticGame.uS])⟩
  ext s
  rw [SemanticGame.icrS, icrR_two, SemanticGame.mem_senderCR_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, q, hρ, hq, hBR⟩
    rw [isFullDistOn_singleton_iff] at hρ
    rw [isFullDist_unit_iff] at hq
    subst hρ hq
    funext c w; cases c
    simpa [e] using hBR () w
  · rintro rfl
    exact ⟨_, _, isFullDistOn_singleton_iff.2 rfl, isFullDist_unit_iff.2 rfl,
      λ c w => by cases c; simp [e]⟩

/-- `R₃ = R₂`: the separating sender is stable. -/
private theorem icrR_three : game.icrR 3 = game.icrR 2 := by
  have e : ∀ f : Fin 2,
      Finset.univ.argmax (game.receiverEU (Pi.single (λ _ x => x) 1) (λ _ => 1) () f) = {f} := by
    rw [Fin.forall_fin_two]
    exact ⟨argmax_fin2_zero (by simp [SemanticGame.receiverEU_single, game]),
      argmax_fin2_one (by simp [SemanticGame.receiverEU_single, game])⟩
  rw [icrR_two]
  ext r
  rw [icrR_succ, show game.senderCR (game.icrR 2) = {λ _ w => w} from icrS_two, Set.mem_ofPred_eq,
    SemanticGame.mem_receiverCR_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩
    rw [isFullDistOn_singleton_iff] at hσ
    rw [isFullDist_unit_iff] at hq
    subst hσ hq
    funext c f; cases c
    simpa [e] using hBR () f
  · rintro rfl
    refine ⟨⟨_, _, isFullDistOn_singleton_iff.2 rfl, isFullDist_unit_iff.2 rfl,
      λ c f => by cases c; simp [e]⟩, λ f hf c => ?_⟩
    exact absurd rfl (hf (λ _ w => w) rfl () f)

/-- Horn's division of pragmatic labor, Example 6: the pragmatically rationalizable strategies
are the convention on which the cheap form marks the frequent world and the costly form the rare
one, the identity strategies on both sides. -/
theorem division_of_pragmatic_labor :
    game.prsS = {λ _ w => w} ∧ game.prsR = {λ _ f => f} :=
  ⟨(game.prsS_eq_of_fixed icrR_three).trans icrS_two,
    (game.prsR_eq_of_fixed icrR_three).trans icrR_two⟩

/-- The costly form is not credible: at the stage `S₁` the sender may still use the cheap form at
the rare world, where the costly form is true; pragmatic rationalizability nevertheless fixes its
reading. -/
theorem not_credible_costly : ¬ game.Credible 1 :=
  λ h => absurd (h 1 (λ _ _ => 0) (by rw [icrS_one]; rfl) () 1 trivial) (by decide)

/-- A row of (4): the signal of Example 6 the sentence realizes and the world it is read as. -/
structure Row where
  signal : Fin 2
  world : Fin 2
  deriving DecidableEq

/-- A row from the paper's features. -/
def Row.ofExample (e : LinguisticExample) : Option Row := do
  let signal : Fin 2 ← match e.feature? "signal" with
    | some "f" => some 0
    | some "f'" => some 1
    | _ => none
  let world : Fin 2 ← match e.feature? "world" with
    | some "w1" => some 0
    | some "w2" => some 1
    | _ => none
  some ⟨signal, world⟩

/-- The two synonyms of (4). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Every pragmatically rationalizable receiver reads each form of (4) as the world the paper
reports: the regular stop for the cheap form, the abnormal one for the costly form. -/
theorem readings_of_4 : ∀ r ∈ rows, ∀ ρ ∈ game.prsR, ρ () r.signal = r.world := by
  intro r hr ρ hρ
  rw [division_of_pragmatic_labor.2, Set.mem_singleton_iff] at hρ
  subst hρ
  revert r; decide

end Horn

end

end Jaeger2014
