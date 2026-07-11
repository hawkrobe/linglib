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

/-!
# Jäger 2014: Rationalizable Signaling

[jaeger-2014]'s iterated cautious response (ICR) model of game-theoretic
pragmatics — the journal-mature version of [jaeger-ebert-2009]'s pragmatic
rationalizability. A *semantic game* equips a signaling game with contexts
(higher-order uncertainty about preferences), an exogenous interpretation
function, and cost-separable sender utilities. Rational interlocutors
iterate *cautious responses* (best responses to some full-support belief,
following Pearce's rationalizability program) starting from the credulous
receiver; the *pragmatically rationalizable strategies* are those recurring
arbitrarily late in the iteration.

Main formalized results:
- `SemanticGame`, `optimalActions` (Def. 1, via `Finset.argmax`),
  `senderBR`/`receiverBR` (Def. 2), `senderCR`/`receiverCR` (Def. 3),
  the ICR sequence `icrR`/`icrS` (Def. 4), `prsS`/`prsR` (Def. 5),
  `IsRationalizable` (Def. 6).
- `prs_rationalizable` (**the paper's Theorem 1**): pragmatically
  rationalizable strategy pairs are rationalizable in the classical sense.
  The proof follows the paper — the ICR sequence is deterministic on a
  finite space, hence eventually periodic; beyond the periodic threshold
  every ICR stage lies inside the recurrence sets, so the recurrence sets
  themselves witness rationalizability.

- Best-response *characterizations*: `mem_senderBR_iff` and
  `mem_receiverBR_iff` reduce the function-space argmaxes of Def. 2 to
  pointwise argmaxes (per context/world for the sender; per context/signal
  against posterior-weighted masses for the receiver), via
  `Finset.mem_argmax_comp_surjective` and `Finset.mem_argmax_pi_sum`.
- `prsS_eq_of_fixed`/`prsR_eq_of_fixed`: at a fixed point of the ICR step
  the recurrence sets collapse to the fixed stage.
- `Credible` — Rabin-style message credibility (§4): a signal is credible
  iff all pragmatically rationalizable senders use it literally.
- **`division_of_pragmatic_labor`** (§5, Example 6): in the two-synonyms
  game with a costly marked form and a 3:1 prior, the pragmatically
  rationalizable strategies are exactly the Horn convention — the cheap
  form marks the frequent world and the costly form the rare one (both
  PRS sets are the identity strategies) — and both signals are credible.

The comparison with [franke-2011]'s IBR model (the paper's §6: Franke's
games are the type-matching specialization, and the models differ exactly
in belief selection — uniform via the Principle of Insufficient Reason
vs. all full-support beliefs) is a planned follow-up, along with the
remaining §5 examples.
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
  ⟨fun x => (h.1 x).le, h.2⟩

/-- A full-support-on-`P` distribution is supported inside any superset. -/
theorem IsFullDistOn.isDistOn [Fintype M] {P P' : Set M} {q : M → ℝ}
    (h : IsFullDistOn P q) (hPP' : P ⊆ P') : IsDistOn P' q :=
  ⟨⟨fun x => (em (x ∈ P)).elim (fun hx => (h.1 x hx).le) (fun hx => (h.2.1 x hx).ge),
    h.2.2⟩,
   fun x hx => h.2.1 x (fun hxP => hx (hPP' hxP))⟩

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
  Finset.univ.argmax (fun a => ∑ w ∈ φ, p w * g.uR c w a)

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
  {r' | ∀ c, r' ∈ Finset.univ.argmax (fun r : C → F → A =>
    ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w)))}

/-- Def. 2 (sender): `s'` is a best response to the belief `(ρ, q)` iff at
every context/world pair it maximizes expected utility against the
receiver strategy distribution `ρ` and context distribution `q`. -/
def senderBR (ρ : (C → F → A) → ℝ) (q : C → ℝ) : Set (C → W → F) :=
  {s' | ∀ c w, s' ∈ Finset.univ.argmax (fun s : C → W → F =>
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
  have he : ∀ (c : C) (w : W), Function.Surjective (fun s : C → W → F => s c w) :=
    fun c w f₀ => ⟨fun _ _ => f₀, rfl⟩
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
  refine Finset.sum_congr rfl fun s _ => ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  conv_rhs => rw [← Finset.mul_sum]
  congr 1
  exact ((Finset.sum_ite_eq Finset.univ (s c' w)
    (fun f => g.uR c w (r c f))).trans (if_pos (Finset.mem_univ _))).symm

/-- Receiver best responses, pointwise: `r'` is a best response iff at
every context and signal it picks an action maximizing posterior-weighted
expected utility. -/
theorem mem_receiverBR_iff (σ : (C → W → F) → ℝ) (q : C → ℝ) (r' : C → F → A) :
    r' ∈ g.receiverBR σ q ↔
      ∀ c f, r' c f ∈ Finset.univ.argmax (g.receiverEU σ q c f) := by
  have he : ∀ c : C, Function.Surjective (fun r : C → F → A => r c) :=
    fun c ρ₀ => ⟨fun _ => ρ₀, rfl⟩
  have hobj : ∀ c, (fun r : C → F → A =>
      ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
      (fun ρ : F → A => ∑ f, g.receiverEU σ q c f (ρ f)) ∘ (fun r => r c) := by
    intro c; funext r; exact g.receiverBR_objective_eq σ q c r
  constructor <;> intro h
  · intro c f
    have h1 := h c
    rw [show (fun r : C → F → A =>
        ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
        (fun ρ : F → A => ∑ f, g.receiverEU σ q c f (ρ f)) ∘ (fun r => r c)
      from hobj c] at h1
    exact (Finset.mem_argmax_pi_sum _).mp
      ((Finset.mem_argmax_comp_surjective (he c) _).mp h1) f
  · intro c
    rw [show (fun r : C → F → A =>
        ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w))) =
        (fun ρ : F → A => ∑ f, g.receiverEU σ q c f (ρ f)) ∘ (fun r => r c)
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

/-- Rabin-style message credibility ([jaeger-2014] §4): a signal is
credible iff every pragmatically rationalizable sender strategy uses it
according to its literal meaning. -/
def Credible (f : F) : Prop :=
  ∀ s ∈ g.prsS, ∀ c w, s c w = f → g.meaning f w

end SemanticGame

end

noncomputable section

/-! ### Support-restricted belief helpers -/

section BeliefHelpers

variable {M : Type*} [Fintype M]

theorem IsFullDistOn.singleton_eq_one {r₀ : M} {ρ : M → ℝ}
    (h : IsFullDistOn {r₀} ρ) : ρ r₀ = 1 := by
  have hsum := h.2.2
  rwa [Finset.sum_eq_single r₀ (fun b _ hb => h.2.1 b (by simp [hb]))
    (fun hb => absurd (Finset.mem_univ _) hb)] at hsum

/-- A sum against a belief supported on a single strategy collapses to the
value at that strategy. -/
theorem sum_mul_of_fullDistOn_singleton {r₀ : M} {ρ : M → ℝ}
    (h : IsFullDistOn {r₀} ρ) (X : M → ℝ) :
    ∑ r, ρ r * X r = X r₀ := by
  rw [Finset.sum_eq_single r₀ (fun b _ hb => by rw [h.2.1 b (by simp [hb]), zero_mul])
    (fun hb => absurd (Finset.mem_univ _) hb), h.singleton_eq_one, one_mul]

/-- A sum against a belief supported on a pair collapses to the two terms. -/
theorem sum_mul_of_fullDistOn_pair [DecidableEq M] {a b : M} (hab : a ≠ b)
    {ρ : M → ℝ} (h : IsFullDistOn {a, b} ρ) (X : M → ℝ) :
    ∑ r, ρ r * X r = ρ a * X a + ρ b * X b :=
  ((Finset.sum_subset (Finset.subset_univ _) fun x _ hx => by
    rw [h.2.1 x (by simpa using hx), zero_mul]).symm).trans
    (Finset.sum_pair hab)

/-- The pair of weights of a full-support belief on a pair sums to 1, with
both weights positive. -/
theorem IsFullDistOn.pair_props [DecidableEq M] {a b : M} (hab : a ≠ b)
    {ρ : M → ℝ} (h : IsFullDistOn {a, b} ρ) :
    0 < ρ a ∧ 0 < ρ b ∧ ρ a + ρ b = 1 := by
  refine ⟨h.1 a (by simp), h.1 b (by simp), ?_⟩
  have hsum := h.2.2
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset M))
    (fun x _ hx => h.2.1 x (by simpa using hx)), Finset.sum_pair hab] at hsum
  exact hsum

/-- The point mass on `r₀` has full support on `{r₀}`. -/
theorem isFullDistOn_pointMass [DecidableEq M] (r₀ : M) :
    IsFullDistOn {r₀} (fun r => if r = r₀ then (1 : ℝ) else 0) :=
  ⟨fun x hx => by simp [Set.mem_singleton_iff.mp hx],
   fun x hx => by simp [Set.mem_singleton_iff] at hx; simp [hx],
   by rw [Finset.sum_ite_eq' Finset.univ r₀ fun _ => (1 : ℝ)]
      exact if_pos (Finset.mem_univ _)⟩

/-- The uniform belief on a pair has full support on it. -/
theorem isFullDistOn_pairUniform [DecidableEq M] {a b : M} (hab : a ≠ b) :
    IsFullDistOn {a, b}
      (fun r => if r = a then (1 : ℝ)/2 else if r = b then 1/2 else 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · dsimp only
    rcases hx with rfl | hx
    · norm_num
    · rw [if_neg (by rintro rfl; exact hab (Set.mem_singleton_iff.mp hx)),
        if_pos (Set.mem_singleton_iff.mp hx)]
      norm_num
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    dsimp only
    rw [if_neg hx.1, if_neg hx.2]
  · rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset M)) (fun x _ hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rw [if_neg hx.1, if_neg hx.2]), Finset.sum_pair hab]
    rw [if_pos rfl, if_neg (Ne.symm hab), if_pos rfl]
    norm_num

/-- A weighted belief on a pair, with weight `t` on `a` and `1 - t` on `b`,
has full support on the pair whenever `0 < t < 1`. -/
theorem isFullDistOn_pairWeighted [DecidableEq M] {a b : M} (hab : a ≠ b)
    {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    IsFullDistOn {a, b}
      (fun r => if r = a then t else if r = b then 1 - t else 0) := by
  refine ⟨fun x hx => ?_, fun x hx => ?_, ?_⟩
  · dsimp only
    rcases hx with rfl | hx
    · rw [if_pos rfl]; exact h0
    · rw [if_neg (by rintro rfl; exact hab (Set.mem_singleton_iff.mp hx)),
        if_pos (Set.mem_singleton_iff.mp hx)]
      linarith
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
    dsimp only
    rw [if_neg hx.1, if_neg hx.2]
  · rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset M)) (fun x _ hx => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      rw [if_neg hx.1, if_neg hx.2]), Finset.sum_pair hab]
    rw [if_pos rfl, if_neg (Ne.symm hab), if_pos rfl]
    ring

omit [Fintype M] in
/-- The weight of a `isFullDistOn_pairWeighted` belief on its second point. -/
theorem pairWeighted_apply_right [DecidableEq M] {a b : M} (hab : a ≠ b) {t : ℝ} :
    (if b = a then t else if b = b then 1 - t else 0) = 1 - t := by
  rw [if_neg (Ne.symm hab), if_pos rfl]

/-- The constant-one function is a full-support distribution over `Unit`. -/
theorem isFullDist_unitOne : IsFullDist (fun _ : Unit => (1 : ℝ)) :=
  ⟨fun _ => one_pos, by simp⟩

theorem IsFullDist.unit_eq_one {q : Unit → ℝ} (h : IsFullDist q) : q () = 1 := by
  have := h.2
  simpa using this

end BeliefHelpers

/-! ### Horn's division of pragmatic labor ([jaeger-2014] §5, Example 6)

Two worlds (world `0` frequent with prior `3/4`, world `1` rare), two
semantically *equivalent* signals (both tautologies), with signal `1`
costlier by one util; matching utilities scaled by 5; a single context.
The ICR trace R₀ … S₂ reaches a fixed point at the Horn convention: the
cheap form marks the frequent world, the costly form the rare one — both
PRS sets are the identity strategies. -/

namespace Horn

/-- Example 6's semantic game. -/
def game : SemanticGame Unit (Fin 2) (Fin 2) (Fin 2) where
  prior := fun w => if w = 0 then 3/4 else 1/4
  prior_pos := by intro w; fin_cases w <;> norm_num
  prior_sum := by rw [Fin.sum_univ_two]; norm_num
  meaning := fun _ _ => True
  vS := fun _ w a => if w = a then 5 else 0
  cost := fun f => if f = 0 then 0 else 1
  uR := fun _ w a => if w = a then 5 else 0

/-- The credulous stage: both signals are tautologies, so the receiver
answers with the a-priori most likely world's action. -/
private theorem icrR_zero : game.icrR 0 = {fun _ _ => 0} := by
  have hopt : ∀ (c : Unit) (f : Fin 2),
      game.optimalActions c (game.extension f) game.prior = {0} := by
    intro c f
    ext a
    simp only [SemanticGame.optimalActions, SemanticGame.extension,
      Finset.mem_argmax, Finset.mem_univ, true_and, true_implies,
      Finset.mem_singleton]
    rw [show (Finset.univ.filter fun w => game.meaning f w) = Finset.univ from by
      simp [game]]
    constructor
    · intro h
      fin_cases a
      · rfl
      · exfalso
        have h0 := h 0
        rw [Fin.sum_univ_two, Fin.sum_univ_two] at h0
        simp only [game] at h0
        norm_num at h0
    · rintro rfl b
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      fin_cases b <;> simp only [game] <;> norm_num
  ext r
  simp only [SemanticGame.icrR, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    funext c f
    have := h c f
    rw [hopt] at this
    simpa using this
  · rintro rfl c f
    rw [hopt]
    exact Finset.mem_singleton_self _

/-! ### Evaluating the ICR trace

Both signals are tautologous, the context is trivial, and only two
strategies ever occur — `fun _ _ => 0` and `fun _ x => x` — so every stage
reduces to a pair of argmaxes over `Fin 2` against a belief whose support
is a singleton or that pair. -/

/-- Both signals mean `True`, so every signal's extension is all worlds. -/
private theorem extension_eq (f : Fin 2) : game.extension f = Finset.univ := by
  simp [SemanticGame.extension, game]

/-- With a trivial context, the sender's expected utility collapses to the
belief-weighted receiver response. -/
private theorem senderEU_eq {ρ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hq : IsFullDist q) (w f : Fin 2) :
    game.senderEU ρ q () w f = ∑ r, ρ r * game.uS () w f (r () f) := by
  simp only [SemanticGame.senderEU]
  exact Finset.sum_congr rfl fun r _ => by simp [hq.unit_eq_one]

/-- With a trivial context, the receiver's per-signal expected utility
collapses to the belief-weighted prior mass. -/
private theorem receiverEU_eq {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hq : IsFullDist q) (f a : Fin 2) :
    game.receiverEU σ q () f a =
      ∑ s, σ s * ∑ w, game.prior w * (if s () w = f then game.uR () w a else 0) := by
  simp only [SemanticGame.receiverEU]
  exact Finset.sum_congr rfl fun s _ => by simp [hq.unit_eq_one]

/-- An argmax over `Fin 2` is pinned down by the two pointwise comparisons. -/
private theorem mem_argmax_fin2 (V : Fin 2 → ℝ) (x : Fin 2) :
    x ∈ Finset.univ.argmax V ↔ V 0 ≤ V x ∧ V 1 ≤ V x := by
  simp only [Finset.mem_argmax, Finset.mem_univ, true_and, true_implies]
  exact ⟨fun h => ⟨h 0, h 1⟩, fun ⟨h0, h1⟩ b => by fin_cases b <;> assumption⟩

/-- Either action can be made optimal for an unexpected signal by a suitably
skewed posterior — the belief-revision clause of `icrR` is always
satisfiable. -/
private theorem optimalActions_witness (x : Fin 2) :
    ∃ p, IsFullDist p ∧ x ∈ game.optimalActions () Finset.univ p := by
  refine ⟨fun w => if w = x then 2/3 else 1/3,
    ⟨fun w => by dsimp only; split_ifs <;> norm_num, by
      rw [Fin.sum_univ_two]; fin_cases x <;> simp <;> norm_num⟩, ?_⟩
  simp only [SemanticGame.optimalActions, mem_argmax_fin2]
  constructor <;> · rw [Fin.sum_univ_two, Fin.sum_univ_two]
                    fin_cases x <;> simp only [game] <;> norm_num

/-! ### Expected-utility values against the trace's beliefs -/

/-- Sender expected utility against a belief pinned to a single receiver. -/
private theorem senderEU_singleton {r₀ : Unit → Fin 2 → Fin 2}
    {ρ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hρ : IsFullDistOn {r₀} ρ) (hq : IsFullDist q) (w f : Fin 2) :
    game.senderEU ρ q () w f = game.uS () w f (r₀ () f) := by
  rw [senderEU_eq hq, sum_mul_of_fullDistOn_singleton hρ]

/-- Sender expected utility against a belief supported on two receivers. -/
private theorem senderEU_pair {a b : Unit → Fin 2 → Fin 2} (hab : a ≠ b)
    {ρ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hρ : IsFullDistOn {a, b} ρ) (hq : IsFullDist q) (w f : Fin 2) :
    game.senderEU ρ q () w f =
      ρ a * game.uS () w f (a () f) + ρ b * game.uS () w f (b () f) := by
  rw [senderEU_eq hq, sum_mul_of_fullDistOn_pair hab hρ]

/-- Receiver expected utility against a belief pinned to a single sender. -/
private theorem receiverEU_singleton {s₀ : Unit → Fin 2 → Fin 2}
    {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hσ : IsFullDistOn {s₀} σ) (hq : IsFullDist q) (f a : Fin 2) :
    game.receiverEU σ q () f a =
      ∑ w, game.prior w * (if s₀ () w = f then game.uR () w a else 0) := by
  rw [receiverEU_eq hq, sum_mul_of_fullDistOn_singleton hσ]

/-- Receiver expected utility against a belief supported on two senders. -/
private theorem receiverEU_pair {s₀ s₁ : Unit → Fin 2 → Fin 2} (hs : s₀ ≠ s₁)
    {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hσ : IsFullDistOn {s₀, s₁} σ) (hq : IsFullDist q) (f a : Fin 2) :
    game.receiverEU σ q () f a =
      σ s₀ * (∑ w, game.prior w * (if s₀ () w = f then game.uR () w a else 0)) +
        σ s₁ * (∑ w, game.prior w * (if s₁ () w = f then game.uR () w a else 0)) := by
  rw [receiverEU_eq hq, sum_mul_of_fullDistOn_pair hs hσ]

/-! ### The two recurring strategies

`fun _ _ => 0` and `fun _ x => x` are the only functions in the trace; the
support sets `{h | h () 0 = 0}` and `{h | h () 0 = 0 ∧ h () 1 = 1}` are their
pair and their common identity element. -/

private theorem zero_ne_id :
    (fun _ _ => 0 : Unit → Fin 2 → Fin 2) ≠ (fun _ x => x) := fun h =>
  absurd (congrFun (congrFun h ()) 1) (by norm_num)

/-- The senders (or receivers) fixing coordinate `0` are exactly the pair. -/
private theorem pair_eq :
    {h : Unit → Fin 2 → Fin 2 | h () 0 = 0} =
      {(fun _ _ => 0), (fun _ x => x)} := by
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h0
    rcases (by omega : h () 1 = 0 ∨ h () 1 = 1) with h1 | h1
    · left; funext c x; cases c; fin_cases x <;> assumption
    · right; funext c x; cases c; fin_cases x <;> simp_all
  · rintro (rfl | rfl) <;> rfl

/-- The identity is the only strategy fixing both coordinates. -/
private theorem singleton_eq :
    {h : Unit → Fin 2 → Fin 2 | h () 0 = 0 ∧ h () 1 = 1} = {fun _ x => x} := by
  ext h
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h0, h1⟩; funext c x; cases c; fin_cases x <;> assumption
  · rintro rfl; exact ⟨rfl, rfl⟩

/-! ### The sender stages S₀ and S₂

Against a receiver who ignores the signal (`fun _ _ => 0`) the sender always
prefers the cheap form; against the literal receiver (`fun _ x => x`) the
sender matches signal to world — the Horn convention. -/

/-- Against the constant receiver, the cheap form is uniquely optimal. -/
private theorem argmax_sender_z {ρ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hρ : IsFullDistOn {(fun _ _ => 0 : Unit → Fin 2 → Fin 2)} ρ) (hq : IsFullDist q)
    (w : Fin 2) : Finset.univ.argmax (game.senderEU ρ q () w) = {0} := by
  ext x
  rw [Finset.mem_singleton, mem_argmax_fin2]
  simp only [senderEU_singleton hρ hq]
  fin_cases w <;> fin_cases x <;> simp only [game, SemanticGame.uS] <;> norm_num

/-- Against the literal receiver, the sender matches signal to world. -/
private theorem argmax_sender_e {ρ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hρ : IsFullDistOn {(fun _ x => x : Unit → Fin 2 → Fin 2)} ρ) (hq : IsFullDist q)
    (w : Fin 2) : Finset.univ.argmax (game.senderEU ρ q () w) = {w} := by
  ext x
  rw [Finset.mem_singleton, mem_argmax_fin2]
  simp only [senderEU_singleton hρ hq]
  fin_cases w <;> fin_cases x <;> simp only [game, SemanticGame.uS] <;> norm_num

/-- S₀: the cautious responses to the credulous receiver send the cheap
form at both worlds. -/
private theorem icrS_zero : game.icrS 0 = {fun _ _ => 0} := by
  show game.senderCR (game.icrR 0) = _
  rw [icrR_zero]
  ext s
  simp only [SemanticGame.senderCR, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, q, hρ, hq, hBR⟩
    rw [game.mem_senderBR_iff] at hBR
    funext c w; cases c
    have := hBR () w
    rw [argmax_sender_z hρ hq, Finset.mem_singleton] at this
    exact this
  · rintro rfl
    refine ⟨_, _, isFullDistOn_pointMass _, isFullDist_unitOne, ?_⟩
    rw [game.mem_senderBR_iff]
    intro c w; cases c
    rw [argmax_sender_z (isFullDistOn_pointMass _) isFullDist_unitOne]
    exact Finset.mem_singleton_self _

/-! ### The receiver stages R₁, R₂ and R₃

The credulous stage sends the cheap form at both worlds, so the cheap form's
receiver is pinned to world `0` while the costly form is unexpected (any
action survives, but the belief-revision clause is vacuously satisfiable).
Once the sender separates, both forms are expected and the receiver reads
each literally. -/

/-- Against the sender who always sends the cheap form, the receiver reads
the cheap form as the frequent world. -/
private theorem argmax_receiver_z0 {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hσ : IsFullDistOn {(fun _ _ => 0 : Unit → Fin 2 → Fin 2)} σ) (hq : IsFullDist q) :
    Finset.univ.argmax (game.receiverEU σ q () 0) = {0} := by
  ext a
  rw [Finset.mem_singleton, mem_argmax_fin2]
  simp only [receiverEU_singleton hσ hq, Fin.sum_univ_two]
  fin_cases a <;> simp [game] <;> norm_num

/-- The costly form is never sent, so every action ties — the receiver is
unconstrained there. -/
private theorem argmax_receiver_z1 {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hσ : IsFullDistOn {(fun _ _ => 0 : Unit → Fin 2 → Fin 2)} σ) (hq : IsFullDist q) :
    Finset.univ.argmax (game.receiverEU σ q () 1) = Finset.univ := by
  have h : game.receiverEU σ q () 1 = fun _ => 0 := by
    funext a
    rw [receiverEU_singleton hσ hq, Fin.sum_univ_two]
    simp [game]
  rw [h, Finset.argmax_const]

/-- R₁: the cautious responses to S₀ read the cheap form as the frequent
world and leave the unexpected costly form unconstrained. -/
private theorem icrR_one : game.icrR 1 = {r | r () 0 = 0} := by
  have hS0 : game.senderCR (game.icrR 0) = {fun _ _ => 0} := icrS_zero
  have hunfold : game.icrR 1 =
      {r ∈ game.receiverCR (game.senderCR (game.icrR 0)) |
        ∀ f, SemanticGame.Unexpected (game.senderCR (game.icrR 0)) f →
          ∀ c, ∃ p, IsFullDist p ∧ r c f ∈ game.optimalActions c (game.extension f) p} :=
    rfl
  rw [hunfold, hS0]
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩
    rw [game.mem_receiverBR_iff] at hBR
    have := hBR () 0
    rw [argmax_receiver_z0 hσ hq, Finset.mem_singleton] at this
    exact this
  · intro hr0
    refine ⟨⟨_, _, isFullDistOn_pointMass _, isFullDist_unitOne, ?_⟩, ?_⟩
    · rw [game.mem_receiverBR_iff]
      intro c f; cases c
      rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl
      · rw [argmax_receiver_z0 (isFullDistOn_pointMass _) isFullDist_unitOne]
        rwa [Finset.mem_singleton]
      · rw [argmax_receiver_z1 (isFullDistOn_pointMass _) isFullDist_unitOne]
        exact Finset.mem_univ _
    · intro f _ c; cases c
      rw [extension_eq]
      exact optimalActions_witness _

/-! ### The sender stage S₁

Against a belief mixing the two receivers, the frequent world still fixes the
cheap form, but the rare world's optimal form depends on how much mass the
literal receiver carries — so both `s () 1 = 0` and `s () 1 = 1` survive,
giving `{s | s () 0 = 0}`. -/

section PairSender
variable {ρ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
  (hρ : IsFullDistOn {(fun _ _ => 0), (fun _ x => x)} ρ) (hq : IsFullDist q)
include hρ hq

/-- At the frequent world the cheap form is optimal against any receiver mix. -/
private theorem sender_pair_w0_eq_zero {x : Fin 2}
    (hx : x ∈ Finset.univ.argmax (game.senderEU ρ q () 0)) : x = 0 := by
  rw [mem_argmax_fin2] at hx
  obtain ⟨hz, he, hsum⟩ := hρ.pair_props zero_ne_id
  by_contra hne
  have hx1 : x = 1 := by omega
  subst hx1
  obtain ⟨h0, -⟩ := hx
  rw [senderEU_pair zero_ne_id hρ hq, senderEU_pair zero_ne_id hρ hq] at h0
  simp only [game, SemanticGame.uS, if_true, if_false, Fin.reduceEq] at h0
  linarith

/-- Membership witness at the frequent world. -/
private theorem zero_mem_sender_pair_w0 :
    (0 : Fin 2) ∈ Finset.univ.argmax (game.senderEU ρ q () 0) := by
  rw [mem_argmax_fin2]
  obtain ⟨hz, he, hsum⟩ := hρ.pair_props zero_ne_id
  refine ⟨le_refl _, ?_⟩
  rw [senderEU_pair zero_ne_id hρ hq, senderEU_pair zero_ne_id hρ hq]
  simp only [game, SemanticGame.uS, if_true, if_false, Fin.reduceEq]; linarith

/-- When the literal receiver is light, the cheap form is optimal at the rare
world too. -/
private theorem zero_mem_sender_pair_w1 (hle : ρ (fun _ x => x) ≤ 1/5) :
    (0 : Fin 2) ∈ Finset.univ.argmax (game.senderEU ρ q () 1) := by
  rw [mem_argmax_fin2]
  obtain ⟨hz, he, hsum⟩ := hρ.pair_props zero_ne_id
  refine ⟨le_refl _, ?_⟩
  rw [senderEU_pair zero_ne_id hρ hq, senderEU_pair zero_ne_id hρ hq]
  simp only [game, SemanticGame.uS, if_true, if_false, Fin.reduceEq]; linarith

/-- When the literal receiver is heavy, the costly form is optimal at the rare
world. -/
private theorem one_mem_sender_pair_w1 (hge : 1/5 ≤ ρ (fun _ x => x)) :
    (1 : Fin 2) ∈ Finset.univ.argmax (game.senderEU ρ q () 1) := by
  rw [mem_argmax_fin2]
  obtain ⟨hz, he, hsum⟩ := hρ.pair_props zero_ne_id
  refine ⟨?_, le_refl _⟩
  rw [senderEU_pair zero_ne_id hρ hq, senderEU_pair zero_ne_id hρ hq]
  simp only [game, SemanticGame.uS, if_true, if_false, Fin.reduceEq]; linarith

end PairSender

/-- S₁: the cautious responses to R₁ still fix the cheap form at the frequent
world; the rare world is free. -/
private theorem icrS_one : game.icrS 1 = {s | s () 0 = 0} := by
  show game.senderCR (game.icrR 1) = _
  rw [icrR_one]
  conv_lhs => rw [pair_eq]
  ext s
  simp only [SemanticGame.senderCR, Set.mem_setOf_eq]
  constructor
  · rintro ⟨ρ, q, hρ, hq, hBR⟩
    rw [game.mem_senderBR_iff] at hBR
    exact sender_pair_w0_eq_zero hρ hq (hBR () 0)
  · intro hs0
    have hmem : s = (fun _ _ => 0) ∨ s = (fun _ x => x) := by
      have hs : s ∈ ({(fun _ _ => 0), (fun _ x => x)} : Set (Unit → Fin 2 → Fin 2)) := by
        rw [← pair_eq]; exact hs0
      simpa [Set.mem_insert_iff] using hs
    rcases hmem with rfl | rfl
    · have hfull := isFullDistOn_pairWeighted zero_ne_id
        (show (0 : ℝ) < 9/10 by norm_num) (by norm_num)
      refine ⟨_, _, hfull, isFullDist_unitOne, ?_⟩
      rw [game.mem_senderBR_iff]
      intro c w; cases c
      rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
      · exact zero_mem_sender_pair_w0 hfull isFullDist_unitOne
      · exact zero_mem_sender_pair_w1 hfull isFullDist_unitOne
          (by rw [pairWeighted_apply_right zero_ne_id]; norm_num)
    · have hfull := isFullDistOn_pairWeighted zero_ne_id
        (show (0 : ℝ) < 1/2 by norm_num) (by norm_num)
      refine ⟨_, _, hfull, isFullDist_unitOne, ?_⟩
      rw [game.mem_senderBR_iff]
      intro c w; cases c
      rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl
      · exact zero_mem_sender_pair_w0 hfull isFullDist_unitOne
      · exact one_mem_sender_pair_w1 hfull isFullDist_unitOne
          (by rw [pairWeighted_apply_right zero_ne_id]; norm_num)

/-! ### The receiver stage R₂

Once the sender separates the worlds, both forms are expected and each is
read literally: the cheap form as the frequent world, the costly form as the
rare one. No signal is unexpected, so the belief-revision clause is vacuous. -/

section PairReceiver
variable {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
  (hσ : IsFullDistOn {(fun _ _ => 0), (fun _ x => x)} σ) (hq : IsFullDist q)
include hσ hq

/-- The cheap form is read as the frequent world against the separating mix. -/
private theorem receiver_pair_f0_eq_zero {x : Fin 2}
    (hx : x ∈ Finset.univ.argmax (game.receiverEU σ q () 0)) : x = 0 := by
  rw [mem_argmax_fin2] at hx
  obtain ⟨hz, he, hsum⟩ := hσ.pair_props zero_ne_id
  by_contra hne
  have hx1 : x = 1 := by omega
  subst hx1
  obtain ⟨h0, -⟩ := hx
  rw [receiverEU_pair zero_ne_id hσ hq, receiverEU_pair zero_ne_id hσ hq] at h0
  simp only [Fin.sum_univ_two, game, if_true, if_false, Fin.reduceEq] at h0
  linarith

/-- Membership witness reading the cheap form as the frequent world. -/
private theorem zero_mem_receiver_pair_f0 :
    (0 : Fin 2) ∈ Finset.univ.argmax (game.receiverEU σ q () 0) := by
  rw [mem_argmax_fin2]
  obtain ⟨hz, he, hsum⟩ := hσ.pair_props zero_ne_id
  refine ⟨le_refl _, ?_⟩
  rw [receiverEU_pair zero_ne_id hσ hq, receiverEU_pair zero_ne_id hσ hq]
  simp only [Fin.sum_univ_two, game, if_true, if_false, Fin.reduceEq]; linarith

/-- The costly form is read as the rare world against the separating mix. -/
private theorem receiver_pair_f1_eq_one {x : Fin 2}
    (hx : x ∈ Finset.univ.argmax (game.receiverEU σ q () 1)) : x = 1 := by
  rw [mem_argmax_fin2] at hx
  obtain ⟨hz, he, hsum⟩ := hσ.pair_props zero_ne_id
  by_contra hne
  have hx0 : x = 0 := by omega
  subst hx0
  obtain ⟨-, h1⟩ := hx
  rw [receiverEU_pair zero_ne_id hσ hq, receiverEU_pair zero_ne_id hσ hq] at h1
  simp only [Fin.sum_univ_two, game, if_true, if_false, Fin.reduceEq] at h1
  linarith

/-- Membership witness reading the costly form as the rare world. -/
private theorem one_mem_receiver_pair_f1 :
    (1 : Fin 2) ∈ Finset.univ.argmax (game.receiverEU σ q () 1) := by
  rw [mem_argmax_fin2]
  obtain ⟨hz, he, hsum⟩ := hσ.pair_props zero_ne_id
  refine ⟨?_, le_refl _⟩
  rw [receiverEU_pair zero_ne_id hσ hq, receiverEU_pair zero_ne_id hσ hq]
  simp only [Fin.sum_univ_two, game, if_true, if_false, Fin.reduceEq]; linarith

end PairReceiver

/-- R₂: the cautious responses to S₁ read both forms literally — the Horn
convention's receiver. Both signals are expected, so the filter is vacuous. -/
private theorem icrR_two : game.icrR 2 = {fun _ f => f} := by
  have hS1 : game.senderCR (game.icrR 1) = {(fun _ _ => 0), (fun _ x => x)} := by
    have h := icrS_one; rw [pair_eq] at h; exact h
  have hunfold : game.icrR 2 =
      {r ∈ game.receiverCR (game.senderCR (game.icrR 1)) |
        ∀ f, SemanticGame.Unexpected (game.senderCR (game.icrR 1)) f →
          ∀ c, ∃ p, IsFullDist p ∧ r c f ∈ game.optimalActions c (game.extension f) p} :=
    rfl
  rw [hunfold, hS1]
  conv_rhs => rw [← singleton_eq]
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩
    rw [game.mem_receiverBR_iff] at hBR
    exact ⟨receiver_pair_f0_eq_zero hσ hq (hBR () 0),
      receiver_pair_f1_eq_one hσ hq (hBR () 1)⟩
  · rintro ⟨hr0, hr1⟩
    refine ⟨⟨_, _, isFullDistOn_pairUniform zero_ne_id, isFullDist_unitOne, ?_⟩, ?_⟩
    · rw [game.mem_receiverBR_iff]
      intro c f; cases c
      rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl
      · rw [hr0]; exact zero_mem_receiver_pair_f0 (isFullDistOn_pairUniform zero_ne_id)
          isFullDist_unitOne
      · rw [hr1]; exact one_mem_receiver_pair_f1 (isFullDistOn_pairUniform zero_ne_id)
          isFullDist_unitOne
    · intro f hf c
      exact absurd rfl (hf (fun _ x => x) (Set.mem_insert_of_mem _ rfl) () f)

/-- S₂: the cautious responses to the literal receiver match signal to world
— the Horn convention's sender. -/
private theorem icrS_two : game.icrS 2 = {fun _ w => w} := by
  show game.senderCR (game.icrR 2) = _
  rw [icrR_two]
  ext s
  simp only [SemanticGame.senderCR, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨ρ, q, hρ, hq, hBR⟩
    rw [game.mem_senderBR_iff] at hBR
    funext c w; cases c
    have := hBR () w
    rw [argmax_sender_e hρ hq, Finset.mem_singleton] at this
    exact this
  · rintro rfl
    refine ⟨_, _, isFullDistOn_pointMass _, isFullDist_unitOne, ?_⟩
    rw [game.mem_senderBR_iff]
    intro c w; cases c
    rw [argmax_sender_e (isFullDistOn_pointMass _) isFullDist_unitOne]
    exact Finset.mem_singleton_self _

/-! ### The fixed point R₃ = R₂

The separating sender is now stable: the receiver's cautious responses to it
again read both forms literally, reproducing R₂. -/

/-- Against the literal sender the cheap form is read as the frequent world. -/
private theorem argmax_receiver_e0 {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hσ : IsFullDistOn {(fun _ x => x : Unit → Fin 2 → Fin 2)} σ) (hq : IsFullDist q) :
    Finset.univ.argmax (game.receiverEU σ q () 0) = {0} := by
  ext a
  rw [Finset.mem_singleton, mem_argmax_fin2]
  simp only [receiverEU_singleton hσ hq, Fin.sum_univ_two]
  fin_cases a <;> simp [game]

/-- Against the literal sender the costly form is read as the rare world. -/
private theorem argmax_receiver_e1 {σ : (Unit → Fin 2 → Fin 2) → ℝ} {q : Unit → ℝ}
    (hσ : IsFullDistOn {(fun _ x => x : Unit → Fin 2 → Fin 2)} σ) (hq : IsFullDist q) :
    Finset.univ.argmax (game.receiverEU σ q () 1) = {1} := by
  ext a
  rw [Finset.mem_singleton, mem_argmax_fin2]
  simp only [receiverEU_singleton hσ hq, Fin.sum_univ_two]
  fin_cases a <;> simp [game]

/-- R₃ reproduces R₂: the ICR sequence has reached its fixed point. -/
private theorem icrR_fixed : game.icrR 3 = game.icrR 2 := by
  rw [icrR_two]
  have hS2 : game.senderCR (game.icrR 2) = {fun _ w => w} := icrS_two
  have hunfold : game.icrR 3 =
      {r ∈ game.receiverCR (game.senderCR (game.icrR 2)) |
        ∀ f, SemanticGame.Unexpected (game.senderCR (game.icrR 2)) f →
          ∀ c, ∃ p, IsFullDist p ∧ r c f ∈ game.optimalActions c (game.extension f) p} :=
    rfl
  rw [hunfold, hS2]
  conv_rhs => rw [← singleton_eq]
  ext r
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩
    rw [game.mem_receiverBR_iff] at hBR
    have h0 := hBR () 0
    have h1 := hBR () 1
    rw [argmax_receiver_e0 hσ hq, Finset.mem_singleton] at h0
    rw [argmax_receiver_e1 hσ hq, Finset.mem_singleton] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨hr0, hr1⟩
    refine ⟨⟨_, _, isFullDistOn_pointMass _, isFullDist_unitOne, ?_⟩, ?_⟩
    · rw [game.mem_receiverBR_iff]
      intro c f; cases c
      rcases (show f = 0 ∨ f = 1 by omega) with rfl | rfl
      · rw [hr0, argmax_receiver_e0 (isFullDistOn_pointMass _) isFullDist_unitOne]
        exact Finset.mem_singleton_self _
      · rw [hr1, argmax_receiver_e1 (isFullDistOn_pointMass _) isFullDist_unitOne]
        exact Finset.mem_singleton_self _
    · intro f hf c
      exact absurd rfl (hf (fun _ x => x) rfl () f)

/-- **Horn's division of pragmatic labor** ([jaeger-2014] §5, Example 6):
in the two-synonyms game, the pragmatically rationalizable strategies are
exactly the Horn convention — the cheap form marks the frequent world and
the costly form the rare one; both PRS sets are the identity strategies. -/
theorem division_of_pragmatic_labor :
    game.prsS = {fun _ w => w} ∧ game.prsR = {fun _ f => f} := by
  have hfix : game.icrR (2 + 1) = game.icrR 2 := icrR_fixed
  exact ⟨(game.prsS_eq_of_fixed hfix).trans icrS_two,
    (game.prsR_eq_of_fixed hfix).trans icrR_two⟩

end Horn

end

end Jaeger2014
