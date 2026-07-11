import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
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

Deviation: utilities are ℚ-valued (the paper uses ℝ) per the project's
exact-arithmetic convention; nothing in the model depends on completeness.

The comparison with [franke-2011]'s IBR model (the paper's §6: Franke's
games are the type-matching specialization, and the models differ exactly
in belief selection — uniform via the Principle of Insufficient Reason
vs. all full-support beliefs) is a planned follow-up, as are the worked
examples (§5) and Rabin-style message credibility.
-/

namespace Jaeger2014

/-! ### Beliefs

Probability distributions and full-support ("cautious") distributions,
including versions supported on a given strategy set — Jäger's `Δ(M)` and
`int(Δ(M))`. -/

variable {M : Type*}

/-- A probability distribution on a finite type: Jäger's `Δ(M)`. -/
def IsDist [Fintype M] (q : M → ℚ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ ∑ x, q x = 1

/-- A full-support probability distribution: Jäger's `int(Δ(M))`. -/
def IsFullDist [Fintype M] (q : M → ℚ) : Prop :=
  (∀ x, 0 < q x) ∧ ∑ x, q x = 1

/-- A distribution supported inside `P`: Jäger's `Δ(P)` for `P ⊆ M`. -/
def IsDistOn [Fintype M] (P : Set M) (q : M → ℚ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ (∀ x ∉ P, q x = 0) ∧ ∑ x, q x = 1

/-- A distribution with support exactly `P`: Jäger's `int(Δ(P)))` for
`P ⊆ M` — positive on `P`, zero off it. -/
def IsFullDistOn [Fintype M] (P : Set M) (q : M → ℚ) : Prop :=
  (∀ x ∈ P, 0 < q x) ∧ (∀ x ∉ P, q x = 0) ∧ ∑ x, q x = 1

theorem IsFullDist.isDist [Fintype M] {q : M → ℚ} (h : IsFullDist q) : IsDist q :=
  ⟨fun x => (h.1 x).le, h.2⟩

/-- A full-support-on-`P` distribution is supported inside any superset. -/
theorem IsFullDistOn.isDistOn [Fintype M] {P P' : Set M} {q : M → ℚ}
    (h : IsFullDistOn P q) (hPP' : P ⊆ P') : IsDistOn P' q :=
  ⟨fun x => (em (x ∈ P)).elim (fun hx => (h.1 x hx).le) (fun hx => (h.2.1 x hx).ge),
   fun x hx => h.2.1 x (fun hxP => hx (hPP' hxP)), h.2.2⟩

/-! ### Semantic games -/

/-- A semantic game ([jaeger-2014] §4): contexts `C` (higher-order
uncertainty about preferences), worlds `W`, signals `F`, actions `A`; a
positive prior over worlds; an exogenous interpretation function
(`meaning`); receiver utilities, and cost-separable sender utilities
(`uS c w f a = vS c w a - cost f`). -/
structure SemanticGame (C W F A : Type*) [Fintype W] where
  /-- The receiver's prior probability over worlds (`p*`). -/
  prior : W → ℚ
  /-- All worlds have positive prior probability. -/
  prior_pos : ∀ w, 0 < prior w
  /-- The prior is a probability distribution. -/
  prior_sum : ∑ w, prior w = 1
  /-- The interpretation function `⟦·⟧`: is signal `f` true at world `w`? -/
  meaning : F → W → Prop
  /-- Context/outcome utilities of the sender. -/
  vS : C → W → A → ℚ
  /-- Signalling costs. -/
  cost : F → ℚ
  /-- The receiver's utility function. -/
  uR : C → W → A → ℚ
  [meaningDecidable : ∀ f, DecidablePred (meaning f)]

attribute [instance] SemanticGame.meaningDecidable

namespace SemanticGame

variable {C W F A : Type*} [Fintype C] [Fintype W] [Fintype F] [Fintype A]
  [DecidableEq C] [DecidableEq W] [DecidableEq F]
  (g : SemanticGame C W F A)

/-- The sender's utility function: outcome utility minus signalling cost. -/
def uS (c : C) (w : W) (f : F) (a : A) : ℚ :=
  g.vS c w a - g.cost f

/-- The extension of a signal: the worlds at which it is true. -/
def extension (f : F) : Finset W :=
  Finset.univ.filter (g.meaning f)

/-- Def. 1: the receiver-optimal actions in context `c` when the belief `p`
is updated with the proposition `φ` — the argmax of `p`-expected receiver
utility over `φ`. -/
def optimalActions (c : C) (φ : Finset W) (p : W → ℚ) : Finset A :=
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
def receiverBR (σ : (C → W → F) → ℚ) (q : C → ℚ) : Set (C → F → A) :=
  {r' | ∀ c, r' ∈ Finset.univ.argmax (fun r : C → F → A =>
    ∑ s, σ s * ∑ c', q c' * ∑ w, g.prior w * g.uR c w (r c (s c' w)))}

/-- Def. 2 (sender): `s'` is a best response to the belief `(ρ, q)` iff at
every context/world pair it maximizes expected utility against the
receiver strategy distribution `ρ` and context distribution `q`. -/
def senderBR (ρ : (C → F → A) → ℚ) (q : C → ℚ) : Set (C → W → F) :=
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
    (∀ s' ∈ S, ∃ ρ q, IsDistOn R ρ ∧ IsDist q ∧ s' ∈ g.senderBR ρ q) ∧
    (∀ r' ∈ R, ∃ σ q, IsDistOn S σ ∧ IsDist q ∧ r' ∈ g.receiverBR σ q) ∧
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
      hq.isDist, hBR⟩
  · -- every recurring receiver strategy is a BR to a belief inside prsS
    intro r' hr'
    obtain ⟨m, hm, hr'm⟩ := hr' (a + 1)
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    have hk : a ≤ k := by omega
    obtain ⟨⟨σ, q, hσ, hq, hBR⟩, -⟩ := hr'm
    exact ⟨σ, q, hσ.isDistOn (g.icrS_subset_prsS hab heq hk),
      hq.isDist, hBR⟩

end SemanticGame

end Jaeger2014
