import Linglib.Core.Probability.Choice.RationalAction
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Luce (1959), Chapter 3: Applications to Utility Theory [luce-1959]

Choices among gambles: `aρb` is "outcome `a` if chance event `ρ` occurs, else
`b`" (p. 78), and `S(A,E) = (A × E × A) ∪ A` collects gambles and pure
alternatives. A decomposable preference structure `⟨A, E, P, Q⟩` (Definition 5)
couples a choice function `P` over `S(A,E)` with an event choice function `Q`
via Axiom 2: `P(aρb, aσb) = P(a,b)·Q(ρ,σ) + P(b,a)·Q(σ,ρ)`.

## Main results

- `DecomposablePreference`: Definition 5 (p. 78), Axiom 2 in full mixture form;
  `gam_of_alt_eq_one` is the reduced form `P(aρb, aσb) = Q(ρ,σ)` under perfect
  discrimination `P(a,b) = 1`, as used inside the proofs of Theorems 13–14.
- `Complementation`: Axiom 3 (p. 83), `P(aρb, x) = P(bρ̄a, x)`, with `E` a
  Boolean algebra as Luce requires. `NontrivialPreference`: Axiom 4 (p. 83).
- `q_compl_compl`: Lemma 9 (p. 84), `Q(ρ, σ) = Q(σ̄, ρ̄)`;
  `v_mul_v_compl_const` derives from it the constancy of `v(ρ)·v(ρ̄)`, the
  source of the `φ(ρ)φ(ρ̄) = constant` clause of §3.D.3 (p. 89).
- `Neutral` / `Favorable` / `Unfavorable`: comparison of an event to its own
  complement — Luce's classes `C(½)`, `C(1)`, `C(0)` (Lemma 11, p. 85).
  `neutral_indifferent` is the first clause of Lemma 10 (p. 84);
  `favorable_gt_unfavorable` is the between-class ordering.
- `theorem13` / `theorem14`: the two §3.D theorems (pp. 86, 89) behind Luce's
  proposed experiment; `gam_of_factored` is the observable consequence (p. 90)
  of the *suggested* local decomposition `v(aρb) = w(a,b)·φ(ρ)` of §3.D.3 —
  Luce offers the factoring as a hypothesis, not a theorem, and so does this
  file.

## Formalization notes

Luce's `P` and `Q` are families of probability measures on subsets of size ≤ 3
(Definition 5); here both are total `ChoiceFn`s, which is where the diagonal
bites: `binary x x = 1`, so Axiom 2 needs its `a ≠ b` guard
(`axiom2_unguarded_false`) and Axiom 3 its two `x`-guards
(`complementation_unguarded_false`) — for Luce those instances are degenerate
singleton choices. Ratio scales enter as `ChoiceFn.BinaryRatioScaleOn`, local
to the gamble set under discussion, because Chapter 3 mixes imperfect
discrimination among gambles with perfect discrimination among pure
alternatives (`P(a,b) = 1`), which a globally positive scale cannot represent.

Theorems 10–12 (pp. 80, 84) — `∼` partitions `E` into (exactly) three
equivalence classes, given Axioms 1–5 — are not formalized: their proofs run
through Lemma 5's cubic identity for `P` on gamble triples, and the
three-class conclusion requires perfect discrimination `Q ∈ {0, 1}` between
the extreme classes, so no globally ratio-scaled `Q` satisfies the
nondegenerate branch; a faithful rendition needs the family-based `P`, `Q`
(Axiom 1 on ≤3-element sets). Recorded as future work.
-/

namespace Luce1959

open Core

variable {A E : Type*} [DecidableEq A] [DecidableEq E]

/-- A gamble `aρb` (p. 78): outcome `win` if the chance event `event` occurs,
    else `lose`. -/
structure Gamble (A E : Type*) where
  /-- Outcome if the event occurs. -/
  win : A
  /-- The conditioning chance event. -/
  event : E
  /-- Outcome if the event does not occur. -/
  lose : A
  deriving DecidableEq

/-- Luce's total alternative set `S(A,E) = (A × E × A) ∪ A` (p. 78): gambles
    together with the pure alternatives. -/
abbrev Alternative (A E : Type*) := Gamble A E ⊕ A

/-- A decomposable preference structure `⟨A, E, P, Q⟩` (Definition 5, p. 78):
    choice over gambles and pure alternatives (`P`), choice over events by
    subjective likelihood (`Q`), coupled by **Axiom 2**:
    `P(aρb, aσb) = P(a,b)·Q(ρ,σ) + P(b,a)·Q(σ,ρ)`.

    Deviations from Luce: `P` and `Q` are total `ChoiceFn`s rather than
    families on ≤3-element subsets satisfying his Axiom 1 (choice-axiom
    consequences enter per-theorem, as `BinaryRatioScaleOn` hypotheses), and
    Axiom 2 carries an `a ≠ b` guard — at `a = b` it is unsatisfiable for a
    total `P` (`axiom2_unguarded_false`), and Luce's own uses all have
    `P(a,b) ∉ {0, 1}` or `P(a,b) = 1` with `a`, `b` a genuine pair. -/
structure DecomposablePreference (A E : Type*) [DecidableEq A] [DecidableEq E] where
  /-- Choice over `S(A,E)`. -/
  P : ChoiceFn (Alternative A E)
  /-- Choice over events by subjective likelihood. -/
  Q : ChoiceFn E
  /-- **Axiom 2** (p. 78), in Luce's full mixture form. -/
  axiom2 : ∀ a b : A, a ≠ b → ∀ ρ σ : E,
    P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
      P.binary (.inr a) (.inr b) * Q.binary ρ σ +
      P.binary (.inr b) (.inr a) * Q.binary σ ρ

/-- Without its `a ≠ b` guard, Axiom 2 is unsatisfiable for a total choice
    function: at `a = b` it forces `P(aρa, aσa) = Q(ρ,σ) + Q(σ,ρ) = 1` in both
    argument orders, contradicting binary complementarity. In Luce's system
    `P(a, a)` is the degenerate singleton choice. -/
theorem axiom2_unguarded_false [Nontrivial E] [Inhabited A]
    (P : ChoiceFn (Alternative A E)) (Q : ChoiceFn E)
    (h : ∀ (a b : A) (ρ σ : E),
      P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
        P.binary (.inr a) (.inr b) * Q.binary ρ σ +
        P.binary (.inr b) (.inr a) * Q.binary σ ρ) : False := by
  obtain ⟨ρ, σ, hρσ⟩ := exists_pair_ne E
  set a := (default : A)
  have hself := P.binary_self (Sum.inr a)
  have hQc := Q.binary_complement hρσ
  have hne : (Sum.inl ⟨a, ρ, a⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, a⟩ := by
    simpa using hρσ
  have hPc := P.binary_complement hne
  have h1 := h a a ρ σ
  have h2 := h a a σ ρ
  rw [hself] at h1 h2
  linarith

namespace DecomposablePreference

variable (dp : DecomposablePreference A E)

/-- Luce's `P(a, b)` for pure alternatives. -/
def alt (a b : A) : ℝ := dp.P.binary (.inr a) (.inr b)

/-- Luce's `P(g, h)` for gambles. -/
def gam (g h : Gamble A E) : ℝ := dp.P.binary (.inl g) (.inl h)

variable {dp}

/-- The reduced decomposition under perfect discrimination, as used inside the
    proofs of Theorems 13–14 (p. 87): if `P(a,b) = 1` then
    `P(aρb, aσb) = Q(ρ, σ)`. -/
theorem gam_of_alt_eq_one {a b : A} (hab : a ≠ b) (h1 : dp.alt a b = 1)
    (ρ σ : E) : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.Q.binary ρ σ := by
  have hc := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  simp only [alt] at h1
  have hba : dp.P.binary (Sum.inr b) (Sum.inr a) = 0 := by linarith
  simp only [gam]
  rw [dp.axiom2 a b hab ρ σ, h1, hba]
  ring

/-- Equal fractions of positives cross-multiply: for positive `x y x' y'`,
    `x/(x+y) = x'/(x'+y') ↔ x·y' = x'·y`. -/
private lemma frac_eq_frac {x y x' y' : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hx' : 0 < x') (hy' : 0 < y') :
    x / (x + y) = x' / (x' + y') ↔ x * y' = x' * y := by
  rw [div_eq_div_iff (by linarith) (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- **Theorem 13** (p. 86): if `P(a,b) = P(c,d) = 1` and binary choice among
    the four gambles `{aρb, aσb, cρd, cσd}` follows a local ratio scale (Luce:
    "all pairwise discriminations in `T` are imperfect", via his Theorem 4),
    then `P(aρb, cρd) = P(aσb, cσd)` — the step-function prediction of §3.D. -/
theorem theorem13 {a b c d : A} {ρ σ : E} {v : Alternative A E → ℝ}
    (hab : a ≠ b) (hcd : c ≠ d) (ha1 : dp.alt a b = 1) (hc1 : dp.alt c d = 1)
    (hv : dp.P.BinaryRatioScaleOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩} v) :
    dp.gam ⟨a, ρ, b⟩ ⟨c, ρ, d⟩ = dp.gam ⟨a, σ, b⟩ ⟨c, σ, d⟩ := by
  by_cases hρσ : ρ = σ
  · subst hρσ; rfl
  by_cases hacbd : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := hacbd
    simp only [gam]
    rw [dp.P.binary_self, dp.P.binary_self]
  have e1 : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ := by
    rw [gam_of_alt_eq_one hab ha1, gam_of_alt_eq_one hcd hc1]
  have h12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have h34 : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hρσ
  have h13 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
    simpa using hacbd
  have h24 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hacbd
  obtain ⟨hpos, hrule⟩ := hv
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  simp only [gam] at e1 ⊢
  rw [hrule _ (by simp) _ (by simp) h12, hrule _ (by simp) _ (by simp) h34] at e1
  rw [hrule _ (by simp) _ (by simp) h13, hrule _ (by simp) _ (by simp) h24,
      frac_eq_frac p1 p3 p2 p4]
  exact ((frac_eq_frac p1 p2 p3 p4).mp e1).trans (mul_comm _ _)

section BooleanEvents

variable [BooleanAlgebra E]

/-- **Axiom 3** (p. 83): "P(aρb, x) = P(bρ̄a, x), where ρ̄ denotes the
    complement of ρ" — `aρb` and `bρ̄a` are the same prospect relabeled.
    The two guards exclude `x ∈ {aρb, bρ̄a}`: for Luce those instances are
    degenerate singleton choices, and over a total `ChoiceFn` the unguarded
    axiom is unsatisfiable (`complementation_unguarded_false`). -/
def Complementation (dp : DecomposablePreference A E) : Prop :=
  ∀ (a b : A) (ρ : E) (x : Alternative A E),
    x ≠ .inl ⟨a, ρ, b⟩ → x ≠ .inl ⟨b, ρᶜ, a⟩ →
      dp.P.binary (.inl ⟨a, ρ, b⟩) x = dp.P.binary (.inl ⟨b, ρᶜ, a⟩) x

/-- Without its guards, Axiom 3 is unsatisfiable for a total choice function:
    `x := bρ̄a` forces `P(aρb, bρ̄a) = 1`, and symmetrically
    `P(bρ̄a, aρb) = 1`, contradicting binary complementarity. -/
theorem complementation_unguarded_false [Nontrivial A]
    (dp : DecomposablePreference A E)
    (h : ∀ (a b : A) (ρ : E) (x : Alternative A E),
      dp.P.binary (.inl ⟨a, ρ, b⟩) x = dp.P.binary (.inl ⟨b, ρᶜ, a⟩) x) :
    False := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne A
  have h1 : dp.P.binary (.inl ⟨a, ⊥, b⟩) (.inl ⟨b, ⊥ᶜ, a⟩) = 1 := by
    rw [h a b ⊥ (.inl ⟨b, ⊥ᶜ, a⟩)]
    exact dp.P.binary_self _
  have h2 : dp.P.binary (.inl ⟨b, ⊥ᶜ, a⟩) (.inl ⟨a, ⊥, b⟩) = 1 := by
    have e := h b a ⊥ᶜ (.inl ⟨a, ⊥, b⟩)
    rw [compl_compl] at e
    rw [e]
    exact dp.P.binary_self _
  have hne : (Sum.inl ⟨a, ⊥, b⟩ : Alternative A E) ≠ Sum.inl ⟨b, ⊥ᶜ, a⟩ := by
    simp [hab]
  have := dp.P.binary_complement hne
  linarith

/-- **Axiom 4** (p. 83): some pair of alternatives and some pair of events are
    discriminated away from ½. Distinctness is explicit: Luce's `P(a*, b*)`
    presupposes a genuine pair (`P(a, a) = 1 ≠ ½` would satisfy the inequality
    degenerately and break the determinant step of Lemma 9). -/
def NontrivialPreference (dp : DecomposablePreference A E) : Prop :=
  (∃ a b : A, a ≠ b ∧ dp.alt a b ≠ 1 / 2) ∧
    ∃ ρ σ : E, ρ ≠ σ ∧ dp.Q.binary ρ σ ≠ 1 / 2

/-- **Lemma 9** (p. 84): under Axioms 3–4, `Q(ρ, σ) = Q(σ̄, ρ̄)`. -/
theorem q_compl_compl (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) (ρ σ : E) :
    dp.Q.binary ρ σ = dp.Q.binary σᶜ ρᶜ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · rw [dp.Q.binary_self, dp.Q.binary_self]
  obtain ⟨⟨a, b, hab, hp⟩, -⟩ := ax4
  have hXY : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have hXY' : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨b, σᶜ, a⟩ := by
    simp [hab]
  have hY'X' : (Sum.inl ⟨b, σᶜ, a⟩ : Alternative A E) ≠ Sum.inl ⟨b, ρᶜ, a⟩ := by
    simpa using compl_injective.ne (Ne.symm hρσ)
  -- flip the second argument `aσb ↝ bσ̄a` (Axiom 3 at schema (a, b, σ))
  have flipY : dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨a, σ, b⟩) =
      dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨b, σᶜ, a⟩) := by
    have e := ax3 a b σ (.inl ⟨a, ρ, b⟩) hXY hXY'
    have c1 := dp.P.binary_complement hXY
    have c2 := dp.P.binary_complement hXY'
    linarith
  -- flip the first argument `aρb ↝ bρ̄a` (Axiom 3 at schema (a, b, ρ))
  have flipX : dp.P.binary (.inl ⟨a, ρ, b⟩) (.inl ⟨b, σᶜ, a⟩) =
      dp.P.binary (.inl ⟨b, ρᶜ, a⟩) (.inl ⟨b, σᶜ, a⟩) :=
    ax3 a b ρ (.inl ⟨b, σᶜ, a⟩) (Ne.symm hXY') hY'X'
  have key := flipY.trans flipX
  rw [dp.axiom2 a b hab ρ σ, dp.axiom2 b a (Ne.symm hab) ρᶜ σᶜ] at key
  have cAB := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  have cQ := dp.Q.binary_complement hρσ
  have cQc := dp.Q.binary_complement (show ρᶜ ≠ σᶜ from compl_injective.ne hρσ)
  simp only [alt] at hp
  have hkey : (dp.Q.binary ρ σ - dp.Q.binary σᶜ ρᶜ) *
      (2 * dp.P.binary (Sum.inr a) (Sum.inr b) - 1) = 0 := by
    linear_combination key -
      dp.P.binary (Sum.inr b) (Sum.inr a) * cQ +
      dp.P.binary (Sum.inr b) (Sum.inr a) * cQc +
      (dp.Q.binary ρ σ - dp.Q.binary σᶜ ρᶜ) * cAB
  rcases mul_eq_zero.mp hkey with h0 | h0
  · linarith
  · exact absurd (by linarith : dp.P.binary (Sum.inr a) (Sum.inr b) = 1 / 2) hp

/-- Under a global binary ratio scale for `Q`, Lemma 9 pins `v(ρ)·v(ρ̄)` to a
    constant — the source of the `φ(ρ)φ(ρ̄) = constant` clause of the §3.D.3
    decomposition (p. 89). -/
theorem v_mul_v_compl_const {v : E → ℝ}
    (hv : dp.Q.BinaryRatioScaleOn Set.univ v) (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) (ρ σ : E) :
    v ρ * v ρᶜ = v σ * v σᶜ := by
  obtain ⟨hpos, hrule⟩ := hv
  rcases eq_or_ne ρ σ with rfl | hρσ
  · rfl
  have h9 := q_compl_compl ax3 ax4 ρ σ
  rw [hrule ρ trivial σ trivial hρσ,
      hrule σᶜ trivial ρᶜ trivial (compl_injective.ne (Ne.symm hρσ))] at h9
  exact ((frac_eq_frac (hpos ρ trivial) (hpos σ trivial) (hpos σᶜ trivial)
    (hpos ρᶜ trivial)).mp h9).trans (mul_comm _ _)

/-- An event indifferent to its own complement: membership in Luce's class
    `C(½)` (Lemma 11, p. 85). -/
def Neutral (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  dp.Q.binary ρ ρᶜ = 1 / 2

/-- An event deemed more likely than its complement: Luce's class `C(1)`. -/
def Favorable (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  1 / 2 < dp.Q.binary ρ ρᶜ

/-- An event deemed less likely than its complement: Luce's class `C(0)`. -/
def Unfavorable (dp : DecomposablePreference A E) (ρ : E) : Prop :=
  dp.Q.binary ρ ρᶜ < 1 / 2

/-- Every event is unfavorable, neutral, or favorable. -/
theorem unfavorable_or_neutral_or_favorable (dp : DecomposablePreference A E)
    (ρ : E) : Unfavorable dp ρ ∨ Neutral dp ρ ∨ Favorable dp ρ :=
  lt_trichotomy _ _

/-- An event is neutral iff its complement is. -/
theorem neutral_compl_iff [Nontrivial E] (ρ : E) :
    Neutral dp ρᶜ ↔ Neutral dp ρ := by
  have hc := dp.Q.binary_complement (show ρ ≠ ρᶜ from (compl_ne_self (a := ρ)).symm)
  unfold Neutral
  rw [compl_compl]
  constructor <;> intro h <;> linarith

/-- An event is favorable iff its complement is unfavorable. -/
theorem favorable_iff_unfavorable_compl [Nontrivial E] (ρ : E) :
    Favorable dp ρ ↔ Unfavorable dp ρᶜ := by
  have hc := dp.Q.binary_complement (show ρ ≠ ρᶜ from (compl_ne_self (a := ρ)).symm)
  unfold Favorable Unfavorable
  rw [compl_compl]
  constructor <;> intro h <;> linarith

private lemma v_eq_v_compl_of_neutral [Nontrivial E] {v : E → ℝ}
    (hpos : ∀ x ∈ Set.univ, 0 < v x)
    (hrule : ∀ x ∈ Set.univ, ∀ y ∈ Set.univ, x ≠ y →
      dp.Q.binary x y = v x / (v x + v y))
    {ρ : E} (hρ : Neutral dp ρ) : v ρ = v ρᶜ := by
  have h := hρ
  unfold Neutral at h
  rw [hrule ρ trivial ρᶜ trivial ((compl_ne_self (a := ρ)).symm)] at h
  have p1 := hpos ρ trivial
  have p2 := hpos ρᶜ trivial
  rw [div_eq_iff (show v ρ + v ρᶜ ≠ 0 by linarith)] at h
  linarith

/-- Two distinct neutral events are indifferent: `Q(ρ, σ) = ½`. This is the
    first clause of Lemma 10 (p. 84) — "if ρ ∼ ρ̄ and σ ∼ σ̄, then ρ ∼ σ" —
    derived here from the ratio scale and Lemma 9 rather than via Luce's
    Theorem 11. Distinctness is required: `Q(ρ, ρ) = 1`. -/
theorem neutral_indifferent [Nontrivial E] {v : E → ℝ}
    (hv : dp.Q.BinaryRatioScaleOn Set.univ v) (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) {ρ σ : E} (hρ : Neutral dp ρ)
    (hσ : Neutral dp σ) (hρσ : ρ ≠ σ) : dp.Q.binary ρ σ = 1 / 2 := by
  obtain ⟨hpos, hrule⟩ := hv
  have hconst := v_mul_v_compl_const ⟨hpos, hrule⟩ ax3 ax4 ρ σ
  rw [← v_eq_v_compl_of_neutral hpos hrule hρ,
      ← v_eq_v_compl_of_neutral hpos hrule hσ] at hconst
  have p1 := hpos ρ trivial
  have p2 := hpos σ trivial
  have hvv : v ρ = v σ := by
    rcases mul_self_eq_mul_self_iff.mp hconst with h | h
    · exact h
    · linarith
  rw [hrule ρ trivial σ trivial hρσ, hvv,
      div_eq_iff (show v σ + v σ ≠ 0 by linarith)]
  ring

/-- Favorable events are preferred to unfavorable ones: the between-class
    ordering `C(1) > C(0)` of the three-class picture (§3.C.2, p. 85),
    under a global ratio scale for `Q`. -/
theorem favorable_gt_unfavorable [Nontrivial E] {v : E → ℝ}
    (hv : dp.Q.BinaryRatioScaleOn Set.univ v) (ax3 : Complementation dp)
    (ax4 : NontrivialPreference dp) {ρ σ : E} (hρ : Favorable dp ρ)
    (hσ : Unfavorable dp σ) : 1 / 2 < dp.Q.binary ρ σ := by
  have hρσ : ρ ≠ σ := by
    rintro rfl
    unfold Favorable at hρ
    unfold Unfavorable at hσ
    linarith
  obtain ⟨hpos, hrule⟩ := hv
  have p1 := hpos ρ trivial
  have p2 := hpos ρᶜ trivial
  have p3 := hpos σ trivial
  have p4 := hpos σᶜ trivial
  -- favorable: v ρ̄ < v ρ; unfavorable: v σ < v σ̄
  have h1 : v ρᶜ < v ρ := by
    have h := hρ
    unfold Favorable at h
    rw [hrule ρ trivial ρᶜ trivial ((compl_ne_self (a := ρ)).symm),
        lt_div_iff₀ (by linarith)] at h
    linarith
  have h2 : v σ < v σᶜ := by
    have h := hσ
    unfold Unfavorable at h
    rw [hrule σ trivial σᶜ trivial ((compl_ne_self (a := σ)).symm),
        div_lt_iff₀ (by linarith)] at h
    linarith
  have hconst := v_mul_v_compl_const ⟨hpos, hrule⟩ ax3 ax4 ρ σ
  -- v ρ² > v ρ · v ρ̄ = v σ · v σ̄ > v σ², hence v σ < v ρ
  have hvv : v σ < v ρ := by nlinarith
  rw [hrule ρ trivial σ trivial hρσ, lt_div_iff₀ (by linarith)]
  linarith

/-- **Theorem 14** (p. 89): with Axiom 3, `P(a,b) = P(d,c) = 1`, and a local
    ratio scale over the six gambles involved, the scale satisfies
    `v(aρb)·v(dρ̄c) = v(aσb)·v(dσ̄c)`. Together with Theorem 13 this is what
    "suggests that `v` may be of the form `v(aρb) = w(a,b)·φ(ρ)`" (§3.D.3). -/
theorem theorem14 [Nontrivial E] (ax3 : Complementation dp)
    {a b c d : A} {ρ σ : E} {v : Alternative A E → ℝ}
    (hab : a ≠ b) (hcd : c ≠ d) (hρσ : ρ ≠ σ) (hacbd : ¬(a = c ∧ b = d))
    (ha1 : dp.alt a b = 1) (hd1 : dp.alt d c = 1)
    (hv : dp.P.BinaryRatioScaleOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩,
        .inl ⟨d, ρᶜ, c⟩, .inl ⟨d, σᶜ, c⟩} v) :
    v (.inl ⟨a, ρ, b⟩) * v (.inl ⟨d, ρᶜ, c⟩) =
      v (.inl ⟨a, σ, b⟩) * v (.inl ⟨d, σᶜ, c⟩) := by
  obtain ⟨hpos, hrule⟩ := hv
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  have p5 := hpos (Sum.inl ⟨d, ρᶜ, c⟩) (by simp)
  have p6 := hpos (Sum.inl ⟨d, σᶜ, c⟩) (by simp)
  -- Axiom 3 transfers the scale across the complement relabeling,
  -- witnessed against the third gamble aρb
  have hρc : v (.inl ⟨c, ρ, d⟩) = v (.inl ⟨d, ρᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, ρᶜ, c⟩ := by
      simp [(compl_ne_self (a := ρ)).symm]
    have e := ax3 c d ρ (.inl ⟨a, ρ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (frac_eq_frac p3 p1 p5 p1).mp e
    exact mul_right_cancel₀ (ne_of_gt p1) this
  have hσc : v (.inl ⟨c, σ, d⟩) = v (.inl ⟨d, σᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, σᶜ, c⟩ := by
      simp [(compl_ne_self (a := σ)).symm]
    have e := ax3 c d σ (.inl ⟨a, σ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (frac_eq_frac p4 p2 p6 p2).mp e
    exact mul_right_cancel₀ (ne_of_gt p2) this
  -- both same-outcome comparisons reduce to Q(ρ, σ)
  have hcd0 : dp.alt c d = 0 := by
    have hc := dp.P.binary_complement
      (show (Sum.inr c : Alternative A E) ≠ Sum.inr d by simpa using hcd)
    simp only [alt] at hd1 ⊢
    linarith
  have e2 : dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ = dp.Q.binary σ ρ := by
    simp only [gam, alt] at hcd0 hd1 ⊢
    rw [dp.axiom2 c d hcd ρ σ, hcd0, hd1]
    ring
  have h34 : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
    simpa using hρσ
  have e2' : dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ = dp.Q.binary ρ σ := by
    have hPc : dp.gam ⟨c, ρ, d⟩ ⟨c, σ, d⟩ + dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ = 1 := by
      simpa [gam] using dp.P.binary_complement h34
    have hQc := dp.Q.binary_complement hρσ
    linarith
  have e1 : dp.gam ⟨a, ρ, b⟩ ⟨a, σ, b⟩ = dp.gam ⟨c, σ, d⟩ ⟨c, ρ, d⟩ := by
    rw [gam_of_alt_eq_one hab ha1, e2']
  have h12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  simp only [gam] at e1
  rw [hrule _ (by simp) _ (by simp) h12,
      hrule _ (by simp) _ (by simp) (Ne.symm h34)] at e1
  have hcross := (frac_eq_frac p1 p2 p4 p3).mp e1
  -- v(aρb)·v(cρd) = v(cσd)·v(aσb); transfer via Axiom 3
  rw [hρc, hσc] at hcross
  linarith [hcross, mul_comm (v (.inl ⟨d, σᶜ, c⟩)) (v (.inl ⟨a, σ, b⟩))]

end BooleanEvents

/-- The observable content of the §3.D.3 suggested factoring
    `v(aρb) = w(a,b)·φ(ρ)` (pp. 89–90): between gambles on the *same* event
    the event weight cancels, so binary choice follows the Luce rule on the
    outcome weights alone — "the step function described in theorem 13 can
    have only one step intermediate between 0 and 1" (p. 90). Luce offers the
    factoring as a hypothesis consistent with Theorems 13–14, not a theorem;
    accordingly it enters here as a hypothesis. -/
theorem gam_of_factored {S : Set (Gamble A E)} {v : Alternative A E → ℝ}
    {w : A → A → ℝ} {φ : E → ℝ}
    (hv : dp.P.BinaryRatioScaleOn (Sum.inl '' S) v) (hφ : ∀ τ, 0 < φ τ)
    (hfac : ∀ x y τ, (⟨x, τ, y⟩ : Gamble A E) ∈ S →
      v (.inl ⟨x, τ, y⟩) = w x y * φ τ)
    {a b c d : A} {ρ : E} (h₁ : (⟨a, ρ, b⟩ : Gamble A E) ∈ S)
    (h₂ : (⟨c, ρ, d⟩ : Gamble A E) ∈ S) (hacbd : ¬(a = c ∧ b = d)) :
    dp.gam ⟨a, ρ, b⟩ ⟨c, ρ, d⟩ = w a b / (w a b + w c d) := by
  obtain ⟨hpos, hrule⟩ := hv
  have m₁ : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ∈ Sum.inl '' S := ⟨_, h₁, rfl⟩
  have m₂ : (Sum.inl ⟨c, ρ, d⟩ : Alternative A E) ∈ Sum.inl '' S := ⟨_, h₂, rfl⟩
  have hg : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, ρ, d⟩ := by
    simpa using hacbd
  have hw1 : 0 < w a b := by
    have h := hpos _ m₁
    rw [hfac a b ρ h₁] at h
    by_contra hw
    push Not at hw
    nlinarith [hφ ρ]
  have hw2 : 0 < w c d := by
    have h := hpos _ m₂
    rw [hfac c d ρ h₂] at h
    by_contra hw
    push Not at hw
    nlinarith [hφ ρ]
  simp only [gam]
  rw [hrule _ m₁ _ m₂ hg, hfac a b ρ h₁, hfac c d ρ h₂,
      show w a b * φ ρ + w c d * φ ρ = (w a b + w c d) * φ ρ by ring,
      mul_div_mul_right _ _ (ne_of_gt (hφ ρ))]

end DecomposablePreference

end Luce1959
