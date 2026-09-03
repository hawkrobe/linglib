import Linglib.Core.Probability.Choice.RationalAction
import Linglib.Processing.Psychophysics.Psychophysics
import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Luce (1959): Individual Choice Behavior [luce-1959]

Formalizes §1.G (the jnd semiorder and the trace), §2.B's power-law Weber
ratio, and Chapter 3's utility theory.

Chapter 3 treats choices among gambles: `aρb` is "outcome `a` if chance event
`ρ` occurs, else `b`" (p. 78), and `S(A,E) = (A × E × A) ∪ A` collects
gambles and pure alternatives. A decomposable preference structure `⟨A, E, P, Q⟩` (Definition 5)
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
- The §3.B.2 chain: `lemma5` (the cubic constraint, p. 80), `eventPref_trans`
  (Lemma 6), `lemma7` (p. 81), and `atMostThreeClasses` — Lemma 8/Theorem 10
  as a four-event pigeonhole. `theorem11` (p. 82): `Q` is constant across
  `∼`-classes; with Lemma 9 it yields both clauses of Lemma 10
  (`neutral_indifferent`, `neutral_of_indiff_neutral`, p. 84).
- `theorem12` (p. 84): given Axioms 3–5 (`HasNeutralEvent` is Axiom 5) and
  nondegeneracy, exactly three classes — Luce's `C(1)`, `C(½)`, `C(0)`
  (`atLeastThreeClasses` is Lemma 11, p. 85).
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

Axiom 1 lives in the structure (`axiom1P`/`axiom1Q`, in
`ChoiceFn.HasChoiceAxiom`'s two-clause form) exactly as Definition 5 demands;
only the §3.C additional axioms and Theorem 10's nondegeneracy enter as
per-theorem hypotheses, as in the book. The three-class theorems are stated
representative-wise — among any four events two are equi-likely
(`atMostThreeClasses`); three pairwise non-equivalent events to one of which
every event is equivalent (`theorem12`) — avoiding quotient machinery; a
`Setoid`-packaged corollary is natural future work. The three-class regime
forces perfect discrimination `Q ∈ {0, 1}` between extreme classes, which is
exactly what `HasChoiceAxiom`'s deletion clause (and no globally positive
ratio scale) tolerates.
-/

namespace Luce1959

open Core

/-!
### §1.G: Just noticeable differences and the trace (pp. 34–37)

A jnd threshold `π ∈ (1/2, 1)` splits pairwise choice into a
discriminable-preference relation `L(π)` and an indistinguishability relation
`I(π)` (Definition 3, p. 34). Given the positive ratio scale delivered by
Theorem 4, the pair satisfies Luce's semiorder axioms (Theorem 5, p. 35) —
trichotomy, I-reflexivity, the interval condition, and no-sandwiching — and
the trace ordering (Definition 4, p. 37) is a weak order coinciding with the
ratio-scale order (Theorem 6, p. 37).
-/

section JustNoticeableDifferences

variable {A : Type*}

/-- The `L(π)` relation (Definition 3, p. 34): `x L(π) y` iff
    `P(x, {x,y}) > π` — `x` is **discriminably preferred** to `y` at
    threshold `π`, for `1/2 < π < 1`. -/
def jndL (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  thr < pairwiseProb v x y

/-- The `I(π)` relation (Definition 3, p. 34): `x I(π) y` iff
    `1 - π ≤ P(x, {x,y}) ≤ π` — `x` and `y` are **indistinguishable** at
    threshold `π`. -/
def jndI (v : A → ℝ) (thr : ℝ) (x y : A) : Prop :=
  1 - thr ≤ pairwiseProb v x y ∧ pairwiseProb v x y ≤ thr

/-- I(π) is symmetric: if `x` and `y` are indistinguishable, so are `y` and
    `x`. -/
theorem jndI_symm (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ) (x y : A)
    (h : jndI v thr x y) : jndI v thr y x := by
  simp only [jndI] at *
  have hc := pairwiseProb_complement (hv x) (hv y)
  constructor <;> linarith [h.1, h.2]

/-- **I-reflexivity**: `x I(π) x`. -/
theorem jndI_refl (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x : A) :
    jndI v thr x x := by
  simp only [jndI, pairwiseProb_self (hv x)]
  constructor <;> linarith

/-- **Trichotomy**: for any `x, y`, exactly one of `xLy`, `yLx`, or `xIy`
    holds. -/
theorem jnd_trichotomy (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y : A) :
    (jndL v thr x y ∧ ¬jndL v thr y x ∧ ¬jndI v thr x y) ∨
    (jndL v thr y x ∧ ¬jndL v thr x y ∧ ¬jndI v thr x y) ∨
    (jndI v thr x y ∧ ¬jndL v thr x y ∧ ¬jndL v thr y x) := by
  have hc := pairwiseProb_complement (hv x) (hv y)
  unfold jndL jndI
  by_cases h₁ : thr < pairwiseProb v x y
  · left; exact ⟨h₁, fun h => by linarith, fun ⟨_, h⟩ => by linarith⟩
  · push Not at h₁
    by_cases h₂ : thr < pairwiseProb v y x
    · right; left; exact ⟨h₂, fun h => by linarith, fun ⟨h, _⟩ => by linarith⟩
    · push Not at h₂
      right; right; exact ⟨⟨by linarith, h₁⟩, fun h => by linarith, fun h => by linarith⟩

/-- **Interval condition**: `xLy ∧ yIz ∧ zLw → xLw`. -/
theorem jndL_interval (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (_hthr_lower : 1 / 2 < thr) (_hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndI v thr y z) (hzw : jndL v thr z w) :
    jndL v thr x w := by
  simp only [jndL, jndI, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z; have hvw := hv w
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  obtain ⟨hyz_lo, _⟩ := hyz
  rw [le_div_iff₀ (add_pos hvy hvz)] at hyz_lo
  rw [lt_div_iff₀ (add_pos hvz hvw)] at hzw
  rw [lt_div_iff₀ (add_pos hvx hvw)]
  -- hxy: thr * v(y) < (1-thr) * v(x)
  -- hyz_lo: (1-thr) * v(z) ≤ thr * v(y)
  -- hzw: thr * v(w) < (1-thr) * v(z)
  -- Chain: thr * v(w) < (1-thr) * v(z) ≤ thr * v(y) < (1-thr) * v(x)
  linarith

/-- **No sandwiching**: `xLy ∧ yLz → ¬(xIw ∧ wIz)` — no `w` can be
    indistinguishable from both endpoints of a discriminable chain. -/
theorem jndL_no_sandwich (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z w : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    ¬(jndI v thr x w ∧ jndI v thr w z) := by
  intro ⟨hxw, hwz⟩
  simp only [jndL, jndI, pairwiseProb] at *
  have hvx := hv x; have hvy := hv y; have hvz := hv z; have hvw := hv w
  rw [lt_div_iff₀ (add_pos hvx hvy)] at hxy
  rw [lt_div_iff₀ (add_pos hvy hvz)] at hyz
  obtain ⟨hxw_lo, hxw_hi⟩ := hxw
  rw [le_div_iff₀ (add_pos hvx hvw)] at hxw_lo
  rw [div_le_iff₀ (add_pos hvx hvw)] at hxw_hi
  obtain ⟨hwz_lo, hwz_hi⟩ := hwz
  rw [le_div_iff₀ (add_pos hvw hvz)] at hwz_lo
  rw [div_le_iff₀ (add_pos hvw hvz)] at hwz_hi
  nlinarith [mul_le_mul_of_nonneg_right hxw_hi (le_of_lt hvw),
             mul_le_mul_of_nonneg_right hwz_hi (le_of_lt hvx),
             mul_lt_mul_of_pos_right hxy (hv z),
             mul_lt_mul_of_pos_right hyz (hv x)]

/-- **L-transitivity**: `xLy ∧ yLz → xLz`. Not one of the semiorder axioms —
    it follows from the interval condition instantiated at `z := y`, via
    I-reflexivity. -/
theorem jndL_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1) (x y z : A)
    (hxy : jndL v thr x y) (hyz : jndL v thr y z) :
    jndL v thr x z :=
  jndL_interval v hv thr hthr_lower hthr_upper x y y z hxy
    (jndI_refl v hv thr hthr_lower hthr_upper y) hyz

/-- The trace relation (Definition 4, p. 37): `x ≥_T y` iff
    `P(x, z) ≥ P(y, z)` for all `z` — dominance in every pairwise comparison
    against a common reference. -/
def traceGe (v : A → ℝ) (x y : A) : Prop :=
  ∀ z : A, pairwiseProb v y z ≤ pairwiseProb v x z

/-- **Theorem 6**: the trace relation is equivalent to the scale ordering
    `v(y) ≤ v(x)`. -/
theorem trace_iff_scale_ge (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ↔ v y ≤ v x := by
  simp only [traceGe]
  constructor
  · intro h
    have := h y
    rwa [pairwiseProb_mono_iff (hv x) (hv y) (hv y)] at this
  · intro hle z
    rwa [pairwiseProb_mono_iff (hv x) (hv y) (hv z)]

/-- Corollary: `x ≥_T y` iff `P(x, y) ≥ 1/2`. -/
theorem trace_iff_pairwiseProb_ge_half (v : A → ℝ) (hv : ∀ a : A, 0 < v a)
    (x y : A) :
    traceGe v x y ↔ 1 / 2 ≤ pairwiseProb v x y := by
  rw [trace_iff_scale_ge v hv, pairwiseProb_ge_half_iff (hv x) (hv y)]

/-- The trace is reflexive: `x ≥_T x`. -/
theorem traceGe_refl (v : A → ℝ) (x : A) : traceGe v x x :=
  λ _ => le_refl _

/-- The trace is transitive: `x ≥_T y ∧ y ≥_T z → x ≥_T z`. -/
theorem traceGe_trans (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y z : A)
    (hxy : traceGe v x y) (hyz : traceGe v y z) :
    traceGe v x z := by
  rw [trace_iff_scale_ge v hv] at *
  linarith

/-- The trace is total: for any `x, y`, either `x ≥_T y` or `y ≥_T x`.
    With `traceGe_refl` and `traceGe_trans`, the trace is a **weak order**
    (total preorder). -/
theorem traceGe_total (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (x y : A) :
    traceGe v x y ∨ traceGe v y x := by
  rw [trace_iff_scale_ge v hv, trace_iff_scale_ge v hv]
  exact le_total (v y) (v x)

/-- The trace agrees with L: if `xLy` for any `π`, then `x ≥_T y`. -/
theorem traceGe_of_jndL (v : A → ℝ) (hv : ∀ a : A, 0 < v a) (thr : ℝ)
    (hthr : 1 / 2 < thr) (x y : A) (h : jndL v thr x y) :
    traceGe v x y := by
  rw [trace_iff_scale_ge v hv]
  rw [jndL, pairwiseProb] at h
  have hD := add_pos (hv x) (hv y)
  have := (lt_div_iff₀ hD).mp h
  nlinarith

end JustNoticeableDifferences

/-!
### §2.B: The power law and Weber's law (pp. 42–44)

For the power scale `v(s) = sⁿ`, [luce-1959] derives the linear
generalization of Weber's law: the just-noticeable intensity ratio at
threshold `π` is `(π/(1−π))^(1/n)`. `stevens_jndL_intensity_ratio` is the
`C = 0` inequality form, stated over `StevensScale` from
`Processing.Psychophysics`.
-/

section PowerLawWeber

open Real

/-- **Weber ratio from the jnd** (§2.B): if `s₁` is discriminably preferred
    to `s₂` at threshold `π` under a power scale with exponent `n`, the
    intensity ratio `s₁/s₂` exceeds `(π/(1-π))^(1/n)`. -/
theorem stevens_jndL_intensity_ratio (σ : StevensScale) (thr : ℝ)
    (hthr_lower : 1 / 2 < thr) (hthr_upper : thr < 1)
    {s₁ s₂ : ℝ} (h₁ : 0 < s₁) (h₂ : 0 < s₂)
    (hL : jndL (· ^ σ.n) thr s₁ s₂) :
    (thr / (1 - thr)) ^ (1 / σ.n) < s₁ / s₂ := by
  simp only [jndL, pairwiseProb] at hL
  have hp₁ : 0 < s₁ ^ σ.n := rpow_pos_of_pos h₁ σ.n
  have hp₂ : 0 < s₂ ^ σ.n := rpow_pos_of_pos h₂ σ.n
  have hd : 0 < s₁ ^ σ.n + s₂ ^ σ.n := add_pos hp₁ hp₂
  rw [lt_div_iff₀ hd] at hL
  have h1mt : 0 < 1 - thr := by linarith
  have hthr_ratio_pos : 0 < thr / (1 - thr) := div_pos (by linarith) h1mt
  have h_ratio : thr / (1 - thr) < (s₁ / s₂) ^ σ.n := by
    rw [div_rpow (le_of_lt h₁) (le_of_lt h₂), div_lt_div_iff₀ h1mt hp₂]; nlinarith
  have h5 := rpow_lt_rpow (le_of_lt hthr_ratio_pos) h_ratio (div_pos one_pos σ.hn_pos)
  rw [← rpow_mul (le_of_lt (div_pos h₁ h₂)), mul_one_div_cancel (ne_of_gt σ.hn_pos),
    rpow_one] at h5
  exact h5

end PowerLawWeber

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
    families on ≤3-element subsets (Axiom 1 enters as the `axiom1P`/`axiom1Q`
    fields, in `ChoiceFn.HasChoiceAxiom`'s two-clause form), and
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
  /-- `P` satisfies Luce's Axiom 1, per Definition 5. -/
  axiom1P : P.HasChoiceAxiom
  /-- `Q` satisfies Luce's Axiom 1, per Definition 5. -/
  axiom1Q : Q.HasChoiceAxiom

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

/-! ### Definition 6: the subjective likelihood order -/

/-- Definition 6 (p. 79): `ρ ≿ σ` iff `Q(ρ, σ) ≥ ½` — `ρ` is deemed at least
    as likely as `σ`. -/
def EventPref (dp : DecomposablePreference A E) (ρ σ : E) : Prop :=
  1 / 2 ≤ dp.Q.binary ρ σ

/-- Subjective equi-likelihood `ρ ∼ σ`: the symmetric part of Definition 6's
    `≿`. On distinct events this is `Q(ρ, σ) = ½` (`eventIndiff_iff_eq_half`);
    on the diagonal it holds since `Q(ρ, ρ) = 1`. -/
def EventIndiff (dp : DecomposablePreference A E) (ρ σ : E) : Prop :=
  EventPref dp ρ σ ∧ EventPref dp σ ρ

theorem eventIndiff_refl (dp : DecomposablePreference A E) (ρ : E) :
    EventIndiff dp ρ ρ := by
  unfold EventIndiff EventPref
  rw [dp.Q.binary_self]
  norm_num

theorem EventIndiff.symm {ρ σ : E} (h : EventIndiff dp ρ σ) :
    EventIndiff dp σ ρ := ⟨h.2, h.1⟩

theorem eventIndiff_iff_eq_half {ρ σ : E} (hne : ρ ≠ σ) :
    EventIndiff dp ρ σ ↔ dp.Q.binary ρ σ = 1 / 2 := by
  have hc := dp.Q.binary_complement hne
  unfold EventIndiff EventPref
  constructor
  · rintro ⟨h1, h2⟩; linarith
  · intro h; exact ⟨by linarith, by linarith⟩

theorem ne_of_not_eventIndiff {ρ σ : E} (h : ¬EventIndiff dp ρ σ) : ρ ≠ σ :=
  λ he => h (he ▸ eventIndiff_refl dp ρ)

/-- Totality of `≿` in strict form: a non-equi-likely pair is strictly
    ordered one way or the other. -/
theorem gt_half_or_of_not_eventIndiff {ρ σ : E} (h : ¬EventIndiff dp ρ σ) :
    1 / 2 < dp.Q.binary ρ σ ∨ 1 / 2 < dp.Q.binary σ ρ := by
  have hne := ne_of_not_eventIndiff h
  have hc := dp.Q.binary_complement hne
  by_contra hcon
  push Not at hcon
  exact h ⟨show 1 / 2 ≤ _ by linarith [hcon.1, hcon.2],
    show 1 / 2 ≤ _ by linarith [hcon.1, hcon.2]⟩

/-- The nondegeneracy hypothesis of **Theorem 10** (p. 80): some genuine pair
    of alternatives is discriminated imperfectly and asymmetrically,
    `P(a, b) ∉ {0, ½, 1}`. -/
def Nondegenerate (dp : DecomposablePreference A E) : Prop :=
  ∃ a b : A, a ≠ b ∧ dp.alt a b ≠ 0 ∧ dp.alt a b ≠ 1 / 2 ∧ dp.alt a b ≠ 1

private lemma alt_pos_pos {a b : A} (hab : a ≠ b) (h0 : dp.alt a b ≠ 0)
    (h1 : dp.alt a b ≠ 1) :
    0 < dp.alt a b ∧ 0 < dp.alt b a ∧ dp.alt a b + dp.alt b a = 1 := by
  have hc : dp.alt a b + dp.alt b a = 1 := dp.P.binary_complement
    (show (Sum.inr a : Alternative A E) ≠ Sum.inr b by simpa using hab)
  have hp0 : 0 ≤ dp.alt a b := dp.P.binary_nonneg _ _
  have hq0 : 0 ≤ dp.alt b a := dp.P.binary_nonneg _ _
  refine ⟨lt_of_le_of_ne hp0 (Ne.symm h0), ?_, hc⟩
  rcases eq_or_lt_of_le hq0 with heq | hlt
  · exact absurd (by linarith : dp.alt a b = 1) h1
  · exact hlt

private lemma mix_pos {p p' q : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < p' + (p - p') * q := by
  rcases eq_or_lt_of_le hq1 with rfl | hq
  · linarith
  · nlinarith [mul_pos hp' (show (0:ℝ) < 1 - q by linarith),
      mul_nonneg hp.le hq0]

private lemma mix_lt_one {p p' q : ℝ} (hp : 0 < p) (hp' : 0 < p')
    (hpp' : p + p' = 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    p' + (p - p') * q < 1 := by
  have h := mix_pos hp' hp hq0 hq1
  nlinarith [h]

/-- Axiom 2 in mixture-collapsed form: for a genuine outcome pair the gamble
    comparison is the `Q`-mixture `P(b,a) + [P(a,b) − P(b,a)]·Q(x, y)`. -/
private lemma gam_mix {a b : A} (hab : a ≠ b) {x y : E} (hxy : x ≠ y) :
    dp.gam ⟨a, x, b⟩ ⟨a, y, b⟩ =
      dp.alt b a + (dp.alt a b - dp.alt b a) * dp.Q.binary x y := by
  have hq := dp.Q.binary_complement hxy
  simp only [gam, alt]
  rw [dp.axiom2 a b hab x y,
      show dp.Q.binary y x = 1 - dp.Q.binary x y by linarith]
  ring

/-! ### The three-class theorems (§3.B.2) -/

/-- **Lemma 5** (p. 80), in denominator-cleared form: Luce's identity
    `(K+1){2[Q(ρ,σ)+Q(σ,τ)+Q(τ,ρ)] − 3} + K²[Q(ρ,σ)Q(σ,τ)Q(τ,ρ) −
    Q(ρ,τ)Q(τ,σ)Q(σ,ρ)] = 0`, `K = P(a,b)/P(b,a) − 1`, multiplied through by
    `P(b,a)²`. From Axiom 2 and Theorem 2 for the gamble triple
    `{aρb, aσb, aτb}`, whose pairwise discrimination is imperfect whenever
    `P(a,b) ∉ {0, 1}`. -/
theorem lemma5 {a b : A} (hab : a ≠ b)
    (h0 : dp.alt a b ≠ 0) (hhalf : dp.alt a b ≠ 1 / 2) (h1 : dp.alt a b ≠ 1)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ) :
    dp.alt a b * dp.alt b a *
        (2 * (dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3) +
      (dp.alt a b - dp.alt b a) ^ 2 *
        (dp.Q.binary ρ σ * dp.Q.binary σ τ * dp.Q.binary τ ρ -
          dp.Q.binary ρ τ * dp.Q.binary τ σ * dp.Q.binary σ ρ) = 0 := by
  obtain ⟨hpa, hpb, hsum⟩ := alt_pos_pos hab h0 h1
  have g12 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, σ, b⟩ := by
    simpa using hρσ
  have g23 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, τ, b⟩ := by
    simpa using hστ
  have g13 : (Sum.inl ⟨a, ρ, b⟩ : Alternative A E) ≠ Sum.inl ⟨a, τ, b⟩ := by
    simpa using hρτ
  have hbnds : ∀ x y : E, x ≠ y →
      0 < dp.P.binary (.inl ⟨a, x, b⟩) (.inl ⟨a, y, b⟩) ∧
        dp.P.binary (.inl ⟨a, x, b⟩) (.inl ⟨a, y, b⟩) < 1 := by
    intro x y hxy
    have hmix := gam_mix (dp := dp) hab hxy
    simp only [gam] at hmix
    rw [hmix]
    exact ⟨mix_pos hpa hpb (dp.Q.binary_nonneg x y) (dp.Q.binary_le_one x y),
      mix_lt_one hpa hpb hsum (dp.Q.binary_nonneg x y) (dp.Q.binary_le_one x y)⟩
  have himp : dp.P.ImperfectOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨a, τ, b⟩} := by
    intro x hx y hy hxy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | exact hbnds _ _ hρσ
      | exact hbnds _ _ hρσ.symm
      | exact hbnds _ _ hστ
      | exact hbnds _ _ hστ.symm
      | exact hbnds _ _ hρτ
      | exact hbnds _ _ hρτ.symm
  have hcyc := dp.axiom1P.binary_mul_cycle g12 g23 g13 himp
  have e12 := gam_mix (dp := dp) hab hρσ
  have e23 := gam_mix (dp := dp) hab hστ
  have e31 := gam_mix (dp := dp) hab hρτ.symm
  have e13 := gam_mix (dp := dp) hab hρτ
  have e32 := gam_mix (dp := dp) hab hστ.symm
  have e21 := gam_mix (dp := dp) hab hρσ.symm
  simp only [gam] at e12 e23 e31 e13 e32 e21
  rw [e12, e23, e31, e13, e32, e21] at hcyc
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary τ σ = 1 - dp.Q.binary σ τ := by
    linarith [dp.Q.binary_complement hστ]
  have f3 : dp.Q.binary ρ τ = 1 - dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  rw [f1, f2, f3] at hcyc ⊢
  have hΔ : dp.alt a b - dp.alt b a ≠ 0 := by
    intro h
    exact hhalf (by linarith)
  refine mul_left_cancel₀ hΔ ?_
  rw [mul_zero]
  linear_combination hcyc

/-- **Lemma 6** (p. 80): `≿` is transitive (with `gt_half_or_of_not_eventIndiff`
    totality, a weak ordering of `E`). -/
theorem eventPref_trans (hnd : Nondegenerate dp)
    {ρ σ τ : E} (h1 : EventPref dp ρ σ) (h2 : EventPref dp σ τ) :
    EventPref dp ρ τ := by
  rcases eq_or_ne ρ σ with rfl | hρσ
  · exact h2
  rcases eq_or_ne σ τ with rfl | hστ
  · exact h1
  rcases eq_or_ne ρ τ with rfl | hρτ
  · show 1 / 2 ≤ _
    rw [dp.Q.binary_self]
    norm_num
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  unfold EventPref at h1 h2 ⊢
  by_contra hcon
  push Not at hcon
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  have hq3 : 1 / 2 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary τ σ = 1 - dp.Q.binary σ τ := by
    linarith [dp.Q.binary_complement hστ]
  have f3 : dp.Q.binary ρ τ = 1 - dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  rw [f1, f2, f3] at h5
  set q1 := dp.Q.binary ρ σ with hq1_def
  set q2 := dp.Q.binary σ τ with hq2_def
  set q3 := dp.Q.binary τ ρ with hq3_def
  have hb1 := dp.Q.binary_le_one ρ σ
  have hb2 := dp.Q.binary_le_one σ τ
  have hb3 := dp.Q.binary_le_one τ ρ
  have s0 : (0:ℝ) ≤ (1 - q2) * (1 - q3) :=
    mul_nonneg (by linarith) (by linarith)
  have s1 : (1 - q1) * ((1 - q2) * (1 - q3)) ≤ q1 * ((1 - q2) * (1 - q3)) :=
    mul_le_mul_of_nonneg_right (by linarith) s0
  have s2 : q1 * ((1 - q2) * (1 - q3)) ≤ q1 * (q2 * (1 - q3)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0:ℝ) ≤ q1)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have s3 : q1 * (q2 * (1 - q3)) ≤ q1 * (q2 * q3) := by
    refine mul_le_mul_of_nonneg_left ?_ (by linarith : (0:ℝ) ≤ q1)
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0:ℝ) < 2 * (q1 + q2 + q3) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (show (0:ℝ) ≤ q1 * q2 * q3 - (1 - q3) * (1 - q2) * (1 - q1) by
        nlinarith [s1, s2, s3])]

/-- `∼` is transitive: with `eventIndiff_refl` and `EventIndiff.symm`, an
    equivalence relation (the content of **Theorem 10**'s first clause). -/
theorem eventIndiff_trans (hnd : Nondegenerate dp)
    {ρ σ τ : E} (h1 : EventIndiff dp ρ σ) (h2 : EventIndiff dp σ τ) :
    EventIndiff dp ρ τ :=
  ⟨eventPref_trans hnd h1.1 h2.1, eventPref_trans hnd h2.2 h1.2⟩

private lemma cubic_of_sum_eq {x y z : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hz : 0 < z) (h : x / (x + y) + y / (y + z) + z / (z + x) = 3 / 2) :
    (x - y) * (y - z) * (x - z) = 0 := by
  have h1 : x + y ≠ 0 := ne_of_gt (add_pos hx hy)
  have h2 : y + z ≠ 0 := ne_of_gt (add_pos hy hz)
  have h3 : z + x ≠ 0 := ne_of_gt (add_pos hz hx)
  field_simp at h
  linear_combination h

/-- **Lemma 7** (p. 81): three distinct events, pairwise imperfectly
    discriminated, cannot lie in three distinct `∼`-classes. -/
theorem lemma7 (hnd : Nondegenerate dp) {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ)
    (hρτ : ρ ≠ τ) (himp : dp.Q.ImperfectOn {ρ, σ, τ}) :
    EventIndiff dp ρ σ ∨ EventIndiff dp σ τ ∨ EventIndiff dp ρ τ := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  have hcyc := dp.axiom1Q.binary_mul_cycle hρσ hστ hρτ himp
  have hzero : dp.alt a b * dp.alt b a *
      (2 * (dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3) = 0 := by
    linear_combination h5 - (dp.alt a b - dp.alt b a) ^ 2 * hcyc
  have hsum32 : dp.Q.binary ρ σ + dp.Q.binary σ τ + dp.Q.binary τ ρ = 3 / 2 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact absurd h' (ne_of_gt (mul_pos hpa hpb))
    · linarith
  obtain ⟨v, hpos, hrule⟩ :=
    dp.axiom1Q.binaryRatioScaleOn ⟨ρ, Finset.mem_insert_self ρ _⟩ himp
  have mρ : ρ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have mσ : σ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have mτ : τ ∈ (↑({ρ, σ, τ} : Finset E) : Set E) := by simp
  have pρ := hpos ρ mρ
  have pσ := hpos σ mσ
  have pτ := hpos τ mτ
  rw [hrule ρ mρ σ mσ hρσ, hrule σ mσ τ mτ hστ,
      hrule τ mτ ρ mρ (Ne.symm hρτ)] at hsum32
  simp only [pairwiseProb] at hsum32
  have key := cubic_of_sum_eq pρ pσ pτ hsum32
  rcases mul_eq_zero.mp key with h' | hρτ'
  · rcases mul_eq_zero.mp h' with hρσ' | hστ'
    · refine Or.inl ((eventIndiff_iff_eq_half hρσ).mpr ?_)
      rw [hrule ρ mρ σ mσ hρσ]
      exact (pairwiseProb_eq_half_iff pρ pσ).mpr (by linarith)
    · refine Or.inr (Or.inl ((eventIndiff_iff_eq_half hστ).mpr ?_))
      rw [hrule σ mσ τ mτ hστ]
      exact (pairwiseProb_eq_half_iff pσ pτ).mpr (by linarith)
  · refine Or.inr (Or.inr ((eventIndiff_iff_eq_half hρτ).mpr ?_))
    rw [hrule ρ mρ τ mτ hρτ]
    exact (pairwiseProb_eq_half_iff pρ pτ).mpr (by linarith)

private lemma boost (hnd : Nondegenerate dp)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ)
    (h1 : dp.Q.binary ρ σ = 1) (h2 : 1 / 2 < dp.Q.binary σ τ) :
    dp.Q.binary ρ τ = 1 := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  by_contra hne
  have hlt : dp.Q.binary ρ τ < 1 :=
    lt_of_le_of_ne (dp.Q.binary_le_one ρ τ) hne
  have hq3 : 0 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have hσρ : dp.Q.binary σ ρ = 0 := by
    linarith [dp.Q.binary_complement hρσ]
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  rw [h1, hσρ] at h5
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0:ℝ) < 2 * (1 + dp.Q.binary σ τ + dp.Q.binary τ ρ) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (mul_nonneg (mul_nonneg one_pos.le (dp.Q.binary_nonneg σ τ))
        (dp.Q.binary_nonneg τ ρ))]

private lemma boost' (hnd : Nondegenerate dp)
    {ρ σ τ : E} (hρσ : ρ ≠ σ) (hστ : σ ≠ τ) (hρτ : ρ ≠ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : dp.Q.binary σ τ = 1) :
    dp.Q.binary ρ τ = 1 := by
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  by_contra hne
  have hlt : dp.Q.binary ρ τ < 1 :=
    lt_of_le_of_ne (dp.Q.binary_le_one ρ τ) hne
  have hq3 : 0 < dp.Q.binary τ ρ := by
    linarith [dp.Q.binary_complement hρτ]
  have hτσ : dp.Q.binary τ σ = 0 := by
    linarith [dp.Q.binary_complement hστ]
  have h5 := lemma5 hab h0 hhalf hone hρσ hστ hρτ
  rw [h2, hτσ] at h5
  nlinarith [h5, mul_pos (mul_pos hpa hpb)
      (show (0:ℝ) < 2 * (dp.Q.binary ρ σ + 1 + dp.Q.binary τ ρ) - 3 by linarith),
    mul_nonneg (sq_nonneg (dp.alt a b - dp.alt b a))
      (mul_nonneg (mul_nonneg (dp.Q.binary_nonneg ρ σ) one_pos.le)
        (dp.Q.binary_nonneg τ ρ))]

private lemma no_strict_cycle (hnd : Nondegenerate dp) {ρ σ τ : E} (hρτ : ρ ≠ τ)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ)
    (h3 : 1 / 2 < dp.Q.binary τ ρ) : False := by
  have hle : EventPref dp ρ τ :=
    eventPref_trans hnd (show EventPref dp ρ σ from h1.le)
      (show EventPref dp σ τ from h2.le)
  have hc := dp.Q.binary_complement hρτ
  unfold EventPref at hle
  linarith

private lemma no_four_chain (hnd : Nondegenerate dp) {ρ σ τ ω : E}
    (nρσ : ¬EventIndiff dp ρ σ) (nρτ : ¬EventIndiff dp ρ τ)
    (nρω : ¬EventIndiff dp ρ ω) (nστ : ¬EventIndiff dp σ τ)
    (nτω : ¬EventIndiff dp τ ω)
    (h1 : 1 / 2 < dp.Q.binary ρ σ) (h2 : 1 / 2 < dp.Q.binary σ τ)
    (h3 : 1 / 2 < dp.Q.binary τ ω) : False := by
  have dρσ := ne_of_not_eventIndiff nρσ
  have dρτ := ne_of_not_eventIndiff nρτ
  have dρω := ne_of_not_eventIndiff nρω
  have dστ := ne_of_not_eventIndiff nστ
  have dτω := ne_of_not_eventIndiff nτω
  have hρτ : 1 / 2 < dp.Q.binary ρ τ := by
    have hle := eventPref_trans hnd (show EventPref dp ρ σ from h1.le)
      (show EventPref dp σ τ from h2.le)
    unfold EventPref at hle
    refine lt_of_le_of_ne hle (Ne.symm (λ he => nρτ ?_))
    exact (eventIndiff_iff_eq_half dρτ).mpr he
  have hQρτ : dp.Q.binary ρ τ = 1 := by
    by_cases hA : dp.Q.binary ρ σ = 1
    · exact boost hnd dρσ dστ dρτ hA h2
    by_cases hB : dp.Q.binary σ τ = 1
    · exact boost' hnd dρσ dστ dρτ h1 hB
    by_cases hC : dp.Q.binary ρ τ = 1
    · exact hC
    have core : ∀ u w : E, u ≠ w → 1 / 2 < dp.Q.binary u w →
        dp.Q.binary u w ≠ 1 →
        (0 < dp.Q.binary u w ∧ dp.Q.binary u w < 1) ∧
          0 < dp.Q.binary w u ∧ dp.Q.binary w u < 1 := by
      intro u w huw hgt hne1
      have hc := dp.Q.binary_complement huw
      have hlt := lt_of_le_of_ne (dp.Q.binary_le_one u w) hne1
      exact ⟨⟨by linarith, hlt⟩, by constructor <;> linarith⟩
    have himp : dp.Q.ImperfectOn {ρ, σ, τ} := by
      intro x hx y hy hxy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      · exact absurd rfl hxy
      · exact (core _ _ dρσ h1 hA).1
      · exact (core _ _ dρτ hρτ hC).1
      · exact (core _ _ dρσ h1 hA).2
      · exact absurd rfl hxy
      · exact (core _ _ dστ h2 hB).1
      · exact (core _ _ dρτ hρτ hC).2
      · exact (core _ _ dστ h2 hB).2
      · exact absurd rfl hxy
    rcases lemma7 hnd dρσ dστ dρτ himp with h | h | h
    · exact absurd h nρσ
    · exact absurd h nστ
    · exact absurd h nρτ
  have hQρω : dp.Q.binary ρ ω = 1 := boost hnd dρτ dτω dρω hQρτ h3
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have h5 := lemma5 hab h0 hhalf hone dρτ dτω dρω
  have hτρ : dp.Q.binary τ ρ = 0 := by
    linarith [dp.Q.binary_complement dρτ]
  have hωρ : dp.Q.binary ω ρ = 0 := by
    linarith [dp.Q.binary_complement dρω]
  rw [hQρτ, hτρ, hωρ] at h5
  have h5' : dp.alt a b * dp.alt b a * (2 * dp.Q.binary τ ω - 1) = 0 := by
    linear_combination h5
  have : dp.Q.binary τ ω = 1 / 2 := by
    rcases mul_eq_zero.mp h5' with h' | h'
    · exact absurd h' (ne_of_gt (mul_pos hpa hpb))
    · linarith
  exact nτω ((eventIndiff_iff_eq_half dτω).mpr this)

private lemma no_chain_insert (hnd : Nondegenerate dp) {a b c ω : E}
    (nab : ¬EventIndiff dp a b) (nac : ¬EventIndiff dp a c)
    (naω : ¬EventIndiff dp a ω) (nbc : ¬EventIndiff dp b c)
    (nbω : ¬EventIndiff dp b ω) (ncω : ¬EventIndiff dp c ω)
    (sab : 1 / 2 < dp.Q.binary a b) (sbc : 1 / 2 < dp.Q.binary b c) :
    False := by
  have N : ∀ {x y : E}, ¬EventIndiff dp x y → ¬EventIndiff dp y x :=
    λ n h => n h.symm
  rcases gt_half_or_of_not_eventIndiff naω with haω | hωa
  · rcases gt_half_or_of_not_eventIndiff nbω with hbω | hωb
    · rcases gt_half_or_of_not_eventIndiff ncω with hcω | hωc
      · exact no_four_chain hnd nab nac naω nbc ncω sab sbc hcω
      · exact no_four_chain hnd nab naω nac nbω (N ncω) sab hbω hωc
    · exact no_four_chain hnd naω nab nac (N nbω) nbc haω hωb sbc
  · exact no_four_chain hnd (N naω) (N nbω) (N ncω) nab nbc hωa sab sbc

/-- **Lemma 8** (p. 81) / the partition clause of **Theorem 10** (p. 80): in
    a nondegenerate decomposable preference structure, `∼` partitions the
    events into at most three classes — among any four events, two are
    subjectively equi-likely. -/
theorem atMostThreeClasses (hnd : Nondegenerate dp) (ρ σ τ ω : E) :
    EventIndiff dp ρ σ ∨ EventIndiff dp ρ τ ∨ EventIndiff dp ρ ω ∨
      EventIndiff dp σ τ ∨ EventIndiff dp σ ω ∨ EventIndiff dp τ ω := by
  by_contra hcon
  push Not at hcon
  obtain ⟨nρσ, nρτ, nρω, nστ, nσω, nτω⟩ := hcon
  have N : ∀ {x y : E}, ¬EventIndiff dp x y → ¬EventIndiff dp y x :=
    λ n h => n h.symm
  rcases gt_half_or_of_not_eventIndiff nρσ with h1 | h1'
  · rcases gt_half_or_of_not_eventIndiff nστ with h2 | h2'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd nρσ nρτ nρω nστ nσω nτω h1 h2
      · exact no_strict_cycle hnd (ne_of_not_eventIndiff nρτ) h1 h2 h3'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd nρτ nρσ nρω (N nστ) nτω nσω h3 h2'
      · exact no_chain_insert hnd (N nρτ) (N nστ) nτω nρσ nρω nσω h3' h1
  · rcases gt_half_or_of_not_eventIndiff nστ with h2 | h2'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_chain_insert hnd (N nρσ) nστ nσω nρτ nρω nτω h1' h3
      · exact no_chain_insert hnd nστ (N nρσ) nσω (N nρτ) nτω nρω h2 h3'
    · rcases gt_half_or_of_not_eventIndiff nρτ with h3 | h3'
      · exact no_strict_cycle hnd (ne_of_not_eventIndiff nστ) h1' h3 h2'
      · exact no_chain_insert hnd (N nστ) (N nρτ) nτω (N nρσ) nσω nρω h2' h1'

private lemma q_congr_left (hnd : Nondegenerate dp) {ρ ρ' σ : E}
    (h : EventIndiff dp ρ ρ') (hρσ : ρ ≠ σ) (hρ'σ : ρ' ≠ σ) :
    dp.Q.binary ρ' σ = dp.Q.binary ρ σ := by
  rcases eq_or_ne ρ ρ' with rfl | hρρ'
  · rfl
  obtain ⟨a, b, hab, h0, hhalf, hone⟩ := hnd
  obtain ⟨hpa, hpb, -⟩ := alt_pos_pos hab h0 hone
  have hhalf1 : dp.Q.binary ρ ρ' = 1 / 2 := (eventIndiff_iff_eq_half hρρ').mp h
  have hhalf2 : dp.Q.binary ρ' ρ = 1 / 2 := by
    linarith [dp.Q.binary_complement hρρ']
  have h5 := lemma5 hab h0 hhalf hone hρρ' hρ'σ hρσ
  have f1 : dp.Q.binary σ ρ = 1 - dp.Q.binary ρ σ := by
    linarith [dp.Q.binary_complement hρσ]
  have f2 : dp.Q.binary σ ρ' = 1 - dp.Q.binary ρ' σ := by
    linarith [dp.Q.binary_complement hρ'σ]
  rw [hhalf1, hhalf2, f1, f2] at h5
  have key : (2 * (dp.alt a b * dp.alt b a) +
      (dp.alt a b - dp.alt b a) ^ 2 / 2) *
      (dp.Q.binary ρ' σ - dp.Q.binary ρ σ) = 0 := by
    linear_combination h5
  rcases mul_eq_zero.mp key with h' | h'
  · nlinarith [mul_pos hpa hpb, sq_nonneg (dp.alt a b - dp.alt b a)]
  · linarith

/-- **Theorem 11** (p. 82): `Q` is constant across `∼`-classes — if `ρ ∼ ρ'`
    and `σ ∼ σ'` then `Q(ρ, σ) = Q(ρ', σ')`. Both comparisons must be genuine
    pairs: at `ρ' = σ'` the total-`ChoiceFn` diagonal `Q(ρ', ρ') = 1` breaks
    the unguarded claim, which Luce's `P(x, x) = ½` convention (p. 5) hides. -/
theorem theorem11 (hnd : Nondegenerate dp) {ρ ρ' σ σ' : E}
    (h1 : EventIndiff dp ρ ρ') (h2 : EventIndiff dp σ σ')
    (hρσ : ρ ≠ σ) (hρ'σ' : ρ' ≠ σ') :
    dp.Q.binary ρ σ = dp.Q.binary ρ' σ' := by
  rcases eq_or_ne ρ' σ with rfl | hρ'σ
  · have e1 := (eventIndiff_iff_eq_half hρσ).mp h1
    have e2 := (eventIndiff_iff_eq_half hρ'σ').mp h2
    rw [e1, e2]
  · have s1 : dp.Q.binary ρ' σ = dp.Q.binary ρ σ := q_congr_left hnd h1 hρσ hρ'σ
    have s2 : dp.Q.binary σ' ρ' = dp.Q.binary σ ρ' :=
      q_congr_left hnd h2 (Ne.symm hρ'σ) (Ne.symm hρ'σ')
    have c1 := dp.Q.binary_complement hρ'σ
    have c2 := dp.Q.binary_complement hρ'σ'
    linarith [s1, s2, c1, c2]

/-- **Theorem 13** (p. 86): if `P(a,b) = P(c,d) = 1` and "all pairwise
    discriminations in the set `T = {aρb, aσb, cρd, cσd}` are imperfect",
    then `P(aρb, cρd) = P(aσb, cσd)` — the step-function prediction of §3.D.
    The local ratio scale of Luce's proof is supplied by Theorem 3
    (`ChoiceFn.HasChoiceAxiom.binaryRatioScaleOn`). -/
theorem theorem13 {a b c d : A} {ρ σ : E}
    (hab : a ≠ b) (hcd : c ≠ d) (ha1 : dp.alt a b = 1) (hc1 : dp.alt c d = 1)
    (himp : dp.P.ImperfectOn
      {.inl ⟨a, ρ, b⟩, .inl ⟨a, σ, b⟩, .inl ⟨c, ρ, d⟩, .inl ⟨c, σ, d⟩}) :
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
  obtain ⟨v, hpos, hrule⟩ := dp.axiom1P.binaryRatioScaleOn
    ⟨_, Finset.mem_insert_self _ _⟩ himp
  have p1 := hpos (Sum.inl ⟨a, ρ, b⟩) (by simp)
  have p2 := hpos (Sum.inl ⟨a, σ, b⟩) (by simp)
  have p3 := hpos (Sum.inl ⟨c, ρ, d⟩) (by simp)
  have p4 := hpos (Sum.inl ⟨c, σ, d⟩) (by simp)
  simp only [gam] at e1 ⊢
  rw [hrule _ (by simp) _ (by simp) h12, hrule _ (by simp) _ (by simp) h34] at e1
  rw [hrule _ (by simp) _ (by simp) h13, hrule _ (by simp) _ (by simp) h24,
      pairwiseProb_eq_pairwiseProb_iff p1 p3 p2 p4]
  exact ((pairwiseProb_eq_pairwiseProb_iff p1 p2 p3 p4).mp e1).trans (mul_comm _ _)

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
  exact ((pairwiseProb_eq_pairwiseProb_iff (hpos ρ trivial) (hpos σ trivial)
    (hpos σᶜ trivial) (hpos ρᶜ trivial)).mp h9).trans (mul_comm _ _)

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

/-- Two distinct neutral events are indifferent — the first clause of
    **Lemma 10** (p. 84), "if ρ ∼ ρ̄ and σ ∼ σ̄, then ρ ∼ σ", via Theorem 11
    and Lemma 9. Distinctness is required: `Q(ρ, ρ) = 1`. -/
theorem neutral_indifferent [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) {ρ σ : E}
    (hρ : Neutral dp ρ) (hσ : Neutral dp σ) (hρσ : ρ ≠ σ) :
    dp.Q.binary ρ σ = 1 / 2 := by
  have iρ : EventIndiff dp ρ ρᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mpr hρ
  have iσ : EventIndiff dp σ σᶜ :=
    (eventIndiff_iff_eq_half (compl_ne_self (a := σ)).symm).mpr hσ
  have h11 := theorem11 hnd iρ iσ hρσ (compl_injective.ne hρσ)
  have h9 := q_compl_compl ax3 ax4 ρᶜ σᶜ
  rw [compl_compl, compl_compl] at h9
  have hc := dp.Q.binary_complement hρσ
  linarith [h11, h9, hc]

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
    rw [hrule ρ trivial ρᶜ trivial ((compl_ne_self (a := ρ)).symm)] at h
    exact (pairwiseProb_gt_half_iff p1 p2).mp h
  have h2 : v σ < v σᶜ := by
    have h := hσ
    unfold Unfavorable at h
    rw [hrule σ trivial σᶜ trivial ((compl_ne_self (a := σ)).symm)] at h
    exact (pairwiseProb_lt_half_iff p3 p4).mp h
  have hconst := v_mul_v_compl_const ⟨hpos, hrule⟩ ax3 ax4 ρ σ
  -- v ρ² > v ρ · v ρ̄ = v σ · v σ̄ > v σ², hence v σ < v ρ
  have hvv : v σ < v ρ := by nlinarith
  rw [hrule ρ trivial σ trivial hρσ]
  exact (pairwiseProb_gt_half_iff p1 p3).mpr hvv

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
    have := (pairwiseProb_eq_pairwiseProb_iff p3 p1 p5 p1).mp e
    exact mul_right_cancel₀ (ne_of_gt p1) this
  have hσc : v (.inl ⟨c, σ, d⟩) = v (.inl ⟨d, σᶜ, c⟩) := by
    have g1 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨c, σ, d⟩ := by
      simpa using hacbd
    have g2 : (Sum.inl ⟨a, σ, b⟩ : Alternative A E) ≠ Sum.inl ⟨d, σᶜ, c⟩ := by
      simp [(compl_ne_self (a := σ)).symm]
    have e := ax3 c d σ (.inl ⟨a, σ, b⟩) g1 g2
    rw [hrule _ (by simp) _ (by simp) (Ne.symm g1),
        hrule _ (by simp) _ (by simp) (Ne.symm g2)] at e
    have := (pairwiseProb_eq_pairwiseProb_iff p4 p2 p6 p2).mp e
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
  have hcross := (pairwiseProb_eq_pairwiseProb_iff p1 p2 p4 p3).mp e1
  -- v(aρb)·v(cρd) = v(cσd)·v(aσb); transfer via Axiom 3
  rw [hρc, hσc] at hcross
  linarith [hcross, mul_comm (v (.inl ⟨d, σᶜ, c⟩)) (v (.inl ⟨a, σ, b⟩))]

/-- **Axiom 5** (p. 84): some event is subjectively as likely as its
    complement. -/
def HasNeutralEvent (dp : DecomposablePreference A E) : Prop :=
  ∃ ε : E, dp.Q.binary ε εᶜ = 1 / 2

/-- The second clause of **Lemma 10** (p. 84): anything equi-likely with a
    neutral event is itself neutral — `C(½)` is exactly the neutral class. -/
theorem neutral_of_indiff_neutral [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp) {ρ σ : E}
    (hρ : Neutral dp ρ) (h : EventIndiff dp σ ρ) : Neutral dp σ := by
  rcases eq_or_ne σ ρ with rfl | hne
  · exact hρ
  have hσρ : dp.Q.binary σ ρ = 1 / 2 := (eventIndiff_iff_eq_half hne).mp h
  have h9 := q_compl_compl ax3 ax4 σ ρ
  have hcc : dp.Q.binary ρᶜ σᶜ = 1 / 2 := by linarith
  have icc : EventIndiff dp σᶜ ρᶜ :=
    ((eventIndiff_iff_eq_half (compl_injective.ne (Ne.symm hne))).mpr hcc).symm
  have h11 := theorem11 hnd h icc (compl_ne_self (a := σ)).symm
    (compl_ne_self (a := ρ)).symm
  unfold Neutral at hρ ⊢
  linarith [h11]

/-- **Lemma 11** (p. 85): with Axioms 3–5 and nondegeneracy there are at
    least three classes — a neutral event, a non-neutral event, and its
    complement are pairwise non-equivalent. -/
theorem atLeastThreeClasses [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp)
    (ax5 : HasNeutralEvent dp) :
    ∃ ε ρ : E, ¬EventIndiff dp ε ρ ∧ ¬EventIndiff dp ε ρᶜ ∧
      ¬EventIndiff dp ρ ρᶜ := by
  obtain ⟨ε, hε⟩ := ax5
  have hex : ∃ ρ : E, ¬Neutral dp ρ := by
    by_contra hall
    push Not at hall
    obtain ⟨ρ₀, σ₀, hρσ₀, hq₀⟩ := ax4.2
    exact hq₀ (neutral_indifferent hnd ax3 ax4 (hall ρ₀) (hall σ₀) hρσ₀)
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ε, ρ, λ h => hρ (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm),
    λ h => hρ ((neutral_compl_iff ρ).mp
      (neutral_of_indiff_neutral hnd ax3 ax4 hε h.symm)),
    λ h => hρ ((eventIndiff_iff_eq_half (compl_ne_self (a := ρ)).symm).mp h)⟩

/-- **Theorem 12** (p. 84): given Axioms 3–5 and a nondegenerately
    discriminated pair of alternatives, `∼` partitions the events into
    exactly three classes: three pairwise non-equivalent events to one of
    which every event is equivalent. -/
theorem theorem12 [Nontrivial E] (hnd : Nondegenerate dp)
    (ax3 : Complementation dp) (ax4 : NontrivialPreference dp)
    (ax5 : HasNeutralEvent dp) :
    ∃ ρ₁ ρ₂ ρ₃ : E,
      (¬EventIndiff dp ρ₁ ρ₂ ∧ ¬EventIndiff dp ρ₁ ρ₃ ∧
        ¬EventIndiff dp ρ₂ ρ₃) ∧
      ∀ σ : E, EventIndiff dp σ ρ₁ ∨ EventIndiff dp σ ρ₂ ∨
        EventIndiff dp σ ρ₃ := by
  obtain ⟨ε, ρ, n1, n2, n3⟩ := atLeastThreeClasses hnd ax3 ax4 ax5
  refine ⟨ε, ρ, ρᶜ, ⟨n1, n2, n3⟩, λ σ => ?_⟩
  rcases atMostThreeClasses hnd σ ε ρ ρᶜ with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd h n1
  · exact absurd h n2
  · exact absurd h n3

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
  rw [hrule _ m₁ _ m₂ hg, pairwiseProb, hfac a b ρ h₁, hfac c d ρ h₂,
      show w a b * φ ρ + w c d * φ ρ = (w a b + w c d) * φ ρ by ring,
      mul_div_mul_right _ _ (ne_of_gt (hφ ρ))]

end DecomposablePreference

end Luce1959
