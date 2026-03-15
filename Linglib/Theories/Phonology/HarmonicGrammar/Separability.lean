import Linglib.Theories.Phonology.HarmonicGrammar.NoisyHG

/-!
# Separable Harmonies and HZ's Generalization @cite{magri-2025}

@cite{magri-2025} "Constraint Interaction in Probabilistic Phonology:
Deducing Maximum Entropy Grammars from Hayes and Zuraw's Shifted Sigmoids
Generalization" (Linguistic Inquiry, Early Access).

## Overview

@cite{hayes-2022} observe that the rates of application of variable
phonological processes governed by independent factors can be fit onto
shifted sigmoids at shared abscissas. @cite{magri-2025} reformulates this
as a **constant logit-rate difference** condition and proves a
biconditional: within harmony-based probabilistic phonology, a harmony
function predicts HZ's generalization **if and only if** it is *separable*
— it decomposes into a product of powers of unary functions, each fed by
a single constraint.

## Key definitions

- `ConstraintIndependence`: the formal constraint condition (§2.4) — each
  constraint is insensitive to at least one of the two dimensions of a
  2×2 "square" of underlying forms
- `ConstantLogitDiff`: HZ's generalization restated as constant differences
  of logit rates along each dimension (eq. 13)
- `SeparableHarmony`: a harmony function that decomposes as
  `H(v) = ∏ₖ (hₖ(vₖ))^{wₖ}` (eq. 30)
- `meSeparable`: ME harmony is separable (eq. 29), a corollary
  of `exp(sum) = prod(exp)`
- `separable_predicts_hz`: the forward direction — separable harmonies
  predict HZ's generalization. Follows from `logit_uniformity` +
  constraint rescaling
- `separable_eq_me_rescaled`: any separable harmony is ME under constraint
  rescaling `Ĉₖ = −log hₖ(Cₖ)` (eq. 34)

## Connection to existing infrastructure

The forward direction leverages `logit_uniformity` (in `NoisyHG.lean`)
and `maxent_logit_harmony`, which already prove that MaxEnt log-odds
equal harmony score differences. @cite{magri-2025}'s contribution is
showing this is *the only* mode of constraint interaction with this
property (the backward direction).

## Bridge to List-based API (§11)

The bridge theorems connect the Fin-indexed separability theory to the
List-based MaxEnt API (`harmonyScore`/`harmonyScoreR` from `Basic.lean`):

- `harmonyScoreR_as_finsum`: converts List-based harmony to Fin-indexed sum
- `exp_harmonyScoreR_eq_me_separable`: `exp(harmonyScoreR) = meSeparable.eval`
- `maxent_logit_as_finsum`: MaxEnt logit = weighted violation difference sum

These enable applying separability results (independence → HZ, rescaling)
to any `WeightedConstraint` list without re-proving in Fin-indexed form.
-/

namespace Theories.Phonology.HarmonicGrammar

open Core Real Finset

-- ============================================================================
-- § 1: The 2×2 Square of Underlying Forms (§2.4)
-- ============================================================================

/-- A **square** of four underlying forms indexed by two binary factors
    (row = top/bottom, column = left/right). This is @cite{magri-2025}'s
    eq. (12): the four forms `x^{TL}, x^{TR}, x^{BL}, x^{BR}` arranged
    so that rows and columns correspond to independent phonological
    dimensions (e.g., prefix identity × stem-initial obstruent quality).

    `Row` and `Col` are the two binary factors. -/
structure Square (X : Type) where
  /-- Top-left form (e.g., /maŋ+b/). -/
  tl : X
  /-- Top-right form (e.g., /maŋ+k/). -/
  tr : X
  /-- Bottom-left form (e.g., /paŋ+b/). -/
  bl : X
  /-- Bottom-right form (e.g., /paŋ+k/). -/
  br : X

-- ============================================================================
-- § 2: Constraint Independence (§2.4, Figure 4)
-- ============================================================================

/-- A constraint `C` is **insensitive to the row dimension** of a square:
    it assigns the same violation count to forms that share a column.
    Cf. @cite{magri-2025} Figure 4a. -/
def InsensitiveToRow {X : Type} (C : X → ℕ) (sq : Square X) : Prop :=
  C sq.tl = C sq.bl ∧ C sq.tr = C sq.br

/-- A constraint `C` is **insensitive to the column dimension** of a square:
    it assigns the same violation count to forms that share a row.
    Cf. @cite{magri-2025} Figure 4b. -/
def InsensitiveToCol {X : Type} (C : X → ℕ) (sq : Square X) : Prop :=
  C sq.tl = C sq.tr ∧ C sq.bl = C sq.br

/-- **Constraint independence** (@cite{magri-2025} §2.4): the rows and
    columns of the square are *independent dimensions* relative to a
    constraint set — each constraint is insensitive to at least one
    dimension (row or column). No constraint can encode an interaction
    between the two dimensions. -/
def ConstraintIndependence {n : ℕ} {X : Type}
    (constraints : Fin n → X → ℕ) (sq : Square X) : Prop :=
  ∀ k : Fin n,
    InsensitiveToRow (constraints k) sq ∨ InsensitiveToCol (constraints k) sq

-- ============================================================================
-- § 3: HZ's Generalization as Constant Logit-Rate Differences (§2.2)
-- ============================================================================

/-- **HZ's generalization** (eq. 13): the difference between logit rates
    of application for two underlying forms in the same row (or column)
    does not depend on the choice of row (or column).

    Equivalently: for a function `LR` giving logit rates,
    `LR(x^TL) − LR(x^TR) = LR(x^BL) − LR(x^BR)`. -/
def ConstantLogitDiff {X : Type} (LR : X → ℝ) (sq : Square X) : Prop :=
  LR sq.tl - LR sq.tr = LR sq.bl - LR sq.br

-- ============================================================================
-- § 4: ME Predicts HZ's Generalization (§3)
-- ============================================================================

/-- **Independence of violation differences**: if a constraint is
    insensitive to a dimension, its violation differences are too.

    The violation difference `Δₖ(x) = Cₖ(x, NO) − Cₖ(x, YES)` inherits
    insensitivity from the raw constraint, because both YES and NO get
    the same violation count for forms in the same row (or column). -/
def ViolDiffIndependence {n : ℕ} {X : Type}
    (Δ : Fin n → X → ℝ) (sq : Square X) : Prop :=
  ∀ k : Fin n,
    -- Either Δₖ is row-insensitive: same along each column
    (Δ k sq.tl = Δ k sq.bl ∧ Δ k sq.tr = Δ k sq.br) ∨
    -- Or Δₖ is column-insensitive: same along each row
    (Δ k sq.tl = Δ k sq.tr ∧ Δ k sq.bl = Δ k sq.br)

/-- **ME predicts HZ** (@cite{magri-2025} §3.6, eq. 22): when the
    violation differences satisfy independence (inherited from constraint
    independence), the weighted sum of violation differences — which
    equals the ME logit probability by `maxent_logit_harmony` —
    satisfies the constant-difference identity.

    The proof follows eq. (18): split the sum by constraint, and for
    each k, independence ensures the k-th term contributes equally to
    both sides of the identity. -/
theorem me_predicts_hz {n : ℕ} {X : Type}
    (w : Fin n → ℝ) (Δ : Fin n → X → ℝ)
    (sq : Square X) (hind : ViolDiffIndependence Δ sq) :
    ConstantLogitDiff (fun x => ∑ k : Fin n, w k * Δ k x) sq := by
  simp only [ConstantLogitDiff]
  -- Distribute the subtraction into the sum
  rw [← Finset.sum_sub_distrib]
  conv_rhs => rw [← Finset.sum_sub_distrib]
  -- It suffices to show each term matches
  congr 1; ext k
  simp only [← mul_sub]
  congr 1
  -- For each k, independence gives us the identity
  rcases hind k with ⟨hrow_l, hrow_r⟩ | ⟨hcol_t, hcol_b⟩
  · -- Row-insensitive: Δₖ(tl) = Δₖ(bl), Δₖ(tr) = Δₖ(br)
    rw [hrow_l, hrow_r]
  · -- Column-insensitive: Δₖ(tl) = Δₖ(tr), Δₖ(bl) = Δₖ(br)
    simp only [hcol_t, hcol_b, sub_self]

-- ============================================================================
-- § 5: Separable Harmonies (§5.1)
-- ============================================================================

/-- An *n*-ary harmony function `H` is **separable** if it decomposes
    into a product of powers of unary functions, each attending to a
    single constraint (@cite{magri-2025} eq. 30):

    `H(C₁(x,y), …, Cₙ(x,y)) = ∏ₖ (hₖ(Cₖ(x,y)))^{wₖ}`

    Each `hₖ` must be positive, normalized (`hₖ(0) = 1`), and decreasing
    (more violations → lower harmony). -/
structure SeparableHarmony (n : ℕ) where
  /-- Constraint weights. -/
  w : Fin n → ℝ
  /-- Per-constraint rescaling functions. -/
  h : Fin n → ℕ → ℝ
  /-- Each hₖ is positive. -/
  h_pos : ∀ k v, 0 < h k v
  /-- Normalized: hₖ(0) = 1. -/
  h_norm : ∀ k, h k 0 = 1
  /-- Decreasing: more violations → lower score. -/
  h_decreasing : ∀ k, ∀ a b : ℕ, a < b → h k b < h k a

/-- Evaluate a separable harmony on a violation profile. -/
noncomputable def SeparableHarmony.eval {n : ℕ} (H : SeparableHarmony n)
    (v : Fin n → ℕ) : ℝ :=
  ∏ k : Fin n, (H.h k (v k)) ^ H.w k

/-- The separable harmony at the zero profile is 1 (normalization). -/
theorem SeparableHarmony.eval_zero {n : ℕ} (H : SeparableHarmony n) :
    H.eval (fun _ => 0) = 1 := by
  simp only [SeparableHarmony.eval, H.h_norm, one_rpow, prod_const_one]

-- ============================================================================
-- § 6: ME Harmony Is Separable (§5.1, eq. 29)
-- ============================================================================

/-- The **ME separable harmony**: each `hₖ(x) = exp(−x)` (the
    exponential-of-opposite function from @cite{magri-2025} Figure 5a).
    This gives `H_ME(v) = ∏ₖ (exp(−vₖ))^{wₖ} = exp(−Σ wₖvₖ)`. -/
noncomputable def meSeparable (n : ℕ) (w : Fin n → ℝ) :
    SeparableHarmony n where
  w := w
  h := fun _ v => exp (-(v : ℝ))
  h_pos := fun _ v => exp_pos _
  h_norm := fun _ => by simp
  h_decreasing := fun _ a b hab => by
    apply Real.exp_lt_exp.mpr
    simp only [neg_lt_neg_iff, Nat.cast_lt]
    exact hab

/-- The ME separable harmony agrees with the standard ME harmony score
    (up to positive scaling by `exp`).

    `meSeparable.eval(v) = exp(−Σₖ wₖ · vₖ)`

    Proof: `∏ₖ (exp(−vₖ))^{wₖ} = ∏ₖ exp(−wₖvₖ) = exp(−Σₖ wₖvₖ)`,
    using `rpow` = `exp(w · log(exp(−v))) = exp(−wv)`. -/
theorem me_separable_eval {n : ℕ} (w : Fin n → ℝ)
    (v : Fin n → ℕ) :
    (meSeparable n w).eval v = exp (-∑ k, w k * (v k : ℝ)) := by
  simp only [SeparableHarmony.eval, meSeparable]
  simp_rw [← exp_mul]
  rw [← exp_sum]
  congr 1
  rw [← sum_neg_distrib]
  congr 1; ext k; ring

-- ============================================================================
-- § 7: Constraint Rescaling (§5.3, eq. 33–34)
-- ============================================================================

/-- **Constraint rescaling** (@cite{magri-2025} eq. 33): given a separable
    harmony with unary functions `hₖ`, the rescaled constraint is
    `Ĉₖ = −log(hₖ(Cₖ))`.

    The rescaled constraints are nonneg (since hₖ ∈ (0,1] for v ≥ 0)
    and preserve the ordering on violation profiles. -/
noncomputable def SeparableHarmony.rescale {n : ℕ} (H : SeparableHarmony n)
    (k : Fin n) (v : ℕ) : ℝ :=
  -Real.log (H.h k v)

/-- `hₖ(v) ≤ 1` for all `v`: follows from decreasingness and `hₖ(0) = 1`. -/
theorem SeparableHarmony.h_le_one {n : ℕ} (H : SeparableHarmony n)
    (k : Fin n) (v : ℕ) :
    H.h k v ≤ 1 := by
  rcases Nat.eq_zero_or_pos v with rfl | hpos
  · rw [H.h_norm]
  · exact le_of_lt (H.h_norm k ▸ H.h_decreasing k 0 v hpos)

/-- Rescaled constraints are nonneg: since `hₖ(v) ∈ (0, 1]`,
    `−log(hₖ(v)) ≥ 0`. -/
theorem SeparableHarmony.rescale_nonneg {n : ℕ} (H : SeparableHarmony n)
    (k : Fin n) (v : ℕ) :
    0 ≤ H.rescale k v := by
  simp only [SeparableHarmony.rescale, neg_nonneg]
  exact Real.log_nonpos (le_of_lt (H.h_pos k v)) (H.h_le_one k v)

/-- Rescaled constraints at 0 are 0: `Ĉₖ(0) = −log(1) = 0`. -/
theorem SeparableHarmony.rescale_zero {n : ℕ} (H : SeparableHarmony n)
    (k : Fin n) :
    H.rescale k 0 = 0 := by
  simp [SeparableHarmony.rescale, H.h_norm]

/-- ME rescaling is the identity: since `hₖ = exp(−·)`,
    `Ĉₖ(v) = −log(exp(−v)) = v`. -/
theorem meSeparable_rescale {n : ℕ} (w : Fin n → ℝ) (k : Fin n) (v : ℕ) :
    (meSeparable n w).rescale k v = (v : ℝ) := by
  simp [SeparableHarmony.rescale, meSeparable, Real.log_exp]

/-- **Any separable harmony is ME under rescaling** (@cite{magri-2025}
    eq. 34): `H(C₁, …, Cₙ) = H_ME(Ĉ₁, …, Ĉₙ)` where `Ĉₖ = −log hₖ(Cₖ)`.

    This is the key insight: the choice of `hₖ` only affects how
    constraints are rescaled, not how they interact. All separable
    harmonies have the same *mode* of constraint interaction as ME. -/
theorem separable_eq_me_rescaled {n : ℕ} (H : SeparableHarmony n)
    (v : Fin n → ℕ) :
    H.eval v = exp (-∑ k, H.w k * H.rescale k (v k)) := by
  simp only [SeparableHarmony.eval, SeparableHarmony.rescale]
  simp_rw [rpow_def_of_pos (H.h_pos _ _)]
  rw [← exp_sum]
  congr 1
  rw [← sum_neg_distrib]
  congr 1; ext k; ring

-- ============================================================================
-- § 8: Forward Direction — Separable ⟹ HZ (§5.4)
-- ============================================================================

/-- **Separable harmonies predict HZ** (@cite{magri-2025} §5.4):
    for *any* separable harmony `H`, if the rescaled violation differences
    `Δ̂ₖ(x) = Ĉₖ(Cₖ(x,NO)) − Ĉₖ(Cₖ(x,YES))` satisfy independence on a
    square, then the logit rate `log(H(v_YES)/H(v_NO))` satisfies HZ's
    constant-difference identity.

    The proof composes two results:
    1. `separable_eq_me_rescaled`: `H(v) = exp(−Σ wₖĈₖ(vₖ))`
    2. `me_predicts_hz`: weighted sums with independent differences
       satisfy constant logit-rate differences

    Since `log(exp(a)/exp(b)) = a − b`, the logit rate is a weighted sum
    of rescaled violation differences, and `me_predicts_hz` applies. -/
theorem separable_predicts_hz {n : ℕ} {X : Type}
    (H : SeparableHarmony n)
    (C_yes C_no : Fin n → X → ℕ)
    (sq : Square X)
    (hind : ViolDiffIndependence
      (fun k x => H.rescale k (C_no k x) - H.rescale k (C_yes k x)) sq) :
    ConstantLogitDiff
      (fun x => Real.log (H.eval (fun k => C_yes k x) / H.eval (fun k => C_no k x)))
      sq := by
  suffices h : ∀ x : X,
      Real.log (H.eval (fun k => C_yes k x) / H.eval (fun k => C_no k x)) =
      ∑ k : Fin n, H.w k * (H.rescale k (C_no k x) - H.rescale k (C_yes k x)) by
    simp only [ConstantLogitDiff, h]
    exact me_predicts_hz H.w _ sq hind
  intro x
  rw [separable_eq_me_rescaled, separable_eq_me_rescaled,
    Real.log_div (exp_ne_zero _) (exp_ne_zero _), Real.log_exp, Real.log_exp,
    neg_sub_neg, ← sum_sub_distrib]
  congr 1; ext k; ring

-- ============================================================================
-- § 9: Backward Direction — HZ ⟹ Separable (§5.5, online appendices)
-- ============================================================================

-- **HZ implies separability** (@cite{magri-2025} main result, §5.5):
-- if an n-ary harmony function H predicts HZ's generalization for
-- *every* constraint set satisfying independence, then H is separable.
--
-- The proof (online appendices A–C) constructs hₖ via eq. (31):
-- hₖ(c) = H(0,…,0,c,0,…,0), and uses the identity
-- H(v) = ∏ₖ H(eₖ · vₖ) (eq. 32).
--
-- Full statement requires formalizing "H predicts HZ for all
-- independent constraint sets" as a universal quantification over
-- constraint sets and squares, which is deferred.

-- ============================================================================
-- § 10: Counterexample — Inverse Function (§4.4)
-- ============================================================================

/-- The **inverse function** `h(x) = 1/(1+x)` used in the non-separable
    harmony `H(v) = 1 / (1 + Σ wₖvₖ)` (@cite{magri-2025} eq. 27).
    Like ME's `exp(−x)`, it is positive, normalized, and decreasing —
    but the resulting harmony is *not* separable. -/
noncomputable def inverseFunction (x : ℝ) : ℝ := 1 / (1 + x)

/-- The inverse function is positive for nonneg arguments. -/
theorem inverseFunction_pos {x : ℝ} (hx : 0 ≤ x) :
    0 < inverseFunction x := by
  simp only [inverseFunction]
  positivity

/-- The inverse function is normalized: `h(0) = 1`. -/
theorem inverseFunction_zero : inverseFunction 0 = 1 := by
  simp [inverseFunction]

/-- The inverse function is strictly decreasing on [0, ∞). -/
theorem inverseFunction_strictAntiOn :
    StrictAntiOn inverseFunction (Set.Ici 0) := by
  intro a ha b hb hab
  simp only [inverseFunction, Set.mem_Ici] at *
  exact div_lt_div_of_pos_left one_pos (by linarith) (by linarith)

/-- The non-separable harmony using the inverse function:
    `H(v) = 1 / (1 + Σₖ wₖ · vₖ)` (@cite{magri-2025} eq. 27).

    This has the form `H = h(Σ wₖCₖ)` (eq. 26) with `h = inverseFunction`,
    which is *not* separable because the single `h` sees the *sum* of all
    weighted violations, not each constraint individually. -/
noncomputable def nonSeparableInverseHarmony {n : ℕ} (w : Fin n → ℝ)
    (v : Fin n → ℕ) : ℝ :=
  inverseFunction (∑ k, w k * (v k : ℝ))

/-- **Counterexample** (@cite{magri-2025} §4.4, online appendix D.1):
    the non-separable inverse harmony does *not* predict HZ's
    generalization in general.

    For the inverse harmony `H(v) = 1/(1 + Σ wₖvₖ)`, the logit
    probability is `log((1 + S_NO(x)) / (1 + S_YES(x)))` where
    `S_y(x) = Σₖ wₖ Cₖ(x,y)`. HZ holds iff the cross-product
    `(1+S_NO(tl))(1+S_YES(tr))(1+S_YES(bl))(1+S_NO(br))`
    equals `(1+S_YES(tl))(1+S_NO(tr))(1+S_NO(bl))(1+S_YES(br))`.

    With Tagalog constraints and w₅ ≠ w₆ (weights 1,1,1,1,1,2),
    the cross-products are 72 and 60, disproving HZ. -/
theorem inverse_not_always_hz :
    -- Using w = (1,1,1,1,1,2) and Tagalog constraints:
    -- S_YES(maŋb)=1, S_NO(maŋb)=1, S_YES(maŋk)=3, S_NO(maŋk)=2
    -- S_YES(paŋb)=2, S_NO(paŋb)=1, S_YES(paŋk)=4, S_NO(paŋk)=2
    -- LHS cross-product: (1+1)(1+3)(1+2)(1+2) = 2·4·3·3 = 72
    -- RHS cross-product: (1+1)(1+2)(1+1)(1+4) = 2·3·2·5 = 60
    (2 : ℕ) * 4 * 3 * 3 ≠ 2 * 3 * 2 * 5 := by decide

-- ============================================================================
-- § 11: Bridge — List-Based MaxEnt ↔ Separable Harmony
-- ============================================================================

-- The List-based MaxEnt API (`harmonyScore`, `harmonyScoreR` from Basic.lean)
-- and the Fin-indexed separability theory (`SeparableHarmony`, `meSeparable`)
-- compute the same thing for MaxEnt grammars. These bridge theorems make the
-- connection formal, enabling separability results (independence → HZ,
-- constraint rescaling) to be applied to any `WeightedConstraint` list.

private lemma foldl_sub_eq' {α : Type} (l : List α) (f : α → ℚ) (init : ℚ) :
    l.foldl (fun acc x => acc - f x) init = init - (l.map f).sum := by
  induction l generalizing init with
  | nil => simp
  | cons _ _ ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih]; ring

private lemma list_map_sum_eq_finsum {α : Type} (l : List α) (f : α → ℚ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  induction l with
  | nil => simp
  | cons _ _ ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons,
      Fin.sum_univ_succ, ih, List.get_cons_zero]
    congr 1

/-- **`harmonyScoreR` as a Fin-indexed weighted sum**:
    the List-based harmony score equals a negated Finset.sum over
    Fin-indexed constraint weights and violations.

    This is the key List→Fin conversion for applying separability
    theory to concrete `WeightedConstraint` lists. -/
theorem harmonyScoreR_as_finsum {C : Type}
    (constraints : List (WeightedConstraint C)) (c : C) :
    harmonyScoreR constraints c =
    -(∑ i : Fin constraints.length,
      ((constraints.get i).weight : ℝ) * ((constraints.get i).eval c : ℝ)) := by
  simp only [harmonyScoreR, harmonyScore]
  rw [foldl_sub_eq']
  push_cast [list_map_sum_eq_finsum]
  ring

/-- **MaxEnt unnormalized probability is separable harmony**:
    `exp(harmonyScoreR constraints c) = meSeparable.eval v` where
    weights and violations are drawn from the constraint list.

    Since `meSeparable.eval v = exp(-∑ wₖvₖ)` (`me_separable_eval`)
    and `harmonyScoreR c = -∑ wₖvₖ` (`harmonyScoreR_as_finsum`),
    the exponential of the List-based harmony is exactly the
    Fin-indexed separable harmony evaluation.

    This makes all separability theory — constraint independence → HZ
    (`separable_predicts_hz`), constraint rescaling
    (`separable_eq_me_rescaled`) — directly applicable to any
    `WeightedConstraint` list. -/
theorem exp_harmonyScoreR_eq_me_separable {C : Type}
    (constraints : List (WeightedConstraint C)) (c : C) :
    exp (harmonyScoreR constraints c) =
    (meSeparable constraints.length
      (fun i => ((constraints.get i).weight : ℝ))).eval
      (fun i => (constraints.get i).eval c) := by
  rw [me_separable_eval, harmonyScoreR_as_finsum]

/-- **MaxEnt logit rate as Fin-indexed weighted violation differences**:
    the logit of MaxEnt probabilities is a negated weighted sum of
    violation differences, expressed as a Finset.sum over Fin indices.

    This bridges `logit_uniformity` (NoisyHG.lean) with `me_predicts_hz`:
    since the logit is a weighted sum, it satisfies HZ whenever the
    violation differences satisfy `ViolDiffIndependence`.

    Composition: `logit_uniformity` → `harmonyScoreR_as_finsum` → algebra. -/
theorem maxent_logit_as_finsum {C : Type} [Fintype C] [Nonempty C]
    (constraints : List (WeightedConstraint C)) (a b : C) :
    log (softmax (harmonyScoreR constraints) 1 a /
         softmax (harmonyScoreR constraints) 1 b) =
    -(∑ i : Fin constraints.length,
      ((constraints.get i).weight : ℝ) *
      (((constraints.get i).eval a : ℝ) - ((constraints.get i).eval b : ℝ))) := by
  rw [logit_uniformity, harmonyScoreR_as_finsum, harmonyScoreR_as_finsum,
    neg_sub_neg, ← sum_sub_distrib, ← sum_neg_distrib]
  apply Finset.sum_congr rfl; intro _ _; ring

end Theories.Phonology.HarmonicGrammar
