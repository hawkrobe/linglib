import Linglib.Core.Optimization.Evaluation
import Mathlib.Order.FixedPoints
import Mathlib.Order.Preorder.Finite
/-!
# Superoptimal: Bidirectional OT via OrderHom.gfp

[blutner-2000] [jaeger-2002]

Mathlib-grounded formulation of [blutner-2000]'s weak Bidirectional OT
"superoptimality" (eq. 14). The set of superoptimal form-meaning pairs is
the **greatest fixed point** of the squared blocking operator on `Set (F × M)`,
defined via mathlib's `OrderHom.gfp` on the `Set α` complete lattice.

## Architecture

The blocking operator `superoptimalSetStep` is anti-monotone (more witnesses ⇒
more blockers ⇒ fewer survivors). Its square is monotone, so mathlib's
`OrderHom.gfp` applies. The substrate definition is:

    superoptimalSet pairs profile := (superoptimalSetStepSq pairs profile).gfp

(Renamed from `superoptimalSet` to `superoptimal` once the legacy list-based
`superoptimal` in `Core/Optimization/Evaluation.lean` is retired.)

Mathlib's GFP API (`isGreatest_gfp`, `le_gfp`, `gfp_le`, `map_gfp`,
Park induction) immediately applies. Per-paper consumers prove
`superoptimalSet pairs profile = S` by exhibiting `S` as an `IsParkWitness`
(§4 below): a fixed point of the unsquared step that absorbs every non-S
pair via blocking. The maximality direction goes through
`Set.Finite.exists_minimalFor`-based minimum-profile descent, anchored in
the `LexNatList` preorder from `Core/Optimization/Evaluation.lean`.
-/

namespace Pragmatics.Bidirectional

open Core.Optimization.Evaluation

variable {F M : Type*}

-- ============================================================================
-- § 1. The blocking relation
-- ============================================================================

/-- `Blocks profile S p`: some witness `q ∈ S` blocks `p` — same form or
    same meaning (not both), strictly better profile under lex order.
    Set-valued sibling of `IsBlocked` (will inherit that name once the
    list-based variant retires). -/
def Blocks (profile : F × M → List Nat) (S : Set (F × M)) (p : F × M) : Prop :=
  ∃ q ∈ S, ((q.1 = p.1 ∧ q.2 ≠ p.2) ∨ (q.1 ≠ p.1 ∧ q.2 = p.2)) ∧
    LexLT (profile q) (profile p)

/-- `Blocks` is monotone in the witness set: more witnesses can only create
    more blockers. -/
theorem Blocks.mono {profile : F × M → List Nat}
    {S T : Set (F × M)} (hST : S ⊆ T) {p : F × M} :
    Blocks profile S p → Blocks profile T p :=
  fun ⟨q, hq, h⟩ => ⟨q, hST hq, h⟩

/-- For `Finset`-coerced witness sets, `Blocks` is decidable: the existential
    over the finite carrier reduces to `Finset.decidableBEx`. This instance is
    the load-bearing piece for `decide`-based per-paper proofs. -/
instance Blocks.decidableOnFinset [DecidableEq F] [DecidableEq M]
    (profile : F × M → List Nat) (S : Finset (F × M)) (p : F × M) :
    Decidable (Blocks profile (↑S : Set (F × M)) p) :=
  decidable_of_iff
    (∃ q ∈ S, ((q.1 = p.1 ∧ q.2 ≠ p.2) ∨ (q.1 ≠ p.1 ∧ q.2 = p.2)) ∧
              LexLT (profile q) (profile p))
    ⟨fun ⟨q, hq, h⟩ => ⟨q, hq, h⟩, fun ⟨q, hq, h⟩ => ⟨q, hq, h⟩⟩

-- ============================================================================
-- § 2. The blocking step (anti-monotone) and its square (monotone)
-- ============================================================================

/-- Single step of the superoptimality computation: keep pairs in `pairs`
    that are NOT blocked by any element of `S`. Anti-monotone in `S`. -/
def superoptimalSetStep (pairs : Set (F × M)) (profile : F × M → List Nat)
    (S : Set (F × M)) : Set (F × M) :=
  { p ∈ pairs | ¬ Blocks profile S p }

theorem superoptimalSetStep_subset (pairs : Set (F × M))
    (profile : F × M → List Nat) (S : Set (F × M)) :
    superoptimalSetStep pairs profile S ⊆ pairs :=
  fun _ hp => hp.1

@[simp] theorem mem_superoptimalSetStep {pairs : Set (F × M)}
    {profile : F × M → List Nat} {S : Set (F × M)} {p : F × M} :
    p ∈ superoptimalSetStep pairs profile S ↔ p ∈ pairs ∧ ¬ Blocks profile S p :=
  Iff.rfl

/-- `superoptimalSetStep` is anti-monotone in the witness set. -/
theorem superoptimalSetStep_antitone (pairs : Set (F × M))
    (profile : F × M → List Nat) :
    Antitone (superoptimalSetStep pairs profile) :=
  fun _ _ hST _ hp => ⟨hp.1, fun hb => hp.2 (hb.mono hST)⟩

/-- The squared step. Anti-monotone composed with anti-monotone is monotone,
    so this is the right object to feed `OrderHom.gfp`. -/
def superoptimalSetStepSq (pairs : Set (F × M)) (profile : F × M → List Nat) :
    Set (F × M) →o Set (F × M) where
  toFun S := superoptimalSetStep pairs profile (superoptimalSetStep pairs profile S)
  monotone' := fun _ _ hST =>
    superoptimalSetStep_antitone pairs profile
      (superoptimalSetStep_antitone pairs profile hST)

@[simp] theorem superoptimalSetStepSq_apply (pairs : Set (F × M))
    (profile : F × M → List Nat) (S : Set (F × M)) :
    superoptimalSetStepSq pairs profile S =
    superoptimalSetStep pairs profile (superoptimalSetStep pairs profile S) := rfl

-- ============================================================================
-- § 3. The canonical superoptimal set: greatest fixed point
-- ============================================================================

/-- [blutner-2000]'s superoptimality (eq. 14): the greatest fixed point
    of the squared blocking operator. Set-valued, anchored in mathlib's
    `OrderHom.gfp` via `Set α`'s `CompleteLattice` instance.

    All mathlib gfp lemmas (`isGreatest_gfp`, `le_gfp`, `gfp_le`, `map_gfp`,
    Park induction) immediately apply. Per-paper consumers typically prove
    `superoptimalSet pairs profile = S` by exhibiting `S` as an
    `IsParkWitness` (§4 below).

    Renamed from `superoptimalSet` to `superoptimal` once the legacy
    list-based `superoptimal` in `Core/Optimization/Evaluation.lean` is retired. -/
noncomputable def superoptimalSet (pairs : Set (F × M))
    (profile : F × M → List Nat) : Set (F × M) :=
  (superoptimalSetStepSq pairs profile).gfp

theorem superoptimalSet_subset (pairs : Set (F × M))
    (profile : F × M → List Nat) :
    superoptimalSet pairs profile ⊆ pairs := by
  unfold superoptimalSet
  rw [← (superoptimalSetStepSq pairs profile).map_gfp]
  exact superoptimalSetStep_subset _ _ _

-- ============================================================================
-- § 4. Park-style witness structure: the consumer-facing API
-- ============================================================================

/-- `IsParkWitness pairs profile S`: structural witness via Park's induction
    that `S` is the greatest fixed point of `superoptimalSetStepSq pairs profile`.
    Three conditions:

    - **`subset`**: `S ⊆ pairs`.
    - **`unblocked`**: every `p ∈ S` is unblocked by `S` (i.e., `S` is a
      fixed point of the unsquared step).
    - **`closure`**: every `p ∈ pairs \ S` is blocked by `S` (uniqueness:
      no proper extension of `S` is a fixed point).

    Together they pin down `S` as the GFP via `superoptimalSet_eq_of_witness`.
    The `unblocked` and `closure` conditions decompose into per-pair blocking
    checks that are typically `decide`-able for finite literal `S` and
    `pairs` (via the `Blocks.decidableOnFinset` instance). -/
structure IsParkWitness (pairs : Set (F × M)) (profile : F × M → List Nat)
    (S : Set (F × M)) : Prop where
  subset    : S ⊆ pairs
  unblocked : ∀ p ∈ S, ¬ Blocks profile S p
  closure   : ∀ p ∈ pairs, p ∉ S → Blocks profile S p

/-- **Witness lemma**: `IsParkWitness pairs profile S` implies
    `superoptimalSet pairs profile = S`.

    Proof structure:
    - `S ≤ gfp` via coinduction (`OrderHom.le_gfp`): `S` is a fixed point
      of `superoptimalSetStep` (from `unblocked` + `closure`), hence of its
      square.
    - `gfp ≤ S` via Park rule (`OrderHom.gfp_le`) with minimum-profile
      descent: any post-fixed-point `T` violating `T ⊆ S` contains a
      profile-minimal `p ∈ T \ S`; the `S`-blocker for `p` (from `closure`)
      is unblocked by `T` (no `S`-element blocks it by `unblocked`; no
      smaller `T \ S`-element blocks it by minimality), hence in `F(T)`,
      contradicting `p ∈ F²(T)`. Descent terminates by
      `Set.Finite.exists_minimalFor` against the `LexNatList` preorder. -/
theorem superoptimalSet_eq_of_witness {pairs : Set (F × M)}
    {profile : F × M → List Nat} {S : Set (F × M)} (h_finite : pairs.Finite)
    (h : IsParkWitness pairs profile S) :
    superoptimalSet pairs profile = S := by
  -- S is a fixed point of the unsquared step.
  have hS_step : superoptimalSetStep pairs profile S = S := by
    ext p
    refine ⟨fun hp => ?_, fun hp => ⟨h.subset hp, h.unblocked p hp⟩⟩
    by_contra hpS
    exact hp.2 (h.closure p hp.1 hpS)
  -- Therefore S is a fixed point of the squared step.
  have hS_sq : superoptimalSetStepSq pairs profile S = S := by
    show superoptimalSetStep pairs profile (superoptimalSetStep pairs profile S) = S
    rw [hS_step, hS_step]
  -- Coinduction: S ≤ gfp.
  have h_le_gfp : S ≤ superoptimalSet pairs profile :=
    OrderHom.le_gfp _ hS_sq.ge
  -- Maximality (Park rule): every post-fixed-point T satisfies T ⊆ S.
  have h_gfp_le : superoptimalSet pairs profile ≤ S := by
    apply OrderHom.gfp_le
    intro T hT
    have hT_pairs : T ⊆ pairs := fun p hp => (hT hp).1
    by_contra h_TS
    -- Pick a profile-minimum element of T \ S using mathlib's canonical
    -- `Set.Finite.exists_minimalFor` against the `LexNatList` preorder.
    obtain ⟨p₀, hp₀_T, hp₀_notS⟩ := Set.not_subset.mp h_TS
    have h_diff_finite : (T \ S).Finite :=
      h_finite.subset (fun x hx => hT_pairs hx.1)
    obtain ⟨p, ⟨hp_T, hp_notS⟩, hp_min⟩ :=
      h_diff_finite.exists_minimalFor (fun x => LexNatList.mk (profile x))
        (T \ S) ⟨p₀, hp₀_T, hp₀_notS⟩
    have hp_pairs : p ∈ pairs := hT_pairs hp_T
    -- p is blocked by S (closure).
    obtain ⟨q, hq_S, hq_dim, hq_lt⟩ := h.closure p hp_pairs hp_notS
    -- Goal: derive contradiction via q ∈ F(T) blocking p, contradicting
    -- p ∈ F²(T) = F(F(T)).
    have hp_F2 : p ∈ superoptimalSetStep pairs profile
                       (superoptimalSetStep pairs profile T) := hT hp_T
    have hp_unblk_FT :
        ¬ Blocks profile (superoptimalSetStep pairs profile T) p := hp_F2.2
    have hq_pairs : q ∈ pairs := h.subset hq_S
    -- q unblocked by T: any blocker r ∈ T is in S (forbidden by `unblocked`)
    -- or in T \ S with smaller profile than p (forbidden by minimality).
    have hq_unblk_T : ¬ Blocks profile T q := by
      rintro ⟨r, hr_T, hr_dim, hr_lt⟩
      by_cases hr_S : r ∈ S
      · exact h.unblocked q hq_S ⟨r, hr_S, hr_dim, hr_lt⟩
      · -- r ∈ T \ S with profile r < profile q < profile p — contradicts minimality.
        have hr_lt_p : LexLT (profile r) (profile p) :=
          lexLT_trans _ _ _ hr_lt hq_lt
        -- MinimalFor: if `f r ≤ f p` then `f p ≤ f r` (i.e., r and p are equivalent
        -- under f). Combined with strict inequality, contradiction.
        exact hr_lt_p.2 (hp_min ⟨hr_T, hr_S⟩ hr_lt_p.1)
    have hq_FT : q ∈ superoptimalSetStep pairs profile T := ⟨hq_pairs, hq_unblk_T⟩
    exact hp_unblk_FT ⟨q, hq_FT, hq_dim, hq_lt⟩
  exact le_antisymm h_gfp_le h_le_gfp

-- ============================================================================
-- § 5. Finset-friendly witness API (the consumer-facing variant)
-- ============================================================================

/-- **Finset-version witness lemma** — for structural arguments where the
    abstract gfp form is needed. Hypotheses are Finset-bounded universals,
    hence decidable when paired with `Blocks.decidableOnFinset`. Per-paper
    consumers typically prefer `superoptimal` (the Finset-native computable
    form below) with one `decide`; this lemma is the bridge for theorems
    stated about `superoptimalSet`. -/
theorem superoptimalSet_eq_of_finset_witness
    [DecidableEq F] [DecidableEq M]
    {pairs S : Finset (F × M)} {profile : F × M → List Nat}
    (h_subset : S ⊆ pairs)
    (h_unblocked : ∀ p ∈ S, ¬ Blocks profile (↑S : Set _) p)
    (h_closure : ∀ p ∈ pairs, p ∉ S → Blocks profile (↑S : Set _) p) :
    superoptimalSet (↑pairs : Set _) profile = ↑S :=
  superoptimalSet_eq_of_witness pairs.finite_toSet
    { subset := Finset.coe_subset.mpr h_subset
      unblocked := fun p hp => h_unblocked p (Finset.mem_coe.mp hp)
      closure := fun p hp_pairs hp_notS =>
        h_closure p (Finset.mem_coe.mp hp_pairs)
          (fun h => hp_notS (Finset.mem_coe.mpr h)) }

-- ============================================================================
-- § 6. Finset-native computable form: the consumer-facing canonical API
-- ============================================================================

section Computable

variable [DecidableEq F] [DecidableEq M]

/-- Single iteration step on `Finset`: keep pairs in `pairs` not blocked by `S`.
    Decidability of `Blocks` on Finset witnesses (via `Blocks.decidableOnFinset`)
    makes this a computable `Finset.filter`. -/
def superoptimalSetStep_TEMPFIN (pairs : Finset (F × M)) (profile : F × M → List Nat)
    (S : Finset (F × M)) : Finset (F × M) :=
  pairs.filter (fun p => ¬ Blocks profile (↑S : Set _) p)

@[simp] theorem mem_superoptimalSetStep_TEMPFIN {pairs : Finset (F × M)}
    {profile : F × M → List Nat} {S : Finset (F × M)} {p : F × M} :
    p ∈ superoptimalSetStep_TEMPFIN pairs profile S ↔
    p ∈ pairs ∧ ¬ Blocks profile (↑S : Set _) p := by
  simp [superoptimalSetStep_TEMPFIN]

/-- Iteration loop with bounded fuel: iterate until fixed point or fuel
    exhausted. For finite `pairs` and games with a unique fixed point of
    the unsquared step, this stabilizes within `2 * pairs.card` iterations. -/
private def superoptimalLoop (pairs : Finset (F × M)) (profile : F × M → List Nat)
    : Finset (F × M) → Nat → Finset (F × M)
  | S, 0 => S
  | S, n + 1 =>
    let S' := superoptimalSetStep_TEMPFIN pairs profile S
    if S' = S then S else superoptimalLoop pairs profile S' n

/-- [blutner-2000]'s superoptimality (Finset-native, computable). Iterates
    `superoptimalSetStep_TEMPFIN` from `pairs` (top) until fixed.

    For consumer use, this is the canonical form — output equality with a
    literal Finset is `decide`-able directly:

    ```
    theorem foo : superoptimal pairs profile = winner := by decide
    ```

    For structural arguments (uniqueness, ranking-invariance across OT
    procedures), use `superoptimalSet` instead, with the Park-witness API.
    The bridge theorem `superoptimal_coe_eq_gfp` connects the two when
    needed. -/
def superoptimal (pairs : Finset (F × M)) (profile : F × M → List Nat) :
    Finset (F × M) :=
  superoptimalLoop pairs profile pairs (2 * pairs.card + 1)

theorem superoptimal_subset (pairs : Finset (F × M)) (profile : F × M → List Nat) :
    superoptimal pairs profile ⊆ pairs := by
  unfold superoptimal
  -- Show: superoptimalLoop pairs profile S n ⊆ pairs whenever S ⊆ pairs.
  suffices h : ∀ n S, S ⊆ pairs → superoptimalLoop pairs profile S n ⊆ pairs from
    h _ pairs subset_rfl
  intro n
  induction n with
  | zero => intro S hS; exact hS
  | succ n ih =>
    intro S hS
    unfold superoptimalLoop
    by_cases h : superoptimalSetStep_TEMPFIN pairs profile S = S
    · simp [h, hS]
    · simp [h]
      exact ih _ (Finset.filter_subset _ _)

/-- The iteration converges: at the returned value, one more step yields
    the same set (i.e., it's a fixed point of the unsquared step), provided
    the iteration actually stabilized within the fuel budget. -/
theorem superoptimal_isFixedPoint (pairs : Finset (F × M))
    (profile : F × M → List Nat)
    (h : superoptimalSetStep_TEMPFIN pairs profile (superoptimal pairs profile) =
         superoptimal pairs profile) :
    superoptimalSetStep_TEMPFIN pairs profile (superoptimal pairs profile) =
    superoptimal pairs profile := h

/-- **Bridge theorem**: when the iteration converges (the Finset returned by
    `superoptimal` is a fixed point of the unsquared step), it coincides with
    the abstract `superoptimalSet` set under coercion. This is the connection
    that lets per-paper consumers prove output equalities via `decide` on the
    computable form, and lift those equalities to the abstract gfp form when
    needed for structural arguments.

    Convergence is `decide`-able for finite literal `pairs`, so the
    hypothesis is typically discharged by `by decide` at use sites. -/
theorem superoptimal_coe_eq_set (pairs : Finset (F × M))
    (profile : F × M → List Nat)
    (h_converged : superoptimalSetStep_TEMPFIN pairs profile (superoptimal pairs profile) =
                   superoptimal pairs profile) :
    (↑(superoptimal pairs profile) : Set _) =
    superoptimalSet (↑pairs : Set _) profile := by
  -- The fixed-point of the unsquared step satisfies the IsParkWitness
  -- conditions, hence equals the gfp by superoptimalSet_eq_of_witness.
  refine (superoptimalSet_eq_of_witness pairs.finite_toSet ?_).symm
  refine
    { subset := Finset.coe_subset.mpr (superoptimal_subset pairs profile)
      unblocked := ?_
      closure := ?_ }
  · -- ∀ p ∈ ↑(superoptimal pairs profile), ¬ Blocks profile (↑(superoptimal ...)) p
    intro p hp
    rw [Finset.mem_coe] at hp
    -- p ∈ superoptimal = F(superoptimal). So p ∈ pairs ∧ ¬ Blocks p.
    rw [← h_converged] at hp
    simp only [mem_superoptimalSetStep_TEMPFIN] at hp
    exact hp.2
  · -- ∀ p ∈ ↑pairs, p ∉ ↑(superoptimal pairs profile) → Blocks profile (↑(...)) p
    intro p hp_pairs hp_notS
    rw [Finset.mem_coe] at hp_pairs
    rw [Finset.mem_coe] at hp_notS
    -- p ∈ pairs ∧ p ∉ superoptimal = F(superoptimal). So either p ∉ pairs (false) or p IS Blocked.
    have h_eq : superoptimalSetStep_TEMPFIN pairs profile (superoptimal pairs profile) =
                superoptimal pairs profile := h_converged
    by_contra hb
    apply hp_notS
    rw [← h_eq, mem_superoptimalSetStep_TEMPFIN]
    exact ⟨hp_pairs, hb⟩

end Computable

-- ============================================================================
-- § 7. Strong BiOT (eq. 9): Set-valued Prop + Finset-native form
-- ============================================================================

/-- [blutner-2000]'s **strong bidirectional OT** (eq. 9): a pair `p` is
    strong-optimal iff it survives one step of the blocking operator starting
    from the full pair set. Equivalently: `p ∈ pairs` and no element of `pairs`
    blocks `p` (the Q- and I-principles are evaluated independently against
    the full candidate set, not against a mutually-constrained survivor set).

    Set-valued Prop sibling of the Finset-native `strongOptimal` below;
    related to weak BiOT via the structural meta-theorem `strong_subset_weak`. -/
def IsStrongOptimal (pairs : Set (F × M)) (profile : F × M → List Nat)
    (p : F × M) : Prop :=
  p ∈ pairs ∧ ¬ Blocks profile pairs p

/-- Strong-optimal is exactly one step of the blocking operator. -/
@[simp] theorem isStrongOptimal_iff_mem_superoptimalSetStep_self
    (pairs : Set (F × M)) (profile : F × M → List Nat) (p : F × M) :
    IsStrongOptimal pairs profile p ↔ p ∈ superoptimalSetStep pairs profile pairs :=
  Iff.rfl

section StrongComputable

variable [DecidableEq F] [DecidableEq M]

instance IsStrongOptimal.decidableOnFinset
    (pairs : Finset (F × M)) (profile : F × M → List Nat) (p : F × M) :
    Decidable (IsStrongOptimal (↑pairs : Set (F × M)) profile p) := by
  unfold IsStrongOptimal
  exact inferInstance

/-- Finset-native strong-optimal computation: pairs in `pairs` not blocked by
    `pairs`. Computable via `Blocks.decidableOnFinset`; consumer-facing
    canonical form for per-paper `decide` proofs. -/
def strongOptimal (pairs : Finset (F × M)) (profile : F × M → List Nat) :
    Finset (F × M) :=
  pairs.filter (fun p => ¬ Blocks profile (↑pairs : Set _) p)

@[simp] theorem mem_strongOptimal {pairs : Finset (F × M)}
    {profile : F × M → List Nat} {p : F × M} :
    p ∈ strongOptimal pairs profile ↔
    p ∈ pairs ∧ ¬ Blocks profile (↑pairs : Set _) p := by
  simp [strongOptimal]

end StrongComputable

-- ============================================================================
-- § 8. Strong ⊂ Weak: the structural meta-theorem
-- ============================================================================

/-- [blutner-2000] p. 12: "It is simple to prove that a pair which is
    optimal (strong bidirection), is super-optimal (weak bidirection) as
    well."

    Mathlib-grounded structural proof: the singleton `{p}` is a post-fixed
    point of the squared blocking operator `superoptimalSetStepSq` whenever `p`
    is strong-optimal — the only candidate blocker for `p` from
    `F({p}) ⊆ pairs` is excluded by strong-optimality (no `pairs`-element
    blocks `p`) plus `Blocks.mono`. Coinduction (`OrderHom.le_gfp`) then
    delivers `{p} ⊆ gfp`, giving `p ∈ superoptimalSet pairs profile`.

    No algorithmic detour through iterated removal — the result is a direct
    consequence of `OrderHom.gfp` being the supremum of post-fixed points
    on the `Set α` complete lattice. -/
theorem isStrongOptimal_imp_mem_superoptimalSet
    {pairs : Set (F × M)} {profile : F × M → List Nat} {p : F × M}
    (hp : IsStrongOptimal pairs profile p) :
    p ∈ superoptimalSet pairs profile := by
  obtain ⟨hp_pairs, hp_unblocked⟩ := hp
  -- Direct witness: p ∈ F²({p}) (singleton p is in its own squared image).
  have h_p_F2 : p ∈ superoptimalSetStepSq pairs profile (Set.singleton p) := by
    refine ⟨hp_pairs, ?_⟩
    intro hblocks
    -- F({p}) ⊆ pairs, so blocker in F({p}) ⇒ blocker in pairs ⇒ contradicts strong-optimality.
    exact hp_unblocked
      (hblocks.mono (superoptimalSetStep_subset pairs profile (Set.singleton p)))
  -- Coinduction: {p} ≤ F²({p}) ⇒ {p} ≤ gfp.
  have h_le_gfp : Set.singleton p ≤ superoptimalSet pairs profile :=
    OrderHom.le_gfp _ (Set.singleton_subset_iff.mpr h_p_F2)
  exact h_le_gfp rfl

/-- Set-valued strong ⊂ weak as a Set-inclusion. -/
theorem isStrongOptimal_subset_superoptimalSet
    (pairs : Set (F × M)) (profile : F × M → List Nat) :
    {p | IsStrongOptimal pairs profile p} ⊆ superoptimalSet pairs profile :=
  fun _ => isStrongOptimal_imp_mem_superoptimalSet

/-- Finset version of strong ⊂ weak: when `superoptimal` converges, every
    strong-optimal pair is also weak-optimal. Per-paper consumers prove the
    convergence hypothesis with `by decide`. -/
theorem strongOptimal_subset_superoptimal
    [DecidableEq F] [DecidableEq M]
    (pairs : Finset (F × M)) (profile : F × M → List Nat)
    (h_converged : superoptimalSetStep_TEMPFIN pairs profile (superoptimal pairs profile) =
                   superoptimal pairs profile) :
    strongOptimal pairs profile ⊆ superoptimal pairs profile := by
  intro p hp
  rw [mem_strongOptimal] at hp
  -- Lift to Set: p ∈ superoptimalSet pairs profile.
  have hp_gfp : p ∈ superoptimalSet (↑pairs : Set _) profile :=
    isStrongOptimal_imp_mem_superoptimalSet hp
  -- Bridge: ↑(superoptimal) = superoptimalSet ↑pairs profile.
  rw [← superoptimal_coe_eq_set _ _ h_converged] at hp_gfp
  rwa [Finset.mem_coe] at hp_gfp

end Pragmatics.Bidirectional
