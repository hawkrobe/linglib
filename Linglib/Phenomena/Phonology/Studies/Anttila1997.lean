import Linglib.Core.Constraint.PermSubsetCombinatorics
import Mathlib.Tactic.NormNum

/-!
# @cite{anttila-1997}: Deriving Variation from Grammar

Formalizes the quantitative variation predictions for Finnish genitive
plurals from @cite{anttila-1997}. Anttila's claim: free variation in
Finnish (and crucially, its statistical biases) is derivable from a
single partially-ranked OT grammar — the variant probabilities equal
the fraction of total rankings consistent with the partial ranking
under which that variant wins.

## The grammar

Anttila stratifies 16 constraints into 5 mutually-ranked strata, with
internal random ordering within each stratum
(@cite{anttila-1997} (49)–(50)):

  Set 1 ≫ Set 2 ≫ Set 3 ≫ Set 4 ≫ Set 5

  - Set 1: \*X.X̀ (1 constraint, NoClash)
  - Set 2: \*L̀, \*H̀ (2 constraints)
  - Set 3: \*H/I, \*Í, \*L.L (3 constraints)
  - Set 4: \*H/O, \*Ó, \*L/A, \*H.H, \*X.X, \*H́ (6 constraints; final
    constraint is `*H́` acute = primary-stressed-heavy, distinct from
    Set 2's `*H̀` grave = secondary-stressed-heavy)
  - Set 5: 8 lower constraints (irrelevant for the variation cases here)

## Substrate consumption

Each variant comparison this paper formalizes is decided by the
internal ordering of *one* stratum (the variants share violations in
all higher strata). Within that stratum, the variant choice is the
classic head-in-Y predicate: the variant that the highest-ranked
distinguishing constraint penalizes less wins. So
`Core.Constraint.PermSubsetCombinatorics.perm_filter_head_in_card`
gives each prediction in closed form:

  `count × |D| = n! × |Y ∩ D|`

where `n = |stratum|`, `D` = constraints distinguishing the variants
within that stratum, `Y` = constraints that favor the chosen variant.
Variant probability = `count / n!`.

## Predictions formalized

From @cite{anttila-1997} table 53:

  - **3ab** (`L.TÍI` ∼ `L.TI`, e.g. `naa.pu.rei.den` ∼ `naa.pu.ri.en`):
    decided in Set 3 (n=3). Weak (`L.TI`) wins 2/3, strong wins 1/3.
  - **4ab** (`H.TÁA` ∼ `H.TA`, e.g. `máa.il.mòi.den` ∼ `máa.il.mo.jen`):
    decided in Set 4 (n=6) with both variants violating two Set-4
    constraints. Each wins 1/2.
  - **5ab** (`H.TÓO` ∼ `H.TO`, e.g. `kór.jaa.mòi.den` ∼ `kór.jaa.mo.jen`):
    decided in Set 4. Strong (`H.TÓO`) wins 1/5, weak wins 4/5.

The categorical motifs (1ab, 2ab, 6ab → 100%/0%) follow from
higher-stratum constraints decisively favoring one variant; we don't
formalize them here.

## Same closed form as @cite{zuraw-2010}

Zuraw's Tagalog factorial typology and Anttila's Finnish variation
predictions both reduce to the same substrate theorem. The reusability
across two phonological domains (English-style segmental constraints
vs. prosodic syllable-prominence constraints) validates the
abstraction.

## Implementation note

We state each prediction as a theorem about
`(Finset.univ.filter <explicit-predicate>).card`, not via a named
intermediate `def count_*` wrapper. Wrapping the filter card in a
named def causes Lean's typeclass elaboration to walk through the
Decidable instance for the predicate during theorem-statement
elaboration, which interacts badly with subsequent `rw` steps inside
the proof — the fix is to state theorems in the unfolded form.
-/

namespace Anttila1997

open Core.Constraint.PermSubsetCombinatorics

-- ============================================================================
-- § 1: Set 3 — three constraints, n = 3
-- ============================================================================

/-- Set-3 constraint indices: `*H/I = 0`, `*Í = 1`, `*L.L = 2`. -/
def D3ab : Finset (Fin 3) := {0, 1, 2}

/-- Constraints favoring strong `L.TÍI`: only `*L.L` (which `L.TI`
    violates). -/
def Y_LTII : Finset (Fin 3) := {2}

/-- Constraints favoring weak `L.TI`: `*H/I` and `*Í` (which `L.TÍI`
    violates). -/
def Y_LTI : Finset (Fin 3) := {0, 1}

/-- **Strong `L.TÍI` wins 1/3 of Set-3 rankings**: 2 out of 6.
    Closed form via `perm_filter_head_in_card`: `count × 3 = 6 × 1`. -/
theorem strong_3ab_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      ∃ x ∈ Y_LTII, (permDList σ D3ab).head? = some x)).card = 2 := by
  have h := perm_filter_head_in_card D3ab Y_LTII
  have h6 : Nat.factorial 3 = 6 := by decide
  have hD : D3ab.card = 3 := by decide
  have hY : (Y_LTII ∩ D3ab).card = 1 := by decide
  rw [h6, hD, hY] at h
  omega

/-- **Weak `L.TI` wins 2/3 of Set-3 rankings**: 4 out of 6. Matches
    @cite{anttila-1997}'s observed frequency 63.1% for `naa.pu.ri.en`
    (table 53, row 3b). -/
theorem weak_3ab_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      ∃ x ∈ Y_LTI, (permDList σ D3ab).head? = some x)).card = 4 := by
  have h := perm_filter_head_in_card D3ab Y_LTI
  have h6 : Nat.factorial 3 = 6 := by decide
  have hD : D3ab.card = 3 := by decide
  have hY : (Y_LTI ∩ D3ab).card = 2 := by decide
  rw [h6, hD, hY] at h
  omega

/-- The two Set-3 outcomes partition the 6 rankings. -/
theorem strong_plus_weak_3ab :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      ∃ x ∈ Y_LTII, (permDList σ D3ab).head? = some x)).card +
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      ∃ x ∈ Y_LTI, (permDList σ D3ab).head? = some x)).card = 6 := by
  rw [strong_3ab_count, weak_3ab_count]

-- ============================================================================
-- § 2: Set 4 — six constraints, n = 6
-- ============================================================================

/-- For motif 4ab (`H.TÁA` ∼ `H.TA`): both variants violate two Set-4
    constraints, but disjoint pairs.
    `H.TÁA` violates `*H.H = 3`, `*H́ = 5`.
    `H.TA` violates `*L/A = 2`, `*X.X = 4`.
    Distinguishing constraints: union `{2, 3, 4, 5}`. -/
def D4ab : Finset (Fin 6) := {2, 3, 4, 5}

/-- Constraints favoring strong `H.TÁA`: `H.TA`'s violations `{2, 4}`. -/
def Y_HTAA : Finset (Fin 6) := {2, 4}

/-- Constraints favoring weak `H.TA`: `H.TÁA`'s violations `{3, 5}`. -/
def Y_HTA : Finset (Fin 6) := {3, 5}

/-- **Strong `H.TÁA` wins 1/2 of Set-4 rankings** (4ab is symmetric).
    Closed form: `count × 4 = 720 × 2 = 1440`, so `count = 360`. -/
theorem strong_4ab_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTAA, (permDList σ D4ab).head? = some x)).card = 360 := by
  have h := perm_filter_head_in_card D4ab Y_HTAA
  have h720 : Nat.factorial 6 = 720 := by decide
  have hD : D4ab.card = 4 := by decide
  have hY : (Y_HTAA ∩ D4ab).card = 2 := by decide
  rw [h720, hD, hY] at h
  omega

/-- **Weak `H.TA` wins 1/2 of Set-4 rankings**. Matches
    @cite{anttila-1997} observed: 49.5% (table 53, row 4b). -/
theorem weak_4ab_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTA, (permDList σ D4ab).head? = some x)).card = 360 := by
  have h := perm_filter_head_in_card D4ab Y_HTA
  have h720 : Nat.factorial 6 = 720 := by decide
  have hD : D4ab.card = 4 := by decide
  have hY : (Y_HTA ∩ D4ab).card = 2 := by decide
  rw [h720, hD, hY] at h
  omega

-- ============================================================================
-- § 3: Set 4 again — motif 5ab (asymmetric)
-- ============================================================================

/-- For motif 5ab (`H.TÓO` ∼ `H.TO`): `H.TÓO` violates four Set-4
    constraints (`*H/O`, `*Ó`, `*H.H`, `*H́` = `{0, 1, 3, 5}`),
    `H.TO` violates only one (`*X.X` = `{4}`).
    Distinguishing constraints: `{0, 1, 3, 4, 5}`. -/
def D5ab : Finset (Fin 6) := {0, 1, 3, 4, 5}

/-- Constraints favoring strong `H.TÓO`: `H.TO`'s sole violation `{4}`. -/
def Y_HTOO : Finset (Fin 6) := {4}

/-- Constraints favoring weak `H.TO`: `H.TÓO`'s four violations
    `{0, 1, 3, 5}`. -/
def Y_HTO : Finset (Fin 6) := {0, 1, 3, 5}

/-- **Strong `H.TÓO` wins 1/5 of Set-4 rankings**: 144 of 720.
    Closed form: `count × 5 = 720 × 1 = 720`, so `count = 144`. -/
theorem strong_5ab_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTOO, (permDList σ D5ab).head? = some x)).card = 144 := by
  have h := perm_filter_head_in_card D5ab Y_HTOO
  have h720 : Nat.factorial 6 = 720 := by decide
  have hD : D5ab.card = 5 := by decide
  have hY : (Y_HTOO ∩ D5ab).card = 1 := by decide
  rw [h720, hD, hY] at h
  omega

/-- **Weak `H.TO` wins 4/5 of Set-4 rankings**: 576 of 720. Matches
    @cite{anttila-1997} observed 82.2% (table 53, row 5b). -/
theorem weak_5ab_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTO, (permDList σ D5ab).head? = some x)).card = 576 := by
  have h := perm_filter_head_in_card D5ab Y_HTO
  have h720 : Nat.factorial 6 = 720 := by decide
  have hD : D5ab.card = 5 := by decide
  have hY : (Y_HTO ∩ D5ab).card = 4 := by decide
  rw [h720, hD, hY] at h
  omega

-- ============================================================================
-- § 4: Variation rates as fractions
-- ============================================================================

/-- All three non-categorical predictions from @cite{anttila-1997}
    table 53 derived in closed form from `perm_filter_head_in_card`.
    Each ratio is `|Y ∩ D| / |D|`, the fraction of permutations of the
    relevant stratum where the corresponding variant wins. -/
theorem variation_rates :
    -- 3ab: strong 1/3, weak 2/3 (counts: 2/6, 4/6)
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      ∃ x ∈ Y_LTII, (permDList σ D3ab).head? = some x)).card : ℚ) / 6 = 1/3 ∧
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 3) =>
      ∃ x ∈ Y_LTI, (permDList σ D3ab).head? = some x)).card : ℚ) / 6 = 2/3 ∧
    -- 4ab: each 1/2 (counts: 360/720)
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTAA, (permDList σ D4ab).head? = some x)).card : ℚ) / 720 = 1/2 ∧
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTA, (permDList σ D4ab).head? = some x)).card : ℚ) / 720 = 1/2 ∧
    -- 5ab: strong 1/5, weak 4/5 (counts: 144/720, 576/720)
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTOO, (permDList σ D5ab).head? = some x)).card : ℚ) / 720 = 1/5 ∧
    ((Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
      ∃ x ∈ Y_HTO, (permDList σ D5ab).head? = some x)).card : ℚ) / 720 = 4/5 := by
  rw [strong_3ab_count, weak_3ab_count,
      strong_4ab_count, weak_4ab_count,
      strong_5ab_count, weak_5ab_count]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

end Anttila1997
