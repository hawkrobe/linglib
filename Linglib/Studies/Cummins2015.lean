import Linglib.Phonology.OptimalityTheory.Tableau
import Linglib.Semantics.Quantification.Numerals.Precision
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.Dist

/-!
# [cummins-2015]: OT constraints on numerically quantified expressions
[cummins-2015] [jansen-pollmann-2001] [prince-smolensky-1993]

[cummins-2015] models the choice of numerically quantified expressions as
classical Optimality Theory: six violable constraints — informativeness
(INFO), quantifier simplicity (QSIMP), numeral salience (NSAL), granularity
(GRAN), numeral priming (NPRI), and quantifier priming (QPRI) — evaluate
candidate expressions against a context, and each speaker's total ranking
deterministically selects a winner, so apparent probabilistic variation is
cross-speaker (and cross-context) ranking variation.

The constraint set runs through the project OT engine: the book's worked
three-constraint tableaux (INFO, NSAL, NPRI over rival `more than n` bounds,
with and without a primed numeral) are decide-checked `Tableau.optimal`
computations, and the book's harmonic-bounding argument — a candidate incurring
a subset of a rival's violations is preferred under any constraint ranking —
is proved for arbitrary constraint systems and instantiated in the toy system.

NSAL follows the book: one violation per missing [jansen-pollmann-2001] k-ness
type (10-, 5-, 2-, 2.5-ness; max 4). `kTypeCount` uses the substrate predicates,
whose witness search starts at base exponent 1 rather than
[jansen-pollmann-2001]'s 0 (`Studies/JansenPollmann2001.lean` records the
divergence); the book leaves the exact roundness inventory open. The
substrate's six-property `roundnessScore` decomposes as `kTypeCount` plus the
two raw divisibility indicators (`roundnessScore_eq_kTypeCount_add`) — the
properties the book sets aside as non-diagnostic of salience.
-/

namespace Cummins2015

open Constraints OptimalityTheory Semantics.Numerals.Roundness
open Semantics.Numerals.Precision (inferPrecisionMode
  inferPrecisionMode_eq_approximate_of_ten_dvd)

/-! ### NSAL: numeral salience as missing k-ness types -/

/-- Count of [jansen-pollmann-2001] k-ness types (10-, 5-, 2-, 2.5-ness) that
`n` exhibits (0–4). [cummins-2015] takes an entirely round number to be one
exhibiting all four. -/
def kTypeCount (n : ℕ) : ℕ :=
  (if HasKness n 1 then 1 else 0) + (if HasKness n 5 then 1 else 0) +
  (if HasKness n 2 then 1 else 0) + (if Has2_5ness n then 1 else 0)

theorem kTypeCount_le_four (n : ℕ) : kTypeCount n ≤ 4 := by
  unfold kTypeCount; split_ifs <;> omega

/-- NSAL violations ([cummins-2015]'s numeral salience constraint): one per
missing k-ness type. Entirely round numbers (100, 1000) incur none; numbers
with no k-ness incur the maximum of four. -/
def nsalViolations (n : ℕ) : ℕ := 4 - kTypeCount n

/-- NSAL violations complement the k-type count. -/
theorem nsalViolations_add_kTypeCount (n : ℕ) :
    nsalViolations n + kTypeCount n = 4 := by
  have := kTypeCount_le_four n
  unfold nsalViolations; omega

/-- Salience comparisons invert k-type comparisons: strictly more k-ness types
is strictly fewer NSAL violations. -/
theorem nsalViolations_lt_iff {n₁ n₂ : ℕ} :
    nsalViolations n₁ < nsalViolations n₂ ↔ kTypeCount n₂ < kTypeCount n₁ := by
  have h₁ := kTypeCount_le_four n₁
  have h₂ := kTypeCount_le_four n₂
  unfold nsalViolations
  omega

/-- The substrate's six-property roundness score is the k-type count plus the
two raw divisibility indicators [cummins-2015] sets aside as non-diagnostic. -/
theorem roundnessScore_eq_kTypeCount_add (n : ℕ) :
    roundnessScore n =
      kTypeCount n + ((if 5 ∣ n then 1 else 0) + (if 10 ∣ n then 1 else 0)) := by
  unfold roundnessScore kTypeCount
  split_ifs <;> omega

example : nsalViolations 100 = 0 := by decide
example : nsalViolations 1000 = 0 := by decide
example : nsalViolations 50 = 1 := by decide   -- lacks 2-ness only
example : nsalViolations 90 = 3 := by decide   -- 10-ness only
example : nsalViolations 102 = 4 := by decide  -- no k-ness at all

/-! ### Candidates, contexts, and the six constraints -/

/-- Quantifier form of a candidate numerical expression. -/
inductive QuantifierForm where
  | bare | exactly | about | moreThan | atLeast
  deriving DecidableEq

/-- Degrees of complexity for QSIMP: bare numerals are simplest; each overt
modifier adds a degree; superlative bounds cost more than comparative ones,
the experimentally supported asymmetry [cummins-2015] adopts to separate the
two single-bound families. -/
def QuantifierForm.complexity : QuantifierForm → ℕ
  | .bare => 0
  | .exactly | .about | .moreThan => 1
  | .atLeast => 2

/-- A candidate numerical expression: a quantifier form applied to a numeral. -/
structure Candidate where
  form : QuantifierForm
  numeral : ℕ
  deriving DecidableEq

/-- Utterance context: the speaker's knowledge (a lower bound on the value
under discussion, the shape of the book's worked examples), the contextually
set granularity level, and the primed numeral and quantifier, if any. -/
structure Context where
  lowerBound : ℕ
  granularity : ℕ
  primedNumeral : Option ℕ := none
  primedForm : Option QuantifierForm := none

/-- INFO ([cummins-2015]'s informativeness constraint): one violation per value
the expression admits that the speaker's knowledge `value ≥ ctx.lowerBound`
already excludes. Bounds admit the known-false values below the speaker's own
bound; point forms admit only their numeral. -/
def infoViolations (ctx : Context) : Constraint Candidate := fun c =>
  match c.form with
  | .moreThan => ctx.lowerBound - (c.numeral + 1)
  | .atLeast => ctx.lowerBound - c.numeral
  | _ => 0

/-- QSIMP: one violation per degree of quantifier complexity. -/
def qsimpViolations : Constraint Candidate := fun c => c.form.complexity

/-- NSAL over candidates: `nsalViolations` pulled back along the numeral. -/
def nsal : Constraint Candidate := Constraint.comap Candidate.numeral nsalViolations

/-- Decimal granularity level of a numeral: the finest base-10 scale on which
it sits (trailing zeros, capped at the thousands level). The book's granularity
is scale-relative; on the base-10 scales of the bare-number domain the level is
the trailing-zero count. -/
def granularityLevel (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if 1000 ∣ n then 3 else if 100 ∣ n then 2 else if 10 ∣ n then 1 else 0

/-- GRAN ([cummins-2015]'s granularity constraint): one violation per level of
mismatch between the contextually set granularity and the level used. -/
def granViolations (ctx : Context) : Constraint Candidate := fun c =>
  Nat.dist ctx.granularity (granularityLevel c.numeral)

/-- NPRI ([cummins-2015]'s numeral priming constraint): a violation iff a
numeral is primed in the preceding context and a different one is used.
Unprimed contexts violate nothing. -/
def npriViolations (ctx : Context) : Constraint Candidate := fun c =>
  match ctx.primedNumeral with
  | none => 0
  | some p => if c.numeral = p then 0 else 1

/-- QPRI ([cummins-2015]'s quantifier priming constraint): a violation iff a
quantifier is primed in the preceding context and a different one is used. -/
def qpriViolations (ctx : Context) : Constraint Candidate := fun c =>
  match ctx.primedForm with
  | none => 0
  | some f => if c.form = f then 0 else 1

/-- The six-constraint system, indexed in the book's enumeration order:
0 = INFO, 1 = QSIMP, 2 = NSAL, 3 = GRAN, 4 = NPRI, 5 = QPRI. -/
def con (ctx : Context) : CON Candidate 6 :=
  ![infoViolations ctx, qsimpViolations, nsal,
    granViolations ctx, npriViolations ctx, qpriViolations ctx]

/-- The book's count of possible idiolects: six constraints admit 720 total
rankings. -/
theorem card_rankings : Fintype.card (Ranking 6) = 720 := by
  rw [Fintype.card_perm, Fintype.card_fin]; rfl

/-! ### The worked tableaux

The book's toy system: INFO, NSAL, and NPRI adjudicate between rival `more
than n` bounds for a speaker who knows `value ≥ 103` (representative
numerals; the shape follows the book's example, where the informative bound's
numeral incurs the maximum four NSAL violations). `more than 102` is maximally
informative but non-salient; `more than 100` is salient but under-informative.
Unprimed, INFO-top speakers pick the former and NSAL-top speakers the latter;
priming 102 leaves only NSAL-top speakers on the round bound. Each ranking
selects a singleton — the book's deterministic-output point — and the factorial
typology has exactly the two idiolect types. -/

/-- The `more than n` candidate. -/
def mt (n : ℕ) : Candidate := ⟨.moreThan, n⟩

/-- Unprimed context: the speaker knows `value ≥ 103`; hundreds granularity. -/
def unprimed : Context := { lowerBound := 103, granularity := 2 }

/-- The same context with `102` primed in the preceding turn. -/
def primed : Context := { unprimed with primedNumeral := some 102 }

theorem unprimed_optimal_of_info_top :
    (Tableau.ofRanking [mt 100, mt 102]
      [infoViolations unprimed, nsal, npriViolations unprimed]).optimal
      = {mt 102} := by decide

theorem unprimed_optimal_of_nsal_top :
    (Tableau.ofRanking [mt 100, mt 102]
      [nsal, infoViolations unprimed, npriViolations unprimed]).optimal
      = {mt 100} := by decide

theorem primed_optimal_of_nsal_top :
    (Tableau.ofRanking [mt 100, mt 102]
      [nsal, npriViolations primed, infoViolations primed]).optimal
      = {mt 100} := by decide

theorem primed_optimal_of_npri_over_nsal :
    (Tableau.ofRanking [mt 100, mt 102]
      [npriViolations primed, nsal, infoViolations primed]).optimal
      = {mt 102} := by decide

/-- Both candidates surface across the six rankings — the book's point that a
deterministic OT system yields apparent variability via ranking variation. -/
theorem toy_factorialTypologySize :
    factorialTypologySize [mt 100, mt 102]
      [infoViolations unprimed, nsal, npriViolations unprimed] = 2 := by decide

/-! ### Harmonic bounding -/

/-- Pointwise violation dominance survives every ranking ([cummins-2015]'s
harmonic-bounding argument, one half): reordering coordinates preserves
pointwise `≤`, and pointwise `≤` entails lexicographic `≤`. -/
theorem profile_le_of_pointwise_le {C : Type*} {n : ℕ} (con : CON C n)
    (r : Ranking n) {c d : C} (h : ∀ i, con i c ≤ con i d) :
    buildViolationProfile (fun p => con (r p)) c
      ≤ buildViolationProfile (fun p => con (r p)) d :=
  Pi.toLex_monotone fun p => h (r p)

/-- A strictly harmonically bounded candidate — one incurring at least a
rival's violations everywhere and strictly more somewhere — is optimal under
no ranking whenever its bounder competes ([cummins-2015]: "preferred under any
constraint ranking"). -/
theorem not_mem_optimal_of_strictBounded {C : Type*} [DecidableEq C] {n : ℕ}
    {con : CON C n} {r : Ranking n} {cands : List C} {hne : cands ≠ []}
    {c d : C} (hc : c ∈ cands) (hle : ∀ i, con i c ≤ con i d)
    (hlt : ∃ i, con i c < con i d) :
    d ∉ (Tableau.ofPerm con r cands hne).optimal := by
  intro hd
  have hne' : (fun p => con (r p) c) ≠ (fun p => con (r p) d) := by
    obtain ⟨j, hj⟩ := hlt
    intro heq
    have := congrFun heq (r.symm j)
    rw [Equiv.apply_symm_apply] at this
    exact absurd this hj.ne
  exact absurd (Tableau.le_of_mem_optimal hd (List.mem_toFinset.mpr hc))
    (not_le.mpr (Pi.toLex_strictMono
      (lt_of_le_of_ne (fun p => hle (r p)) hne')))

/-- Instance in the full six-constraint system: `more than 100` harmonically
bounds `more than 90` in the unprimed context (weakly better on all six
constraints, strictly on INFO, NSAL, and GRAN), so `more than 90` wins under
none of the 720 rankings. -/
theorem moreThan90_never_optimal (r : Ranking 6) :
    mt 90 ∉ (Tableau.ofPerm (con unprimed) r [mt 90, mt 100, mt 102]).optimal :=
  not_mem_optimal_of_strictBounded (c := mt 100) (by decide) (by decide)
    (by decide)

/-! ### Round numerals and approximate construal -/

/-- Fully salient numerals admit the approximate construal: zero NSAL
violations force 10-ness, hence divisibility by 10, which the precision
substrate maps to `.approximate` — the association between round numbers and
approximate readings that [cummins-2015] inherits from the imprecision
literature. -/
theorem inferPrecisionMode_eq_approximate_of_nsalViolations_eq_zero {n : ℕ}
    (h : nsalViolations n = 0) : inferPrecisionMode n = .approximate := by
  have h10 : HasKness n 1 := by
    by_contra hk
    unfold nsalViolations kTypeCount at h
    rw [if_neg hk] at h
    split_ifs at h
  exact inferPrecisionMode_eq_approximate_of_ten_dvd h10.ten_dvd

end Cummins2015
