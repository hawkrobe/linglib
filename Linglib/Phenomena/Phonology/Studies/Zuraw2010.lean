import Linglib.Theories.Phonology.OptimalityTheory.Constraints
import Linglib.Core.Constraint.PermSubsetCombinatorics

/-!
# @cite{zuraw-2010}: Factorial Typology of Nasal Substitution

Formalizes the factorial typology of Tagalog-style nasal substitution
from @cite{zuraw-2010} (NLLT 28: 417–472). When a nasal-final prefix
(e.g. maŋ-) is concatenated with an obstruent-initial stem, the nasal
and the obstruent may **coalesce** into a single nasal retaining the
place of the latter:

- `maŋ+bigáj` → `mamigáj` 'to distribute' (nasal substitution = YES)
- `paŋ+tabój` → `pantabój` 'to goad' (faithful cluster = NO)

## Substrate consumption

Each constraint ranking is an `Equiv.Perm (Fin 6)`. For each stem-initial
consonant `c`, the YES/NO decision under ranking `σ` is determined by the
*first* distinguishing constraint in the ranking, captured by
`Core.Constraint.PermSubsetCombinatorics.perm_filter_head_in_card`:

  `(# rankings where YES wins for c) × |D_c| = 6! × |Y_c ∩ D_c|`

where `D_c` is the set of constraint indices that distinguish YES from NO
for `c`, and `Y_c ⊆ D_c` is the subset that favors YES. This closed form
yields each per-consonant substitution count by a single arithmetic step,
with no 6! = 720 enumeration.

## Constraint set

Six constraints drive the typology:

- **DEP-C** (faithfulness): penalizes deletion of the stem-initial C —
  i.e. violated by NO (the faithful retention) for every stem
- **\*NC** (markedness): penalizes nasal + voiceless-obstruent clusters
- **\*ASSOC** (markedness): penalizes multiple association (coalescence)
- **\*\[ŋ, \*\[n, \*\[m** (markedness, stringent hierarchy): penalizes
  stem-initial nasals resulting from coalescence

## Implicational universals (structural)

The voicing effect (voiced→YES implies voiceless→YES at the same place)
and the place effect (backer→YES implies fronter→YES within a voicing
class) follow from the set-theoretic relationships between `D_c` and
`Y_c` across consonants — proved structurally per-ranking, no enumeration.

## Dictionary data

@cite{zuraw-2010}'s Tagalog dictionary counts confirm the voicing
effect: voiceless stems show higher substitution rates than voiced
stems at the labial place (p: 253/263 vs b: 177/277).

## Relation to other Tagalog NS analyses

The closely-related study files
`Phenomena/Phonology/Studies/ZurawHayes2017.lean` and
`Phenomena/Phonology/Studies/Magri2025.lean` analyze a 2×2 sub-square
of this same phenomenon (maŋ-other / paŋ-res prefixes × /b/ /k/ stems)
under a different constraint inventory (DEP-C / \*NC / \*[stemŋ] /
\*[stemŋ]/n / prefix-indexed UNIFORMITY) for a MaxEnt analysis of the
Hayes-Zuraw shifted-sigmoids generalization. The constraint sets and
the data slices differ; the two strands are complementary readings of
@cite{zuraw-2010}'s underlying phenomenon.
-/

namespace Zuraw2010

open Core.Constraint.OT Phonology.Constraints
open Core.Constraint.PermSubsetCombinatorics

/-! ## § 0: Stems, Substitution Decisions, Dictionary Counts -/

/-- The six stem-initial obstruents in @cite{zuraw-2010}'s nasal
    substitution typology. Coalescence maps each to its homorganic
    nasal: p,b → m; t,d → n; k,g → ŋ. -/
inductive StemC where
  | p | t | k   -- voiceless
  | b | d | g   -- voiced
  deriving DecidableEq, Repr

/-- Whether nasal substitution applies. -/
inductive SubSt where
  | yes  -- coalescence: nasal + obstruent → nasal
  | no   -- faithful: nasal cluster preserved
  deriving DecidableEq, Repr

/-- A candidate is a stem consonant paired with a substitution decision. -/
abbrev NSCand := StemC × SubSt

/-- Dictionary substitution rate for voiceless labial p (253/263 ≈ 96.2%).
    Counts as reported in @cite{zuraw-2010} from a Tagalog dictionary
    corpus study. -/
def dictRate_p : ℚ := 253 / 263

/-- Dictionary substitution rate for voiced labial b (177/277 ≈ 63.9%).
    Counts as reported in @cite{zuraw-2010} from a Tagalog dictionary
    corpus study. -/
def dictRate_b : ℚ := 177 / 277

/-- **Voicing effect in dictionary data** (labial place): voiceless p
    has a higher substitution rate than voiced b. -/
theorem dict_voicing_labial : dictRate_p > dictRate_b := by
  norm_num [dictRate_p, dictRate_b]

-- ============================================================================
-- § 1: Constraints
-- ============================================================================

/-- DEP-C: penalizes the faithful candidate for every input C without a
    surface correspondent. Violated by NO for every stem (the YES candidate
    deletes the stem-initial C; NO retains it).
    DEP-C as the constraint violated by non-substitution follows
    @cite{zuraw-2010}'s discussion in §4.2.
    NB: in earlier commits this constraint was labeled \*NC; renamed for
    fidelity to the paper's notation, where \*NC is reserved for the
    voiceless-only constraint (see `starNC` below). -/
def depC : NamedConstraint NSCand :=
  mkMark "DEP-C" fun c => c.2 = SubSt.no

/-- \*NC: penalizes nasal + voiceless-obstruent sequences. Violated by NO
    for voiceless stems only. Per @cite{zuraw-2010} ex. (17):
    "\*NC: A [+nasal] segment must not be immediately followed by a
    [-voice, -sonorant] segment". -/
def starNC : NamedConstraint NSCand :=
  mkMark "*NC" fun c => c.1 ∈ [StemC.p, .t, .k] ∧ c.2 = .no

/-- *ASSOC: penalizes multiple association (coalescence). Violated by YES. -/
def starAssoc : NamedConstraint NSCand :=
  mkMark "*ASSOC" fun c => c.2 = SubSt.yes

/-- *\[ŋ: stems must not begin with ŋ. Violated by YES for velar stems. -/
def starInitVelar : NamedConstraint NSCand :=
  mkMark "*[ŋ" fun c => c.1 ∈ [StemC.k, .g] ∧ c.2 = .yes

/-- *\[n: stems must not begin with n or backer. Violated by YES for
    coronal and velar stems. -/
def starInitCorVel : NamedConstraint NSCand :=
  mkMark "*[n" fun c => c.1 ∈ [StemC.t, .d, .k, .g] ∧ c.2 = .yes

/-- *\[m: stems must not begin with m or backer. Violated by YES for all. -/
def starInitAll : NamedConstraint NSCand :=
  mkMark "*[m" fun c => c.2 = SubSt.yes

/-- The six constraints, indexed for substrate consumption.
    Order matches @cite{zuraw-2010}'s six freely-ranked constraints:
    DEP-C, \*NC, \*ASSOCIATE, \*[ŋ, \*[n, \*[m. -/
def constraint : Fin 6 → NamedConstraint NSCand
  | 0 => depC
  | 1 => starNC
  | 2 => starAssoc
  | 3 => starInitVelar
  | 4 => starInitCorVel
  | 5 => starInitAll

/-- Legacy list form, retained for callers that want a `List`. -/
def allConstraints : List (NamedConstraint NSCand) :=
  [depC, starNC, starAssoc, starInitVelar, starInitCorVel, starInitAll]

-- ============================================================================
-- § 2: Constraint Violation Profiles
-- ============================================================================

/-- The stringent *\[N hierarchy assigns increasing violation counts to
    nasals at backer places: labial m=1, coronal n=2, velar ŋ=3. -/
theorem stringency_violations :
    starInitAll.eval (.p, .yes) + starInitCorVel.eval (.p, .yes) +
      starInitVelar.eval (.p, .yes) = 1 ∧
    starInitAll.eval (.t, .yes) + starInitCorVel.eval (.t, .yes) +
      starInitVelar.eval (.t, .yes) = 2 ∧
    starInitAll.eval (.k, .yes) + starInitCorVel.eval (.k, .yes) +
      starInitVelar.eval (.k, .yes) = 3 := by decide

/-- *ASSOC and *\[m have identical violation profiles. -/
theorem assoc_eq_initAll (c : StemC) (s : SubSt) :
    starAssoc.eval (c, s) = starInitAll.eval (c, s) := by
  cases c <;> cases s <;> rfl

-- ============================================================================
-- § 3: D_c and Y_c — distinguishing and YES-favoring constraint sets
-- ============================================================================

/-- For each consonant `c`, the set of constraint indices that distinguish
    `(c, YES)` from `(c, NO)`. The substitution outcome depends only on
    the relative order of these constraints. -/
def relevant : StemC → Finset (Fin 6)
  | .p => {0, 1, 2, 5}
  | .t => {0, 1, 2, 4, 5}
  | .k => {0, 1, 2, 3, 4, 5}
  | .b => {0, 2, 5}
  | .d => {0, 2, 4, 5}
  | .g => {0, 2, 3, 4, 5}

/-- For each consonant `c`, the constraint indices that favor YES
    (assign fewer violations to YES than NO). -/
def yesFav : StemC → Finset (Fin 6)
  | .p => {0, 1}
  | .t => {0, 1}
  | .k => {0, 1}
  | .b => {0}
  | .d => {0}
  | .g => {0}

-- ============================================================================
-- § 4: Per-Consonant Substitution Predicate (substrate-native)
-- ============================================================================

/-- YES wins over NO for consonant `c` under ranking `σ` iff the
    highest-ranked constraint that distinguishes them is YES-favoring. -/
def subWinsP (σ : Equiv.Perm (Fin 6)) (c : StemC) : Prop :=
  ∃ x ∈ yesFav c, (permDList σ (relevant c)).head? = some x

instance : ∀ (σ : Equiv.Perm (Fin 6)) (c : StemC), Decidable (subWinsP σ c) :=
  fun _ _ => Multiset.decidableExistsMultiset

/-- The per-consonant substitution count: number of rankings under
    which YES wins for consonant `c`. -/
def subCount (c : StemC) : Nat :=
  (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => subWinsP σ c)).card

-- ============================================================================
-- § 5: Closed-Form Substitution Counts via the Substrate
-- ============================================================================

/-- The substrate equation specialized to consonant `c`:
    `subCount c × |D_c| = 6! × |Y_c ∩ D_c|`. -/
theorem subCount_mul_relevant (c : StemC) :
    subCount c * (relevant c).card =
      720 * ((yesFav c) ∩ (relevant c)).card := by
  have h := perm_filter_head_in_card (relevant c) (yesFav c)
  have h720 : Nat.factorial 6 = 720 := by decide
  rw [h720] at h
  -- subCount and the substrate's filter use the same set, possibly with different
  -- DecidablePred instances. Use Finset.filter_congr (Iff.rfl) to bridge.
  have h_filter : Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => subWinsP σ c) =
      Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) =>
        ∃ x ∈ yesFav c, (permDList σ (relevant c)).head? = some x) :=
    Finset.filter_congr (fun _ _ => Iff.rfl)
  show (Finset.univ.filter (fun σ : Equiv.Perm (Fin 6) => subWinsP σ c)).card *
      (relevant c).card = _
  rw [h_filter]; exact h

/-- Substitution count for voiceless labial p: 360 of 720 rankings. -/
theorem subCount_p : subCount .p = 360 := by
  have h := subCount_mul_relevant .p
  have hD : (relevant .p).card = 4 := by decide
  have hY : ((yesFav .p) ∩ (relevant .p)).card = 2 := by decide
  rw [hD, hY] at h; omega

/-- Substitution count for voiceless coronal t: 288 of 720 rankings. -/
theorem subCount_t : subCount .t = 288 := by
  have h := subCount_mul_relevant .t
  have hD : (relevant .t).card = 5 := by decide
  have hY : ((yesFav .t) ∩ (relevant .t)).card = 2 := by decide
  rw [hD, hY] at h; omega

/-- Substitution count for voiceless velar k: 240 of 720 rankings. -/
theorem subCount_k : subCount .k = 240 := by
  have h := subCount_mul_relevant .k
  have hD : (relevant .k).card = 6 := by decide
  have hY : ((yesFav .k) ∩ (relevant .k)).card = 2 := by decide
  rw [hD, hY] at h; omega

/-- Substitution count for voiced labial b: 240 of 720 rankings. -/
theorem subCount_b : subCount .b = 240 := by
  have h := subCount_mul_relevant .b
  have hD : (relevant .b).card = 3 := by decide
  have hY : ((yesFav .b) ∩ (relevant .b)).card = 1 := by decide
  rw [hD, hY] at h; omega

/-- Substitution count for voiced coronal d: 180 of 720 rankings. -/
theorem subCount_d : subCount .d = 180 := by
  have h := subCount_mul_relevant .d
  have hD : (relevant .d).card = 4 := by decide
  have hY : ((yesFav .d) ∩ (relevant .d)).card = 1 := by decide
  rw [hD, hY] at h; omega

/-- Substitution count for voiced velar g: 144 of 720 rankings. -/
theorem subCount_g : subCount .g = 144 := by
  have h := subCount_mul_relevant .g
  have hD : (relevant .g).card = 5 := by decide
  have hY : ((yesFav .g) ∩ (relevant .g)).card = 1 := by decide
  rw [hD, hY] at h; omega

/-- All six factorial percentages, matching @cite{zuraw-2010} §3.5's
    free-ranking summary (the prose enumerates them as 50%, 40%, 33%,
    33%, 25%, 20% for p, t/s, k, b, d, g respectively).
    Each derived in closed form from the substrate's
    `perm_filter_head_in_card` — no 6! enumeration. -/
theorem factorial_percentages :
    subCount .p = 360 ∧ subCount .t = 288 ∧ subCount .k = 240 ∧
    subCount .b = 240 ∧ subCount .d = 180 ∧ subCount .g = 144 :=
  ⟨subCount_p, subCount_t, subCount_k, subCount_b, subCount_d, subCount_g⟩

/-- The factorial percentages as fractions of 720 total rankings:
    p=50%, t=40%, k=33⅓%, b=33⅓%, d=25%, g=20%. -/
theorem factorial_rates :
    (subCount .p : ℚ) / 720 = 1/2 ∧
    (subCount .t : ℚ) / 720 = 2/5 ∧
    (subCount .k : ℚ) / 720 = 1/3 ∧
    (subCount .b : ℚ) / 720 = 1/3 ∧
    (subCount .d : ℚ) / 720 = 1/4 ∧
    (subCount .g : ℚ) / 720 = 1/5 := by
  rw [subCount_p, subCount_t, subCount_k, subCount_b, subCount_d, subCount_g]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num

-- ============================================================================
-- § 6: Place and Voicing Monotonicity (count-level)
-- ============================================================================

/-- Place monotonicity: the factorial percentage strictly decreases from
    labial to velar within each voicing class. -/
theorem place_monotonicity :
    subCount .p > subCount .t ∧ subCount .t > subCount .k ∧
    subCount .b > subCount .d ∧ subCount .d > subCount .g := by
  rw [subCount_p, subCount_t, subCount_k, subCount_b, subCount_d, subCount_g]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Voicing monotonicity: voiceless substitution count is at least as
    high as voiced at every place. -/
theorem voicing_monotonicity :
    subCount .p ≥ subCount .b ∧ subCount .t ≥ subCount .d ∧
    subCount .k ≥ subCount .g := by
  rw [subCount_p, subCount_t, subCount_k, subCount_b, subCount_d, subCount_g]
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================================
-- § 7: Implicational Universals (structural, per-ranking)
-- ============================================================================

/-- Helper: filtering `z :: zs` by `(· ∈ D)` when `z ∈ D` puts `z` first. -/
private lemma filter_cons_head_of_mem {α : Type*} [DecidableEq α]
    (D : Finset α) (z : α) (zs : List α) (hzD : z ∈ D) :
    ((z :: zs).filter (· ∈ D)).head? = some z := by
  rw [List.filter_cons, if_pos (by simpa using hzD)]
  rfl

/-- Helper: filtering `z :: zs` by `(· ∈ D)` when `z ∉ D` recurses to `zs`. -/
private lemma filter_cons_head_of_not_mem {α : Type*} [DecidableEq α]
    (D : Finset α) (z : α) (zs : List α) (hzD : z ∉ D) :
    ((z :: zs).filter (· ∈ D)).head? = (zs.filter (· ∈ D)).head? := by
  rw [List.filter_cons, if_neg (by simpa using hzD)]

/-- Helper: the head of a list filtered by `D` is the first element of
    the original list that lies in `D`. Used in both implication theorems.

    Hypotheses: `D' ⊆ D`, `Y' ⊆ Y`, and any "extra" element of `D \ D'`
    is in `Y` (so it's a YES-favoring element when it appears as head of
    `L.filter (· ∈ D)`). -/
private lemma head_filter_subset_extends
    {α : Type*} [DecidableEq α] {D D' Y Y' : Finset α}
    (h_D : D' ⊆ D) (h_Y : Y' ⊆ Y)
    (h_extra : ∀ x ∈ D, x ∉ D' → x ∈ Y) :
    ∀ (L : List α),
      (∃ x ∈ Y', (L.filter (· ∈ D')).head? = some x) →
      (∃ y ∈ Y, (L.filter (· ∈ D)).head? = some y) := by
  intro L
  induction L with
  | nil =>
    rintro ⟨_, _, hx⟩; simp at hx
  | cons z zs ih =>
    rintro ⟨x, hxY', hx⟩
    by_cases hzD : z ∈ D
    · refine ⟨z, ?_, filter_cons_head_of_mem D z zs hzD⟩
      by_cases hzD' : z ∈ D'
      · -- z is the head of the D'-filter, so z = x ∈ Y' ⊆ Y
        rw [filter_cons_head_of_mem D' z zs hzD'] at hx
        rw [show z = x from Option.some.inj hx]
        exact h_Y hxY'
      · exact h_extra z hzD hzD'
    · -- z ∉ D ⊇ D', so z ∉ D': both filters skip z
      have hzD' : z ∉ D' := fun h => hzD (h_D h)
      rw [filter_cons_head_of_not_mem D' z zs hzD'] at hx
      obtain ⟨y, hyY, hy⟩ := ih ⟨x, hxY', hx⟩
      exact ⟨y, hyY, (filter_cons_head_of_not_mem D z zs hzD).trans hy⟩

/-- Helper: when `D ⊆ D'`, if the head of `L.filter (· ∈ D')` is in
    `Y' ⊆ D`, then the head of `L.filter (· ∈ D)` exists, equals it,
    and lies in `Y` (assuming `Y' ⊆ Y`). Used for the place-effect
    implication where the "source" `c'` has the larger D. -/
private lemma head_filter_smaller_inherits
    {α : Type*} [DecidableEq α] {D D' Y Y' : Finset α}
    (h_D : D ⊆ D') (h_Y : Y' ⊆ Y) (h_Y_in_D : Y' ⊆ D) :
    ∀ (L : List α),
      (∃ x ∈ Y', (L.filter (· ∈ D')).head? = some x) →
      (∃ y ∈ Y, (L.filter (· ∈ D)).head? = some y) := by
  intro L
  induction L with
  | nil =>
    rintro ⟨_, _, hx⟩; simp at hx
  | cons z zs ih =>
    rintro ⟨x, hxY', hx⟩
    by_cases hzD' : z ∈ D'
    · -- z is the head of the D'-filter, so z = x ∈ Y' ⊆ D
      rw [filter_cons_head_of_mem D' z zs hzD'] at hx
      rw [show z = x from Option.some.inj hx]
      have hxD : x ∈ D := h_Y_in_D hxY'
      exact ⟨x, h_Y hxY', filter_cons_head_of_mem D x zs hxD⟩
    · -- z ∉ D' ⊇ D, so z ∉ D: both filters skip z
      have hzD : z ∉ D := fun h => hzD' (h_D h)
      rw [filter_cons_head_of_not_mem D' z zs hzD'] at hx
      obtain ⟨y, hyY, hy⟩ := ih ⟨x, hxY', hx⟩
      exact ⟨y, hyY, (filter_cons_head_of_not_mem D z zs hzD).trans hy⟩

/-- **Voicing-style implication**: if `c'` has a smaller distinguishing
    set than `c`, but `c`'s extras all favor YES, then `c' subbed ⇒ c
    subbed`. Used for voiced→voiceless implications. -/
theorem subWinsP_extends_smaller_D
    {c c' : StemC} {σ : Equiv.Perm (Fin 6)}
    (h_D : relevant c' ⊆ relevant c)
    (h_Y : yesFav c' ⊆ yesFav c)
    (h_extra : ∀ x ∈ relevant c, x ∉ relevant c' → x ∈ yesFav c)
    (h_c' : subWinsP σ c') : subWinsP σ c := by
  exact head_filter_subset_extends h_D h_Y h_extra (permToList σ) h_c'

/-- **Place-style implication**: if `c'` has a larger distinguishing
    set than `c`, but `c'`'s YES-favorers all lie in `c`'s smaller set,
    then `c' subbed ⇒ c subbed`. Used for backer→fronter implications
    within a voicing class. -/
theorem subWinsP_extends_larger_D
    {c c' : StemC} {σ : Equiv.Perm (Fin 6)}
    (h_D : relevant c ⊆ relevant c')
    (h_Y : yesFav c' ⊆ yesFav c)
    (h_subset : yesFav c' ⊆ relevant c)
    (h_c' : subWinsP σ c') : subWinsP σ c := by
  exact head_filter_smaller_inherits h_D h_Y h_subset (permToList σ) h_c'

/-- **Voicing effect, labial**: if voiced labial b undergoes substitution,
    so does voiceless labial p. Per-ranking, structural — no enumeration. -/
theorem voicing_b_implies_p (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .b → subWinsP σ .p :=
  subWinsP_extends_smaller_D (by decide) (by decide) (by decide)

/-- **Voicing effect, coronal**: voiced d subs implies voiceless t subs. -/
theorem voicing_d_implies_t (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .d → subWinsP σ .t :=
  subWinsP_extends_smaller_D (by decide) (by decide) (by decide)

/-- **Voicing effect, velar**: voiced g subs implies voiceless k subs. -/
theorem voicing_g_implies_k (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .g → subWinsP σ .k :=
  subWinsP_extends_smaller_D (by decide) (by decide) (by decide)

/-- **Place effect, voiceless k→t**: if velar k subs, coronal t also subs. -/
theorem place_k_implies_t (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .k → subWinsP σ .t :=
  subWinsP_extends_larger_D (by decide) (by decide) (by decide)

/-- **Place effect, voiceless t→p**: if coronal t subs, labial p also subs. -/
theorem place_t_implies_p (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .t → subWinsP σ .p :=
  subWinsP_extends_larger_D (by decide) (by decide) (by decide)

/-- **Place effect, voiced g→d**: if velar g subs, coronal d also subs. -/
theorem place_g_implies_d (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .g → subWinsP σ .d :=
  subWinsP_extends_larger_D (by decide) (by decide) (by decide)

/-- **Place effect, voiced d→b**: if coronal d subs, labial b also subs. -/
theorem place_d_implies_b (σ : Equiv.Perm (Fin 6)) :
    subWinsP σ .d → subWinsP σ .b :=
  subWinsP_extends_larger_D (by decide) (by decide) (by decide)

/-- **Tagalog-style maximal substitution**: if velar voiced g subs, every
    other consonant subs too. Composition of voicing + place effects. -/
theorem g_implies_all (σ : Equiv.Perm (Fin 6)) (h : subWinsP σ .g) :
    subWinsP σ .p ∧ subWinsP σ .t ∧ subWinsP σ .k ∧
    subWinsP σ .b ∧ subWinsP σ .d ∧ subWinsP σ .g := by
  have h_d := place_g_implies_d σ h
  have h_b := place_d_implies_b σ h_d
  have h_k := voicing_g_implies_k σ h
  have h_t := place_k_implies_t σ h_k
  have h_p := place_t_implies_p σ h_t
  exact ⟨h_p, h_t, h_k, h_b, h_d, h⟩

-- ============================================================================
-- § 8: Connection to Tagalog
-- ============================================================================

/-- Tagalog exhibits nasal substitution for all six consonants. The
    grammar realizing this corresponds to DEP-C (and \*NC, where
    voicelessness applies) ranked above every YES-disfavoring constraint.
    The probabilistic 2×2-square version of this pattern under a
    different constraint inventory is treated in
    `Phenomena/Phonology/Studies/ZurawHayes2017.lean` and
    `Phenomena/Phonology/Studies/Magri2025.lean`.

    Witness for full substitution: any ranking with DEP-C at position 0.
    Then for every consonant c, head of permDList σ (relevant c) = 0,
    which is in yesFav c. Concretely, the identity permutation suffices. -/
theorem tagalog_full_substitution :
    ∃ σ : Equiv.Perm (Fin 6),
      subWinsP σ .p ∧ subWinsP σ .t ∧ subWinsP σ .k ∧
      subWinsP σ .b ∧ subWinsP σ .d ∧ subWinsP σ .g := by
  refine ⟨1, ?_⟩  -- identity permutation: σ i = i, so first relevant index is 0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · refine ⟨0, by decide, ?_⟩
      decide

end Zuraw2010
