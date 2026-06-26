import Linglib.Phonology.OptimalityTheory.Constraints
import Linglib.Phonology.HarmonicGrammar.PartiallyOrderedConstraints
import Linglib.Core.Optimization.PermSubsetCombinatorics

/-!
# [zuraw-2010]: Factorial Typology of Nasal Substitution

Formalizes the factorial typology of Tagalog-style nasal substitution
from [zuraw-2010] (NLLT 28: 417–472). When a nasal-final prefix
(e.g. maŋ-) is concatenated with an obstruent-initial stem, the nasal
and the obstruent may **coalesce** into a single nasal retaining the
place of the latter:

- `maŋ+bigáj` → `mamigáj` 'to distribute' (nasal substitution = YES)
- `paŋ+tabój` → `pantabój` 'to goad' (faithful cluster = NO)

## Substrate consumption

This file routes through the project's POC (Partially Ordered
Constraints) substrate. For each stem-initial consonant `c`:

- `vp : StemC → SubSt → Fin 6 → ℕ` is the violation profile derived
  directly from the six constraint definitions (no separate stipulation).
- `relevant c : Finset (Fin 6)` and `yesFav c : Finset (Fin 6)` are
  computed from `vp` (`{i : vp c .yes i ≠ vp c .no i}` and
  `{i : vp c .yes i < vp c .no i}` respectively), with concrete
  `decide`-discharged values.
- `subProb c : ℚ` is `HarmonicGrammar.PartialOrderConstraints.pocPredict`
  applied to the discrete partial order on `Fin 6` — i.e. uniform sampling
  over all 720 total orders.
- The closed-form rate `|Y_c ∩ D_c| / |D_c|` follows by a single
  application of `picksAt_rate_eq` (which combines the binary-PicksAt
  bridge with `perm_filter_head_in_card`'s rational form), with
  no enumeration of 6! = 720 rankings.

The structural implication theorems in §7 reuse
`Core.Optimization.PermSubsetCombinatorics.head_filter_subset_extends`
and `head_filter_smaller_inherits` (lifted from earlier versions of
this file's private helpers) — pure list-filter monotonicity facts
that any binary-output OT factorial-typology study can consume.

## Constraint set

Six constraints drive the factorial typology, matching [zuraw-2010]'s
§4.2 footnote 17 (page 446) where the free-ranking enumeration appears:

- **NasSub** (project-canonical name following [zuraw-hayes-2017]
  ex. (3); extensionally coincides with [zuraw-2010]'s DEP-C —
  see `nasSub` docstring): violated by NO for every stem.
- **\*NC**, after [pater-1999]: penalizes nasal+voiceless-obstruent
  clusters; violated by NO for voiceless stems.
- **\*ASSOC** (faithfulness): penalizes adding a new association line;
  violated by YES for every stem.
- **\*\[ŋ, \*\[n, \*\[m** (markedness, stringent hierarchy after
  [prince-1997-stringency] and [delacy-2002]): penalize
  stem-initial nasals at velar/coronal/labial places respectively
  (with backer = more violations).

Other Zuraw 2010 constraints (MAX(+nas), UNIFORMITY, MORPHEMECOHESION,
NOCODA, \*GEMINATE, NASASSIM, IDENT(place), FAITH-OO, INTEGRITY-IO) are
held high-ranked per Zuraw's analytical choice and do not appear here;
they would not vary the YES/NO outcome on the candidate set considered.

## Implicational universals (structural)

The voicing effect (voiced→YES implies voiceless→YES at the same place)
and the place effect (backer→YES implies fronter→YES within a voicing
class) follow from the set-theoretic relationships between `D_c` and
`Y_c` across consonants — proved structurally per-ranking, no enumeration.
These typological generalizations are independently established in
[newman-1984]'s overview of Western Austronesian and replicated
in [blust-2004]'s 48-language survey.

## Dictionary data

[zuraw-2010]'s Tagalog dictionary counts (paper §2.2, page 423)
confirm the voicing effect: voiceless stems show higher substitution
rates than voiced stems at the labial place (p: 253/263 vs b: 177/277).

## Relation to other Tagalog NS analyses

The closely-related study files
`Studies/ZurawHayes2017.lean` and
`Studies/Magri2025.lean` analyze a 2×2 sub-square
of this same phenomenon (maŋ-other / paŋ-res prefixes × /b/ /k/ stems)
under a different constraint inventory (NasSub / \*NC / \*[stemŋ] /
\*[stemŋ]/n / prefix-indexed UNIFORMITY) for a MaxEnt analysis of the
Hayes-Zuraw shifted-sigmoids generalization. The constraint sets and
the data slices differ; the two strands are complementary readings of
[zuraw-2010]'s underlying phenomenon. ZurawHayes2017 and Magri2025
import the constraint identity definitions in §1 below via `comap` —
those definitions must remain stable.
-/

namespace Zuraw2010

open Constraints Core.Optimization Constraints OptimalityTheory OptimalityTheory
open Core.Optimization HarmonicGrammar.PartialOrderConstraints
open Core.Optimization Core.Optimization.PermSubsetCombinatorics

/-! ## § 0: Stems, Substitution Decisions, Dictionary Counts -/

/-- The six stem-initial obstruents in [zuraw-2010]'s nasal
    substitution typology. Coalescence maps each to its homorganic
    nasal: p,b → m; t,d → n; k,g → ŋ. -/
inductive StemC where
  | p | t | k   -- voiceless
  | b | d | g   -- voiced
  deriving DecidableEq, Repr, Fintype

/-- Whether nasal substitution applies. -/
inductive SubSt where
  | yes  -- coalescence: nasal + obstruent → nasal
  | no   -- faithful: nasal cluster preserved
  deriving DecidableEq, Repr, Fintype

/-- A candidate is a stem consonant paired with a substitution decision. -/
abbrev NSCand := StemC × SubSt

/-- Dictionary substitution rate for voiceless labial p (253/263 ≈ 96.2%).
    Counts as reported in [zuraw-2010] §2.2 (page 423) from a
    Tagalog dictionary corpus study. -/
def dictRate_p : ℚ := 253 / 263

/-- Dictionary substitution rate for voiced labial b (177/277 ≈ 63.9%).
    Counts as reported in [zuraw-2010] §2.2 (page 423) from a
    Tagalog dictionary corpus study. -/
def dictRate_b : ℚ := 177 / 277

/-- **Voicing effect in dictionary data** (labial place): voiceless p
    has a higher substitution rate than voiced b. -/
theorem dict_voicing_labial : dictRate_p > dictRate_b := by
  norm_num [dictRate_p, dictRate_b]

-- ============================================================================
-- § 1: Constraints
-- ============================================================================

/-- **NasSub** (project-canonical name following [zuraw-hayes-2017]
    ex. (3)). Extensionally equivalent to [zuraw-2010]'s DEP-C in
    the present 6-constraint analysis, though the two papers frame the
    same constraint differently:

    - [zuraw-2010] §3.1 (page 432, ex. 6): **faithfulness DEP-C**,
      penalizes inserting a segmental host for the floating [+nas]
      feature. Violated by NO candidate `pamⱼ-bɪɡaj` because the
      inserted [m] segment has no input correspondent.
    - [zuraw-hayes-2017] ex. (3): **markedness NasSub**, penalizes
      nasal + obstruent across morpheme boundaries.

    Both fire on every NO candidate in the present 6-constraint subset,
    so the violation profile coincides. We follow Zuraw-Hayes 2017's
    naming for consistency with downstream files
    (`ZurawHayes2017.lean`, `Magri2025.lean`).

    NB: In earlier commits this constraint was labeled \*NC; renamed
    for fidelity to the paper's notation, where \*NC is reserved for
    the voiceless-only constraint (see `starNC` below). -/
def nasSub : NamedConstraint NSCand :=
  mkMark "NasSub" fun c => c.2 = SubSt.no

/-- **\*NC**, after [pater-1999] (Austronesian NS) and
    [pater-2001] (revisited). Penalizes nasal + voiceless-obstruent
    sequences. Violated by NO for voiceless stems only. Per
    [zuraw-2010] ex. (17) (page 436): "\*NC: A [+nasal] segment
    must not be immediately followed by a [-voice, -sonorant] segment". -/
def starNC : NamedConstraint NSCand :=
  mkMark "*NC" fun c => c.1 ∈ [StemC.p, .t, .k] ∧ c.2 = .no

/-- **\*ASSOC**: penalizes adding a new association line (faithfulness).
    Per [zuraw-2010] (page 432, ex. 7), this is
    "*ASSOCIATE_hetero-morphemic" — the local restriction of a more
    general *ASSOC family that fires on association lines crossing
    morpheme boundaries. Violated by YES for every stem. -/
def starAssoc : NamedConstraint NSCand :=
  mkMark "*ASSOC" fun c => c.2 = SubSt.yes

/-- **\*\[ŋ**, after [prince-1997-stringency] and [delacy-2002]
    on stringency hierarchies; [zuraw-2010] ex. (19) (page 437).
    Stems must not begin with ŋ. Violated by YES for velar stems
    (k, g coalesce to stem-initial ŋ). -/
def starInitVelar : NamedConstraint NSCand :=
  mkMark "*[ŋ" fun c => c.1 ∈ [StemC.k, .g] ∧ c.2 = .yes

/-- **\*\[n**: stringency-hierarchy member after
    [prince-1997-stringency], [delacy-2002]; [zuraw-2010]
    ex. (19) (page 437). Stems must not begin with n or backer.
    Violated by YES for coronal and velar stems. -/
def starInitCorVel : NamedConstraint NSCand :=
  mkMark "*[n" fun c => c.1 ∈ [StemC.t, .d, .k, .g] ∧ c.2 = .yes

/-- **\*\[m**: top of the stringency hierarchy after
    [prince-1997-stringency], [delacy-2002]; [zuraw-2010]
    ex. (19) (page 437). Stems must not begin with m or backer.
    Violated by YES for all stems (every coalesced output is
    stem-initial nasal of some place). -/
def starInitAll : NamedConstraint NSCand :=
  mkMark "*[m" fun c => c.2 = SubSt.yes

/-- The six constraints, indexed for substrate consumption.
    Order matches [zuraw-2010]'s §4.2 footnote 17 (page 446):
    NasSub, \*NC, \*ASSOC, \*[ŋ, \*[n, \*[m. -/
def constraint : Fin 6 → NamedConstraint NSCand
  | 0 => nasSub
  | 1 => starNC
  | 2 => starAssoc
  | 3 => starInitVelar
  | 4 => starInitCorVel
  | 5 => starInitAll

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

/-- *ASSOC and *\[m have identical violation profiles on this candidate
    space. A coincidence of the 0/1-violation simplification rather than
    a deep identity: in [zuraw-2010]'s richer analysis, *ASSOC's
    flat penalty contrasts with *[m's stringency-hierarchy role. -/
theorem assoc_eq_initAll (c : StemC) (s : SubSt) :
    starAssoc.eval (c, s) = starInitAll.eval (c, s) := by
  cases c <;> cases s <;> rfl

-- ============================================================================
-- § 3: Substrate Adapter (POC-routed)
-- ============================================================================

/-- Violation profile derived from the constraint definitions, in the
    `Input → Output → Fin n → ℕ` shape required by
    `PartialOrderConstraints.PicksAt` and `pocPredict`. -/
def vp (c : StemC) (s : SubSt) (i : Fin 6) : ℕ :=
  (constraint i).eval (c, s)

/-- POC candidate set per stem: both YES and NO are available for every
    stem-initial obstruent. -/
def nsCands : StemC → Finset SubSt := fun _ => Finset.univ

/-- The set of constraint indices that distinguish YES from NO for stem
    `c` — i.e. constraints that disagree on the two candidates' violation
    counts. Computed directly from `vp`; see `relevant_*` below for
    concrete `decide`-discharged values. -/
def relevant (c : StemC) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => vp c .yes i ≠ vp c .no i)

/-- The set of constraint indices that **favor YES** for stem `c` —
    constraints assigning fewer violations to YES than to NO. Computed
    from `vp`; see `yesFav_*` below for concrete values. -/
def yesFav (c : StemC) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => vp c .yes i < vp c .no i)

/-! Concrete `decide`-discharged values for `relevant` and `yesFav`,
matching [zuraw-2010] §4.2 footnote 17's per-consonant constraint
subsets. -/

@[simp] theorem relevant_p : relevant .p = ({0, 1, 2, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_t : relevant .t = ({0, 1, 2, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_k : relevant .k = ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_b : relevant .b = ({0, 2, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_d : relevant .d = ({0, 2, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_g : relevant .g = ({0, 2, 3, 4, 5} : Finset (Fin 6)) := by decide

@[simp] theorem yesFav_p : yesFav .p = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_t : yesFav .t = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_k : yesFav .k = ({0, 1} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_b : yesFav .b = ({0} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_d : yesFav .d = ({0} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_g : yesFav .g = ({0} : Finset (Fin 6)) := by decide

/-- The candidate set for any stem is the two-element set `{.yes, .no}`. -/
private theorem nsCands_two (c : StemC) : nsCands c = {SubSt.yes, SubSt.no} := by
  unfold nsCands; ext o; cases o <;> simp

-- ============================================================================
-- § 4: Substitution Probability via POC
-- ============================================================================

/-- Substitution probability under POC sampling with the discrete partial
    order: the fraction of all `6! = 720` total orders that pick YES as
    the OT optimum for stem `c`. -/
def subProb (c : StemC) : ℚ :=
  pocPredict nsCands vp (discrete 6) c .yes

-- ============================================================================
-- § 5: Closed-Form Rates via the Substrate
-- ============================================================================

/-- The substrate-derived closed-form rate: `subProb c = |Y_c ∩ D_c| / |D_c|`,
    where `Y_c = yesFav c` and `D_c = relevant c`. Direct application of
    `pocPredict_discrete_binary_rate`. -/
private theorem subProb_eq_rate (c : StemC) :
    subProb c = ((yesFav c ∩ relevant c).card : ℚ) / (relevant c).card :=
  pocPredict_discrete_binary_rate nsCands vp c .yes .no
    (nsCands_two c) (fun heq => SubSt.noConfusion heq)
    (relevant c) (yesFav c)
    (fun k => by simp [relevant])
    (fun k => by simp [yesFav])

/-- Substitution rate for voiceless labial p: 50% of 720 rankings. -/
theorem subProb_p : subProb .p = 1/2 := by
  rw [subProb_eq_rate, relevant_p, yesFav_p,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 1, 2, 5}).card = 2 from by decide,
      show ({0, 1, 2, 5} : Finset (Fin 6)).card = 4 from by decide]
  norm_num

/-- Substitution rate for voiceless coronal t: 40% of 720 rankings. -/
theorem subProb_t : subProb .t = 2/5 := by
  rw [subProb_eq_rate, relevant_t, yesFav_t,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 1, 2, 4, 5}).card = 2 from by decide,
      show ({0, 1, 2, 4, 5} : Finset (Fin 6)).card = 5 from by decide]
  norm_num

/-- Substitution rate for voiceless velar k: 33⅓% of 720 rankings. -/
theorem subProb_k : subProb .k = 1/3 := by
  rw [subProb_eq_rate, relevant_k, yesFav_k,
      show (({0, 1} : Finset (Fin 6)) ∩ {0, 1, 2, 3, 4, 5}).card = 2 from by decide,
      show ({0, 1, 2, 3, 4, 5} : Finset (Fin 6)).card = 6 from by decide]
  norm_num

/-- Substitution rate for voiced labial b: 33⅓% of 720 rankings. -/
theorem subProb_b : subProb .b = 1/3 := by
  rw [subProb_eq_rate, relevant_b, yesFav_b,
      show (({0} : Finset (Fin 6)) ∩ {0, 2, 5}).card = 1 from by decide,
      show ({0, 2, 5} : Finset (Fin 6)).card = 3 from by decide]
  norm_num

/-- Substitution rate for voiced coronal d: 25% of 720 rankings. -/
theorem subProb_d : subProb .d = 1/4 := by
  rw [subProb_eq_rate, relevant_d, yesFav_d,
      show (({0} : Finset (Fin 6)) ∩ {0, 2, 4, 5}).card = 1 from by decide,
      show ({0, 2, 4, 5} : Finset (Fin 6)).card = 4 from by decide]
  norm_num

/-- Substitution rate for voiced velar g: 20% of 720 rankings. -/
theorem subProb_g : subProb .g = 1/5 := by
  rw [subProb_eq_rate, relevant_g, yesFav_g,
      show (({0} : Finset (Fin 6)) ∩ {0, 2, 3, 4, 5}).card = 1 from by decide,
      show ({0, 2, 3, 4, 5} : Finset (Fin 6)).card = 5 from by decide]
  norm_num

/-- All six factorial percentages, matching [zuraw-2010] §4.2
    footnote 17 (page 446)'s free-ranking summary (50%, 40%, 33⅓%,
    33⅓%, 25%, 20% for p, t, k, b, d, g respectively). Each derived in
    closed form from the substrate's `picksAt_rate_eq` — no 6!
    enumeration. -/
theorem factorial_rates :
    subProb .p = 1/2 ∧ subProb .t = 2/5 ∧ subProb .k = 1/3 ∧
    subProb .b = 1/3 ∧ subProb .d = 1/4 ∧ subProb .g = 1/5 :=
  ⟨subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g⟩

-- ============================================================================
-- § 6: Place and Voicing Monotonicity (rate-level)
-- ============================================================================

/-- **Place monotonicity** (model property): the factorial rate strictly
    decreases from labial to velar within each voicing class. NB: the
    place effect within voiceless is statistically *not* significant
    in [zuraw-2010]'s §5 acceptability data (paper page 459: in a
    mixed-effects model labials get a slightly *lower* rating difference
    than dentals — by 0.3 points — but this is not significant). The
    strict inequality below is therefore a property of the 6-constraint
    factorial idealization, not a paper-citable empirical claim about
    voiceless stems. -/
theorem place_monotonicity :
    subProb .p > subProb .t ∧ subProb .t > subProb .k ∧
    subProb .b > subProb .d ∧ subProb .d > subProb .g := by
  rw [subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-- **Voicing monotonicity**: voiceless substitution rate is at least as
    high as voiced at every place. Empirically robust across all of
    [zuraw-2010]'s data sources (Fig 1 dictionary, Fig 8 corpus,
    Fig 14 acceptability, Fig 15 web survey) — also significant in
    every mixed-effects model the paper reports. -/
theorem voicing_monotonicity :
    subProb .p ≥ subProb .b ∧ subProb .t ≥ subProb .d ∧
    subProb .k ≥ subProb .g := by
  rw [subProb_p, subProb_t, subProb_k, subProb_b, subProb_d, subProb_g]
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

-- ============================================================================
-- § 7: Implicational Universals (per-ranking, structural)
-- ============================================================================

/-! These structural per-ranking implication theorems formalize the
cross-linguistic implicational universals established in
[newman-1984]'s overview of Western Austronesian (replicated in
[blust-2004]'s 48-language survey): *if NS applies to a voiced
obstruent, it applies to the corresponding voiceless obstruent;
if NS applies to a stop, it applies to any fronter stop of the same
voicing*. The substrate proofs go via the lifted helpers
`Core.Optimization.PermSubsetCombinatorics.head_filter_subset_extends`
and `head_filter_smaller_inherits` (originally private here, lifted to
substrate alongside `perm_filter_head_in_card`). -/

/-- **Voicing-style extension**: if `c'` has a smaller distinguishing
    set than `c` but `c`'s extras all favor YES, then `c' substitutes`
    implies `c substitutes`. Used for voiced→voiceless implications. -/
theorem PicksAt_extends_smaller_D
    {σ : Equiv.Perm (Fin 6)} {c c' : StemC}
    (h_D : relevant c' ⊆ relevant c)
    (h_Y : yesFav c' ⊆ yesFav c)
    (h_extra : ∀ x ∈ relevant c, x ∉ relevant c' → x ∈ yesFav c)
    (h_c' : PicksAt nsCands vp σ c' .yes) :
    PicksAt nsCands vp σ c .yes := by
  rw [picksAt_binary_iff_permDList_head_lt
        nsCands vp c' .yes .no (nsCands_two c')
        (fun heq => SubSt.noConfusion heq)] at h_c'
  rw [picksAt_binary_iff_permDList_head_lt
        nsCands vp c .yes .no (nsCands_two c)
        (fun heq => SubSt.noConfusion heq)]
  exact head_filter_subset_extends h_D h_Y h_extra _ h_c'

/-- **Place-style extension**: if `c'` has a larger distinguishing set
    than `c` but `c'`'s YES-favorers all lie in `c`'s smaller set, then
    `c' substitutes` implies `c substitutes`. Used for backer→fronter
    implications within a voicing class. -/
theorem PicksAt_extends_larger_D
    {σ : Equiv.Perm (Fin 6)} {c c' : StemC}
    (h_D : relevant c ⊆ relevant c')
    (h_Y : yesFav c' ⊆ yesFav c)
    (h_subset : yesFav c' ⊆ relevant c)
    (h_c' : PicksAt nsCands vp σ c' .yes) :
    PicksAt nsCands vp σ c .yes := by
  rw [picksAt_binary_iff_permDList_head_lt
        nsCands vp c' .yes .no (nsCands_two c')
        (fun heq => SubSt.noConfusion heq)] at h_c'
  rw [picksAt_binary_iff_permDList_head_lt
        nsCands vp c .yes .no (nsCands_two c)
        (fun heq => SubSt.noConfusion heq)]
  exact head_filter_smaller_inherits h_D h_Y h_subset _ h_c'

/-- **Voicing effect, labial**: if voiced labial b undergoes substitution,
    so does voiceless labial p. Per-ranking, structural — no enumeration. -/
theorem voicing_b_implies_p (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .b .yes → PicksAt nsCands vp σ .p .yes :=
  PicksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- **Voicing effect, coronal**: voiced d subs implies voiceless t subs. -/
theorem voicing_d_implies_t (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .d .yes → PicksAt nsCands vp σ .t .yes :=
  PicksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- **Voicing effect, velar**: voiced g subs implies voiceless k subs. -/
theorem voicing_g_implies_k (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .g .yes → PicksAt nsCands vp σ .k .yes :=
  PicksAt_extends_smaller_D (by decide) (by decide) (by decide)

/-- **Place effect, voiceless k→t**: if velar k subs, coronal t also subs. -/
theorem place_k_implies_t (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .k .yes → PicksAt nsCands vp σ .t .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- **Place effect, voiceless t→p**: if coronal t subs, labial p also subs. -/
theorem place_t_implies_p (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .t .yes → PicksAt nsCands vp σ .p .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- **Place effect, voiced g→d**: if velar g subs, coronal d also subs. -/
theorem place_g_implies_d (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .g .yes → PicksAt nsCands vp σ .d .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- **Place effect, voiced d→b**: if coronal d subs, labial b also subs. -/
theorem place_d_implies_b (σ : Equiv.Perm (Fin 6)) :
    PicksAt nsCands vp σ .d .yes → PicksAt nsCands vp σ .b .yes :=
  PicksAt_extends_larger_D (by decide) (by decide) (by decide)

/-- **Tagalog-style maximal substitution**: if velar voiced g subs, every
    other consonant subs too. Composition of voicing + place effects —
    the upper end of the [newman-1984] / [blust-2004]
    implicational hierarchy. -/
theorem g_implies_all (σ : Equiv.Perm (Fin 6)) (h : PicksAt nsCands vp σ .g .yes) :
    PicksAt nsCands vp σ .p .yes ∧ PicksAt nsCands vp σ .t .yes ∧
    PicksAt nsCands vp σ .k .yes ∧ PicksAt nsCands vp σ .b .yes ∧
    PicksAt nsCands vp σ .d .yes ∧ PicksAt nsCands vp σ .g .yes := by
  have h_d := place_g_implies_d σ h
  have h_b := place_d_implies_b σ h_d
  have h_k := voicing_g_implies_k σ h
  have h_t := place_k_implies_t σ h_k
  have h_p := place_t_implies_p σ h_t
  exact ⟨h_p, h_t, h_k, h_b, h_d, h⟩

-- ============================================================================
-- § 8: Pattern (j) Witness — Maximal Substitution
-- ============================================================================

/-- A ranking exists under which every consonant undergoes substitution
    — corresponding to **Pattern (j)** in [zuraw-2010] Table 5
    (page 462), exemplified by Limos Kalinga, Ginaang Kalinga, and
    Sarangani Manobo (paper page 463; not Tagalog itself, which has
    *variation*: Fig 1 rates of 96/91/92/64/26/2% for p/t/k/b/d/g).
    Witness: the identity permutation, under which NasSub (constraint
    index 0) is highest-ranked and favors YES for every stem.

    The probabilistic 2×2-square version of the Tagalog variation
    pattern under a different constraint inventory is treated in
    `Studies/ZurawHayes2017.lean` and
    `Studies/Magri2025.lean`. -/
theorem pattern_j_witness :
    ∃ σ : Equiv.Perm (Fin 6),
      PicksAt nsCands vp σ .p .yes ∧ PicksAt nsCands vp σ .t .yes ∧
      PicksAt nsCands vp σ .k .yes ∧ PicksAt nsCands vp σ .b .yes ∧
      PicksAt nsCands vp σ .d .yes ∧ PicksAt nsCands vp σ .g .yes :=
  ⟨1, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Zuraw2010
