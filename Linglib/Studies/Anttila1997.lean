import Linglib.Phonology.HarmonicGrammar.PartiallyOrderedConstraints
import Linglib.Core.Optimization.PermSubsetCombinatorics
import Mathlib.Tactic.NormNum

/-!
# [anttila-1997]: Deriving Variation from Grammar

Formalizes the quantitative variation predictions for Finnish genitive
plurals from [anttila-1997]. Anttila's claim: free variation in
Finnish (and crucially, its statistical biases) is derivable from a
single partially-ranked OT grammar — the variant probabilities equal
the fraction of total rankings consistent with the partial ranking
under which that variant wins.

## The grammar

Anttila stratifies 16 constraints into 5 mutually-ranked strata, with
internal random ordering within each stratum
([anttila-1997] eq. (49)–(50), page 21):

  Set 1 ≫ Set 2 ≫ Set 3 ≫ Set 4 ≫ Set 5

  - Set 1: \*X̀.X̀ (1 constraint, NoClash)
  - Set 2: \*L̀, \*H̀ (2 constraints; secondary-stress *L, *H)
  - Set 3: \*H/I, \*Í, \*L.L (3 constraints)
  - Set 4: \*H/O, \*Ó, \*L/A, \*H.H, \*X.X, \*H́ (6 constraints; final
    constraint is `*H́` acute = primary-stressed-heavy, distinct from
    Set 2's `*H̀` grave = secondary-stressed-heavy)
  - Set 5: 8 lower constraints (irrelevant for the variation cases here)

## Substrate consumption

This file routes through the project's POC (Partially Ordered
Constraints) substrate. For each motif, a violation-profile function
`vp : Input → Variant → Fin n → ℕ` derives `relevant` (where vp
disagrees on the two variants) and `yesFav` (where vp favors the
chosen variant). `pocPredict` over `discrete n` (uniform sampling
over all `n!` total orders) gives the variant probability;
`picksAt_rate_eq` reduces `pocPredict` to `|Y ∩ D| / |D|` in closed
form — no enumeration of `n!` rankings.

Two POC instances, one per stratum:

- **Set 3 (n = 3)**: motif 3ab only. Input is `Unit` (single motif).
- **Set 4 (n = 6)**: motifs 4ab and 5ab. Input is `Set4Motif` to
  distinguish the two motifs' violation profiles.

## Note on candidate-feature substrate

We stipulate violation profiles via `vp` rather than defining
`Constraint` instances. This matches Anttila's own level of
abstraction: the paper works directly with violation profiles
([anttila-1997] page 22: "knowing that the weak variant violates
one constraint (\*L.L) while the strong variant violates two (\*H/I,
\*Í) gives us the result directly"). True `Constraint`
formalisations would require a Finnish syllable substrate (input
forms with stress / weight / sonority features feeding into syllable
structure) which doesn't yet exist in linglib.

## Predictions formalized

From [anttila-1997] table 52 (page 22) and table 53 (page 23):

  - **3ab** (`L.TÍI` ∼ `L.TI`, e.g. `naa.pu.rei.den` ∼ `naa.pu.ri.en`):
    decided in Set 3 (n=3). Strong wins 1/3, weak wins 2/3.
    Observed: 36.9% / 63.1% (215 / 368 corpus tokens).
  - **4ab** (`H.TÁA` ∼ `H.TA`, e.g. `máa.il.mòi.den` ∼ `máa.il.mo.jen`):
    decided in Set 4 (n=6) with both variants violating two Set-4
    constraints. Each wins 1/2.
    Observed: 50.5% / 49.5% (46 / 45 corpus tokens).
  - **5ab** (`H.TÓO` ∼ `H.TO`, e.g. `kór.jaa.mòi.den` ∼ `kór.jaa.mo.jen`):
    decided in Set 4. Strong wins 1/5, weak wins 4/5.
    Observed: 17.8% / 82.2% (76 / 350 corpus tokens).

## Out of scope

- **Categorical motifs 1ab, 2ab, 6ab.** Per [anttila-1997] table 52,
  these are decided by Set 1 (NoClash) and Set 2 (\*L̀ / \*H̀), which this
  file doesn't model. The categorical predictions follow from
  higher-stratum constraints decisively favoring one variant.
- **`Constraint` instances** for \*H/I, \*Í, \*L.L, etc. — would
  require a Finnish syllable substrate (see "Note on candidate-feature
  substrate" above).
- **Observed-vs-predicted comparison theorems.** The paper's table 53
  shows a small gap between predicted (1/3, 2/3, 1/2, 1/2, 1/5, 4/5)
  and observed; this gap is empirical noise around the discrete
  prediction (the paper itself notes "as the quantitative predictions
  of our model are discrete probabilities (1/2, 1/3, 1/5 etc.) it
  would be difficult to get any closer", page 23).

## Same closed form as [zuraw-2010], [coetzee-pater-2011]

Anttila's Finnish variation, Zuraw's Tagalog factorial typology, and
Coetzee & Pater's English t/d-deletion all reduce to the same
substrate predictor `pocPredict (discrete n)` with binary candidate
spaces — variant probability = `|Y ∩ D| / |D|` (where D distinguishes
and Y favors the chosen variant). The reusability across three
phonological domains validates the abstraction; see
`Studies/Zuraw2010.lean` and
`Studies/CoetzeePater2011.lean` for sister
consumers.
-/

namespace Anttila1997

open Core.Optimization HarmonicGrammar.PartialOrderConstraints

/-! ## § 0: Variant type — strong vs weak genitive plural -/

/-- The two genitive-plural variants: strong (heavy penult, final
    syllable onset /t/ or /d/) vs weak (light penult, onset /j/ or
    absent). See [anttila-1997] ex. (1) page 3. -/
inductive Variant
  | strong
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The opposite variant: `strong ↔ weak`. -/
def Variant.other : Variant → Variant
  | .strong => .weak
  | .weak   => .strong

@[simp] theorem Variant.other_strong : Variant.other .strong = .weak := rfl
@[simp] theorem Variant.other_weak   : Variant.other .weak   = .strong := rfl

/-- The two variants are distinct. -/
theorem Variant.ne_other : ∀ v : Variant, v ≠ v.other
  | .strong => fun heq => Variant.noConfusion heq
  | .weak   => fun heq => Variant.noConfusion heq

-- ============================================================================
-- § 1: Set 3 — three constraints, n = 3 (motif 3ab)
-- ============================================================================

/-- Set-3 candidate set per (trivial, single-motif) input. -/
def m3Cands : Unit → Finset Variant := fun _ => Finset.univ

/-- Set-3 violation profile for motif 3ab (`L.TÍI` ∼ `L.TI`). Constraint
    indexing matches [anttila-1997] eq. (50): `*H/I = 0`, `*Í = 1`,
    `*L.L = 2`. Strong (`L.TÍI`) violates `*H/I` and `*Í`; weak (`L.TI`)
    violates `*L.L`. -/
def m3Vp : Unit → Variant → Fin 3 → ℕ
  | (), .strong, ⟨0, _⟩ => 1   -- L.TÍI violates *H/I
  | (), .strong, ⟨1, _⟩ => 1   -- L.TÍI violates *Í
  | (), .weak,   ⟨2, _⟩ => 1   -- L.TI   violates *L.L
  | _,  _,       _      => 0

/-- Constraints in Set 3 that distinguish strong from weak for motif 3ab. -/
def relevant_3 : Finset (Fin 3) :=
  Finset.univ.filter (fun i => m3Vp () .strong i ≠ m3Vp () .weak i)

/-- Constraints in Set 3 that favor strong for motif 3ab. -/
def yesFav_3_strong : Finset (Fin 3) :=
  Finset.univ.filter (fun i => m3Vp () .strong i < m3Vp () .weak i)

/-- Constraints in Set 3 that favor weak for motif 3ab. -/
def yesFav_3_weak : Finset (Fin 3) :=
  Finset.univ.filter (fun i => m3Vp () .weak i < m3Vp () .strong i)

@[simp] theorem relevant_3_eq : relevant_3 = ({0, 1, 2} : Finset (Fin 3)) := by decide
@[simp] theorem yesFav_3_strong_eq : yesFav_3_strong = ({2} : Finset (Fin 3)) := by decide
@[simp] theorem yesFav_3_weak_eq : yesFav_3_weak = ({0, 1} : Finset (Fin 3)) := by decide

/-- Variant probability via POC sampling under the discrete partial order. -/
def subProb_3 (v : Variant) : ℚ :=
  pocPredict m3Cands m3Vp (discrete 3) () v

/-- The candidate set for motif 3, written as `{v, v.other}` for any
    variant `v` (used to satisfy `picksAt_rate_eq`'s two-cand hypothesis
    for both choices of `chosen`). -/
private theorem m3Cands_eq_pair (v : Variant) :
    m3Cands () = ({v, v.other} : Finset Variant) := by
  unfold m3Cands; cases v <;> (ext o; cases o <;> simp [Variant.other])

/-- Bridge from `pocPredict` to closed-form rate `|Y ∩ D| / |D|` for
    motif 3, factored once and reused by both rate theorems. -/
private theorem subProb_3_eq_rate (v : Variant)
    (D Y : Finset (Fin 3))
    (h_D : ∀ k, k ∈ D ↔ m3Vp () v k ≠ m3Vp () v.other k)
    (h_Y : ∀ k, k ∈ Y ↔ m3Vp () v k < m3Vp () v.other k) :
    subProb_3 v = ((Y ∩ D).card : ℚ) / (D.card : ℚ) :=
  pocPredict_discrete_binary_rate m3Cands m3Vp () v v.other
    (m3Cands_eq_pair v) (Variant.ne_other v) D Y h_D h_Y

/-- **Strong `L.TÍI` wins 1/3 of Set-3 rankings**. Closed form via
    `picksAt_rate_eq`: `|{2} ∩ {0,1,2}| / |{0,1,2}| = 1/3`. -/
theorem strongProb_3_eq : subProb_3 .strong = 1/3 := by
  rw [subProb_3_eq_rate .strong relevant_3 yesFav_3_strong
        (fun k => by simp [relevant_3])
        (fun k => by simp [yesFav_3_strong]),
      relevant_3_eq, yesFav_3_strong_eq,
      show (({2} : Finset (Fin 3)) ∩ {0, 1, 2}).card = 1 from by decide,
      show ({0, 1, 2} : Finset (Fin 3)).card = 3 from by decide]
  norm_num

/-- **Weak `L.TI` wins 2/3 of Set-3 rankings**. Matches
    [anttila-1997]'s observed frequency 63.1% for `naa.pu.ri.en`
    (table 53, row 3b). -/
theorem weakProb_3_eq : subProb_3 .weak = 2/3 := by
  rw [subProb_3_eq_rate .weak relevant_3 yesFav_3_weak
        (fun k => by
          simp only [relevant_3, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.symm, fun h => h.symm⟩)
        (fun k => by simp [yesFav_3_weak]),
      relevant_3_eq, yesFav_3_weak_eq,
      show (({0, 1} : Finset (Fin 3)) ∩ {0, 1, 2}).card = 2 from by decide,
      show ({0, 1, 2} : Finset (Fin 3)).card = 3 from by decide]
  norm_num

-- ============================================================================
-- § 2: Set 4 — six constraints, n = 6 (motifs 4ab and 5ab)
-- ============================================================================

/-- The two motifs decided by Set 4: 4ab (`H.TÁA` ∼ `H.TA`) and 5ab
    (`H.TÓO` ∼ `H.TO`). They share the same six-constraint stratum but
    have different violation profiles. -/
inductive Set4Motif
  | four
  | five
  deriving DecidableEq, Repr, Fintype

/-- Set-4 candidate set per motif. -/
def m45Cands : Set4Motif → Finset Variant := fun _ => Finset.univ

/-- Set-4 violation profile for motifs 4ab and 5ab. Constraint indexing
    matches [anttila-1997] eq. (50): `*H/O = 0`, `*Ó = 1`,
    `*L/A = 2`, `*H.H = 3`, `*X.X = 4`, `*H́ = 5`.

    Motif 4ab (`H.TÁA` ∼ `H.TA`): strong violates `*H.H, *H́`; weak
    violates `*L/A, *X.X` (per [anttila-1997] table 52).
    Motif 5ab (`H.TÓO` ∼ `H.TO`): strong violates `*H/O, *Ó, *H.H, *H́`;
    weak violates only `*X.X`. -/
def m45Vp : Set4Motif → Variant → Fin 6 → ℕ
  | .four, .strong, ⟨3, _⟩ => 1   -- H.TÁA violates *H.H
  | .four, .strong, ⟨5, _⟩ => 1   -- H.TÁA violates *H́
  | .four, .weak,   ⟨2, _⟩ => 1   -- H.TA  violates *L/A
  | .four, .weak,   ⟨4, _⟩ => 1   -- H.TA  violates *X.X
  | .five, .strong, ⟨0, _⟩ => 1   -- H.TÓO violates *H/O
  | .five, .strong, ⟨1, _⟩ => 1   -- H.TÓO violates *Ó
  | .five, .strong, ⟨3, _⟩ => 1   -- H.TÓO violates *H.H
  | .five, .strong, ⟨5, _⟩ => 1   -- H.TÓO violates *H́
  | .five, .weak,   ⟨4, _⟩ => 1   -- H.TO  violates *X.X
  | _,     _,       _      => 0

/-- Set-4 distinguishing-constraint set for motif `m`. -/
def relevant_45 (m : Set4Motif) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => m45Vp m .strong i ≠ m45Vp m .weak i)

/-- Set-4 strong-favoring constraint set for motif `m`. -/
def yesFav_45_strong (m : Set4Motif) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => m45Vp m .strong i < m45Vp m .weak i)

/-- Set-4 weak-favoring constraint set for motif `m`. -/
def yesFav_45_weak (m : Set4Motif) : Finset (Fin 6) :=
  Finset.univ.filter (fun i => m45Vp m .weak i < m45Vp m .strong i)

@[simp] theorem relevant_45_four : relevant_45 .four = ({2, 3, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem relevant_45_five : relevant_45 .five = ({0, 1, 3, 4, 5} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_45_strong_four : yesFav_45_strong .four = ({2, 4} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_45_weak_four : yesFav_45_weak .four = ({3, 5} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_45_strong_five : yesFav_45_strong .five = ({4} : Finset (Fin 6)) := by decide
@[simp] theorem yesFav_45_weak_five : yesFav_45_weak .five = ({0, 1, 3, 5} : Finset (Fin 6)) := by decide

/-- Variant probability via POC sampling under the discrete partial order. -/
def subProb_45 (m : Set4Motif) (v : Variant) : ℚ :=
  pocPredict m45Cands m45Vp (discrete 6) m v

/-- The Set-4 candidate set for any motif, written as `{v, v.other}` for
    any variant `v`. -/
private theorem m45Cands_eq_pair (m : Set4Motif) (v : Variant) :
    m45Cands m = ({v, v.other} : Finset Variant) := by
  unfold m45Cands; cases v <;> (ext o; cases o <;> simp [Variant.other])

/-- Bridge from `pocPredict` to closed-form rate `|Y ∩ D| / |D|` for
    Set-4 motifs, factored once and reused by all four rate theorems. -/
private theorem subProb_45_eq_rate (m : Set4Motif) (v : Variant)
    (D Y : Finset (Fin 6))
    (h_D : ∀ k, k ∈ D ↔ m45Vp m v k ≠ m45Vp m v.other k)
    (h_Y : ∀ k, k ∈ Y ↔ m45Vp m v k < m45Vp m v.other k) :
    subProb_45 m v = ((Y ∩ D).card : ℚ) / (D.card : ℚ) :=
  pocPredict_discrete_binary_rate m45Cands m45Vp m v v.other
    (m45Cands_eq_pair m v) (Variant.ne_other v) D Y h_D h_Y

/-- **Motif 4ab strong `H.TÁA` wins 1/2 of Set-4 rankings**. Closed form
    via `picksAt_rate_eq`: `|{2,4} ∩ {2,3,4,5}| / |{2,3,4,5}| = 2/4 = 1/2`. -/
theorem strongProb_4ab_eq : subProb_45 .four .strong = 1/2 := by
  rw [subProb_45_eq_rate .four .strong (relevant_45 .four) (yesFav_45_strong .four)
        (fun k => by simp [relevant_45])
        (fun k => by simp [yesFav_45_strong]),
      relevant_45_four, yesFav_45_strong_four,
      show (({2, 4} : Finset (Fin 6)) ∩ {2, 3, 4, 5}).card = 2 from by decide,
      show ({2, 3, 4, 5} : Finset (Fin 6)).card = 4 from by decide]
  norm_num

/-- **Motif 4ab weak `H.TA` wins 1/2 of Set-4 rankings**. Matches
    [anttila-1997] observed 49.5% (table 53, row 4b). -/
theorem weakProb_4ab_eq : subProb_45 .four .weak = 1/2 := by
  rw [subProb_45_eq_rate .four .weak (relevant_45 .four) (yesFav_45_weak .four)
        (fun k => by
          simp only [relevant_45, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.symm, fun h => h.symm⟩)
        (fun k => by simp [yesFav_45_weak]),
      relevant_45_four, yesFav_45_weak_four,
      show (({3, 5} : Finset (Fin 6)) ∩ {2, 3, 4, 5}).card = 2 from by decide,
      show ({2, 3, 4, 5} : Finset (Fin 6)).card = 4 from by decide]
  norm_num

/-- **Motif 5ab strong `H.TÓO` wins 1/5 of Set-4 rankings**. Closed form:
    `|{4} ∩ {0,1,3,4,5}| / |{0,1,3,4,5}| = 1/5`. -/
theorem strongProb_5ab_eq : subProb_45 .five .strong = 1/5 := by
  rw [subProb_45_eq_rate .five .strong (relevant_45 .five) (yesFav_45_strong .five)
        (fun k => by simp [relevant_45])
        (fun k => by simp [yesFav_45_strong]),
      relevant_45_five, yesFav_45_strong_five,
      show (({4} : Finset (Fin 6)) ∩ {0, 1, 3, 4, 5}).card = 1 from by decide,
      show ({0, 1, 3, 4, 5} : Finset (Fin 6)).card = 5 from by decide]
  norm_num

/-- **Motif 5ab weak `H.TO` wins 4/5 of Set-4 rankings**. Matches
    [anttila-1997] observed 82.2% (table 53, row 5b). -/
theorem weakProb_5ab_eq : subProb_45 .five .weak = 4/5 := by
  rw [subProb_45_eq_rate .five .weak (relevant_45 .five) (yesFav_45_weak .five)
        (fun k => by
          simp only [relevant_45, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨fun h => h.symm, fun h => h.symm⟩)
        (fun k => by simp [yesFav_45_weak]),
      relevant_45_five, yesFav_45_weak_five,
      show (({0, 1, 3, 5} : Finset (Fin 6)) ∩ {0, 1, 3, 4, 5}).card = 4 from by decide,
      show ({0, 1, 3, 4, 5} : Finset (Fin 6)).card = 5 from by decide]
  norm_num

-- ============================================================================
-- § 3: Variation rates aggregator + binary completeness
-- ============================================================================

/-- All six variation rate predictions from [anttila-1997] table 52
    derived in closed form from the POC substrate. -/
theorem variation_rates :
    subProb_3 .strong = 1/3 ∧ subProb_3 .weak = 2/3 ∧
    subProb_45 .four .strong = 1/2 ∧ subProb_45 .four .weak = 1/2 ∧
    subProb_45 .five .strong = 1/5 ∧ subProb_45 .five .weak = 4/5 :=
  ⟨strongProb_3_eq, weakProb_3_eq,
   strongProb_4ab_eq, weakProb_4ab_eq,
   strongProb_5ab_eq, weakProb_5ab_eq⟩

/-- The two binary outcomes for motif 3ab partition the probability mass
    (sum to 1). Direct corollary of the rate equalities. -/
theorem binary_complete_3ab : subProb_3 .strong + subProb_3 .weak = 1 := by
  rw [strongProb_3_eq, weakProb_3_eq]; norm_num

/-- The two binary outcomes for motif 4ab partition the probability mass. -/
theorem binary_complete_4ab :
    subProb_45 .four .strong + subProb_45 .four .weak = 1 := by
  rw [strongProb_4ab_eq, weakProb_4ab_eq]; norm_num

/-- The two binary outcomes for motif 5ab partition the probability mass. -/
theorem binary_complete_5ab :
    subProb_45 .five .strong + subProb_45 .five .weak = 1 := by
  rw [strongProb_5ab_eq, weakProb_5ab_eq]; norm_num

end Anttila1997
