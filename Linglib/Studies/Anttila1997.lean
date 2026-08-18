import Linglib.Phonology.HarmonicGrammar.PartiallyOrderedConstraints
import Mathlib.Tactic.NormNum

/-!
# [anttila-1997]: Deriving Variation from Grammar

Formalizes the Finnish genitive-plural predictions of [anttila-1997]: free
variation — including its statistical biases — follows from a single
partially-ranked OT grammar, a variant's probability being the fraction of
total rankings under which it wins. Categorical outputs are the limiting case
where every ranking converges on the same winner (probability 1 or 0), so
categorical and variable motifs fall out of the same grammar.

Page and item numbers cite the ROA-63 manuscript version (May 1995); the
published chapter [anttila-1997] paginates 35–68.

## The grammar

Anttila's final grammar (eq. (50), page 21) stratifies 20 constraints into 5
mutually-ranked sets:

  - Set 1: \*X́.X́ (No Clash)
  - Set 2: \*Ĺ (Peak Prominence: no stressed lights), \*H (Weight-to-Stress:
    no unstressed heavies)
  - Set 3: \*H/I, \*Í, \*L.L
  - Set 4: \*H/O, \*Ó, \*L/A, \*H.H, \*H́, \*X.X
  - Set 5: 8 lower constraints (\*H/A, \*Á, \*L/O, \*L/I, \*A, \*O, \*I, \*L)

Sets 3 and 4 — the two "intermediary constraint sets" of eq. (49) — are
internally unranked: "While mutually ranked, the sets are internally random"
(page 21), so each evaluation samples a total order of the deciding stratum.
(Set 5 carries internal rankings, \*L/O ≫ \*L/I and \*A ≫ \*O ≫ \*I, but never
decides the motifs modeled here.)

## Substrate consumption

This file routes through the POC (Partially Ordered Constraints) substrate.
Per stratum, a violation-profile function `vp : Motif → Variant → Fin n → ℕ`
feeds `pocPredict` over `discrete n` (uniform sampling over all `n!`
stratum-internal rankings), and `pocPredict_discrete_binary_rate` reduces each
probability to the closed form `|Y ∩ D| / |D|`, where `D` is the set of
constraints distinguishing the two variants and `Y` those favoring the chosen
one — mirroring the paper's own shortcut ("Drawing the tableaux was in fact
unnecessary … knowing that the weak variant violates one constraint (\*L.L)
while the strong variant violates two (\*H/I, \*Í) gives us the result
directly", page 22).

Two POC instances, one per stratum: Set 3 (n = 3) decides motifs 1ab, 2ab,
3ab, 6ab; Set 4 (n = 6) decides motifs 4ab, 5ab.

We stipulate violation profiles via `vp` rather than defining `Constraint`
instances over candidate structures: the paper's quantitative section works
directly at violation-profile granularity (table (52)). True `Constraint`
formalisations would need a Finnish syllable substrate (stress / weight /
sonority features feeding syllable structure) which doesn't yet exist in
linglib.

## Predictions formalized

All six motif competitions of table (52) (page 22); observed 3-syllabic-stem
frequencies from table (53) (page 23):

  - **1ab** (`L.TÁA` ∼ `L.TA`, `ká.me.ròi.den` ∼ `ká.me.ro.jen`): strong wins
    in all rankings. Observed: 99.4% / 0.6% (720 / 4 corpus tokens).
  - **2ab** (`L.TÓO` ∼ `L.TO`, `hé.te.ròi.den` ∼ `hé.te.ro.jen`): strong wins
    in all rankings. Observed: 99.5% / 0.5% (389 / 2).
  - **3ab** (`L.TÍI` ∼ `L.TI`, `náa.pu.rèi.den` ∼ `náa.pu.ri.en`): strong wins
    1/3, weak 2/3. Observed: 36.9% / 63.1% (215 / 368).
  - **4ab** (`H.TÁA` ∼ `H.TA`, `máa.il.mòi.den` ∼ `máa.il.mo.jen`): each wins
    1/2. Observed: 50.5% / 49.5% (46 / 45).
  - **5ab** (`H.TÓO` ∼ `H.TO`, `kór.jaa.mòi.den` ∼ `kór.jaa.mo.jen`): strong
    wins 1/5, weak 4/5. Observed: 17.8% / 82.2% (76 / 350).
  - **6ab** (`H.TÍI` ∼ `H.TI`, `pó.lii.sèi.den` ∼ `pó.lii.si.en`): strong
    loses in all rankings. Observed: 1.6% / 98.4% (13 / 806).

## Out of scope

- **Sets 1, 2, and 5**, and the categorical short-stem patterns that the
  stress constraints of Sets 1–2 decide (mono- and disyllabic stems, the
  paper's §2.1 and §5.1–5.2).
- **Observed-vs-predicted comparison theorems.** Table (53)'s small gap
  between predicted and observed is empirical noise around the discrete
  prediction ("as the quantitative predictions of our model are discrete
  probabilities (1/2, 1/3, 1/5 etc.) it would be difficult to get any
  closer", page 23).
-/

namespace Anttila1997

open HarmonicGrammar.PartialOrderConstraints

/-! ### Variants -/

/-- The two genitive-plural variants: strong (heavy penult, final-syllable
onset /t/ or /d/) vs weak (light penult, onset /j/ or absent)
([anttila-1997] ex. (1), page 3). -/
inductive Variant
  | strong
  | weak
  deriving DecidableEq, Repr, Fintype

/-- The opposite variant: `strong ↔ weak`. -/
def Variant.other : Variant → Variant
  | .strong => .weak
  | .weak   => .strong

theorem Variant.ne_other (v : Variant) : v ≠ v.other := by cases v <;> decide

/-- Both variants compete for every input: the candidate set is the pair
`{v, v.other}` for either choice of `v`. -/
theorem Variant.univ_eq_pair (v : Variant) :
    (Finset.univ : Finset Variant) = {v, v.other} := by cases v <;> decide

/-! ### Set 3 — three constraints, motifs 1ab, 2ab, 3ab, 6ab -/

/-- The four motifs of [anttila-1997] table (52) decided by Set 3: 1ab
(`L.TÁA` ∼ `L.TA`), 2ab (`L.TÓO` ∼ `L.TO`), 3ab (`L.TÍI` ∼ `L.TI`), 6ab
(`H.TÍI` ∼ `H.TI`). -/
inductive Set3Motif
  | one
  | two
  | three
  | six
  deriving DecidableEq, Repr, Fintype

/-- Set-3 violation profile from [anttila-1997] table (52). Constraint
indices follow eq. (50): `*H/I = 0`, `*Í = 1`, `*L.L = 2`. -/
def set3Vp : Set3Motif → Variant → Fin 3 → ℕ
  | .one,   .weak,   ⟨2, _⟩ => 1   -- L.TA  violates *L.L
  | .two,   .weak,   ⟨2, _⟩ => 1   -- L.TO  violates *L.L
  | .three, .strong, ⟨0, _⟩ => 1   -- L.TÍI violates *H/I
  | .three, .strong, ⟨1, _⟩ => 1   -- L.TÍI violates *Í
  | .three, .weak,   ⟨2, _⟩ => 1   -- L.TI  violates *L.L
  | .six,   .strong, ⟨0, _⟩ => 1   -- H.TÍI violates *H/I
  | .six,   .strong, ⟨1, _⟩ => 1   -- H.TÍI violates *Í
  | _,      _,       _      => 0

/-- Probability that variant `v` wins motif `m` under uniform sampling of the
`3! = 6` Set-3-internal rankings. -/
def set3Prob (m : Set3Motif) (v : Variant) : ℚ :=
  pocPredict (fun _ => Finset.univ) set3Vp (discrete 3) m v

/-- Bridge from `pocPredict` to the closed-form rate `|Y ∩ D| / |D|` for
Set 3, shared by all eight rate theorems. -/
private theorem set3Prob_eq_rate (m : Set3Motif) (v : Variant)
    (D Y : Finset (Fin 3))
    (h_D : ∀ k, k ∈ D ↔ set3Vp m v k ≠ set3Vp m v.other k)
    (h_Y : ∀ k, k ∈ Y ↔ set3Vp m v k < set3Vp m v.other k) :
    set3Prob m v = ((Y ∩ D).card : ℚ) / (D.card : ℚ) :=
  pocPredict_discrete_binary_rate _ set3Vp m v v.other (Variant.univ_eq_pair v)
    v.ne_other D Y h_D h_Y

/-- **Motif 1ab strong `L.TÁA` wins in all rankings** — only the weak variant
violates a Set-3 constraint (`*L.L`), so `D = Y = {2}` and the rate is `1`:
the categorical limiting case. -/
theorem strongProb_1ab : set3Prob .one .strong = 1 := by
  rw [set3Prob_eq_rate .one .strong {2} {2} (by decide) (by decide)]
  decide +kernel

/-- **Motif 1ab weak `L.TA` loses in all rankings** ([anttila-1997]
table (53): observed 0.6%, an artefact of the spelling of /kollega/). -/
theorem weakProb_1ab : set3Prob .one .weak = 0 := by
  rw [set3Prob_eq_rate .one .weak {2} ∅ (by decide) (by decide)]
  decide +kernel

/-- **Motif 2ab strong `L.TÓO` wins in all rankings** — same Set-3 profile as
motif 1ab. -/
theorem strongProb_2ab : set3Prob .two .strong = 1 := by
  rw [set3Prob_eq_rate .two .strong {2} {2} (by decide) (by decide)]
  decide +kernel

/-- **Motif 2ab weak `L.TO` loses in all rankings**. -/
theorem weakProb_2ab : set3Prob .two .weak = 0 := by
  rw [set3Prob_eq_rate .two .weak {2} ∅ (by decide) (by decide)]
  decide +kernel

/-- **Motif 3ab strong `L.TÍI` wins 1/3 of Set-3 rankings**: `D = {0, 1, 2}`,
`Y = {2}` (`*L.L`, violated by weak alone). Observed 36.9% for
`náa.pu.rèi.den` ([anttila-1997] table (53), row 3a). -/
theorem strongProb_3ab : set3Prob .three .strong = 1/3 := by
  rw [set3Prob_eq_rate .three .strong {0, 1, 2} {2} (by decide) (by decide)]
  decide +kernel

/-- **Motif 3ab weak `L.TI` wins 2/3 of Set-3 rankings**: `Y = {0, 1}`
(`*H/I`, `*Í`, violated by strong alone). Observed 63.1% for `náa.pu.ri.en`
([anttila-1997] table (53), row 3b). -/
theorem weakProb_3ab : set3Prob .three .weak = 2/3 := by
  rw [set3Prob_eq_rate .three .weak {0, 1, 2} {0, 1} (by decide) (by decide)]
  decide +kernel

/-- **Motif 6ab strong `H.TÍI` loses in all rankings** — only the strong
variant violates Set-3 constraints (`*H/I`, `*Í`), so `Y = ∅`. -/
theorem strongProb_6ab : set3Prob .six .strong = 0 := by
  rw [set3Prob_eq_rate .six .strong {0, 1} ∅ (by decide) (by decide)]
  decide +kernel

/-- **Motif 6ab weak `H.TI` wins in all rankings** ([anttila-1997]
table (53): observed 98.4%). -/
theorem weakProb_6ab : set3Prob .six .weak = 1 := by
  rw [set3Prob_eq_rate .six .weak {0, 1} {0, 1} (by decide) (by decide)]
  decide +kernel

/-! ### Set 4 — six constraints, motifs 4ab and 5ab -/

/-- The two motifs of [anttila-1997] table (52) decided by Set 4: 4ab
(`H.TÁA` ∼ `H.TA`) and 5ab (`H.TÓO` ∼ `H.TO`). -/
inductive Set4Motif
  | four
  | five
  deriving DecidableEq, Repr, Fintype

/-- Set-4 violation profile from [anttila-1997] table (52). Constraint
indices follow eq. (50): `*H/O = 0`, `*Ó = 1`, `*L/A = 2`, `*H.H = 3`,
`*H́ = 4`, `*X.X = 5`. -/
def set4Vp : Set4Motif → Variant → Fin 6 → ℕ
  | .four, .strong, ⟨3, _⟩ => 1   -- H.TÁA violates *H.H
  | .four, .strong, ⟨4, _⟩ => 1   -- H.TÁA violates *H́
  | .four, .weak,   ⟨2, _⟩ => 1   -- H.TA  violates *L/A
  | .four, .weak,   ⟨5, _⟩ => 1   -- H.TA  violates *X.X
  | .five, .strong, ⟨0, _⟩ => 1   -- H.TÓO violates *H/O
  | .five, .strong, ⟨1, _⟩ => 1   -- H.TÓO violates *Ó
  | .five, .strong, ⟨3, _⟩ => 1   -- H.TÓO violates *H.H
  | .five, .strong, ⟨4, _⟩ => 1   -- H.TÓO violates *H́
  | .five, .weak,   ⟨5, _⟩ => 1   -- H.TO  violates *X.X
  | _,     _,       _      => 0

/-- Probability that variant `v` wins motif `m` under uniform sampling of the
`6! = 720` Set-4-internal rankings. -/
def set4Prob (m : Set4Motif) (v : Variant) : ℚ :=
  pocPredict (fun _ => Finset.univ) set4Vp (discrete 6) m v

/-- Bridge from `pocPredict` to the closed-form rate `|Y ∩ D| / |D|` for
Set 4, shared by all four rate theorems. -/
private theorem set4Prob_eq_rate (m : Set4Motif) (v : Variant)
    (D Y : Finset (Fin 6))
    (h_D : ∀ k, k ∈ D ↔ set4Vp m v k ≠ set4Vp m v.other k)
    (h_Y : ∀ k, k ∈ Y ↔ set4Vp m v k < set4Vp m v.other k) :
    set4Prob m v = ((Y ∩ D).card : ℚ) / (D.card : ℚ) :=
  pocPredict_discrete_binary_rate _ set4Vp m v v.other (Variant.univ_eq_pair v)
    v.ne_other D Y h_D h_Y

/-- **Motif 4ab strong `H.TÁA` wins 1/2 of Set-4 rankings**: `D = {2, 3, 4, 5}`,
`Y = {2, 5}` (`*L/A`, `*X.X`, violated by weak alone). Observed 50.5% for
`máa.il.mòi.den` ([anttila-1997] table (53), row 4a). -/
theorem strongProb_4ab : set4Prob .four .strong = 1/2 := by
  rw [set4Prob_eq_rate .four .strong {2, 3, 4, 5} {2, 5} (by decide) (by decide)]
  decide +kernel

/-- **Motif 4ab weak `H.TA` wins 1/2 of Set-4 rankings**: `Y = {3, 4}`
(`*H.H`, `*H́`). Observed 49.5% for `máa.il.mo.jen` ([anttila-1997]
table (53), row 4b). -/
theorem weakProb_4ab : set4Prob .four .weak = 1/2 := by
  rw [set4Prob_eq_rate .four .weak {2, 3, 4, 5} {3, 4} (by decide) (by decide)]
  decide +kernel

/-- **Motif 5ab strong `H.TÓO` wins 1/5 of Set-4 rankings**:
`D = {0, 1, 3, 4, 5}`, `Y = {5}` (`*X.X`, violated by weak alone). Observed
17.8% for `kór.jaa.mòi.den` ([anttila-1997] table (53), row 5a). -/
theorem strongProb_5ab : set4Prob .five .strong = 1/5 := by
  rw [set4Prob_eq_rate .five .strong {0, 1, 3, 4, 5} {5} (by decide) (by decide)]
  decide +kernel

/-- **Motif 5ab weak `H.TO` wins 4/5 of Set-4 rankings**: `Y = {0, 1, 3, 4}`
(`*H/O`, `*Ó`, `*H.H`, `*H́`). Observed 82.2% for `kór.jaa.mo.jen`
([anttila-1997] table (53), row 5b). -/
theorem weakProb_5ab : set4Prob .five .weak = 4/5 := by
  rw [set4Prob_eq_rate .five .weak {0, 1, 3, 4, 5} {0, 1, 3, 4} (by decide) (by decide)]
  decide +kernel

/-! ### Completeness — each variable motif's two outcomes partition the mass -/

/-- Every Set-3 ranking picks a winner for motif 3ab: the two variants'
probabilities sum to 1. -/
theorem complete_3ab : set3Prob .three .strong + set3Prob .three .weak = 1 := by
  rw [strongProb_3ab, weakProb_3ab]; norm_num

/-- Every Set-4 ranking picks a winner for motif 4ab. -/
theorem complete_4ab : set4Prob .four .strong + set4Prob .four .weak = 1 := by
  rw [strongProb_4ab, weakProb_4ab]; norm_num

/-- Every Set-4 ranking picks a winner for motif 5ab. -/
theorem complete_5ab : set4Prob .five .strong + set4Prob .five .weak = 1 := by
  rw [strongProb_5ab, weakProb_5ab]; norm_num

end Anttila1997
