import Linglib.Phonology.HarmonicGrammar.PartiallyOrderedConstraints
import Mathlib.Data.Fin.VecNotation

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

`finnishGrammar` is "the grammar for Finnish, final version" (eq. (50),
page 21) in full: 20 constraints in 5 mutually-ranked sets, as a single
`stratified` partial order on `Fin 20`:

  - Set 1: \*X́.X́ (No Clash)
  - Set 2: \*Ĺ (Peak Prominence: no stressed lights), \*H (Weight-to-Stress:
    no unstressed heavies)
  - Set 3: \*H/I, \*Í, \*L.L
  - Set 4: \*H/O, \*Ó, \*L/A, \*H.H, \*H́, \*X.X
  - Set 5: \*H/A, \*Á, \*L/O, \*L/I, \*A, \*O, \*I, \*L, with internal
    rankings \*L/O ≫ \*L/I and \*A ≫ \*O ≫ \*I (`setFiveInner`)

Sets 3 and 4 — the "intermediary constraint sets" of eq. (49) — are internally
unranked: "While mutually ranked, the sets are internally random" (page 21),
so each evaluation samples a total order.

## Substrate consumption

Each motif's probability is `pocPredict` over `finnishGrammar` — uniform
sampling of the total rankings consistent with the whole grammar, not a
per-stratum sub-grammar. The substrate's deciding-stratum theorem
(`pocPredict_stratified_binary_rate`) reduces each competition to the closed
form `|favoring ∩ Dₖ| / |Dₖ|` over the deciding stratum's active set — the
paper's own shortcut ("Drawing the tableaux was in fact unnecessary … knowing
that the weak variant violates one constraint (\*L.L) while the strong variant
violates two (\*H/I, \*Í) gives us the result directly", page 22) — with the
irrelevance of the lower strata a theorem rather than an aside.

Violation profiles are stipulated from table (52) rather than derived from
`Constraint` instances: the paper's quantitative section works directly at
violation-profile granularity. True `Constraint` formalisations would need a
Finnish syllable substrate (stress / weight / sonority features feeding
syllable structure) which doesn't yet exist in linglib. Sets 1–2 tie on every
motif (the stress constraints are inactive on these long-stem competitions,
witnessed by table (52) carrying only Set 3 and Set 4 columns); Set-5 cells
are set to 0 — the deciding-stratum theorem makes them provably irrelevant,
so no Set-5 profile fidelity is claimed.

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

`winProb_strong_add_weak` verifies the two variants partition the probability
mass for every motif (`sum_pocPredict_eq_one` substrate instance).

## Out of scope

- **The categorical short-stem patterns** decided by the stress constraints of
  Sets 1–2 (mono- and disyllabic stems, the paper's §2.1 and §5.1–5.2).
- **Observed-vs-predicted comparison theorems.** Table (53)'s small gap
  between predicted and observed is empirical noise around the discrete
  prediction ("as the quantitative predictions of our model are discrete
  probabilities (1/2, 1/3, 1/5 etc.) it would be difficult to get any
  closer", page 23).
-/

namespace Anttila1997

open HarmonicGrammar

/-! ### Variants and motifs -/

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

/-- The six motif competitions of [anttila-1997] table (52): 1ab
(`L.TÁA` ∼ `L.TA`), 2ab (`L.TÓO` ∼ `L.TO`), 3ab (`L.TÍI` ∼ `L.TI`), 4ab
(`H.TÁA` ∼ `H.TA`), 5ab (`H.TÓO` ∼ `H.TO`), 6ab (`H.TÍI` ∼ `H.TI`). -/
inductive Motif
  | one
  | two
  | three
  | four
  | five
  | six
  deriving DecidableEq, Repr, Fintype

/-! ### The grammar for Finnish, final version

Constraint roster, in eq. (50)'s column order: `0` = \*X́.X́ (Set 1); `1` =
\*Ĺ, `2` = \*H (Set 2); `3` = \*H/I, `4` = \*Í, `5` = \*L.L (Set 3); `6` =
\*H/O, `7` = \*Ó, `8` = \*L/A, `9` = \*H.H, `10` = \*H́, `11` = \*X.X
(Set 4); `12` = \*H/A, `13` = \*Á, `14` = \*L/O, `15` = \*L/I, `16` = \*A,
`17` = \*O, `18` = \*I, `19` = \*L (Set 5). -/

/-- Stratum assignment: constraint `c` belongs to Set `stratumOf c + 1` of
[anttila-1997] eq. (50). -/
def stratumOf : Fin 20 → Fin 5 :=
  ![0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 4, 4, 4]

/-- The Set-5-internal rankings of [anttila-1997] eq. (50): \*L/O ≫ \*L/I
(`14 ≫ 15`) and \*A ≫ \*O ≫ \*I (`16 ≫ 17 ≫ 18`), transitively closed. -/
def setFiveInner : Fin 20 → Fin 20 → Prop :=
  fun a b => a = b ∨
    (a, b) ∈ ([(14, 15), (16, 17), (17, 18), (16, 18)] : List (Fin 20 × Fin 20))

instance : DecidableRel setFiveInner := by
  unfold setFiveInner; infer_instance

instance : IsPartialOrder (Fin 20) setFiveInner where
  refl _ := Or.inl rfl
  trans := by decide
  antisymm := by decide

/-- **The grammar for Finnish, final version** ([anttila-1997] eq. (50),
page 21): five mutually-ranked strata, internally free except for
`setFiveInner`'s Set-5 rankings. -/
def finnishGrammar : Fin 20 → Fin 20 → Prop := stratified stratumOf setFiveInner

instance : IsPartialOrder (Fin 20) finnishGrammar :=
  inferInstanceAs (IsPartialOrder (Fin 20) (stratified stratumOf setFiveInner))

instance : DecidableRel finnishGrammar :=
  inferInstanceAs (DecidableRel (stratified stratumOf setFiveInner))

/-- Violation profile over the full constraint roster, from [anttila-1997]
table (52). Sets 1–2 tie on every motif and Set-5 cells are 0 (provably
irrelevant; see module docstring). -/
def vp : Motif → Variant → Fin 20 → ℕ
  | .one,   .weak,   ⟨5, _⟩  => 1   -- L.TA  violates *L.L
  | .two,   .weak,   ⟨5, _⟩  => 1   -- L.TO  violates *L.L
  | .three, .strong, ⟨3, _⟩  => 1   -- L.TÍI violates *H/I
  | .three, .strong, ⟨4, _⟩  => 1   -- L.TÍI violates *Í
  | .three, .weak,   ⟨5, _⟩  => 1   -- L.TI  violates *L.L
  | .four,  .strong, ⟨9, _⟩  => 1   -- H.TÁA violates *H.H
  | .four,  .strong, ⟨10, _⟩ => 1   -- H.TÁA violates *H́
  | .four,  .weak,   ⟨8, _⟩  => 1   -- H.TA  violates *L/A
  | .four,  .weak,   ⟨11, _⟩ => 1   -- H.TA  violates *X.X
  | .five,  .strong, ⟨6, _⟩  => 1   -- H.TÓO violates *H/O
  | .five,  .strong, ⟨7, _⟩  => 1   -- H.TÓO violates *Ó
  | .five,  .strong, ⟨9, _⟩  => 1   -- H.TÓO violates *H.H
  | .five,  .strong, ⟨10, _⟩ => 1   -- H.TÓO violates *H́
  | .five,  .weak,   ⟨11, _⟩ => 1   -- H.TO  violates *X.X
  | .six,   .strong, ⟨3, _⟩  => 1   -- H.TÍI violates *H/I
  | .six,   .strong, ⟨4, _⟩  => 1   -- H.TÍI violates *Í
  | _,      _,       _       => 0

/-- Probability that variant `v` wins motif `m` under uniform sampling of the
total rankings consistent with `finnishGrammar`. -/
def winProb (m : Motif) (v : Variant) : ℚ :=
  pocPredict (fun _ => Finset.univ) vp finnishGrammar m v

/-- Bridge to the deciding-stratum closed form, shared by all twelve rate
theorems. -/
private theorem winProb_eq_rate (m : Motif) (v : Variant) (k : Fin 5)
    (h_triv : ∀ a b, stratumOf a = k → stratumOf b = k → setFiveInner a b → a = b)
    (h_tie : ∀ c, stratumOf c < k → vp m v c = vp m v.other c)
    (h_dec : ((active vp m v v.other).filter (stratumOf · = k)).Nonempty) :
    winProb m v =
      ((favoring vp m v v.other ∩
          (active vp m v v.other).filter (stratumOf · = k)).card : ℚ) /
        (((active vp m v v.other).filter (stratumOf · = k)).card : ℚ) :=
  pocPredict_stratified_binary_rate (Variant.univ_eq_pair v) v.ne_other h_triv h_tie h_dec

/-! ### Rate theorems — table (52), all six motifs -/

/-- **Motif 1ab strong `L.TÁA` wins in all rankings** — only the weak variant
violates a deciding-stratum constraint (`*L.L`), so `D = Y = {5}` and the rate
is `1`: the categorical limiting case. -/
theorem strongProb_1ab : winProb .one .strong = 1 := by
  rw [winProb_eq_rate .one .strong 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 1ab weak `L.TA` loses in all rankings** ([anttila-1997]
table (53): observed 0.6%, an artefact of the spelling of /kollega/). -/
theorem weakProb_1ab : winProb .one .weak = 0 := by
  rw [winProb_eq_rate .one .weak 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 2ab strong `L.TÓO` wins in all rankings** — same Set-3 profile as
motif 1ab. -/
theorem strongProb_2ab : winProb .two .strong = 1 := by
  rw [winProb_eq_rate .two .strong 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 2ab weak `L.TO` loses in all rankings**. -/
theorem weakProb_2ab : winProb .two .weak = 0 := by
  rw [winProb_eq_rate .two .weak 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 3ab strong `L.TÍI` wins 1/3 of rankings**: decided in Set 3 with
`D = {*H/I, *Í, *L.L}`, `Y = {*L.L}` (violated by weak alone). Observed 36.9%
for `náa.pu.rèi.den` ([anttila-1997] table (53), row 3a). -/
theorem strongProb_3ab : winProb .three .strong = 1/3 := by
  rw [winProb_eq_rate .three .strong 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 3ab weak `L.TI` wins 2/3 of rankings**: `Y = {*H/I, *Í}` (violated
by strong alone). Observed 63.1% for `náa.pu.ri.en` ([anttila-1997]
table (53), row 3b). -/
theorem weakProb_3ab : winProb .three .weak = 2/3 := by
  rw [winProb_eq_rate .three .weak 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 4ab strong `H.TÁA` wins 1/2 of rankings**: decided in Set 4 with
`D = {*L/A, *H.H, *H́, *X.X}`, `Y = {*L/A, *X.X}` (violated by weak alone).
Observed 50.5% for `máa.il.mòi.den` ([anttila-1997] table (53), row 4a). -/
theorem strongProb_4ab : winProb .four .strong = 1/2 := by
  rw [winProb_eq_rate .four .strong 3 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 4ab weak `H.TA` wins 1/2 of rankings**: `Y = {*H.H, *H́}`.
Observed 49.5% for `máa.il.mo.jen` ([anttila-1997] table (53), row 4b). -/
theorem weakProb_4ab : winProb .four .weak = 1/2 := by
  rw [winProb_eq_rate .four .weak 3 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 5ab strong `H.TÓO` wins 1/5 of rankings**: decided in Set 4 with
`D = {*H/O, *Ó, *H.H, *H́, *X.X}`, `Y = {*X.X}` (violated by weak alone).
Observed 17.8% for `kór.jaa.mòi.den` ([anttila-1997] table (53), row 5a). -/
theorem strongProb_5ab : winProb .five .strong = 1/5 := by
  rw [winProb_eq_rate .five .strong 3 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 5ab weak `H.TO` wins 4/5 of rankings**: `Y = {*H/O, *Ó, *H.H,
*H́}`. Observed 82.2% for `kór.jaa.mo.jen` ([anttila-1997] table (53),
row 5b). -/
theorem weakProb_5ab : winProb .five .weak = 4/5 := by
  rw [winProb_eq_rate .five .weak 3 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 6ab strong `H.TÍI` loses in all rankings** — only the strong
variant violates deciding-stratum constraints (`*H/I`, `*Í`), so `Y = ∅`. -/
theorem strongProb_6ab : winProb .six .strong = 0 := by
  rw [winProb_eq_rate .six .strong 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-- **Motif 6ab weak `H.TI` wins in all rankings** ([anttila-1997]
table (53): observed 98.4%). -/
theorem weakProb_6ab : winProb .six .weak = 1 := by
  rw [winProb_eq_rate .six .weak 2 (by decide) (by decide) (by decide)]
  decide +kernel

/-! ### Completeness -/

/-- Every ranking of `finnishGrammar` picks a winner for every motif: the two
variants' probabilities sum to 1 (`sum_pocPredict_eq_one` instance). -/
theorem winProb_strong_add_weak (m : Motif) :
    winProb m .strong + winProb m .weak = 1 :=
  pocPredict_binary_add_eq_one (r := finnishGrammar) (i := m)
    (Variant.univ_eq_pair .strong) (Variant.ne_other .strong) (by cases m <;> decide)

end Anttila1997
