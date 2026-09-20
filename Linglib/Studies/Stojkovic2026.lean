import Mathlib.Tactic.DeriveFintype
import Linglib.Phonology.Hiatus
import Linglib.Phonology.OptimalityTheory.Correspondence
import Linglib.Phonology.OptimalityTheory.Tableau

/-!
# Stojković (2026): Same Form, Different Grammars: The Slavic [ov]~[u] Alternation

This file formalizes Stojković's account of the Slavic verbalizer, the suffix of verbs derived
from nouns and adjectives. The suffix is [u] before the consonant-initial theme of the present
stem and a vowel followed by [v] before the vowel-initial theme of the infinitive stem, where
the languages fall into three groups: [ov] throughout, [ov] alternating with [ev] after a
palatal, and [uv] throughout.

Stojković gives the suffix one underlying form in every language, a defective diphthong whose
first base node has no features and whose second is high and back but neither a vowel nor a
consonant. A candidate leaves the form as it is, deletes the empty node and makes the second
a vowel, or fills the empty node with a backness and a height and makes the second the
consonant [v]. Here each candidate is its string of segments together with its correspondence
to the input, and every constraint is computed from those: NOHIATUS is the hiatus count of the
output, MAX the input nodes without a correspondent, a DEP constraint the corresponding pairs
whose output has a feature value its input lacks, and the constraint against sharing the
adjacent pairs of front segments whose first is underlyingly front. A front vowel is a
candidate only after a palatal, whose [−back] it shares.

## Main results

* `delete_optimal`: before the consonant-initial theme every group's ranking deletes the
  node, giving [u].
* `ov_optimal`, `ovEv_optimal`, `uv_optimal`: before the vowel-initial theme the three
  rankings give [ov] after both kinds of consonant, [ov] after a plain consonant and [ev]
  after a palatal, and [uv] after both.
* `uv_bounds_ov`: over the paper's own constraints the candidate [uv] harmonically bounds
  [ov], so no ranking of them gives [ov].
* `patterns`: the patterns the factorial typology of the four variable constraints derives.
* `present_stem`: [u] in the present stem, and [uv] in Bulgarian and Macedonian, from one
  grammar per language.

## Implementation notes

The paper's tableaux never penalize the epenthesis of [+high], so that over its constraints
[uv] does at least as well as [ov] on every constraint and better on DEP[−high]
(`uv_bounds_ov`). The paper attributes the [o] of the first two groups to the markedness of
[+high], and that preference is made a constraint here, DEP[+high], ranked where each group
needs it. The candidates are the paper's: a deleted node with [v], which the paper sets aside,
is not among them. The languages and their groups are those of the paper's Table 3, and the
present themes those of its Table 1.

## References

* [stojkovic-2026]
-/

namespace Stojkovic2026

open Phonology Constraints OptimalityTheory

/-! ### Segments -/

/-- The first base node of the verbalizer, which has no features. -/
def node₀ : Segment := Segment.ofSpecs []

/-- The second base node of the verbalizer, high and back but neither vowel nor consonant. -/
def glide₀ : Segment := Segment.ofSpecs [(.high, true), (.back, true)]

/-- The vowel [u], the second node as a vowel. -/
def u : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.consonantal, false), (.high, true), (.back, true)]

/-- The consonant [v], the second node as a consonant. -/
def v : Segment :=
  Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.high, true), (.back, true)]

/-- `vowel back high` is the vowel with the given backness and height, the first node filled:
[o], [u], [e] and [i]. -/
def vowel (back high : Bool) : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.consonantal, false), (.back, back), (.high, high)]

/-- The theme vowel /-a-/ of the infinitive stem. -/
def a : Segment :=
  Segment.ofSpecs [(.syllabic, true), (.consonantal, false), (.low, true), (.high, false),
    (.back, true)]

/-- The glide that begins the theme /-je-/ of the present stem. -/
def j : Segment :=
  Segment.ofSpecs [(.syllabic, false), (.consonantal, false), (.high, true), (.back, false)]

/-- A plain stem-final consonant, as the [p] of Silesian *ɕtop-ov-a-*. -/
def plain : Segment :=
  Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.labial, true), (.high, false)]

/-- A palatal stem-final consonant, as the [tɕ] of Silesian *pajtɕ-ov-a-*. -/
def palatal : Segment :=
  Segment.ofSpecs [(.syllabic, false), (.consonantal, true), (.coronal, true), (.high, true),
    (.back, false)]

/-! ### Contexts and candidates -/

/-- A context is the stem-final consonant before the verbalizer and the segment after it. -/
structure Context where
  /-- The stem-final consonant. -/
  stemFinal : Segment
  /-- The first segment of the theme. -/
  next : Segment

/-- A candidate realization of the verbalizer. -/
inductive Candidate where
  /-- The underlying form unchanged. -/
  | faithful
  /-- The empty node deleted and the second node a vowel, [u]. -/
  | delete
  /-- The empty node filled with a backness and a height and the second node [v]. -/
  | fill (back high : Bool)
  deriving DecidableEq, Fintype, Repr

namespace Candidate

/-- [ov], the node filled as a back mid vowel. -/
abbrev ov : Candidate := .fill true false

/-- [ev], the node filled as a front mid vowel. -/
abbrev ev : Candidate := .fill false false

/-- [uv], the node filled as a back high vowel. -/
abbrev uv : Candidate := .fill true true

/-- [iv], the node filled as a front high vowel. -/
abbrev iv : Candidate := .fill false true

/-- [u], the node deleted. -/
abbrev uMono : Candidate := .delete

end Candidate

variable (c : Context)

/-- The input is the stem-final consonant, the two nodes of the verbalizer, and the theme. -/
def input : List Segment := [c.stemFinal, node₀, glide₀, c.next]

/-- `output c k` is the string of segments of the candidate `k`. -/
def output : Candidate → List Segment
  | .faithful => input c
  | .delete => [c.stemFinal, u, c.next]
  | .fill back high => [c.stemFinal, vowel back high, v, c.next]

/-- The index pairs of the correspondence of a candidate to the input, in which deletion
leaves the empty node without a correspondent. -/
def pairs : Candidate → List (ℕ × ℕ)
  | .delete => [(0, 0), (2, 1), (3, 2)]
  | _ => Correspondence.diagonalPairs 4

/-- `corr c k` is the correspondence between the input and the candidate `k`. -/
def corr (k : Candidate) : Correspondence Correspondence.Side Segment :=
  Correspondence.ofPairs (fun | .lhs => input c | .rhs => output c k)
    (fun | .lhs, .rhs => pairs k | _, _ => [])

/-- The candidates of a context. A front vowel shares the [−back] of a palatal and so is a
candidate only after one. -/
def candidates : List Candidate :=
  [.faithful, .delete, .ov, .uv] ++ if c.stemFinal.HasValue .back false then [.ev, .iv] else []

/-- The four fillings of the node. -/
def fissionCandidates : List Candidate := [.ov, .ev, .uv, .iv]

/-! ### The languages -/

/-- The languages of the paper's Table 3. Belarusian and Russian are placed provisionally, on
the evidence of native speakers and of the orthography. -/
inductive SlavicLang where
  | belarusian | bunyev | czech | kashubian | lowerSorbian | pannonianRusyn | podlachian
  | polish | silesian | slovak | upperSorbian
  | bcms | carpathianRusyn | russian | slovenian
  | bulgarian | lemkoRusyn | macedonian | ukrainian
  deriving DecidableEq, Fintype, Repr

/-- The three groups by the vowel of the verbalizer before the vowel-initial theme. -/
inductive VBLZGroup where
  /-- [ov] after every consonant. -/
  | ovGroup
  /-- [ov] after a plain consonant and [ev] after a palatal. -/
  | ovEvGroup
  /-- [uv] after every consonant. -/
  | uvGroup
  deriving DecidableEq, Fintype, Repr

/-- The forms of the verbalizer attested before the vowel-initial theme in each group. -/
def VBLZGroup.forms : VBLZGroup → List Candidate
  | .ovGroup => [.ov]
  | .ovEvGroup => [.ov, .ev]
  | .uvGroup => [.uv]

/-- The group of each language (Table 3). -/
def SlavicLang.vblzGroup : SlavicLang → VBLZGroup
  | .belarusian | .bunyev | .czech | .kashubian | .lowerSorbian | .pannonianRusyn | .podlachian
  | .polish | .silesian | .slovak | .upperSorbian => .ovGroup
  | .bcms | .carpathianRusyn | .russian | .slovenian => .ovEvGroup
  | .bulgarian | .lemkoRusyn | .macedonian | .ukrainian => .uvGroup

/-- The first segment of the theme that follows the verbalizer in the present stem. Bulgarian
and Macedonian have the vowel-initial theme there as in the infinitive stem, and the other
languages have /-je-/ (Table 1). -/
def SlavicLang.presentTheme : SlavicLang → Segment
  | .bulgarian | .macedonian => a
  | _ => j

/-! ### Constraints -/

/-- NOHIATUS counts the adjacent vowels of the output. -/
def noHiatus : Constraint Candidate := fun k ↦ Hiatus.count (output c k)

/-- SPECIFY counts the output segments that have neither a height nor a backness. -/
def specify : Constraint Candidate := fun k ↦
  (output c k).countP fun s ↦ decide (s.Unspecified .high ∧ s.Unspecified .back)

/-- MAX counts the input nodes that have no correspondent in the output. -/
def maxNode : Constraint Candidate := fun k ↦ (corr c k).maxViol .lhs .rhs

/-- `dep f val` counts the corresponding pairs whose output has the value `val` of the feature
`f` and whose input lacks it, the epenthesis of that value. -/
def dep (f : Feature) (val : Bool) : Constraint Candidate := fun k ↦
  (corr c k).depViolFeature (·.HasValue f val) .lhs .rhs

/-- \*SHARE[−back] counts the adjacent pairs of output segments that are both [−back] and whose
first is [−back] in the input, the sharing of a palatal's frontness with the following vowel. -/
def noShareBack : Constraint Candidate := fun k ↦
  ((output c k).zip (output c k).tail).countP fun p ↦
    decide (p.1.HasValue .back false ∧ p.2.HasValue .back false ∧ p.1 ∈ input c)

/-- DEP[+back]. -/
abbrev depBack : Constraint Candidate := dep c .back true

/-- DEP[−high]. -/
abbrev depMinusHigh : Constraint Candidate := dep c .high false

/-- DEP[+high], the constraint this file adds for the paper's markedness of [+high]. -/
abbrev depHigh : Constraint Candidate := dep c .high true

/-- The paper's constraints. -/
def paperConstraints : List (Constraint Candidate) :=
  [noHiatus c, specify c, noShareBack c, depBack c, depMinusHigh c, maxNode c]

/-- The four constraints whose ranking varies across the groups. -/
def variableConstraints : List (Constraint Candidate) :=
  [noShareBack c, depBack c, depMinusHigh c, depHigh c]

/-! ### Rankings -/

/-- A ranking of the variable constraints, completed by the undominated NOHIATUS and SPECIFY
above them and MAX below. -/
def ranking (vs : List (Context → Constraint Candidate)) : List (Constraint Candidate) :=
  [noHiatus c, specify c] ++ vs.map (· c) ++ [maxNode c]

/-- The ranking of the [ov] group, the paper's (17) with DEP[+high] above DEP[+back]. -/
def ovRanking : List (Context → Constraint Candidate) :=
  [noShareBack, depHigh, depBack, depMinusHigh]

/-- The ranking of the [ov]~[ev] group, the paper's (21) with DEP[+high] below DEP[+back]. -/
def ovEvRanking : List (Context → Constraint Candidate) :=
  [depBack, depHigh, noShareBack, depMinusHigh]

/-- The ranking of the [uv] group, the paper's (29) with DEP[+high] at the bottom. -/
def uvRanking : List (Context → Constraint Candidate) :=
  [depMinusHigh, noShareBack, depBack, depHigh]

/-- `optimal c vs` is the set of winners in the context `c` under the ranking `vs` of the
variable constraints. -/
def optimal (vs : List (Context → Constraint Candidate)) : Finset Candidate :=
  (Tableau.ofRanking (candidates c) (ranking c vs) (by simp [candidates])).optimal

/-! ### The three groups -/

/-- Before the consonant-initial theme of the present stem every group's ranking deletes the
empty node, giving [u], after a plain consonant and after a palatal alike. -/
theorem delete_optimal :
    ∀ stem ∈ [plain, palatal], ∀ vs ∈ [ovRanking, ovEvRanking, uvRanking],
      optimal ⟨stem, j⟩ vs = {.delete} := by
  decide

/-- The ranking of the [ov] group gives [ov] before the vowel-initial theme, after a plain
consonant and after a palatal alike. -/
theorem ov_optimal : ∀ stem ∈ [plain, palatal], optimal ⟨stem, a⟩ ovRanking = {.ov} := by
  decide

/-- The ranking of the [ov]~[ev] group gives [ov] after a plain consonant and [ev] after a
palatal. -/
theorem ovEv_optimal :
    optimal ⟨plain, a⟩ ovEvRanking = {.ov} ∧ optimal ⟨palatal, a⟩ ovEvRanking = {.ev} := by
  decide

/-- The ranking of the [uv] group gives [uv] after a plain consonant and after a palatal
alike. -/
theorem uv_optimal : ∀ stem ∈ [plain, palatal], optimal ⟨stem, a⟩ uvRanking = {.uv} := by
  decide

/-! ### Harmonic bounding over the paper's constraints -/

/-- Over the paper's constraints [uv] does at least as well as [ov] on every constraint and
better on DEP[−high], before the vowel-initial theme. -/
theorem uv_le_ov :
    ∀ stem ∈ [plain, palatal], (∀ con ∈ paperConstraints ⟨stem, a⟩, con .uv ≤ con .ov) ∧
      depMinusHigh ⟨stem, a⟩ .uv < depMinusHigh ⟨stem, a⟩ .ov := by
  decide

/-- So no ranking of the paper's constraints gives [ov]: the candidate [uv] harmonically bounds
it. -/
theorem uv_bounds_ov {stem : Segment} (hstem : stem ∈ [plain, palatal])
    {rk : List (Constraint Candidate)} (hrk : rk.Perm (paperConstraints ⟨stem, a⟩)) :
    Candidate.ov ∉
      (Tableau.ofRanking (candidates ⟨stem, a⟩) rk (by simp [candidates])).optimal := by
  obtain ⟨hle, hlt⟩ := uv_le_ov stem hstem
  obtain ⟨i, hi⟩ := List.mem_iff_get.1
    (hrk.mem_iff.2 (by simp [paperConstraints] : depMinusHigh ⟨stem, a⟩ ∈ paperConstraints _))
  refine Tableau.ofPerm_notMem_optimal_of_lt (c := .uv) (by simp [candidates]) ?_
  exact Pi.lt_def.2 ⟨fun k ↦ hle _ (hrk.mem_iff.1 (rk.get_mem k)), i, by rw [hi]; exact hlt⟩

/-! ### Factorial typology -/

/-- `pattern vs` is the pair of winners before the vowel-initial theme under the ranking `vs`,
after a plain consonant and after a palatal. -/
def pattern (vs : List (Context → Constraint Candidate)) : Finset Candidate × Finset Candidate :=
  (optimal ⟨plain, a⟩ vs, optimal ⟨palatal, a⟩ vs)

/-- The rankings of the four variable constraints derive four patterns, those of the paper's
(31): [ov] throughout, [ov] alternating with [ev], [uv] throughout, and [uv] alternating with
[iv], which no Slavic language is known to show. -/
theorem patterns :
    ([noShareBack, depBack, depMinusHigh, depHigh].permutations'.map pattern).eraseDups =
      [({.uv}, {.uv}), ({.uv}, {.iv}), ({.ov}, {.ov}), ({.ov}, {.ev})] := by
  decide

/-- Without DEP[+high] only the two patterns with [uv] are derived. -/
theorem patterns_of_paperConstraints :
    ([noShareBack, depBack, depMinusHigh].permutations'.map pattern).eraseDups =
      [({.uv}, {.uv}), ({.uv}, {.iv})] := by
  decide

/-- The ranking of a group. -/
def VBLZGroup.ranking : VBLZGroup → List (Context → Constraint Candidate)
  | .ovGroup => ovRanking
  | .ovEvGroup => ovEvRanking
  | .uvGroup => uvRanking

/-- The attested forms of each group are exactly the winners of its ranking before the
vowel-initial theme, and [iv], which the typology derives, is attested in no group. -/
theorem attested :
    (∀ g : VBLZGroup, ∀ k : Candidate,
      k ∈ g.forms ↔ k ∈ (pattern g.ranking).1 ∪ (pattern g.ranking).2) ∧
    ∀ g : VBLZGroup, Candidate.iv ∉ g.forms := by
  decide

/-- In the present stem the ranking of each language gives [u] before the theme /-je-/, and
[uv] in Bulgarian and Macedonian, whose present theme begins with a vowel. The exception
follows from the same grammar and needs no morphological condition. -/
theorem present_stem (l : SlavicLang) :
    ∀ stem ∈ [plain, palatal], optimal ⟨stem, l.presentTheme⟩ l.vblzGroup.ranking =
      if l = .bulgarian ∨ l = .macedonian then {.uv} else {.delete} := by
  intro stem hstem
  split_ifs with h
  · rcases h with rfl | rfl <;> exact uv_optimal stem hstem
  · have hj : l.presentTheme = j := by cases l <;> simp_all [SlavicLang.presentTheme]
    rw [hj]
    exact delete_optimal stem hstem _ (by cases l.vblzGroup <;> simp [VBLZGroup.ranking])

end Stojkovic2026
