import Linglib.Pragmatics.SocialMeaning.IndexicalField
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.DeriveFintype

/-!
# Labov (2006): The Social Stratification of English in New York City

This file formalizes the stratification data of [labov-2006], the second edition of the 1966
Lower East Side survey. The department store survey of Chapter 3 orders the stores by the
prestige variant of (r) and by stops in *fourth* (`deptStore_stratification`,
`thStop_strictAnti`). The class stratification table of Chapter 7 gives the indices of the five
phonological variables (r), (æh), (oh), (th), and (dh) for three class groups across the
contextual styles; its cells are the rows of `table78`, and the two regularities Labov reads
off the stratification diagrams are stated over them: at each style the classes are ordered
toward the standard with class (`ClassStratified`), and within each class the index moves
toward the standard with formality (`StyleShifted`). Four variables show both
(`r_stratified`, `aeh_stratified`, `th_stratified`, `dh_stratified`); (oh) shows the one
real deviation, the lower class neither stratified against the other classes nor shifting
with style (`oh_real_deviation`), which Labov takes to mean that (oh) is not a variable for
lower-class speakers, while the other two classes shift regularly
(`oh_shift_working_middle`). The (ing) indices of Chapter 10 by age and class are
`StratificationProfile`s: older speakers show the stable stigmatized pattern of Case I-A
except that in casual speech the highest class does not use the least */in/*, a crossover
between the two middle groups (`ingOlder_case_IA`, `ingOlder_crossover`). All five
phonological variables and (ing) are markers, stratified by class and shifting with style,
with (r) a change from above, (æh) and (oh) changes from below, and (th), (dh), and (ing)
stable (`variableBehavior`, `all_markers`).

## Implementation notes

Indices follow the book: (r) is the percentage of the constricted variant, (æh) and (oh) are
vowel-height indices on which a higher value is closer to the standard, and (th) and (dh) are
percentages of non-fricative variants, so `Variable.standardUp` records the direction in
which each index approaches the standard. Cells of Table 7.8 are rows because the styles
measured differ by variable, five for (r), four for the vowels, three for the consonants. The
(r) crossover of the lower middle class above the upper middle class in the two formal
styles appears in Figures 7.10 and 7.11 over six class groups without a table and is not
encoded; the crossover predicate is exercised on the (ing) table instead. The (ing) table
groups the socioeconomic index as 0–2, 3–6, 7–8, and 9, differently from Table 7.8.

## References

* [labov-2006]
-/

namespace Labov2006

open SocialMeaning.IndexicalField

/-! ### Class groups -/

/-- The three class groups of Table 7.8: socioeconomic index 0–2, 3–5, and 6–9, with 23, 28,
and 30 informants. -/
inductive ClassGroup where
  | lower
  | working
  | middle
  deriving DecidableEq, Repr, Fintype

/-- The rank of a class group. -/
@[simp] def ClassGroup.rank : ClassGroup → ℕ
  | .lower => 0
  | .working => 1
  | .middle => 2

instance : LinearOrder ClassGroup :=
  LinearOrder.lift' ClassGroup.rank (λ a b h => by cases a <;> cases b <;> simp_all)

/-! ### The department store survey (Chapter 3) -/

/-- The three stores, ordered by prestige. -/
inductive Store where
  | klein
  | macys
  | saks
  deriving DecidableEq, Repr

/-- The rank of a store. -/
@[simp] def Store.rank : Store → ℕ
  | .klein => 0
  | .macys => 1
  | .saks => 2

instance : LinearOrder Store :=
  LinearOrder.lift' Store.rank (λ a b h => by cases a <;> cases b <;> simp_all)

/-- The distribution of (r) among complete responses, Table 3.4: the percentages of employees
using the constricted variant in all four positions, in some, and in none. -/
structure DeptStoreResult where
  /-- Percentage with (r-1) in all four positions. -/
  allR1 : ℕ
  /-- Percentage with (r-1) in some positions. -/
  someR1 : ℕ
  /-- Percentage with no (r-1). -/
  noR1 : ℕ
  deriving Repr

/-- Table 3.4, over 33, 48, and 34 employees. -/
def deptStore : Store → DeptStoreResult
  | .saks => ⟨24, 46, 30⟩
  | .macys => ⟨22, 37, 41⟩
  | .klein => ⟨6, 12, 82⟩

/-- The percentage of employees with any constricted (r). -/
def anyR1 (s : Store) : ℕ := (deptStore s).allR1 + (deptStore s).someR1

/-- Any use of (r-1) increases with the prestige of the store. -/
theorem deptStore_stratification : StrictMono anyR1 := by
  intro a b h; cases a <;> cases b <;> revert h <;> decide

/-- The percentage of employees using a stop in *fourth*. -/
def thStop : Store → ℕ
  | .saks => 0
  | .macys => 4
  | .klein => 15

/-- Stops in *fourth* decrease with the prestige of the store. -/
theorem thStop_strictAnti : StrictAnti thStop := by
  intro a b h; cases a <;> cases b <;> revert h <;> decide

/-! ### Table 7.8: class stratification of the five variables -/

/-- The five phonological variables of the survey. -/
inductive Variable where
  | r
  | aeh
  | oh
  | th
  | dh
  deriving DecidableEq, Repr

/-- Whether a higher index is closer to the standard: so for (r), the percentage of the
constricted variant, and for the vowel-height indices (æh) and (oh); not for (th) and (dh),
percentages of non-fricative variants. -/
def Variable.standardUp : Variable → Bool
  | .r | .aeh | .oh => true
  | .th | .dh => false

/-- A cell of Table 7.8. -/
structure Cell where
  /-- The variable. -/
  var : Variable
  /-- The class group. -/
  group : ClassGroup
  /-- The contextual style. -/
  style : ContextualStyle
  /-- The index. -/
  value : ℚ
  deriving DecidableEq, Repr

/-- Table 7.8: (r) at five styles, (æh) and (oh) at four, (th) and (dh) at three. -/
def table78 : List Cell :=
  [⟨.r, .lower, .casual, 5/2⟩, ⟨.r, .lower, .careful, 21/2⟩, ⟨.r, .lower, .reading, 29/2⟩,
   ⟨.r, .lower, .wordList, 47/2⟩, ⟨.r, .lower, .minimalPair, 99/2⟩,
   ⟨.r, .working, .casual, 4⟩, ⟨.r, .working, .careful, 25/2⟩, ⟨.r, .working, .reading, 21⟩,
   ⟨.r, .working, .wordList, 35⟩, ⟨.r, .working, .minimalPair, 55⟩,
   ⟨.r, .middle, .casual, 25/2⟩, ⟨.r, .middle, .careful, 25⟩, ⟨.r, .middle, .reading, 29⟩,
   ⟨.r, .middle, .wordList, 111/2⟩, ⟨.r, .middle, .minimalPair, 70⟩,
   ⟨.aeh, .lower, .casual, 23⟩, ⟨.aeh, .lower, .careful, 27⟩, ⟨.aeh, .lower, .reading, 29⟩,
   ⟨.aeh, .lower, .wordList, 32⟩,
   ⟨.aeh, .working, .casual, 25⟩, ⟨.aeh, .working, .careful, 28⟩,
   ⟨.aeh, .working, .reading, 61/2⟩, ⟨.aeh, .working, .wordList, 32⟩,
   ⟨.aeh, .middle, .casual, 27⟩, ⟨.aeh, .middle, .careful, 30⟩, ⟨.aeh, .middle, .reading, 34⟩,
   ⟨.aeh, .middle, .wordList, 35⟩,
   ⟨.oh, .lower, .casual, 23⟩, ⟨.oh, .lower, .careful, 24⟩, ⟨.oh, .lower, .reading, 24⟩,
   ⟨.oh, .lower, .wordList, 21⟩,
   ⟨.oh, .working, .casual, 39/2⟩, ⟨.oh, .working, .careful, 22⟩,
   ⟨.oh, .working, .reading, 23⟩, ⟨.oh, .working, .wordList, 24⟩,
   ⟨.oh, .middle, .casual, 20⟩, ⟨.oh, .middle, .careful, 47/2⟩, ⟨.oh, .middle, .reading, 53/2⟩,
   ⟨.oh, .middle, .wordList, 59/2⟩,
   ⟨.th, .lower, .casual, 78⟩, ⟨.th, .lower, .careful, 65⟩, ⟨.th, .lower, .reading, 87/2⟩,
   ⟨.th, .working, .casual, 68⟩, ⟨.th, .working, .careful, 107/2⟩,
   ⟨.th, .working, .reading, 27⟩,
   ⟨.th, .middle, .casual, 51/2⟩, ⟨.th, .middle, .careful, 33/2⟩, ⟨.th, .middle, .reading, 10⟩,
   ⟨.dh, .lower, .casual, 157/2⟩, ⟨.dh, .lower, .careful, 56⟩, ⟨.dh, .lower, .reading, 49⟩,
   ⟨.dh, .working, .casual, 127/2⟩, ⟨.dh, .working, .careful, 89/2⟩,
   ⟨.dh, .working, .reading, 34⟩,
   ⟨.dh, .middle, .casual, 59/2⟩, ⟨.dh, .middle, .careful, 33/2⟩, ⟨.dh, .middle, .reading, 13⟩]

/-- `a` is closer to the standard than `b` on variable `v`. -/
def Variable.Closer (v : Variable) (a b : ℚ) : Prop :=
  if v.standardUp then b < a else a < b

instance (v : Variable) (a b : ℚ) : Decidable (v.Closer a b) := by
  unfold Variable.Closer; infer_instance

/-- Class stratification of `v` on the groups satisfying `P`: at every style, a higher class
is closer to the standard. -/
def ClassStratified (v : Variable) (P : ClassGroup → Prop) [DecidablePred P] : Prop :=
  ∀ c₁ ∈ table78, ∀ c₂ ∈ table78, c₁.var = v → c₂.var = v → P c₁.group →
    P c₂.group → c₁.style = c₂.style → c₁.group < c₂.group → v.Closer c₂.value c₁.value

/-- Style shifting of `v` within the group `g`: a more formal style is closer to the
standard. -/
def StyleShifted (v : Variable) (g : ClassGroup) : Prop :=
  ∀ c₁ ∈ table78, ∀ c₂ ∈ table78, c₁.var = v → c₂.var = v → c₁.group = g →
    c₂.group = g → c₁.style < c₂.style → v.Closer c₂.value c₁.value

instance (v : Variable) (P : ClassGroup → Prop) [DecidablePred P] :
    Decidable (ClassStratified v P) := by
  unfold ClassStratified; infer_instance

instance (v : Variable) (g : ClassGroup) : Decidable (StyleShifted v g) := by
  unfold StyleShifted; infer_instance

/-- (r): the three classes are differentiated at every style, and every class rises toward the
standard with formality, at all fifteen points of Figure 7.1. -/
theorem r_stratified : ClassStratified .r (λ _ => True) ∧ ∀ g, StyleShifted .r g := by
  decide +kernel

/-- (æh): every class shifts with style, and the classes are differentiated except that the
lower and working classes converge in word lists (Figure 7.2). -/
theorem aeh_stratified :
    (∀ g, StyleShifted .aeh g) ∧ ClassStratified .aeh (· ≠ .lower) ∧
      ClassStratified .aeh (· ≠ .working) := by
  decide +kernel

/-- (th): regular class and style stratification (Figure 7.4). -/
theorem th_stratified : ClassStratified .th (λ _ => True) ∧ ∀ g, StyleShifted .th g := by
  decide +kernel

/-- (dh): regular class and style stratification (Figure 7.5). -/
theorem dh_stratified : ClassStratified .dh (λ _ => True) ∧ ∀ g, StyleShifted .dh g := by
  decide +kernel

/-- The real deviation of (oh), Figure 7.3: the lower class neither stands in the class
stratification, its casual index lying beyond the middle class's, nor shifts with style, its
word-list index lying below its casual one. -/
theorem oh_real_deviation :
    ¬ ClassStratified .oh (λ _ => True) ∧ ¬ StyleShifted .oh .lower := by
  decide +kernel

/-- The working and middle classes shift (oh) regularly with style and are stratified. -/
theorem oh_shift_working_middle :
    StyleShifted .oh .working ∧ StyleShifted .oh .middle ∧ ClassStratified .oh (· ≠ .lower) := by
  decide +kernel

/-! ### (ing) by age and class (Table 10.10) -/

/-- The socioeconomic groups of Table 10.10: index 0–2, 3–6, 7–8, and 9. -/
inductive INGClass where
  | sc1
  | sc2
  | sc3
  | sc4
  deriving DecidableEq, Repr, Fintype

/-- The rank of a group. -/
@[simp] def INGClass.rank : INGClass → ℕ
  | .sc1 => 0
  | .sc2 => 1
  | .sc3 => 2
  | .sc4 => 3

instance : LinearOrder INGClass :=
  LinearOrder.lift' INGClass.rank (λ a b h => by cases a <;> cases b <;> simp_all)

/-- The two styles of Table 10.10, casual and careful speech. -/
inductive INGStyle where
  | A
  | B
  deriving DecidableEq, Repr, Fintype

/-- The rank of a style. -/
@[simp] def INGStyle.rank : INGStyle → ℕ
  | .A => 0
  | .B => 1

instance : LinearOrder INGStyle :=
  LinearOrder.lift' INGStyle.rank (λ a b h => by cases a <;> cases b <;> simp_all)

/-- The (ing) index, the percentage of */in/*, of speakers aged 20–39. -/
def ingYoung : StratificationProfile INGClass INGStyle where
  index
    | .sc1, .A => 90 | .sc1, .B => 75
    | .sc2, .A => 60 | .sc2, .B => 45
    | .sc3, .A => 43 | .sc3, .B => 50
    | .sc4, .A => 0 | .sc4, .B => 2

/-- The (ing) index of speakers aged 40 and over. -/
def ingOlder : StratificationProfile INGClass INGStyle where
  index
    | .sc1, .A => 85 | .sc1, .B => 50
    | .sc2, .A => 48 | .sc2, .B => 27
    | .sc3, .A => 21 | .sc3, .B => 12
    | .sc4, .A => 23 | .sc4, .B => 2

/-- Younger speakers are stratified in casual speech. -/
theorem ingYoung_monotone_casual : ingYoung.isMonotoneDown [.A] := by
  unfold StratificationProfile.isMonotoneDown
  decide

/-- Older speakers show the pattern of Case I-A, a stigmatized feature not involved in change:
every class shifts toward the standard in careful speech, in which the classes are
stratified. -/
theorem ingOlder_case_IA :
    ingOlder.hasStyleShift [.sc1, .sc2, .sc3, .sc4] ∧ ingOlder.isMonotoneDown [.B] := by
  unfold StratificationProfile.hasStyleShift StratificationProfile.isMonotoneDown
  decide

/-- The one departure from Case I-A: in casual speech the highest group does not use the least
*/in/*, crossing the lower middle group. -/
theorem ingOlder_crossover : ingOlder.hasCrossover .sc3 .sc4 .B .A := by
  unfold StratificationProfile.hasCrossover
  decide

/-! ### The variables' behaviour -/

/-- The behaviour of each variable: all are markers, stratified by class and shifting with
style; (r) is a change from above, (æh) and (oh) changes from below, (th) and (dh) stable. -/
def variableBehavior : Variable → VariableBehavior
  | .r => ⟨.second, .changeFromAbove⟩
  | .aeh => ⟨.second, .changeFromBelow⟩
  | .oh => ⟨.second, .changeFromBelow⟩
  | .th => ⟨.second, .stable⟩
  | .dh => ⟨.second, .stable⟩

/-- Every phonological variable of the survey is a marker. -/
theorem all_markers (v : Variable) : (variableBehavior v).isMarker := by
  cases v <;> rfl

/-- (ing), Case I-A: a stable stigmatized marker. -/
def ingBehavior : VariableBehavior := ⟨.second, .stable⟩

end Labov2006
