module

public import Linglib.Semantics.Presupposition.Trivalent
public import Linglib.Logic.Modal.Defs
public import Mathlib.Data.Set.Lattice.Bounded

/-!
# Karttunen (1973): Presuppositions of Compound Sentences

This file formalizes [karttunen-1973], which asks how the presuppositions of a compound sentence
are determined by those of its parts. The cumulative hypothesis of Langendoen and Savin adds them
up; Karttunen keeps it for the *holes*, factives, aspectuals and implicatives, which let every
presupposition of their complement through, and sets against them the *plugs*, verbs of saying,
which let none through, and the *filters*, the connectives, which let a presupposition of their
second clause through unless the first clause filters it: `if A then B` (13) and `A and B` (17)
presuppose what `A` presupposes and each presupposition of `B` that `A` does not entail, and
`A or B` (24) each presupposition of `B` that `¬A` does not entail. A sentence has a set of
presuppositions, each filtered on its own (`Sentence`), and the connectives take the filtering
relation as a parameter: entailment in the original conditions, entailment from assumed facts in
the revisions of §9 (`Filters`).

§8 derives the rule for conjunction and the rule for disjunction from the rule for conditionals by
Harman's principles, that internal negation keeps presuppositions and that the classical
equivalences of `A ⊃ B` with `¬A ∨ B` and of `A & B` with `¬(¬A ∨ ¬B)` keep them
(`harman_conj`, `harman_disj`), and the rules satisfy the principles. The rules are not
commutative ((16), (22)), so the principle that equivalent sentences share presuppositions can
hold only of such chosen equivalences. §9's Geraldine example (25) presupposes (27) absolutely but
not given (28), and does again in the contrary context the paper sketches; the Nixon examples (30)
call for the same relativization with every connective. §10 finds no truth-functional three-valued
conjunction that behaves like a filter: Bochvar's internal conjunction is a hole, his external one
a plug, and Łukasiewicz's filters by the falsity of the other conjunct, so that (35b) comes out
presupposition-free and (35a) does not. §11 finds that a hole *believe* survives (37) only through
the equivalence (38), and fails on (42), whence the tentative verdict that attitude verbs are
plugs.

## Implementation notes

* The entailment a filter uses is from the truth of the first clause, which requires its
  presuppositions as well as its assertion (`Sentence.truth`), so a presupposition that both
  clauses share is filtered as the second clause's and kept as the first's, as fn. 10 says.
* The per-presupposition rule is tested on *Jack has children, and Jack's children regret that
  baldness is hereditary*, built from the presuppositions of (1a) and (1b): it filters the first
  presupposition of the second conjunct and keeps the second, where a single conjoined
  presupposition would keep both.
* Murphy's restrictions on the assumed facts of §9 are read set-theoretically: some set of the
  facts, possibly empty, entails the presupposition together with the premise, is consistent with
  the premise, and does not entail the presupposition alone. On this reading the empty set filters
  only a presupposition the premise entails, of a consistent premise, that is not a tautology
  (`filters_empty_iff`), so the revised condition keeps the tautological presupposition of fn. 13
  (`univ_mem_presupposes_disj_filters`), which the footnote counts as filtered under the
  revised condition as well as the original.
* Van Fraassen's conjunction (34c), which the paper finds to behave as Łukasiewicz's on (35), is
  left out.

## References

* [karttunen-1973]
* [bochvar-1937]
* [hintikka-1962]
-/

@[expose] public section

namespace Karttunen1973

open Presupposition

variable {W : Type*}

/-! ### Sentences -/

/-- A sentence as the projection rules see it: its assertion, and the propositions it presupposes,
each of which a filter keeps or removes on its own. -/
structure Sentence (W : Type*) where
  /-- Where the assertion holds. -/
  assertion : Set W
  /-- The propositions the sentence presupposes. -/
  presupposes : Set (Set W)

namespace Sentence

variable (A : Sentence W) {C : Set W}

/-- Where the sentence is true: its presuppositions and its assertion hold. -/
def truth : Set W := A.assertion ∩ ⋂₀ A.presupposes

/-- Internal negation, which keeps the presuppositions. -/
def neg : Sentence W := ⟨A.assertionᶜ, A.presupposes⟩

@[simp] theorem presupposes_neg : A.neg.presupposes = A.presupposes := rfl

@[simp] theorem neg_neg : A.neg.neg = A := by simp [neg]

/-- A sentence entails each of its presuppositions (fn. 10). -/
theorem truth_subset_of_mem (h : C ∈ A.presupposes) : A.truth ⊆ C :=
  fun _ hw ↦ hw.2 C h

/-- The sentence of a partial proposition, which presupposes its presupposition. -/
def ofPartialProp (p : PartialProp W) : Sentence W := ⟨{w | p.assertion w}, {{w | p.presup w}}⟩

end Sentence

/-! ### The filters (§5–§7) -/

section Filters

variable (φ : Set W → Set W → Prop) (A B : Sentence W)

/-- (13): `if A then B` presupposes what `A` presupposes and each presupposition of `B` that `A`
does not filter, by the relation `φ` from the truth of `A`. -/
def cond : Sentence W :=
  ⟨A.assertionᶜ ∪ B.assertion, A.presupposes ∪ {C ∈ B.presupposes | ¬ φ A.truth C}⟩

/-- (17): `A and B` presupposes what `A` presupposes and each presupposition of `B` that `A` does
not filter. -/
def conj : Sentence W :=
  ⟨A.assertion ∩ B.assertion, A.presupposes ∪ {C ∈ B.presupposes | ¬ φ A.truth C}⟩

/-- (24): `A or B` presupposes what `A` presupposes and each presupposition of `B` that the
negation of `A` does not filter. -/
def disj : Sentence W :=
  ⟨A.assertion ∪ B.assertion, A.presupposes ∪ {C ∈ B.presupposes | ¬ φ A.neg.truth C}⟩

/-- (13a): a conditional presupposes what its antecedent presupposes, even what the antecedent
filters as a presupposition of the consequent (fn. 10). -/
theorem presupposes_subset_cond : A.presupposes ⊆ (cond φ A B).presupposes :=
  Set.subset_union_left

/-- Under the original condition, a filtered presupposition holds wherever the first conjunct is
true, so the conjunction is true exactly where both conjuncts are. -/
theorem truth_conj : (conj (· ⊆ ·) A B).truth = A.truth ∩ B.truth := by
  ext w
  simp only [Sentence.truth, conj, Set.mem_inter_iff, Set.mem_sInter, Set.mem_union,
    Set.mem_sep_iff]
  constructor
  · rintro ⟨⟨ha, hb⟩, h⟩
    refine ⟨⟨ha, fun C hC ↦ h C (.inl hC)⟩, hb, fun C hC ↦ ?_⟩
    by_cases hf : A.truth ⊆ C
    · exact hf ⟨ha, fun C hC ↦ h C (.inl hC)⟩
    · exact h C (.inr ⟨hC, hf⟩)
  · rintro ⟨⟨ha, hA⟩, hb, hB⟩
    exact ⟨⟨ha, hb⟩, fun C ↦ by rintro (hC | ⟨hC, -⟩) <;> simp_all⟩

/-! ### Harman's derivation (§8) -/

/-- The rules satisfy Harman's principle for the equivalence of `A ⊃ B` with `¬A ∨ B`. -/
theorem presupposes_cond : (cond φ A B).presupposes = (disj φ A.neg B).presupposes := by
  simp [cond, disj]

/-- The rules satisfy Harman's principle for the equivalence of `A & B` with `¬(¬A ∨ ¬B)`. -/
theorem presupposes_conj : (conj φ A B).presupposes = (disj φ A.neg B.neg).neg.presupposes := by
  simp [conj, disj]

/-- The rules satisfy Harman's principle for the equivalence of `A ∨ B` with `¬A ⊃ B`. -/
theorem presupposes_disj : (disj φ A B).presupposes = (cond φ A.neg B).presupposes := rfl

end Filters

section Harman

variable {S : Type*} {neg : S → S} {cond conj disj : S → S → S} {π : S → Set (Set W)}
  {f : S → Set W → Prop}

/-- Harman's derivation of (17) from (13) (§8): if internal negation keeps presuppositions, and
`A ⊃ B` shares them with `¬A ∨ B` and `A & B` with `¬(¬A ∨ ¬B)`, then a conditional that filters
a presupposition of `B` when `A` filters it makes the conjunction filter it the same way. -/
theorem harman_conj (hneg : ∀ A, π (neg A) = π A)
    (hcond : ∀ A B, π (cond A B) = π (disj (neg A) B))
    (hconj : ∀ A B, π (conj A B) = π (neg (disj (neg A) (neg B))))
    (h13 : ∀ A B, π (cond A B) = π A ∪ {C ∈ π B | ¬ f A C}) (A B : S) :
    π (conj A B) = π A ∪ {C ∈ π B | ¬ f A C} := by
  rw [hconj, hneg, ← hcond, h13, hneg]

/-- The rule for disjunction (24) by the same reasoning (§8): with `A ∨ B` sharing its
presuppositions with `¬A ⊃ B`, the disjunction filters a presupposition of `B` when `¬A` filters
it. -/
theorem harman_disj (hneg : ∀ A, π (neg A) = π A)
    (hdisj : ∀ A B, π (disj A B) = π (cond (neg A) B))
    (h13 : ∀ A B, π (cond A B) = π A ∪ {C ∈ π B | ¬ f A C}) (A B : S) :
    π (disj A B) = π A ∪ {C ∈ π B | ¬ f (neg A) C} := by
  rw [hdisj, h13, hneg]

end Harman

/-! ### Jack's children (§5–§7) -/

/-- `Jack has children`, over whether he does. -/
def hasChildren : Sentence Bool := ⟨{true}, ∅⟩

/-- `Jack has no children`. -/
def noChildren : Sentence Bool := hasChildren.neg

/-- `All of Jack's children are bald`, which presupposes that Jack has children; the assertion is
idealized. -/
def allBald : Sentence Bool := ⟨Set.univ, {{true}}⟩

private theorem truth_hasChildren : hasChildren.truth = {true} := by
  simp [Sentence.truth, hasChildren]

private theorem truth_noChildren : noChildren.truth = {false} := by
  ext b; cases b <;> simp [Sentence.truth, Sentence.neg, noChildren, hasChildren]

private theorem truth_allBald : allBald.truth = {true} := by
  simp [Sentence.truth, allBald]

/-- (16a) presupposes nothing and (16b) that Jack has children: conjunction is not commutative on
presuppositions. -/
theorem presupposes_conj_16 :
    (conj (· ⊆ ·) hasChildren allBald).presupposes = ∅ ∧
      (conj (· ⊆ ·) allBald hasChildren).presupposes = {{true}} := by
  refine ⟨Set.eq_empty_of_forall_notMem fun C ↦ ?_, ?_⟩
  · rintro (h | ⟨hC, h⟩)
    · exact h
    · exact h (by rw [truth_hasChildren, Set.mem_singleton_iff.1 hC])
  · ext C
    simp [conj, allBald, hasChildren]

/-- (22a) presupposes nothing, and by (24a) (22b) presupposes that Jack has children, a sentence
the paper leaves undecided (fn. 11). -/
theorem presupposes_disj_22 :
    (disj (· ⊆ ·) noChildren allBald).presupposes = ∅ ∧
      (disj (· ⊆ ·) allBald noChildren).presupposes = {{true}} := by
  refine ⟨Set.eq_empty_of_forall_notMem fun C ↦ ?_, ?_⟩
  · rintro (h | ⟨hC, h⟩)
    · exact h
    · refine h ?_
      rw [Set.mem_singleton_iff.1 hC, noChildren, Sentence.neg_neg, truth_hasChildren]
  · ext C
    simp [disj, allBald, noChildren, hasChildren, Sentence.neg]

/-- The rule for conditionals does not carry over to disjunction (§8): (11a) presupposes nothing,
but `Either Jack has children or all of Jack's children are bald` presupposes that he has
children, since his having none does not entail it. -/
theorem presupposes_cond_11a_disj :
    (cond (· ⊆ ·) hasChildren allBald).presupposes = ∅ ∧
      {true} ∈ (disj (· ⊆ ·) hasChildren allBald).presupposes := by
  refine ⟨Set.eq_empty_of_forall_notMem fun C ↦ ?_, .inr ⟨rfl, fun h ↦ ?_⟩⟩
  · rintro (h | ⟨hC, h⟩)
    · exact h
    · exact h (by rw [truth_hasChildren, Set.mem_singleton_iff.1 hC])
  · rw [← noChildren, truth_noChildren] at h
    exact absurd (h rfl) (by simp)

/-- `Jack has children, and Jack's children regret that baldness is hereditary`, over whether
Jack has children and whether baldness is hereditary: the second conjunct presupposes both, (1a)
and (1b), and the rule (17) filters the first, which the first conjunct entails, and keeps the
second. -/
theorem presupposes_conj_regret :
    {w | w.2} ∈ (conj (· ⊆ ·) (⟨{w | w.1}, ∅⟩ : Sentence (Bool × Bool))
      ⟨Set.univ, {{w | w.1}, {w | w.2}}⟩).presupposes ∧
    {w | w.1} ∉ (conj (· ⊆ ·) (⟨{w | w.1}, ∅⟩ : Sentence (Bool × Bool))
      ⟨Set.univ, {{w | w.1}, {w | w.2}}⟩).presupposes := by
  have ht : (⟨{w | w.1}, ∅⟩ : Sentence (Bool × Bool)).truth = {w | w.1} := by
    simp [Sentence.truth]
  refine ⟨.inr ⟨.inr rfl, fun h ↦ ?_⟩, ?_⟩
  · rw [ht] at h
    exact absurd (h (show (true, false) ∈ {w : Bool × Bool | w.1} from rfl)) (by simp)
  · rintro (h | ⟨-, h⟩)
    · exact h
    · exact h ht.le

/-! ### Assumed facts (§9) -/

/-- (24b′) and (17b′): given the assumed facts `F`, the premise `P` filters `C` when some set of
them, possibly empty, entails `C` together with `P`, though it does not entail the negation of `P`
nor `C` alone (Murphy's restrictions). -/
def Filters (F : Set (Set W)) (P C : Set W) : Prop :=
  ∃ X ⊆ F, ⋂₀ X ∩ P ⊆ C ∧ ¬ ⋂₀ X ⊆ Pᶜ ∧ ¬ ⋂₀ X ⊆ C

/-- With no assumed facts, a premise filters what it entails, if it is consistent and what it
entails is not a tautology. -/
theorem filters_empty_iff {P C : Set W} :
    Filters ∅ P C ↔ P ⊆ C ∧ P.Nonempty ∧ C ≠ Set.univ := by
  simp [Filters, Set.subset_empty_iff, Set.not_subset, Set.eq_univ_iff_forall, Set.nonempty_def]

/-- No set of assumed facts filters a tautology, which each of them entails alone. -/
theorem not_filters_univ (F : Set (Set W)) (P : Set W) : ¬ Filters F P Set.univ :=
  fun ⟨_, _, _, _, h⟩ ↦ h (Set.subset_univ _)

/-- Whether Geraldine is a Mormon and whether she has worn holy underwear. -/
inductive Geraldine where
  | mormonWorn
  | mormonUnworn
  | gentileWorn
  | gentileUnworn

/-- (26) `Geraldine is a Mormon`. -/
abbrev mormon : Set Geraldine := {.mormonWorn, .mormonUnworn}

/-- (27) `Geraldine has worn holy underwear`. -/
abbrev worn : Set Geraldine := {.mormonWorn, .gentileWorn}

/-- (25) `Either Geraldine is not a Mormon or she has given up wearing her holy underwear`,
whose second disjunct presupposes (27); its assertion is idealized. -/
def geraldine (φ : Set Geraldine → Set Geraldine → Prop) : Sentence Geraldine :=
  disj φ ⟨mormonᶜ, ∅⟩ ⟨Set.univ, {worn}⟩

private theorem truth_mormon : (⟨mormonᶜ, ∅⟩ : Sentence Geraldine).neg.truth = mormon := by
  simp [Sentence.truth, Sentence.neg]

/-- Absolutely, (25) presupposes (27): (26) does not entail it. -/
theorem worn_mem_geraldine : worn ∈ (geraldine (· ⊆ ·)).presupposes := by
  refine .inr ⟨rfl, fun h ↦ ?_⟩
  rw [truth_mormon] at h
  exact absurd (h (show Geraldine.mormonUnworn ∈ mormon by simp)) (by simp)

/-- Given (28) `All Mormons have worn holy underwear`, (25) does not presuppose (27): (26) and
(28) together entail it. -/
theorem worn_not_mem_geraldine_28 :
    worn ∉ (geraldine (Filters {{Geraldine.mormonUnworn}ᶜ})).presupposes := by
  rintro (h | ⟨-, h⟩)
  · exact h
  · rw [truth_mormon] at h
    refine h ⟨{{Geraldine.mormonUnworn}ᶜ}, le_rfl, ?_, ?_, ?_⟩ <;> simp only [Set.sInter_singleton]
    · rintro (_ | _ | _ | _) ⟨h1, h2⟩ <;> simp_all
    · intro h'
      exact absurd (h' (show Geraldine.mormonWorn ∈ ({.mormonUnworn}ᶜ : Set Geraldine) by simp))
        (by simp)
    · intro h'
      exact absurd (h' (show Geraldine.gentileUnworn ∈ ({.mormonUnworn}ᶜ : Set Geraldine) by simp))
        (by simp)

/-- In the contrary context the paper sketches, where Mormons must not wear holy underwear, (25)
presupposes (27). -/
theorem worn_mem_geraldine_contrary :
    worn ∈ (geraldine (Filters {{Geraldine.mormonWorn}ᶜ})).presupposes := by
  refine .inr ⟨rfl, ?_⟩
  rw [truth_mormon]
  rintro ⟨X, hX, h, -, -⟩
  rcases Set.subset_singleton_iff_eq.1 hX with rfl | rfl
  · simp only [Set.sInter_empty, Set.univ_inter] at h
    exact absurd (h (show Geraldine.mormonUnworn ∈ mormon by simp)) (by simp)
  · simp only [Set.sInter_singleton] at h
    exact absurd (h (show Geraldine.mormonUnworn ∈ ({.mormonWorn}ᶜ ∩ mormon : Set Geraldine) by
      simp)) (by simp)

/-- Murphy's first restriction: an assumed fact that contradicts the negated first disjunct,
`Geraldine is not a Mormon`, filters nothing, so (25) presupposes (27) relative to it. -/
theorem worn_mem_geraldine_notMormon : worn ∈ (geraldine (Filters {mormonᶜ})).presupposes := by
  refine .inr ⟨rfl, ?_⟩
  rw [truth_mormon]
  rintro ⟨X, hX, h, hc, -⟩
  rcases Set.subset_singleton_iff_eq.1 hX with rfl | rfl
  · simp only [Set.sInter_empty, Set.univ_inter] at h
    exact absurd (h (show Geraldine.mormonUnworn ∈ mormon by simp)) (by simp)
  · exact hc (by simp)

/-- `Nixon will appoint J. Edgar Hoover to the Cabinet`, over whether he will and whether Hoover is
a homosexual (32). -/
def appoint : Sentence (Bool × Bool) := ⟨{w | w.1}, ∅⟩

/-- `He will regret having appointed a homosexual`, which presupposes (31). -/
def regret : Sentence (Bool × Bool) := ⟨Set.univ, {{w | w.1 ∧ w.2}}⟩

private theorem filters_32 :
    Filters {{w : Bool × Bool | w.2}} appoint.truth {w | w.1 ∧ w.2} := by
  refine ⟨_, le_rfl, ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    simp only [Set.sInter_singleton, appoint, Sentence.truth, Set.sInter_empty, Set.inter_univ] at *
  · exact fun w ⟨h2, h1⟩ ↦ ⟨h1, h2⟩
  · exact absurd (h (show (true, true) ∈ {w : Bool × Bool | w.2} from rfl)) (by simp)
  · exact absurd (h (show (false, true) ∈ {w : Bool × Bool | w.2} from rfl)) (by simp)

/-- (30a–c) with no assumed facts: each presupposes (31), which (33) alone does not entail. -/
theorem mem_presupposes_30 :
    {w | w.1 ∧ w.2} ∈ (cond (Filters ∅) appoint regret).presupposes ∧
      {w | w.1 ∧ w.2} ∈ (conj (Filters ∅) appoint regret).presupposes ∧
      {w | w.1 ∧ w.2} ∈ (disj (Filters ∅) appoint.neg regret).presupposes := by
  have h : ¬ Filters ∅ appoint.truth {w : Bool × Bool | w.1 ∧ w.2} := fun h ↦ by
    have := filters_empty_iff.1 h |>.1 (show (true, false) ∈ appoint.truth by
      simp [Sentence.truth, appoint])
    simp at this
  exact ⟨.inr ⟨rfl, h⟩, .inr ⟨rfl, h⟩, .inr ⟨rfl, by simpa using h⟩⟩

/-- (30a–c): given (32), none of the conditional, the conjunction and the disjunction presupposes
(31), since (32) and (33) together entail it. -/
theorem not_mem_presupposes_30 :
    {w | w.1 ∧ w.2} ∉ (cond (Filters {{w | w.2}}) appoint regret).presupposes ∧
      {w | w.1 ∧ w.2} ∉ (conj (Filters {{w | w.2}}) appoint regret).presupposes ∧
      {w | w.1 ∧ w.2} ∉ (disj (Filters {{w | w.2}}) appoint.neg regret).presupposes := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro (h | ⟨-, h⟩)
  all_goals first | exact h | exact h (by simpa using filters_32)

/-- `John is dumb`, over whether he is. -/
def johnDumb : Sentence Bool := ⟨{true}, ∅⟩

/-- `He knows that if it rains, it rains`, which presupposes a tautology (fn. 13). -/
def knowsTautology : Sentence Bool := ⟨Set.univ, {Set.univ}⟩

/-- Fn. 13: the original condition (24b) filters the tautology presupposed by the second disjunct
of `Either John is dumb, or he knows that if it rains, it rains`. -/
theorem univ_not_mem_presupposes_disj :
    Set.univ ∉ (disj (· ⊆ ·) johnDumb knowsTautology).presupposes := by
  rintro (h | ⟨-, h⟩)
  · exact h
  · exact h (Set.subset_univ _)

/-- Fn. 13's tautology, which the revised condition (24b′) keeps: with Murphy's restrictions no
set of assumed facts filters it. -/
theorem univ_mem_presupposes_disj_filters (F : Set (Set Bool)) :
    Set.univ ∈ (disj (Filters F) johnDumb knowsTautology).presupposes :=
  .inr ⟨rfl, not_filters_univ F _⟩

/-! ### Truth-functional conjunction (§10) -/

section TruthFunctional

variable (p q : PartialProp W) (w : W)

/-- Bochvar's internal conjunction (34a) ([bochvar-1937]), the substrate's `PartialProp.and`, is
a hole: it is defined only where both conjuncts are. -/
theorem presup_and : (p.and q).presup w ↔ p.presup w ∧ q.presup w := Iff.rfl

/-- Bochvar's external conjunction (34d), the conjunction of the conjuncts' truth, `t(A) & t(B)`
(fn. 18), is a plug: it is defined everywhere. -/
theorem presup_and_truthOp : (p.truthOp.and q.truthOp).presup w := ⟨trivial, trivial⟩

/-- Łukasiewicz's conjunction (34b), the substrate's `PartialProp.andStrong`, is defined wherever a
conjunct is false, whatever the other conjunct presupposes. -/
theorem presup_andStrong_of_false (hp : p.presup w) (hf : ¬ p.assertion w) :
    (p.andStrong q).presup w :=
  .inr (.inl ⟨hp, hf⟩)

end TruthFunctional

/-- Whether Paris is the capital of France and whether France has a king. -/
inductive France where
  | parisKing
  | parisNoKing
  | marseilleKing
  | marseilleNoKing

/-- `Paris is the capital of France`. -/
abbrev capitalParis : Set France := {.parisKing, .parisNoKing}

/-- `France has a king`. -/
abbrev hasKing : Set France := {.parisKing, .marseilleKing}

/-- `The king of France is bald`, which presupposes a king; the assertion is idealized. -/
def kingBald : PartialProp France := ⟨(· ∈ hasKing), fun _ ↦ True⟩

/-- (35) at the actual world, with no king: Łukasiewicz's conjunction leaves (35a) `Paris is the
capital of France, and the king of France is bald` undefined but makes (35b), with `Marseilles`,
false. -/
theorem presup_andStrong_35 :
    ¬ ((PartialProp.ofProp (· ∈ capitalParis)).andStrong kingBald).presup .parisNoKing ∧
      ((PartialProp.ofProp (· ∉ capitalParis)).andStrong kingBald).presup .parisNoKing := by
  refine ⟨?_, presup_andStrong_of_false _ _ _ trivial (by simp [PartialProp.ofProp])⟩
  simp [PartialProp.andStrong, PartialProp.ofProp, kingBald]

/-- (35): by (17) both sentences presuppose a king, since neither capital entails one. -/
theorem hasKing_mem_presupposes_conj_35 :
    {w | w ∈ hasKing} ∈ (conj (· ⊆ ·) (.ofPartialProp (.ofProp (· ∈ capitalParis)))
        (.ofPartialProp kingBald)).presupposes ∧
      {w | w ∈ hasKing} ∈ (conj (· ⊆ ·) (.ofPartialProp (.ofProp (· ∉ capitalParis)))
        (.ofPartialProp kingBald)).presupposes := by
  refine ⟨.inr ⟨rfl, fun h ↦ ?_⟩, .inr ⟨rfl, fun h ↦ ?_⟩⟩
  · exact absurd (h (show France.parisNoKing ∈ _ by
      simp [Sentence.truth, Sentence.ofPartialProp, PartialProp.ofProp])) (by simp)
  · exact absurd (h (show France.marseilleNoKing ∈ _ by
      simp [Sentence.truth, Sentence.ofPartialProp, PartialProp.ofProp])) (by simp)

/-- The substrate's middle-Kleene `PartialProp.andFilter` is a truth table too, and shares
Łukasiewicz's verdict on (35b): it filters the presupposition of the second conjunct where the
first is false. -/
theorem andFilter_35b :
    ((PartialProp.ofProp (· ∉ capitalParis)).andFilter kingBald).presup .parisNoKing := by
  simp [PartialProp.andFilter, PartialProp.ofProp, kingBald]

/-! ### Propositional attitudes (§11) -/

section Attitudes

variable (φ : Set W → Set W → Prop) (att att₁ att₂ : Set W → Set W) (a c : Set W)

/-- A hole lets the presuppositions of its complement through. -/
def hole (att : Set W → Set W) (A : Sentence W) : Sentence W := ⟨att A.assertion, A.presupposes⟩

/-- A plug blocks them. -/
def plug (att : Set W → Set W) (A : Sentence W) : Sentence W := ⟨att A.assertion, ∅⟩

/-- (37) `Bill believes that Fred has been beating Zelda, and furthermore, Bill believes that Fred
has stopped beating Zelda`, and (42) with *hope* as the second attitude, with holes: the compound
presupposes that Fred has been beating Zelda unless believing it filters it, which under entailment
takes a veridical belief. -/
theorem mem_presupposes_conj_hole :
    a ∈ (conj φ (hole att₁ ⟨a, ∅⟩) (hole att₂ ⟨c, {a}⟩)).presupposes ↔ ¬ φ (att₁ a) a := by
  simp [conj, hole, Sentence.truth]

/-- (39) `Bill believes that Fred has been beating Zelda, and furthermore, that Fred has stopped
beating her`: the filter applies inside the complement, and nothing is presupposed whether the verb
is a hole or a plug. -/
theorem presupposes_hole_conj : (hole att (conj (· ⊆ ·) ⟨a, ∅⟩ ⟨c, {a}⟩)).presupposes = ∅ :=
  Set.eq_empty_of_forall_notMem fun _ ↦ by rintro (h | ⟨rfl, h⟩) <;> simp_all [Sentence.truth]

/-- (38): with belief as necessity over the believer's doxastic alternatives, (37) and (39)
assert the same ([hintikka-1962]), so a hole *believe* is saved on (37) only by the
equivalence. -/
theorem assertion_hole_box_conj (R : W → W → Prop) (A B : Sentence W) :
    (hole (ModalLogic.box R) (conj φ A B)).assertion =
      (conj φ (hole (ModalLogic.box R) A) (hole (ModalLogic.box R) B)).assertion := by
  ext w
  exact ModalLogic.box_and R _ _ w

/-- (42) as the conjunction of two distinct attitudes (43) admits no such equivalence; as plugs,
the attitudes leave it presupposing nothing, the paper's tentative verdict for the class. -/
theorem presupposes_conj_plug (A B : Sentence W) :
    (conj φ (plug att₁ A) (plug att₂ B)).presupposes = ∅ := by
  simp [conj, plug]

end Attitudes

end Karttunen1973
