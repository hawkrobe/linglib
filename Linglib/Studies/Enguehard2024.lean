import Linglib.Data.Examples.Enguehard2024
import Linglib.Semantics.Presupposition.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Enguehard (2024): What Number Marking on Indefinites Means

This file formalizes [enguehard-2024]'s conceivability presupposition and its account by
forward-looking competition. A singular indefinite infers exactly one witness and a plural one
at least two, (1), yet under negation both mean that the witness set is empty, (2) and (3), the
number inference being a scalar enrichment absent from downward-entailing environments
([spector-2007], [zweig-2009]). What survives negation, questions and conditionals is the
conceivability presupposition (7): the singular presupposes that exactly one witness is
conceivable and the plural that more than one is, so that a book has no *tables of contents*
and no *chapter*, (5) and (6). When both cardinalities are conceivable either number may be
used, and the production experiment of §3 shows that the choice tracks how often the objects
come in groups: the five conditions (11) teach a probability of multiple symbols from 0 to 1,
and the share of negated plural indefinites in the rule the participants then state rises
gradiently with it, both numbers being produced in every intermediate condition. This is the
gradient hypothesis H2 of (10); it refutes the null hypothesis and the categorical H1 that
[farkas-de-swart-2010]'s prototypicality generalization (8) yields, which Maximize
Presupposition ([sauerland-2003]) derives in §4.1 as a complementary distribution, competition
being unable to produce use conditions that overlap. The account of §5 rests on the dynamic
potential of negated indefinites, which set up referents for bathroom pronouns, double negation,
modals and denials, (14)–(17), in a bilateral or two-level dynamic semantics
([krahmer-muskens-1995], [elliott-2020]), and on the number matching of bound pronouns,
(18)–(20): a pronoun bears the referent's number feature ([sudo-2012]), is interpreted
maximally, and must fit the actual cardinality, so the denial of a negated singular indefinite
is ineffable when the card has several circles, (22). The principle (23), Provide useful
referents, then yields the conceivability presupposition, a referent whose number can never fit
being useless, and cannot be obeyed where both numbers can fit, so the speaker minimizes the
chance of ineffability by a best guess from the distribution of witnesses.

## Implementation notes

* Situations carry the cardinality of the witness set, and the conceivability presupposition
  quantifies over the conceivable situations; it is therefore constant across evaluation worlds
  and projects through `PartialProp.neg` unchanged. The book examples take their conceivable
  cardinalities from world knowledge, at most one table of contents and never a single chapter.
* The hypotheses of (10) are predicates on the share of plural among the negated indefinites
  produced in a condition. The paper reports Figure 2 graphically, so no observed share is
  typed; the finding enters through the hypotheses' logical relations and the prose above.
* The dynamic side is kept to what §5 states, a referent with a number feature and a pronoun
  that matches it and the actual cardinality; the paper provides no dynamic semantics and none
  is imported.
* The examples are `Data.Examples.Enguehard2024`.

## References

* [enguehard-2024]
* [farkas-de-swart-2010]
* [spector-2007]
* [zweig-2009]
* [sauerland-2003]
* [krahmer-muskens-1995]
* [elliott-2020]
* [sudo-2012]
* [sudo-2023]
-/

namespace Enguehard2024

open Presupposition Data.Examples Enguehard2024.Examples

/-- The number of an indefinite. -/
inductive Number
  | sg
  | pl
  deriving DecidableEq, Repr

/-- The inference about the witness set that (1)–(3) record. -/
inductive Inference
  | one
  | atLeastTwo
  | zero
  deriving DecidableEq, Repr

/-- The inference as a condition on the cardinality of the witness set. -/
def Inference.holds : Inference → ℕ → Prop
  | .one, k => k = 1
  | .atLeastTwo, k => 2 ≤ k
  | .zero, k => k = 0

instance (i : Inference) (k : ℕ) : Decidable (i.holds k) := by
  cases i <;> unfold Inference.holds <;> infer_instance

/-- The number inference of a positive indefinite, (1). -/
def Number.inference : Number → Inference
  | .sg => .one
  | .pl => .atLeastTwo

/-- A cardinality fits a number: exactly one for the singular, at least two for the plural. -/
def Number.Fits (n : Number) (k : ℕ) : Prop := n.inference.holds k

instance (n : Number) (k : ℕ) : Decidable (n.Fits k) := by unfold Number.Fits; infer_instance

/-! ### The number inference and its loss under negation -/

/-- The numbers as named in the rows. -/
def numberTable : List (String × Number) := [("sg", .sg), ("pl", .pl)]

/-- The inferences as named in the rows. -/
def inferenceTable : List (String × Inference) :=
  [("one", .one), ("atLeastTwo", .atLeastTwo), ("zero", .zero)]

/-- Whether the indefinite is negated or negative, as named in the rows. -/
def polarityTable : List (String × Bool) :=
  [("positive", false), ("negated", true), ("negative", true)]

/-- An indefinite of (1)–(3): its number, whether it is negated, and the inference it carries. -/
structure IndefiniteRow where
  number : Number
  negated : Bool
  inference : Inference
  deriving DecidableEq, Repr

/-- A row from an example. -/
def IndefiniteRow.ofExample (ex : LinguisticExample) : Option IndefiniteRow := do
  pure ⟨← ex.parse? "number" numberTable, ← ex.parse? "polarity" polarityTable,
    ← ex.parse? "inference" inferenceTable⟩

/-- The indefinites of (1)–(3). -/
def indefiniteRows : List IndefiniteRow := Examples.all.filterMap IndefiniteRow.ofExample

/-- A positive indefinite infers the cardinality fitting its number; a negated one infers an
empty witness set whatever its number, (1)–(3). -/
theorem indefiniteRows_inference :
    ∀ r ∈ indefiniteRows, r.inference = if r.negated then .zero else r.number.inference := by
  decide

/-! ### The conceivability presupposition -/

variable {W : Type*}

/-- Some conceivable situation has a witness set whose cardinality satisfies `P`. -/
def Conceivable (C : W → Prop) (card : W → ℕ) (P : ℕ → Prop) : Prop := ∃ w, C w ∧ P (card w)

/-- The negated indefinite of number `n`: it asserts that the witness set is empty and
presupposes that a cardinality fitting `n` is conceivable, (7). -/
def negated (C : W → Prop) (card : W → ℕ) (n : Number) : PartialProp W where
  presup _ := Conceivable C card n.Fits
  assertion w := card w = 0

/-- Both numbers assert the same thing under negation. -/
theorem negated_assertion (C : W → Prop) (card : W → ℕ) (n n' : Number) :
    (negated C card n).assertion = (negated C card n').assertion := rfl

/-- The presupposition is constant across evaluation worlds. -/
theorem negated_presup_const (C : W → Prop) (card : W → ℕ) (n : Number) (w w' : W) :
    (negated C card n).presup w ↔ (negated C card n).presup w' := Iff.rfl

/-- The presupposition projects through negation, (15). -/
theorem negated_neg_presup (C : W → Prop) (card : W → ℕ) (n : Number) :
    (negated C card n).neg.presup = (negated C card n).presup := rfl

/-- A book has at most one table of contents. -/
def tableOfContents : ℕ → Prop := (· ≤ 1)

/-- A book never has a single chapter. -/
def chapters : ℕ → Prop := (· ≠ 1)

/-- (5): the singular presupposition of *table of contents* is met, the plural one fails. -/
theorem tableOfContents_presup :
    (negated tableOfContents id .sg).presup 0 ∧ ¬ (negated tableOfContents id .pl).presup 0 :=
  ⟨⟨1, le_rfl, rfl⟩, λ ⟨k, hk, h⟩ => absurd (h.trans hk) (by decide)⟩

/-- (6): the plural presupposition of *chapters* is met, the singular one fails. -/
theorem chapters_presup :
    (negated chapters id .pl).presup 0 ∧ ¬ (negated chapters id .sg).presup 0 :=
  ⟨⟨2, by simp [chapters], by decide⟩, λ ⟨_, hk, h⟩ => hk h⟩

/-! ### The production experiment -/

/-- The five conditions (11), by the probability that symbols of a kind come in multiples. -/
inductive Condition
  | sg
  | sgPl
  | mix
  | plSg
  | pl
  deriving DecidableEq, Repr

/-- The probability of multiple symbols of a kind, when there are any. -/
def Condition.pMultiple : Condition → ℚ
  | .sg => 0
  | .sgPl => 1 / 10
  | .mix => 1 / 2
  | .plSg => 9 / 10
  | .pl => 1

/-- A production profile: the share of plural among the negated indefinites produced in a
condition. -/
abbrev Profile := Condition → ℚ

/-- H0: productions do not depend on the distribution, (10a). -/
def H0 (f : Profile) : Prop := ∀ c c', f c = f c'

/-- H1: singular where uniqueness dominates and plural otherwise, plural at parity, (10b). -/
def H1 (f : Profile) : Prop := ∀ c, f c = if c.pMultiple < 1 / 2 then 0 else 1

/-- H2: the more multiples the more plural, and both numbers at parity, (10c). -/
def H2 (f : Profile) : Prop :=
  (∀ c c', c.pMultiple < c'.pMultiple → f c < f c') ∧ 0 < f .mix ∧ f .mix < 1

theorem H1.not_H0 {f : Profile} (h : H1 f) : ¬ H0 f := by
  intro h0
  have hs := h .sg
  have hp := h .pl
  norm_num [Condition.pMultiple] at hs hp
  linarith [h0 .sg .pl]

/-- No profile without overlap is gradient: the observed singular and plural productions in
every intermediate condition refute every complementary profile (§4.1). -/
theorem not_H2_of_complementary {f : Profile} (h : ∀ c, f c = 0 ∨ f c = 1) : ¬ H2 f := by
  intro h2
  rcases h .mix with hm | hm <;> linarith [h2.2.1, h2.2.2]

theorem H1.not_H2 {f : Profile} (h : H1 f) : ¬ H2 f :=
  not_H2_of_complementary λ c => by rw [h c]; split_ifs <;> simp

/-- Maximize Presupposition with an equivalent plural and a singular whose presupposition is
`S`: the plural is used exactly where the singular's presupposition fails. -/
def mpProfile (S : Condition → Prop) [DecidablePred S] : Profile := λ c => if S c then 0 else 1

theorem mpProfile_complementary (S : Condition → Prop) [DecidablePred S] (c : Condition) :
    mpProfile S c = 0 ∨ mpProfile S c = 1 := by
  unfold mpProfile; split_ifs <;> simp

/-- With the singular presupposing that any witness is certainly unique, the plural is used
everywhere but in the Sg condition. -/
theorem mpProfile_certain_uniqueness (c : Condition) :
    mpProfile (·.pMultiple = 0) c = if c = .sg then 0 else 1 := by
  cases c <;> norm_num [mpProfile, Condition.pMultiple] <;> decide

/-- With the singular presupposing that prototypical witnesses are unique, (8) read as
uniqueness in most situations, Maximize Presupposition yields H1, which the experiment
refutes: singular is produced in the Mix and PlSg conditions. -/
theorem mpProfile_prototypical : H1 (mpProfile (·.pMultiple < 1 / 2)) := λ _ => rfl

/-! ### Referents and their continuations -/

/-- The pronouns of (18)–(19). -/
inductive Pronoun
  | it
  | they
  deriving DecidableEq, Repr

/-- The number feature a pronoun bears, (a). -/
def Pronoun.number : Pronoun → Number
  | .it => .sg
  | .they => .pl

/-- The pronoun of a number. -/
def Number.pronoun : Number → Pronoun
  | .sg => .it
  | .pl => .they

@[simp] theorem Pronoun.number_pronoun (n : Number) : n.pronoun.number = n := by cases n <;> rfl

/-- A pronoun, read maximally, fits the actual cardinality of its referent, (b) and (c). -/
def Pronoun.Appropriate (p : Pronoun) (k : ℕ) : Prop := p.number.Fits k

/-- The pronouns as named in the rows. -/
def pronounTable : List (String × Pronoun) := [("it", .it), ("they", .they)]

/-- A continuation of (18)–(19): the number of the negated indefinite, the pronoun, and the
judgment. -/
structure ContinuationRow where
  antecedent : Number
  pronoun : Pronoun
  judgment : Features.Judgment
  deriving DecidableEq, Repr

/-- A row from an example. -/
def ContinuationRow.ofExample (ex : LinguisticExample) : Option ContinuationRow := do
  pure ⟨← ex.parse? "antecedent" numberTable, ← ex.parse? "pronoun" pronounTable, ex.judgment⟩

/-- The continuations of (18)–(19). -/
def continuationRows : List ContinuationRow := Examples.all.filterMap ContinuationRow.ofExample

/-- (18)–(19): a pronoun bound by a negated indefinite must match it in number, (a). -/
theorem continuationRows_match :
    ∀ r ∈ continuationRows, r.judgment = .acceptable ↔ r.pronoun.number = r.antecedent := by
  decide

/-- The referent set up by an indefinite of number `n` can be used in a continuation about a
witness set of cardinality `k`: some pronoun bears its number and fits the cardinality. -/
def Usable (n : Number) (k : ℕ) : Prop := ∃ p : Pronoun, p.number = n ∧ p.Appropriate k

theorem usable_iff_fits (n : Number) (k : ℕ) : Usable n k ↔ n.Fits k :=
  ⟨λ ⟨_, hp, h⟩ => hp ▸ h,
    λ h => ⟨n.pronoun, Pronoun.number_pronoun n, by simpa [Pronoun.Appropriate]⟩⟩

/-- The denier of (22) is left with a witness but no licit pronoun: the referent of a negated
singular indefinite is unusable when there are several circles. -/
theorem not_usable_sg_of_two_le {k : ℕ} (hk : 2 ≤ k) : ¬ Usable .sg k := by
  rw [usable_iff_fits]; show ¬ k = 1; omega

/-- A referent of number `n` is useful when some conceivable situation lets a continuation use
it, the principle (23). -/
def Useful (C : W → Prop) (card : W → ℕ) (n : Number) : Prop := Conceivable C card (Usable n)

/-- (23) yields the conceivability presupposition (7): the referent of `n` is useful exactly
when the negated indefinite's presupposition holds. -/
theorem useful_iff_presup (C : W → Prop) (card : W → ℕ) (n : Number) (w : W) :
    Useful C card n ↔ (negated C card n).presup w := by
  simp only [Useful, negated, Conceivable, usable_iff_fits]

/-- Where both numbers are conceivable, (23) cannot be obeyed: each number's referent is
unusable in some conceivable situation that has a witness. -/
theorem exists_not_usable (C : W → Prop) (card : W → ℕ)
    (hsg : Conceivable C card Number.sg.Fits) (hpl : Conceivable C card Number.pl.Fits) :
    ∀ n, ∃ w, C w ∧ 1 ≤ card w ∧ ¬ Usable n (card w) := by
  intro n
  cases n
  · obtain ⟨w, hw, h⟩ := hpl
    exact ⟨w, hw, by change 2 ≤ card w at h; omega, not_usable_sg_of_two_le h⟩
  · obtain ⟨w, hw, h⟩ := hsg
    refine ⟨w, hw, by change card w = 1 at h; omega, ?_⟩
    rw [usable_iff_fits]; change ¬ 2 ≤ card w; change card w = 1 at h; omega

/-- The chance that a referent of number `n` proves unusable when a witness set has several
members with probability `p`: the ineffability the speaker's best guess minimizes. -/
def ineffabilityChance (p : ℚ) : Number → ℚ
  | .sg => p
  | .pl => 1 - p

/-- The singular's chance of ineffability rises and the plural's falls with the probability of
multiples, the sensitivity to the distribution that §3 finds. -/
theorem ineffabilityChance_sg_monotone : Monotone (ineffabilityChance · .sg) := λ _ _ h => h

theorem ineffabilityChance_pl_antitone : Antitone (ineffabilityChance · .pl) := λ _ _ h => by
  simp only [ineffabilityChance]; linarith

/-- The conceivability presupposition as the limiting case (§6): in the extreme conditions the
number whose presupposition fails is the one whose referent is certainly unusable. -/
theorem ineffabilityChance_extreme :
    ineffabilityChance Condition.pl.pMultiple .sg = 1 ∧
      ineffabilityChance Condition.sg.pMultiple .pl = 1 := by
  norm_num [ineffabilityChance, Condition.pMultiple]

end Enguehard2024
