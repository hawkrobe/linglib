import Linglib.Data.Examples.Rett2015
import Linglib.Fragments.English.Predicates.Adjectival
import Linglib.Semantics.Degree.Basic

/-!
# Rett (2015): evaluativity as implicature

[rett-2015] derives the distribution of evaluativity across degree constructions (the book's
Table 3.1) from two Neo-Gricean implicatures: a Quantity implicature strengthens the otherwise
tautological positive construction (Chapter 3), and the Marked Meaning Principle (Chapter 5,
after [horn-1984]'s division of pragmatic labor) makes the marked, negative antonym
evaluative in exactly the *polar-invariant* constructions — equatives and degree questions —
where its unmarked antonym has the same truth conditions. Antonym polarity is the adjective's
`Adjective.polarity`, the `ScalePolarity` that `Degree.equativeSem` and
`Degree.comparativeSem` already take as their direction; negative antonyms are the marked
members of their pairs ([bierwisch-1989], [kennedy-2007]).

## Main definitions

* `IsPolarInvariant`: Rett's classification of constructions.
* `implicature`, `Evaluative`: the implicature route, if any, deriving evaluativity for a
  construction and polarity.
* `evaluativity`: the same for a fragment adjective, read off its lexicalized polarity.

## Main results

* `implicature_eq_manner_iff`: the Marked Meaning Principle — Manner-derived evaluativity
  exactly for the marked antonym in a polar-invariant construction.
* `exact_equative_antonym_invariant`, `comparative_antonym_variant`: the equative and
  comparative rows of `IsPolarInvariant` derived from `Degree.equativeSem` and
  `Degree.comparativeSem`.
* `evaluative_iff_observed`: the predictions match every Table 3.1 judgment.
-/

namespace Rett2015

open Degree (ScalePolarity)
open Degree
open English.Predicates.Adjectival (tall short)

/-! ### Polar (in)variance and markedness -/

/-- Rett's polar (in)variance: in a polar-invariant construction the two antonyms yield the
same truth conditions, so the marked antonym has an unmarked competitor. Equatives and degree
questions are polar-invariant; positives, comparatives, and measure phrases are not. -/
def IsPolarInvariant : Construction → Prop
  | .equative | .degreeQuestion => True
  | .positive | .comparative | .measurePhrase => False

instance : DecidablePred IsPolarInvariant
  | .equative | .degreeQuestion => isTrue trivial
  | .positive | .comparative | .measurePhrase => isFalse id

/-- Negative antonyms are the marked members of their pairs. -/
def IsMarked : ScalePolarity → Prop
  | .negative => True
  | .positive => False

instance : DecidablePred IsMarked
  | .negative => isTrue trivial
  | .positive => isFalse id

/-! ### The implicature derivation -/

/-- The implicature route deriving evaluativity: Quantity (Chapter 3's degree tautology) or
Manner (Chapter 5's Marked Meaning Principle). -/
inductive Implicature where
  | quantity
  | manner
  deriving DecidableEq, Repr

/-- The implicature deriving evaluativity for a construction and antonym polarity, if any:
positives are strengthened by Quantity for both antonyms, and polar-invariant constructions
get Manner-derived evaluativity for the marked antonym only. -/
def implicature : Construction → ScalePolarity → Option Implicature
  | .positive, _ => some .quantity
  | .equative, .negative | .degreeQuestion, .negative => some .manner
  | _, _ => none

/-- A construction–polarity pair is evaluative iff some implicature derives it. -/
def Evaluative (c : Construction) (p : ScalePolarity) : Prop := implicature c p ≠ none

instance (c : Construction) (p : ScalePolarity) : Decidable (Evaluative c p) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- The Marked Meaning Principle: Manner-derived evaluativity exactly for the marked antonym
in a polar-invariant construction. -/
theorem implicature_eq_manner_iff (c : Construction) (p : ScalePolarity) :
    implicature c p = some .manner ↔ IsPolarInvariant c ∧ IsMarked p := by
  cases c <;> cases p <;> decide

/-- Quantity-derived evaluativity is the positive construction's alone. -/
theorem implicature_eq_quantity_iff (c : Construction) (p : ScalePolarity) :
    implicature c p = some .quantity ↔ c = .positive := by
  cases c <;> cases p <;> decide

/-- Evaluativity is the positive construction or the Marked Meaning Principle. -/
theorem evaluative_iff (c : Construction) (p : ScalePolarity) :
    Evaluative c p ↔ c = .positive ∨ (IsPolarInvariant c ∧ IsMarked p) := by
  cases c <;> cases p <;> decide

/-! ### The book's contrasts

Chapter 1's *How short is Adam?* and *Adam is as short as Doug* are evaluative; their
positive-antonym counterparts are not. -/

/-- The implicature deriving evaluativity for a fragment adjective in a construction, read off
its lexicalized polarity. -/
def evaluativity (a : GradableAdjective) (c : Construction) : Option Implicature :=
  a.polarity.bind (implicature c)

theorem as_short_as : evaluativity short .equative = some .manner := rfl

theorem as_tall_as : evaluativity tall .equative = none := rfl

theorem how_short : evaluativity short .degreeQuestion = some .manner := rfl

/-! ### Polar variance grounded in the comparison semantics

[rett-2015] reduces polar (in)variance to mutual entailment of the antonyms' non-evaluative
readings: the strengthened ("exactly") equatives of the two antonyms share truth conditions,
so a truth-conditionally equivalent unmarked alternative exists and the Marked Meaning
Principle can fire; the antonym comparatives exclude each other, so no such alternative
exists. Degree questions pattern with the equative — both antonyms' true answers are the
subject's actual measure. -/

section PolarVarianceGrounding

variable {Entity D : Type*} [LinearOrder D] (μ : Entity → D) (a b : Entity)

/-- "A is exactly as tall as B" and "A is exactly as short as B" are mutually entailing: each
strengthened equative reduces to `μ a = μ b`. -/
theorem exact_equative_antonym_invariant :
    (equativeSem μ a b .positive ∧ ¬ comparativeSem μ a b .positive) ↔
      (equativeSem μ a b .negative ∧ ¬ comparativeSem μ a b .negative) := by
  simp only [equativeSem, comparativeSem, ge_iff_le, not_lt]
  exact and_comm

/-- Both strengthened antonym equatives are the "exactly" reading
`Degree.equativeStrengthened`. -/
theorem exact_equative_eq_strengthened :
    (equativeSem μ a b .positive ∧ ¬ comparativeSem μ a b .positive) ↔
      equativeStrengthened μ a b := by
  simp only [equativeSem, comparativeSem, equativeStrengthened, ge_iff_le, not_lt,
    le_antisymm_iff]
  exact and_comm

/-- The antonym comparatives exclude each other: "A is taller than B" and "A is shorter than
B" cannot both hold. -/
theorem comparative_antonyms_exclusive :
    comparativeSem μ a b .positive → ¬ comparativeSem μ a b .negative :=
  fun h => lt_asymm h

/-- Whenever the antonyms could differ (`μ a ≠ μ b`), they do: the antonym comparatives have
complementary truth conditions, so no truth-conditionally equivalent unmarked alternative
exists. -/
theorem comparative_antonym_variant (h : μ a ≠ μ b) :
    comparativeSem μ a b .positive ↔ ¬ comparativeSem μ a b .negative := by
  simp only [comparativeSem, not_lt]
  exact ⟨le_of_lt, fun hle => hle.lt_of_ne h.symm⟩

end PolarVarianceGrounding

/-! ### Table 3.1 -/

/-- A Table 3.1 judgment: construction, antonym polarity, and whether the sentence is
evaluative. The ungrammatical negative-antonym measure phrase carries no judgment. -/
def datum (e : Data.Examples.LinguisticExample) : Option (Construction × ScalePolarity × Bool) :=
  do
    let c ← match e.feature? "construction" with
      | some "positive" => some Construction.positive
      | some "comparative" => some .comparative
      | some "equative" => some .equative
      | some "measurePhrase" => some .measurePhrase
      | some "degreeQuestion" => some .degreeQuestion
      | _ => none
    let p ← match e.feature? "polarity" with
      | some "positive" => some ScalePolarity.positive
      | some "negative" => some .negative
      | _ => none
    let v ← match e.feature? "evaluative" with
      | some "true" => some true
      | some "false" => some false
      | _ => none
    pure (c, p, v)

/-- The Table 3.1 judgments. -/
def data : List (Construction × ScalePolarity × Bool) := Examples.all.filterMap datum

/-- The predictions match every Table 3.1 judgment. -/
theorem evaluative_iff_observed : ∀ d ∈ data, Evaluative d.1 d.2.1 ↔ d.2.2 = true := by
  decide

end Rett2015
