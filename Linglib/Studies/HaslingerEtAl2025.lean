import Linglib.Fragments.German.Distributives
import Linglib.Data.Examples.HaslingerEtAl2025

/-!
# Haslinger, Rosina, Schmitt and Wurm (2025): On the relation between distributivity and maximality

This file formalizes [haslinger-etal-2025]'s answer to whether every obligatorily distributive
operator blocks non-maximal construals of its associate plural. German *jed-* is distributive and
exception-intolerant in both its determiner and its distance use, *alle* and numeral indefinites
are exception-intolerant but not distributive, and definite plurals are neither (their (5)); the
distance distributor *jeweils* fills the remaining cell, since some speakers accept it in
scenarios whose question under discussion makes an exception irrelevant, where DP-*jeder* is
rejected and distance *jeder* mostly rejected (their §3). `Item.class` is the classification,
read off the German fragment where it has an entry and off the paper's truth-value judgments in
the scenarios of their (3) for the rest, and `jeweils_answers_Q` is the negative answer. In
[kriz-spector-2021]'s parameter semantics the contrast is a maximal distributive operator against
a tolerant one with a contextually supplied tolerance: `jeweils_accepts_magnets` runs the magnets
scenario of their (23), where the tolerance identifies the pluralities the explosion question does
not distinguish, and the speakers who reject *jeweils* there are those for whom the tolerance is
the identity. The same tools define the hypothetical determiner *jeder\** of their (27), which
accepts the scenario as well (`jederStar_accepts_magnets`), so the framework does not predict the
absence of exception-tolerant distributive determiners; the paper relates *jeweils*'s
permissiveness to its lacking a determiner use instead (`determiner_maximal`).

## Implementation notes

The questionnaire's ratings are prose: DP-*jeder* was overwhelmingly rejected, *jeweils* judged
bimodally, distance *jeder* mostly rejected, and 15 of 18 participants rated the *jeweils* member
of a minimal pair above its distance-*jeder* counterpart. The paper's examples and scenarios are
the rows of `Data/Examples/HaslingerEtAl2025.json`; the (3) judgments classify an item as
distributive when it is false in the cumulative scenario (3b) and as maximal when it is false in
the exception scenario (3c), which for *jeweils* out of the blue gives the maximal cell, the
non-maximal construal needing the questionnaire's contexts. The tolerance of the magnets scenario
tolerates every nonempty subplurality of the boxes, since one box with two magnets already
answers the explosion question.

## References

* [haslinger-etal-2025]
* [kriz-spector-2021]
-/

namespace HaslingerEtAl2025

open Plurality Plurality.Distributivity German.Distributives Data.Examples

/-- The expressions of their (5) and (22): the distance distributor *jeweils* beside the
determiner and distance uses of *jed-*, *alle*, numeral indefinites and definite plurals. -/
inductive Item where
  | definitePlural
  | numeralIndefinite
  | alle
  | jederDP
  | jederDistance
  | jeweils
  deriving DecidableEq, Repr, Fintype

/-- Whether the item is a determiner. -/
def Item.IsDeterminer : Item → Prop
  | .jederDP | .alle | .numeralIndefinite => True
  | .definitePlural | .jederDistance | .jeweils => False

instance : DecidablePred Item.IsDeterminer
  | .jederDP | .alle | .numeralIndefinite => isTrue trivial
  | .definitePlural | .jederDistance | .jeweils => isFalse not_false

/-- The two properties of their (5), obligatory distributivity and exception intolerance, read
off the German fragment where it has an entry. -/
def Item.class : Item → DistMaxClass
  | .definitePlural => .nonDistNonMax
  | .numeralIndefinite => .nonDistMax
  | .alle => alleEntry.distMaxClass
  | .jederDP | .jederDistance => jederEntry.distMaxClass
  | .jeweils => jeweilsEntry.distMaxClass

/-- Their question Q answered in the negative: an obligatorily distributive item that permits
exceptions. -/
theorem jeweils_answers_Q :
    Item.jeweils.class.isDistributive ∧ ¬ Item.jeweils.class.isMaximal := by decide

/-- Every cell of the classification is filled, the fourth by *jeweils*. -/
theorem four_cells : ∀ c : DistMaxClass, ∃ i : Item, i.class = c
  | .distMax => ⟨.jederDP, rfl⟩
  | .distNonMax => ⟨.jeweils, rfl⟩
  | .nonDistMax => ⟨.alle, rfl⟩
  | .nonDistNonMax => ⟨.definitePlural, rfl⟩

/-- Their §4 observation: among the attested items, every determiner is exception-intolerant. -/
theorem determiner_maximal : ∀ i : Item, i.IsDeterminer → i.class.isMaximal := by decide

/-! ### The scenarios of their (3) -/

/-- The classification an example row's judgments in their (3) determine: distributive if false
in the cumulative scenario (3b), maximal if false in the exception scenario (3c). -/
def classOfExample (ex : LinguisticExample) : Option DistMaxClass := do
  let b ← ex.feature? "trueIn3b"
  let c ← ex.feature? "trueIn3c"
  pure <| match b == "no", c == "no" with
    | true, true => .distMax
    | true, false => .distNonMax
    | false, true => .nonDistMax
    | false, false => .nonDistNonMax

/-- The rows of their (1), (2), (4) and (22a) classify the items as their (5) does, *jeweils* out
of the blue included. -/
theorem class_of_rows :
    ∀ p ∈ [(Item.jederDP, Examples.ex1), (.jederDistance, Examples.ex2), (.alle, Examples.ex4a),
      (.numeralIndefinite, Examples.ex4b), (.definitePlural, Examples.ex4c)],
      classOfExample p.2 = some p.1.class := by
  decide

theorem jeweils_maximal_out_of_the_blue : classOfExample Examples.ex22a = some .distMax := by
  decide

/-! ### The magnets scenario of their (23) -/

/-- The five boxes of their (23a). -/
abbrev Box := Fin 5

/-- Box `b` contains two magnets: all but the fifth. -/
def hasTwoMagnets (b : Box) (_ : Unit) : Prop := b < 4

instance (b : Box) (u : Unit) : Decidable (hasTwoMagnets b u) := inferInstanceAs (Decidable (b < 4))

/-- DP-*jeder* and distance *jeder*, `distMaximal`: false, since one box has one magnet. -/
theorem jeder_rejects_magnets : ¬ distMaximal hasTwoMagnets Finset.univ () := by decide

/-- *jeweils* with the tolerance the explosion question induces, every nonempty subplurality:
true, witnessed by the four boxes with two magnets. -/
theorem jeweils_accepts_magnets : distTolerant hasTwoMagnets Tolerance.trivial Finset.univ () := by
  decide

/-- The speakers who reject *jeweils* in the scenario are those whose tolerance is the identity,
for whom it coincides with *jeder*. -/
theorem jeweils_identity_rejects_magnets :
    ¬ distTolerant hasTwoMagnets Tolerance.identity Finset.univ () :=
  λ h => jeder_rejects_magnets
    ((distMaximal_iff_identity hasTwoMagnets Finset.univ () Finset.univ_nonempty).mpr h)

/-- The hypothetical determiner *jeder\** of their (27) accepts the scenario as *jeweils* does:
the framework's tools do not predict its absence. -/
theorem jederStar_accepts_magnets :
    distTolerantQuant (λ _ _ => True) hasTwoMagnets Tolerance.trivial Finset.univ () :=
  ⟨{0, 1, 2, 3}, by decide, by decide, by decide, λ _ _ => trivial, by decide⟩

end HaslingerEtAl2025
