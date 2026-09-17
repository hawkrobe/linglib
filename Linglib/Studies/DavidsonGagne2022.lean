import Linglib.Data.Examples.DavidsonGagne2022
import Linglib.Fragments.ASL.Determiners
import Linglib.Semantics.Mereology
import Linglib.Semantics.Presupposition.Basic
import Linglib.Semantics.Quantification.DomainRestriction
import Mathlib.Order.Heyting.Basic

/-!
# Davidson and Gagne (2022): "More is up" for domain restriction in ASL

A plural pronoun, a directional verb or a quantifier of ASL signed higher in signing space than
the neutral plane refers to, or quantifies over, a wider domain than the contextually given
one: at neutral height *all became vampires* is about the friends who watched the film, at a
higher locus about everyone in the world, a third level fits between them, and the heights are
relative rather than absolute. The height is not emphasis or gesture, since it weakens rather
than strengthens an existential and context cannot override it, and it is not the domain
widening of free-choice indefinites, since it attaches to negative and proportional
quantifiers as well. It enters only where the structure contains a pronoun: bare nouns cannot
take it, plain verbs need a separate `IX-arc`, directional verbs incorporate it, and a
quantifier incorporates it or takes a following `IX-arc` as its phonology allows. The paper
analyses height as a presuppositional feature of the plural pronoun, the neutral height
requiring the referent's parts to lie in the context and a marked height requiring the referent
to properly contain it, with the convention that vertically ordered marked loci denote properly
nested plurals; a quantifier composes with the pronoun through a partitive, so that its domain
is the pronoun's referent.

We state the feature semantics, the partitive composition and the monotonicity argument over
the mereology and presupposition substrate, classify the fragment's quantifier signs by how they
realise the pronoun, and check the paper's examples.

## Implementation notes

* The marked height is one binary feature, since the paper keeps a feature rather than a purely
  iconic mapping; the ordering among marked loci is the paper's convention (45), a strictly
  monotone map from heights to plurals, taken as a hypothesis where it is used.
* A context in which the neutral pronoun denotes the sum of the contextual individuals is
  the parts of that sum, which is how (50) recovers *all of them* as quantification over the
  context.

## References

* [K. Davidson and D. Gagne, *"More is up" for domain restriction in ASL*
  (2022)][davidson-gagne-2022]
* [L. Bergen, *Joint inference in pragmatic reasoning* (2016)][bergen-2016]
* [W. A. Ladusaw, *Semantic constraints on the English partitive construction*
  (1982)][ladusaw-1982]
* [C. A. Padden, *Interaction of morphology and syntax in American Sign Language*
  (1988)][padden-1988]
* [P. Schlenker, J. Lamberton and M. Santoro, *Iconic variables*
  (2013)][schlenker-lamberton-santoro-2013]
* [J. Stanley and Z. Gendler Szabó, *On quantifier domain restriction*
  (2000)][stanley-szab-2000]
-/

namespace DavidsonGagne2022

open Quantification Presupposition Data.Examples ASL.Determiners

variable {E : Type*} [PartialOrder E]

/-! ### The height feature on plural pronouns -/

/-- (46a) `⟦arc⟧`: the referent of the plural pronoun is not an atom. -/
def Arc (x : E) : Prop := ¬ Mereology.Atom x

/-- (47c) `⟦neutral⟧`: every part of the referent lies in the contextual domain. -/
def Neutral (C : Set E) (x : E) : Prop := Set.Iic x ⊆ C

/-- (44), (46b) `⟦domain-k⟧`: the referent properly contains the contextual domain. -/
def Domain (C : Set E) (x : E) : Prop := C ⊂ Set.Iic x

/-- (47b) `⟦-a⟧`: a marked horizontal locus presupposes a distinct focus alternative. -/
def Contrast (alt : E → Set E) (x : E) : Prop := ∃ y ∈ alt x, x ≠ y

/-- The vertical feature of §5: the neutral plane, or a marked locus above it. -/
inductive Height
  | neutral
  | marked
  deriving DecidableEq

/-- The presupposition a height feature contributes in the context `C`. -/
def Height.presup (C : Set E) : Height → E → Prop
  | .neutral => Neutral C
  | .marked => Domain C

open Classical in
/-- (46e), (47e) `⟦[ixᵢ]-arc-h⟧^{g,C}`: the pronoun denotes `g i` when that is a non-atomic
plural meeting the height presupposition, and is otherwise undefined. -/
noncomputable def ixArc {ι : Type*} (g : ι → E) (C : Set E) (h : Height) (i : ι) : Option E :=
  if Arc (g i) ∧ h.presup C (g i) then some (g i) else none

/-- A referent within the context does not properly extend it: the two heights exclude each
other. -/
theorem not_domain_of_neutral {C : Set E} {x : E} (h : Neutral C x) : ¬ Domain C x :=
  λ h' => h'.2 h

/-- When the context is the parts of its sum `c`, the neutral presupposition is parthood of
`c` and the marked one is proper extension of `c`. -/
theorem neutral_iff {c x : E} : Neutral (Set.Iic c) x ↔ x ≤ c := Set.Iic_subset_Iic

theorem domain_iff {c x : E} : Domain (Set.Iic c) x ↔ c < x := Set.Iic_ssubset_Iic

/-- (48): under the convention (45) that vertical order maps marked loci to proper parts, the
marked presupposition met at one locus is met at every higher one. -/
theorem domain_of_lt {H : Type*} [Preorder H] {ref : H → E} (hconv : StrictMono ref)
    {C : Set E} {k k' : H} (hk : Domain C (ref k)) (hkk' : k < k') : Domain C (ref k') :=
  hk.trans (Set.Iic_ssubset_Iic.2 (hconv hkk'))

/-- (14): the remainder of a plane less an established locus sums with it to the plane, and a
higher plane's remainder contains the neutral plane's. -/
theorem remainder {E : Type*} [GeneralizedCoheytingAlgebra E] {a d d' : E} (h : a ≤ d)
    (h' : d ≤ d') : a ⊔ d \ a = d ∧ d \ a ≤ d' \ a :=
  ⟨sup_sdiff_cancel_right h, sdiff_le_sdiff_right h'⟩

/-! ### Partitive composition -/

/-- (50b) `⟦of⟧ = λx λy. y ≤ x` ([ladusaw-1982]): the parts of the pronoun's referent. -/
def partitive (x : E) : E → Prop := (· ≤ x)

/-- (50e), (51e) `FS(ALL)` composed with a partitive pronoun, over worlds `W`: defined where
the pronoun is, and asserting that every part of its referent satisfies the scope. -/
def fsAllOf {W : Type*} (pron : W → Option E) (Q : E → W → Prop) : PartialProp W :=
  PartialProp.presupOfReferent pron λ x w => every_sem (partitive x) (Q · w)

/-- The quantifier presupposes what its pronoun presupposes: `FS(ALL)-of-[ixᵢ-arc-h]` is
defined iff `g i` is a non-atomic plural meeting the height presupposition. -/
theorem fsAllOf_ixArc_presup {W ι : Type*} {g : ι → E} {C : Set E} {h : Height} {i : ι}
    {Q : E → W → Prop} {w : W} :
    (fsAllOf (λ _ => ixArc g C h i) Q).presup w ↔ Arc (g i) ∧ h.presup C (g i) := by
  simp only [fsAllOf, PartialProp.presupOfReferent_presup, ixArc]
  split_ifs with hp <;> simp [hp]

/-- (50e): where the neutral pronoun denotes the sum of the context, `FS(ALL)-neutral`
quantifies over the context. -/
theorem fsAllOf_assertion {W : Type*} {pron : W → Option E} {Q : E → W → Prop} {w : W} {c : E}
    (h : pron w = some c) : (fsAllOf pron Q).assertion w = ∀ y ∈ Set.Iic c, Q y w :=
  PartialProp.presupOfReferent_assertion_some pron _ w c h

/-- §4: with the marked pronoun denoting a plural containing the neutral one, `FS(ALL)` and
`NONE` at the higher locus entail their neutral forms, while `SOMEONE` at the neutral locus
entails its high form. -/
theorem all_of_le {x x' : E} (h : x ≤ x') (Q : E → Prop) :
    every_sem (partitive x') Q → every_sem (partitive x) Q :=
  every_restrictor_down _ _ Q λ _ hy => le_trans hy h

theorem no_of_le {x x' : E} (h : x ≤ x') (Q : E → Prop) :
    no_sem (partitive x') Q → no_sem (partitive x) Q :=
  no_restrictor_down _ _ Q λ _ hy => le_trans hy h

theorem some_of_le {x x' : E} (h : x ≤ x') (Q : E → Prop) :
    some_sem (partitive x) Q → some_sem (partitive x') Q :=
  some_restrictor_up _ _ Q λ _ hy => le_trans hy h

/-- Height is not intensification (§4, after (36)): a part of the wider plural outside the
narrower one makes `SOMEONE-high` true where `SOMEONE-neutral` is false, so on no reading of
height as strengthening, on which the high form would entail the neutral one as
[bergen-2016] has for stressed quantifiers, does the existential come out right. -/
theorem not_strengthening {x x' w : E} (hw : w ≤ x') (hwx : ¬ w ≤ x) :
    ¬ ∀ Q : E → Prop, some_sem (partitive x') Q → some_sem (partitive x) Q :=
  λ h => let ⟨_, hy, e⟩ := h (· = w) ⟨w, hw, rfl⟩; hwx (e ▸ hy)

/-! ### Realising the pronoun in the quantifier -/

/-- The quantifier signs that incorporate the pronoun and carry the height themselves
((32)–(36), (39)). -/
def incorporating : List Quantifier := [fsAll, noneSym, someone, something, one, two]

/-- The quantifier signs whose phonology holds them in place, so that the height-marked
`IX-arc` follows them ((37), (39)). -/
def sequential : List Quantifier := [few, each, most, allB, many]

/-- Each quantifier row realises height as its sign's class predicts. -/
theorem realization_rows :
    ∀ e ∈ Examples.all, ∀ q ∈ ASL.Determiners.all, e.feature? "quantifier" = some q.form →
      (e.feature? "realization" = some "simultaneous" → q ∈ incorporating) ∧
      (e.feature? "realization" = some "sequential" → q ∈ sequential) := by
  decide

/-- (38): a quantifier that incorporates the pronoun rejects a further height-marked
`IX-arc`. -/
theorem no_double_marking :
    ∀ e ∈ Examples.all, e.feature? "realization" = some "both" → e.judgment = .ungrammatical := by
  decide

/-- Height marks a verb itself only in [padden-1988]'s directional class ((21)–(24)); a plain
verb takes a separate `IX-arc`. -/
theorem verb_height_iff_directional :
    ∀ e ∈ Examples.all, e.feature? "heightOn" = some "verb" →
      (e.judgment = .acceptable ↔ e.feature? "verbClass" = some "directional") := by
  decide

/-- (27): height on a bare noun has no widened-domain reading. -/
theorem noun_no_widening :
    ∀ e ∈ Examples.all, e.feature? "heightOn" = some "noun" →
      e.readings.lookup "widened" = some .unacceptable := by
  decide

end DavidsonGagne2022
