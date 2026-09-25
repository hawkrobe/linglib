module

public import Linglib.Syntax.Agreement.Controller
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Data.List.Sort

/-!
# Bybee's relevance hierarchy

[bybee-1985]'s comparative inventory of verbal inflectional categories,
ordered by semantic relevance to the stem, and the stem-outward
sortedness this order induces on affix sequences.

`MorphCategory` is a comparative concept, not a universal slot inventory: languages own their
slot types (`AffixTemplate Slot`, `Mayan.VerbSlot`, `Japanese.Verb.Slot`), and a
cross-linguistic relevance claim pulls the order back along a `Slot → MorphCategory` hom
supplied by the study that draws the comparison. The order is `Preorder.lift peripherality`
and a sequence respects the hierarchy when it is `List.SortedLE`.

## Main definitions

* `MorphCategory`: Bybee's comparative inventory, with the relevance `Preorder`.
* `MorphCategory.peripherality`: the rank realizing the order, `MorphCategory.le_iff`.

## References

* [J. Bybee, *Morphology: A Study of the Relation between Meaning and Form* (1985)][bybee-1985]
* [G. D. S. Anderson, *Auxiliary Verb Constructions* (2006)][anderson-2006a]
* [J. H. Greenberg, *Some Universals of Grammar with Particular Reference to the Order of
  Meaningful Elements* (1963)][greenberg-1963]
* [M. Miestamo, *Standard Negation: The Negation of Declarative Verbal Main Clauses in a
  Typological Perspective* (2005)][miestamo-2005]
* [L. Stassen, *Comparative Constructions* (2013)][stassen-2013]
-/

@[expose] public section

namespace Morphology

/-- Morpheme functional category: [bybee-1985]'s comparative inventory
(plus documented linglib extensions — see `peripherality`).

Categories are ordered by semantic relevance to the verb stem:
more relevant categories appear closer to the stem in suffixal
morphology. A comparative concept: language-particular slot systems
relate to it by fragment-supplied homs, not by instantiation. -/
inductive MorphCategory where
  | stem
  | derivation    -- derives verbs from other categories (e.g., *suru*)
  | valence       -- causative, applicative, reciprocal
  | voice         -- passive, potential
  | aspect        -- perfective, imperfective
  | tense         -- past, future, present
  | mood          -- desiderative, subjunctive, imperative
  | negation      -- negation markers
  /-- Agreement morphology, parameterized by the grammatical role of
      the controlling NP (`Agreement.Controller`). The role
      distinction (subj vs obj vs poss vs ...) is what allows
      [anderson-2006a]'s split/doubled AVC typology to be Lean-checkable;
      [bybee-1985]'s `personAgr / personAgrObj / genderAgr` source
      distinctions also round-trip cleanly. -/
  | agreement (controller : Agreement.Controller)
  | nonfinite     -- nonfinite markers, interrogative/relative
  | number        -- number marking on nouns (not verb agreement)
  | degree        -- comparative/superlative on adjectives
  deriving Repr, DecidableEq

/-- Peripherality: numerical embedding of Bybee's relevance hierarchy
where **higher = farther from stem = less semantically relevant**.

In Bybee's text, "high relevance" means *more* semantically
integrated with the stem ([bybee-1985] Ch 2 §2.1 p. 13). The
substrate uses the *opposite* numerical direction: stem = 0 (most
relevant), agreement = 8 (least relevant), so that Nat ordering
mirrors stem-outward linear position in suffixing morphology
(Ch 2 §6 iconicity, p. 33). The field name `peripherality` makes
this directionality explicit and avoids the wrong-on-its-face
gloss "high relevance rank means low relevance."

Bybee's own categories (Ch 2 §3) are valence, voice, aspect, tense, mood and agreement. The
others are extensions, with the ranks chosen here:
- `derivation` (rank 1): Bybee Ch 4 argues lex/deriv/infl is a
  *continuum*, not a discrete level on the relevance scale.
- `number` (rank 3): Bybee discusses verbal-number agreement at
  the low end (with person agreement). Noun number is treated
  separately (Ch 2 §6 cites [greenberg-1963] only, "stem < number
  < case" for nouns). Cross-comparison of noun-number rank with
  verb-aspect rank is an artifact of unifying both onto one scale.
- `degree` (rank 5): Bybee never discusses adjectival degree
  morphology. Comparative morphology is often *derivational*
  cross-linguistically ([stassen-2013]).
- `negation` (rank 7): Bybee discusses negation as a kind of mood
  (Part II Ch 8 §5), not a separate level. Rank 7 is plausible
  per [miestamo-2005] cross-linguistic ordering data, but is a
  linglib extension.
- `nonfinite` (rank 9): not on Bybee's hierarchy at all (nonfinite
  morphology often changes syntactic category, outside the scope
  of inflectional categories proper). -/
def MorphCategory.peripherality : MorphCategory → Nat
  | .stem        => 0
  | .derivation  => 1
  | .valence     => 2
  | .number      => 3
  | .voice       => 3
  | .aspect      => 4
  | .degree      => 5
  | .tense       => 5
  | .mood        => 6
  | .negation    => 7
  | .agreement _ => 8  -- any controller role lands at Bybee rank 8
  | .nonfinite   => 9

/-! ### The relevance order

`peripherality` is a rank function; the object the hierarchy is about is the preorder it induces,
`Preorder.lift peripherality`: `a ≤ b` when `a` is at least as stem-relevant as `b`. Only a
preorder, since the rank is not injective (voice and number share one). A slot sequence respects
the hierarchy when it is sorted stem-outward by this order, mathlib's `List.SortedLE`; a
language's slots are compared by pulling the order back along a `Slot → MorphCategory` hom,
sortedness of the image, with the hom carrying the analytical commitments
(`Studies/HahnDegenFutrell2021.lean` for the worked example). -/

instance : Preorder MorphCategory := Preorder.lift MorphCategory.peripherality

instance : DecidableLE MorphCategory :=
  fun a b ↦ inferInstanceAs (Decidable (a.peripherality ≤ b.peripherality))

instance : DecidableLT MorphCategory :=
  fun a b ↦ inferInstanceAs (Decidable (a.peripherality < b.peripherality))

theorem MorphCategory.le_iff {a b : MorphCategory} :
    a ≤ b ↔ a.peripherality ≤ b.peripherality := Iff.rfl

theorem MorphCategory.lt_iff {a b : MorphCategory} :
    a < b ↔ a.peripherality < b.peripherality := Iff.rfl

end Morphology
