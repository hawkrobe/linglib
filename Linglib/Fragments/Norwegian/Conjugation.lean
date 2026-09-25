module

public import Mathlib.Data.List.Basic

/-!
# Norwegian conjugation

This file defines the stem of a Bokmål verb and builds it from the infinitive by the weak
classes of Faarlund, Lie and Vannebo's reference grammar. A stem is the infinitive, the present,
the preterite and the past participle. A weak verb of the first class, the largest and the
productive one, has the preterite and the participle in *-et*, *kaste*, *kastet*, *kastet*, with
*-a* as a rarer written variant. A weak verb of the second class has a preterite in *-te*,
*-de* or *-dde* and a participle in *-t*, *-d* or *-dd*: *-te* after most stems, *reiste*,
*reist*, *-de* after a stem in a voiced *-d*, *-g* or *-v* or in the diphthongs *-ei* and *-øy*,
*levde*, *levd*, and *-dde* after a stem in a single vowel, *rodde*, *rodd*; a double consonant
at the end of the stem is written single before these endings, *kjenne*, *kjente*, *bygge*,
*bygde*. The present adds *-er* to the stem, or *-r* to a stem in a stressed vowel. A strong
verb, or a weak verb with a vowel change such as *sette*, *satte*, *satt*, gives its principal
parts.

## Main definitions

* `Norwegian.Conjugation.Stem`: the infinitive, present, preterite and past participle.
* `Norwegian.Conjugation.weak1`, `weak2a`, `weak2b`, `weak2c`: the stem of a weak verb of each
  class, from its infinitive.
* `Norwegian.Conjugation.principalParts`: the stem of a verb given by its four forms.

## References

* [faarlund-lie-vannebo-1997]
-/

@[expose] public section

namespace Norwegian.Conjugation

/-- The stem of a verb is its infinitive, its present, its preterite and its past participle. -/
structure Stem where
  /-- The infinitive. -/
  infinitive : String
  /-- The present. -/
  present : String
  /-- The preterite. -/
  preterite : String
  /-- The past participle. -/
  participle : String
  deriving DecidableEq, Repr

/-- `root inf` is the root of the infinitive `inf`, the infinitive less a final *-e*. -/
def root (inf : String) : String :=
  match inf.toList.reverse with
  | 'e' :: r => String.ofList r.reverse
  | _ => inf

/-- `dentalStem inf` is the root of `inf` with a final double consonant written single, the
stem the dental endings of the second class attach to, *kjenn* to *kjen*. -/
def dentalStem (inf : String) : String :=
  match (root inf).toList.reverse with
  | c :: c' :: r => if c = c' then String.ofList (c :: r).reverse else root inf
  | _ => root inf

/-- `weak1 inf` is the stem of a weak verb of the first class, with *-er*, *-et* and *-et* on
the root, as *kaste*, *kaster*, *kastet*, *kastet*. -/
def weak1 (inf : String) : Stem :=
  { infinitive := inf, present := root inf ++ "er", preterite := root inf ++ "et",
    participle := root inf ++ "et" }

/-- `weak2a inf` is the stem of a weak verb of the second class with the preterite in *-te*
and the participle in *-t*, as *reise*, *reiser*, *reiste*, *reist*. -/
def weak2a (inf : String) : Stem :=
  { infinitive := inf, present := root inf ++ "er", preterite := dentalStem inf ++ "te",
    participle := dentalStem inf ++ "t" }

/-- `weak2b inf` is the stem of a weak verb of the second class with the preterite in *-de*
and the participle in *-d*, as *leve*, *lever*, *levde*, *levd*. -/
def weak2b (inf : String) : Stem :=
  { infinitive := inf, present := root inf ++ "er", preterite := dentalStem inf ++ "de",
    participle := dentalStem inf ++ "d" }

/-- `weak2c inf` is the stem of a weak verb of the second class whose stem ends in a single
stressed vowel, with *-r*, *-dde* and *-dd* on the infinitive, as *ro*, *ror*, *rodde*,
*rodd*. -/
def weak2c (inf : String) : Stem :=
  { infinitive := inf, present := inf ++ "r", preterite := inf ++ "dde",
    participle := inf ++ "dd" }

/-- `principalParts inf pres pret pp` is the stem of a verb given by its four forms, a strong
verb or a weak verb with a vowel change. -/
def principalParts (inf pres pret pp : String) : Stem :=
  { infinitive := inf, present := pres, preterite := pret, participle := pp }

/-- The verbs of the first class have the same form in the preterite and the participle. -/
theorem weak1_preterite_eq_participle (inf : String) :
    (weak1 inf).preterite = (weak1 inf).participle := rfl

/-- The double consonant is written single before the dental endings, *kjenne*, *kjente*,
*kjent* and *bygge*, *bygde*, *bygd*. -/
theorem weak2_double_consonant :
    (weak2a "kjenne").preterite = "kjente" ∧ (weak2a "kjenne").participle = "kjent" ∧
      (weak2b "bygge").preterite = "bygde" ∧ (weak2b "bygge").participle = "bygd" := by
  decide

end Norwegian.Conjugation
