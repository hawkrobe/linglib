import Linglib.Semantics.Degree.Gradability.Basic

/-! # Adjectival Predicate Lexicon Fragment

Gradable adjective entries following [kennedy-2007], typed with
`Degree.GradableAdjective` (the syntactic `Syntax/Adjective` lexeme
refined with the degree-semantic layer). Each entry stores its surface form, scalar
`dimension`, lexicalized pole (`isLowerEndpoint`) or `standardOverride`, and antonym
data; the scale shape (`scaleType`), positive `standard`, and Kennedy `adjectiveClass`
are *derived* views, not stored — the fix for the old `scaleType` field that conflated
scale shape with pole (`wet`/`dry` share one closed `.wetness` scale). The derived
Kennedy classification is exercised at the end of this file.
-/

namespace English.Predicates.Adjectival

open Degree (AntonymRelation GradableAdjective)
open Core.Order (Boundedness)
open Features (EvaluativeValence)
open Features (NegationType)


/-- [kennedy-2007]
An adjectival predicate entry.

This is an alias for `GradableAdjective` from the Theory module, re-exported
here for the Fragments organization.
-/
abbrev AdjectivalPredicateEntry := GradableAdjective


/-- "tall" — open scale, contrary to "short" -/
def tall : AdjectivalPredicateEntry where
  form := "tall"
  dimension := some .height
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "short" — open scale, contrary to "tall" -/
def short : AdjectivalPredicateEntry where
  form := "short"
  dimension := some .height
  antonymForm := some "tall"
  antonymRelation := some .contrary


/--
"happy" — open scale, contrary to "unhappy"

Note: This is the 1-place adjectival predicate "x is happy".
For the 2-place attitude predicate "x is happy that p", see
`Semantics/Attitudes/Preferential.lean`.
-/
def happy : AdjectivalPredicateEntry where
  form := "happy"
  dimension := some .happiness
  antonymForm := some "unhappy"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "unhappy" — open scale, contrary to "happy" -/
def unhappy : AdjectivalPredicateEntry where
  form := "unhappy"
  dimension := some .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "sad" — open scale, contrary to "happy" (near-synonym of unhappy) -/
def sad : AdjectivalPredicateEntry where
  form := "sad"
  dimension := some .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary
  evaluativeValence := some .negative


/-- "full" — closed scale, contradictory to "empty" -/
def full : AdjectivalPredicateEntry where
  form := "full"
  dimension := some .fullness
  antonymForm := some "empty"
  antonymRelation := some .contradictory  -- Closed scales often contradictory

/-- "empty" — closed fullness scale, lower pole ⇒ minimum standard,
    contradictory to "full". -/
def empty : AdjectivalPredicateEntry where
  form := "empty"
  dimension := some .fullness
  isLowerEndpoint := true
  antonymForm := some "full"
  antonymRelation := some .contradictory


/-- "hot" — open scale, contrary to "cold" -/
def hot : AdjectivalPredicateEntry where
  form := "hot"
  dimension := some .temperature
  antonymForm := some "cold"
  antonymRelation := some .contrary

/-- "cold" — open scale, contrary to "hot" -/
def cold : AdjectivalPredicateEntry where
  form := "cold"
  dimension := some .temperature
  antonymForm := some "hot"
  antonymRelation := some .contrary


/-- "expensive" — open scale, contrary to "cheap" -/
def expensive : AdjectivalPredicateEntry where
  form := "expensive"
  dimension := some .cost
  antonymForm := some "cheap"
  antonymRelation := some .contrary

/-- "cheap" — open scale, contrary to "expensive" -/
def cheap : AdjectivalPredicateEntry where
  form := "cheap"
  dimension := some .cost
  antonymForm := some "expensive"
  antonymRelation := some .contrary

/-- "wet" — closed wetness scale, lower pole ⇒ minimum standard (true with any
    non-zero wetness). Shares the closed `.wetness` scale with "dry"; the two
    differ only in pole. -/
def wet : AdjectivalPredicateEntry where
  form := "wet"
  dimension := some .wetness
  isLowerEndpoint := true
  antonymForm := some "dry"
  antonymRelation := some .contradictory

/-- "dry" — closed wetness scale, upper pole ⇒ maximum standard (true only at
    complete dryness). -/
def dry : AdjectivalPredicateEntry where
  form := "dry"
  dimension := some .wetness
  antonymForm := some "wet"
  antonymRelation := some .contradictory


/-- "clean" — closed scale (maximally clean), contradictory to "dirty" -/
def clean : AdjectivalPredicateEntry where
  form := "clean"
  dimension := some .cleanliness
  antonymForm := some "dirty"
  antonymRelation := some .contradictory

/-- "dirty" — closed scale (maximally dirty), contradictory to "clean" -/
def dirty : AdjectivalPredicateEntry where
  form := "dirty"
  dimension := some .cleanliness
  antonymForm := some "clean"
  antonymRelation := some .contradictory
  evaluativeValence := some .negative

/-- "straight" — closed scale (maximally straight), contradictory to "bent" -/
def straight : AdjectivalPredicateEntry where
  form := "straight"
  dimension := some .straightness
  antonymForm := some "bent"
  antonymRelation := some .contradictory

/-- "flat" — closed scale (maximally flat), contradictory to "bumpy" -/
def flat : AdjectivalPredicateEntry where
  form := "flat"
  dimension := some .flatness
  antonymForm := some "bumpy"
  antonymRelation := some .contradictory
  spatialConfigType := some .surfaceOrient

/-- "open" — closed scale (maximally open), contradictory to "closed" -/
def open_ : AdjectivalPredicateEntry where
  form := "open"
  dimension := some .openness
  antonymForm := some "closed"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "closed" — closed scale, contradictory to "open" -/
def closed_ : AdjectivalPredicateEntry where
  form := "closed"
  dimension := some .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "shut" — closed scale, contradictory to "open" (near-synonym of "closed") -/
def shut : AdjectivalPredicateEntry where
  form := "shut"
  dimension := some .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "free" — closed scale (maximally free = unattached), contradictory to "stuck" -/
def free_ : AdjectivalPredicateEntry where
  form := "free"
  dimension := some .freedom
  antonymForm := some "stuck"
  antonymRelation := some .contradictory
  spatialConfigType := some .unattachment

/-- "loose" — closed scale (maximally loose), contradictory to "tight" -/
def loose : AdjectivalPredicateEntry where
  form := "loose"
  dimension := some .tightness
  antonymForm := some "tight"
  antonymRelation := some .contradictory
  spatialConfigType := some .unattachment

/-- "tight" — closed scale (maximally tight), contradictory to "loose" -/
def tight : AdjectivalPredicateEntry where
  form := "tight"
  dimension := some .tightness
  antonymForm := some "loose"
  antonymRelation := some .contradictory

/-- "bent" — closed straightness scale, lower pole ⇒ minimum standard (true with
    any non-zero bend). Shares the closed `.straightness` scale with "straight". -/
def bent : AdjectivalPredicateEntry where
  form := "bent"
  dimension := some .straightness
  isLowerEndpoint := true
  antonymForm := some "straight"
  antonymRelation := some .contradictory

/-- "smooth" — closed scale, contradictory to "rough" -/
def smooth : AdjectivalPredicateEntry where
  form := "smooth"
  dimension := some .smoothness
  antonymForm := some "rough"
  antonymRelation := some .contradictory

/-- "rough" — closed scale, contradictory to "smooth" -/
def rough : AdjectivalPredicateEntry where
  form := "rough"
  dimension := some .smoothness
  antonymForm := some "smooth"
  antonymRelation := some .contradictory

/-- "hard" — open scale, contrary to "soft" -/
def hard : AdjectivalPredicateEntry where
  form := "hard"
  dimension := some .hardness
  antonymForm := some "soft"
  antonymRelation := some .contrary

/-- "soft" — open scale, contrary to "hard" -/
def soft : AdjectivalPredicateEntry where
  form := "soft"
  dimension := some .hardness
  antonymForm := some "hard"
  antonymRelation := some .contrary

/-- "pure" — closed scale (maximally pure), contradictory to "impure" -/
def pure_ : AdjectivalPredicateEntry where
  form := "pure"
  dimension := some .purity
  antonymForm := some "impure"
  antonymRelation := some .contradictory

/-- "dead" — closed scale (absolute: maximal endpoint), contradictory to "alive" -/
def dead : AdjectivalPredicateEntry where
  form := "dead"
  dimension := some .alive
  antonymForm := some "alive"
  antonymRelation := some .contradictory

/-- "alive" — closed scale (absolute), contradictory to "dead" -/
def alive : AdjectivalPredicateEntry where
  form := "alive"
  dimension := some .alive
  antonymForm := some "dead"
  antonymRelation := some .contradictory

/-- "large" — open scale, contrary to "small" -/
def large : AdjectivalPredicateEntry where
  form := "large"
  dimension := some .generalSize
  antonymForm := some "small"
  antonymRelation := some .contrary

/-- "small" — open scale, contrary to "large" -/
def small : AdjectivalPredicateEntry where
  form := "small"
  dimension := some .generalSize
  antonymForm := some "large"
  antonymRelation := some .contrary

/-- "gigantic" — open scale, contrary to "tiny", informationally stronger than "large" -/
def gigantic : AdjectivalPredicateEntry where
  form := "gigantic"
  dimension := some .generalSize
  antonymForm := some "tiny"
  antonymRelation := some .contrary

/-- "tiny" — open scale, contrary to "gigantic", informationally stronger than "small" -/
def tiny : AdjectivalPredicateEntry where
  form := "tiny"
  dimension := some .generalSize
  antonymForm := some "gigantic"
  antonymRelation := some .contrary

/-- "pristine" — closed scale, contrary to "filthy" (extreme absolute: gap exists) -/
def pristine : AdjectivalPredicateEntry where
  form := "pristine"
  dimension := some .cleanliness
  antonymForm := some "filthy"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "filthy" — closed scale, contrary to "pristine" (extreme absolute: gap exists) -/
def filthy : AdjectivalPredicateEntry where
  form := "filthy"
  dimension := some .cleanliness
  antonymForm := some "pristine"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "long" — open scale, contrary to "short" (length dimension) -/
def long : AdjectivalPredicateEntry where
  form := "long"
  dimension := some .length
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "wide" — open scale, contrary to "narrow" -/
def wide : AdjectivalPredicateEntry where
  form := "wide"
  dimension := some .width
  antonymForm := some "narrow"
  antonymRelation := some .contrary

/-- "cool" — open scale, contrary to "warm" -/
def cool : AdjectivalPredicateEntry where
  form := "cool"
  dimension := some .temperature
  antonymForm := some "warm"
  antonymRelation := some .contrary

/-- "warm" — open scale, contrary to "cool" -/
def warm : AdjectivalPredicateEntry where
  form := "warm"
  dimension := some .temperature
  antonymForm := some "cool"
  antonymRelation := some .contrary

/-! ## Physical dimension adjectives -/

/-- "heavy" — open scale, contrary to "light" -/
def heavy : AdjectivalPredicateEntry where
  form := "heavy"
  dimension := some .weight
  antonymForm := some "light"
  antonymRelation := some .contrary

/-- "light" — open scale, contrary to "heavy" -/
def light : AdjectivalPredicateEntry where
  form := "light"
  dimension := some .weight
  antonymForm := some "heavy"
  antonymRelation := some .contrary

/-- "thick" — open scale, contrary to "thin" -/
def thick : AdjectivalPredicateEntry where
  form := "thick"
  dimension := some .thickness
  antonymForm := some "thin"
  antonymRelation := some .contrary

/-- "thin" — open scale, contrary to "thick" -/
def thin : AdjectivalPredicateEntry where
  form := "thin"
  dimension := some .thickness
  antonymForm := some "thick"
  antonymRelation := some .contrary

/-- "deep" — open scale, contrary to "shallow" -/
def deep : AdjectivalPredicateEntry where
  form := "deep"
  dimension := some .depth
  antonymForm := some "shallow"
  antonymRelation := some .contrary

/-- "shallow" — open scale, contrary to "deep" -/
def shallow : AdjectivalPredicateEntry where
  form := "shallow"
  dimension := some .depth
  antonymForm := some "deep"
  antonymRelation := some .contrary

/-- "strong" — open scale, contrary to "weak" -/
def strong : AdjectivalPredicateEntry where
  form := "strong"
  dimension := some .strength
  antonymForm := some "weak"
  antonymRelation := some .contrary

/-- "weak" — open scale, contrary to "strong" -/
def weak : AdjectivalPredicateEntry where
  form := "weak"
  dimension := some .strength
  antonymForm := some "strong"
  antonymRelation := some .contrary

/-- "fast" — open scale, contrary to "slow" -/
def fast : AdjectivalPredicateEntry where
  form := "fast"
  dimension := some .speed
  antonymForm := some "slow"
  antonymRelation := some .contrary

/-- "slow" — open scale, contrary to "fast" -/
def slow : AdjectivalPredicateEntry where
  form := "slow"
  dimension := some .speed
  antonymForm := some "fast"
  antonymRelation := some .contrary

/-- "old" — open scale, contrary to "young" -/
def old : AdjectivalPredicateEntry where
  form := "old"
  dimension := some .age
  antonymForm := some "young"
  antonymRelation := some .contrary

/-- "young" — open scale, contrary to "old" -/
def young : AdjectivalPredicateEntry where
  form := "young"
  dimension := some .age
  antonymForm := some "old"
  antonymRelation := some .contrary

/-! ## Sensory adjectives -/

/-- "bright" — open scale, contrary to "dark" -/
def bright : AdjectivalPredicateEntry where
  form := "bright"
  dimension := some .brightness
  antonymForm := some "dark"
  antonymRelation := some .contrary

/-- "dark" — open scale, contrary to "bright" -/
def dark : AdjectivalPredicateEntry where
  form := "dark"
  dimension := some .brightness
  antonymForm := some "bright"
  antonymRelation := some .contrary

/-- "loud" — open scale, contrary to "quiet" -/
def loud : AdjectivalPredicateEntry where
  form := "loud"
  dimension := some .volume
  antonymForm := some "quiet"
  antonymRelation := some .contrary

/-- "quiet" — open scale, contrary to "loud" -/
def quiet : AdjectivalPredicateEntry where
  form := "quiet"
  dimension := some .volume
  antonymForm := some "loud"
  antonymRelation := some .contrary

/-! ## Evaluative adjectives -/

/-- "good" — open value scale, contrary to "bad". "good" takes a contextual
    standard and patterns with relative adjectives ([beltrama-2025] §3); on the
    open `.value` scale this class is *derived* (open ⇒ contextual) rather than
    stipulated, so no `standardOverride` is needed. -/
def good : AdjectivalPredicateEntry where
  form := "good"
  dimension := some .value
  antonymForm := some "bad"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "bad" — value scale, contrary to "good" -/
def bad : AdjectivalPredicateEntry where
  form := "bad"
  dimension := some .value
  antonymForm := some "good"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "beautiful" — open scale, contrary to "ugly" -/
def beautiful : AdjectivalPredicateEntry where
  form := "beautiful"
  dimension := some .beauty
  antonymForm := some "ugly"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "ugly" — open scale, contrary to "beautiful" -/
def ugly : AdjectivalPredicateEntry where
  form := "ugly"
  dimension := some .beauty
  antonymForm := some "beautiful"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "important" — open scale -/
def important : AdjectivalPredicateEntry where
  form := "important"
  dimension := some .importance

/-- "safe" — open scale, contrary to "dangerous" -/
def safe : AdjectivalPredicateEntry where
  form := "safe"
  dimension := some .safety
  antonymForm := some "dangerous"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "dangerous" — open scale, contrary to "safe" -/
def dangerous : AdjectivalPredicateEntry where
  form := "dangerous"
  dimension := some .danger
  antonymForm := some "safe"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-! ## Physical disturbance deverbal adjectives

[tham-2025]: physical disturbance predicates are associated with a totally
closed, multi-point scale. Lower bound = physical instantiation of disturbance;
upper bound = spatial extent of host entity. Gradable (*more cracked*, *badly
dented*), compatible with *completely* and *partially*. Contra
[rappaport-hovav-2014] (two-point) and [rotstein-winter-2004]
(lower-bounded only). -/

/-- "cracked" — closed scale, contradictory to "uncracked".
    Deverbal adjective from *crack* (Levin 45.1 Break verbs).
    NOT a two-point scale: accepts *more cracked*, *completely cracked*,
    *partially cracked*, *badly cracked* ([tham-2025] §2.3–2.4). -/
def cracked : AdjectivalPredicateEntry where
  form := "cracked"
  dimension := some .cracking

/-- "dented" — closed scale.
    Deverbal adjective from *dent*. Accepts *more dented*, *completely dented*,
    *badly dented* ([tham-2025] (11a), (20b)). -/
def dented : AdjectivalPredicateEntry where
  form := "dented"
  dimension := some .denting

/-- "scratched" — closed scale.
    Deverbal adjective from *scratch*. Accepts *more scratched*, *completely
    scratched*, *badly scratched* ([tham-2025] (11b), (20c)). -/
def scratched : AdjectivalPredicateEntry where
  form := "scratched"
  dimension := some .scratching

/-- "shattered" — closed scale, NON-GRADABLE.
    Deverbal adjective from *shatter* (Levin 45.1 Break verbs).
    Contrast: ??*more shattered*, punctual verb, no durative reading.
    Not a physical disturbance predicate ([tham-2025] (12c)). -/
def shattered : AdjectivalPredicateEntry where
  form := "shattered"
  dimension := some .shattering

/-! ## Mildly positive adjectives (MPAs)

[beltrama-2025]: MPAs encode a necessity standard — the minimum value
required for pursuit. They share properties with both relative (context-sensitive,
gradable) and absolute (no zone of indifference, crisp judgments, *barely*
compatible) predicates. -/

/-- "nice" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *nicely*. -/
def nice : AdjectivalPredicateEntry where
  form := "nice"
  dimension := some .value
  evaluativeValence := some .positive

/-- "pleasant" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *pleasantly*. -/
def pleasant : AdjectivalPredicateEntry where
  form := "pleasant"
  dimension := some .value
  antonymForm := some "unpleasant"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "decent" — a mildly-positive adjective: open `.value` scale with a functional
    (necessity) standard ([beltrama-2025]), recorded via `standardOverride`. -/
def decent : AdjectivalPredicateEntry where
  form := "decent"
  dimension := some .value
  standardOverride := some .functional
  evaluativeValence := some .positive

/-- "acceptable" — mildly-positive adjective; open `.value` scale, functional
    standard ([beltrama-2025]). Deverbal *-able* form: the modal suffix
    contributes the functional standard. -/
def acceptable : AdjectivalPredicateEntry where
  form := "acceptable"
  dimension := some .value
  standardOverride := some .functional
  evaluativeValence := some .positive

/-- "adequate" — mildly-positive adjective; open `.value` scale, functional
    (necessity) standard ([beltrama-2025]). -/
def adequate : AdjectivalPredicateEntry where
  form := "adequate"
  dimension := some .value
  standardOverride := some .functional
  evaluativeValence := some .positive

/-! ## Deadjectival intensifier bases ([nouwen-2024])

Adjectival bases for deadjectival intensifiers. Evaluative adjectives
(horrible, wonderful) derive H-degree or M-degree intensifiers via the
Goldilocks effect. Mirative (unusual, surprising) and modal (possible,
impossible) bases follow Zwicky's generalization. -/

-- Negative-evaluative bases → H-degree intensifiers

/-- "horrible" — open scale, negative evaluative. Base for H-degree *horribly*. -/
def horrible : AdjectivalPredicateEntry where
  form := "horrible"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "terrible" — open scale, negative evaluative. Base for H-degree *terribly*. -/
def terrible : AdjectivalPredicateEntry where
  form := "terrible"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "awful" — open scale, negative evaluative. Base for H-degree *awfully*. -/
def awful : AdjectivalPredicateEntry where
  form := "awful"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "dreadful" — open scale, negative evaluative. Base for H-degree *dreadfully*. -/
def dreadful : AdjectivalPredicateEntry where
  form := "dreadful"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "frightening" — open scale, negative evaluative. Base for H-degree *frighteningly*. -/
def frightening : AdjectivalPredicateEntry where
  form := "frightening"
  dimension := some .danger
  evaluativeValence := some .negative

/-- "disgusting" — open scale, negative evaluative. Base for H-degree *disgustingly*. -/
def disgusting : AdjectivalPredicateEntry where
  form := "disgusting"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "annoying" — open scale, negative evaluative. Base for H-degree *annoyingly*. -/
def annoying : AdjectivalPredicateEntry where
  form := "annoying"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "unpleasant" — open scale, negative evaluative, contrary to "pleasant". -/
def unpleasant : AdjectivalPredicateEntry where
  form := "unpleasant"
  dimension := some .value
  antonymForm := some "pleasant"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "scary" — open scale, negative evaluative. Base for H-degree *scarily*. -/
def scary : AdjectivalPredicateEntry where
  form := "scary"
  dimension := some .danger
  evaluativeValence := some .negative

-- Positive-evaluative bases → M-degree intensifiers

/-- "wonderful" — open scale, positive evaluative. Base for M-degree *wonderfully*. -/
def wonderful : AdjectivalPredicateEntry where
  form := "wonderful"
  dimension := some .quality
  evaluativeValence := some .positive

/-- "delightful" — open scale, positive evaluative. Base for M-degree *delightfully*. -/
def delightful : AdjectivalPredicateEntry where
  form := "delightful"
  dimension := some .quality
  evaluativeValence := some .positive

/-- "gorgeous" — open scale, positive evaluative. Base for M-degree *gorgeously*. -/
def gorgeous : AdjectivalPredicateEntry where
  form := "gorgeous"
  dimension := some .beauty
  evaluativeValence := some .positive

-- Mirative bases → H-degree intensifiers (not evaluative; §2.4.2)

/-- "unusual" — open scale, neutral (mirative), contrary to "usual". -/
def unusual : AdjectivalPredicateEntry where
  form := "unusual"
  dimension := some .expectation
  antonymForm := some "usual"
  antonymRelation := some .contrary
  evaluativeValence := some .neutral

/-- "surprising" — open scale, neutral (mirative). Base for H-degree *surprisingly*. -/
def surprising : AdjectivalPredicateEntry where
  form := "surprising"
  dimension := some .expectation
  evaluativeValence := some .neutral

/-- "remarkable" — open scale, positive evaluative (§2.4.1). Extreme positive
    evaluation: H-degree *remarkably* despite positive valence (Goldilocks exception). -/
def remarkable : AdjectivalPredicateEntry where
  form := "remarkable"
  dimension := some .quality
  evaluativeValence := some .positive

/-- "stunning" — open scale, positive evaluative (Figure 2, upper-right quadrant).
    Extreme positive evaluation: H-degree *stunningly* (Goldilocks exception). -/
def stunning : AdjectivalPredicateEntry where
  form := "stunning"
  dimension := some .quality
  evaluativeValence := some .positive

-- Modal bases (Zwicky's generalization)

/-- "usual" — open scale, neutral (modal), contrary to "unusual". -/
def usual : AdjectivalPredicateEntry where
  form := "usual"
  dimension := some .expectation
  antonymForm := some "unusual"
  antonymRelation := some .contrary
  evaluativeValence := some .neutral

/-- "expected" — open scale, neutral (modal). Unattested as intensifier (*expectedly). -/
def expected : AdjectivalPredicateEntry where
  form := "expected"
  dimension := some .expectation
  evaluativeValence := some .neutral

/-- "possible" — open scale, neutral (modal), contradictory to "impossible". -/
def possible : AdjectivalPredicateEntry where
  form := "possible"
  dimension := some .possibility
  antonymForm := some "impossible"
  antonymRelation := some .contradictory
  evaluativeValence := some .neutral

/-- "impossible" — open scale, neutral (modal), contradictory to "possible". -/
def impossible : AdjectivalPredicateEntry where
  form := "impossible"
  dimension := some .possibility
  antonymForm := some "possible"
  antonymRelation := some .contradictory
  evaluativeValence := some .neutral

/-- All adjectival predicate entries -/
def allEntries : List (AdjectivalPredicateEntry) := [
  -- Height / size
  tall, short, large, small, gigantic, tiny,
  -- Happiness / evaluative
  happy, unhappy, sad,
  -- Fullness
  full, empty,
  -- Temperature
  hot, cold, cool, warm,
  -- Cost
  expensive, cheap,
  -- Wetness
  wet, dry,
  -- State: cleanliness, shape, surface
  clean, dirty, straight, bent, flat, smooth, rough,
  -- State: openness / barrier
  open_, closed_, shut,
  -- State: attachment / fit
  free_, loose, tight,
  -- State: hardness, purity, alive
  hard, soft, pure_, dead, alive,
  -- State: physical disturbance ([tham-2025])
  cracked, dented, scratched, shattered,
  -- Informationally strong
  pristine, filthy,
  -- Physical dimensions
  long, wide, heavy, light, thick, thin, deep, shallow,
  strong, weak, fast, slow, old, young,
  -- Sensory
  bright, dark, loud, quiet,
  -- Evaluative
  good, bad, beautiful, ugly, important, safe, dangerous, nice, pleasant,
  -- Mildly positive adjectives ([beltrama-2025])
  decent, acceptable, adequate,
  -- Intensifier bases: negative-evaluative ([nouwen-2024])
  horrible, terrible, awful, dreadful, frightening,
  disgusting, annoying, unpleasant, scary,
  -- Intensifier bases: positive-evaluative
  wonderful, delightful, gorgeous,
  -- Intensifier bases: mirative
  unusual, surprising, remarkable, stunning,
  -- Intensifier bases: modal
  usual, expected, possible, impossible
]

/-- Look up an entry by form -/
def lookup (form : String) : Option (AdjectivalPredicateEntry) :=
  allEntries.find? (·.form == form)

/-! ### Derived Kennedy classification

The scale shape, positive standard, and Kennedy class are `GradableAdjective`
views derived from each entry's `dimension` + pole/override — nothing here is a
stored field ([kennedy-2007], [kennedy-mcnally-2005]). Everything closes by
`rfl`/`decide`, so the migration off the old stored `scaleType` is checked. -/

-- scale *shape* is the dimension's; `wet`/`dry` no longer disagree on it:
theorem tall_open : tall.scaleType = .open_ := rfl
theorem wet_closed : wet.scaleType = .closed := rfl
theorem dry_closed : dry.scaleType = .closed := rfl

-- the pole the old `scaleType` conflated, now recovered from `isLowerEndpoint`:
theorem wet_min : wet.standard = .minEndpoint := rfl
theorem dry_max : dry.standard = .maxEndpoint := rfl

-- every Kennedy class, derived from (dimension, pole, override):
theorem tall_relative     : tall.adjectiveClass = .relativeGradable := rfl
theorem good_relative     : good.adjectiveClass = .relativeGradable := rfl
theorem full_absMax       : full.adjectiveClass = .absoluteMaximum := rfl
theorem straight_absMax   : straight.adjectiveClass = .absoluteMaximum := rfl
theorem dry_absMax        : dry.adjectiveClass = .absoluteMaximum := rfl
theorem empty_absMin      : empty.adjectiveClass = .absoluteMinimum := rfl
theorem wet_absMin        : wet.adjectiveClass = .absoluteMinimum := rfl
theorem bent_absMin       : bent.adjectiveClass = .absoluteMinimum := rfl
theorem decent_mildlyPos  : decent.adjectiveClass = .mildlyPositive := rfl
theorem acceptable_mildlyPos : acceptable.adjectiveClass = .mildlyPositive := rfl
theorem adequate_mildlyPos   : adequate.adjectiveClass = .mildlyPositive := rfl

-- comparison-class dependence: only the open-scale relatives require one:
theorem tall_requires_cc  : tall.IsRelative := by decide
theorem good_requires_cc  : good.IsRelative := by decide
theorem wet_no_cc         : ¬ wet.IsRelative := by decide
theorem full_no_cc        : ¬ full.IsRelative := by decide
theorem decent_no_cc      : ¬ decent.IsRelative := by decide

/-- Every entry above carries a scalar dimension, so all are gradable. -/
theorem all_gradable :
    tall.IsGradable ∧ full.IsGradable ∧ wet.IsGradable ∧ good.IsGradable ∧
      decent.IsGradable := by decide

end English.Predicates.Adjectival
