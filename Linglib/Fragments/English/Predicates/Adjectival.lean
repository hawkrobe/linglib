import Linglib.Theories.Semantics.Gradability.Theory

/-! # Adjectival Predicate Lexicon Fragment

Gradable adjective entries following @cite{kennedy-2007}. Scale type, dimension, antonyms.
-/

namespace Fragments.English.Predicates.Adjectival

open Semantics.Gradability (AntonymRelation GradableAdjEntry)
open Core.Scale (Boundedness)
open Features (EvaluativeValence)
open Features (NegationType)


/-- @cite{kennedy-2007}
An adjectival predicate entry.

This is an alias for `GradableAdjEntry` from the Theory module, re-exported
here for the Fragments organization.
-/
abbrev AdjectivalPredicateEntry := GradableAdjEntry


/-- "tall" — open scale, contrary to "short" -/
def tall : AdjectivalPredicateEntry where
  form := "tall"
  scaleType := .open_
  dimension := .height
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "short" — open scale, contrary to "tall" -/
def short : AdjectivalPredicateEntry where
  form := "short"
  scaleType := .open_
  dimension := .height
  antonymForm := some "tall"
  antonymRelation := some .contrary


/--
"happy" — open scale, contrary to "unhappy"

Note: This is the 1-place adjectival predicate "x is happy".
For the 2-place attitude predicate "x is happy that p", see
`Theories/Semantics/Attitudes/Preferential.lean`.
-/
def happy : AdjectivalPredicateEntry where
  form := "happy"
  scaleType := .open_
  dimension := .happiness
  antonymForm := some "unhappy"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "unhappy" — open scale, contrary to "happy" -/
def unhappy : AdjectivalPredicateEntry where
  form := "unhappy"
  scaleType := .open_
  dimension := .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "sad" — open scale, contrary to "happy" (near-synonym of unhappy) -/
def sad : AdjectivalPredicateEntry where
  form := "sad"
  scaleType := .open_
  dimension := .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary
  evaluativeValence := some .negative


/-- "full" — closed scale, contradictory to "empty" -/
def full : AdjectivalPredicateEntry where
  form := "full"
  scaleType := .closed
  dimension := .fullness
  antonymForm := some "empty"
  antonymRelation := some .contradictory  -- Closed scales often contradictory

/-- "empty" — closed scale, contradictory to "full" -/
def empty : AdjectivalPredicateEntry where
  form := "empty"
  scaleType := .closed
  dimension := .fullness
  antonymForm := some "full"
  antonymRelation := some .contradictory


/-- "hot" — open scale, contrary to "cold" -/
def hot : AdjectivalPredicateEntry where
  form := "hot"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "cold"
  antonymRelation := some .contrary

/-- "cold" — open scale, contrary to "hot" -/
def cold : AdjectivalPredicateEntry where
  form := "cold"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "hot"
  antonymRelation := some .contrary


/-- "expensive" — open scale, contrary to "cheap" -/
def expensive : AdjectivalPredicateEntry where
  form := "expensive"
  scaleType := .open_
  dimension := .cost
  antonymForm := some "cheap"
  antonymRelation := some .contrary

/-- "cheap" — open scale, contrary to "expensive" -/
def cheap : AdjectivalPredicateEntry where
  form := "cheap"
  scaleType := .open_
  dimension := .cost
  antonymForm := some "expensive"
  antonymRelation := some .contrary

/-- "wet" — lower-closed scale (minimum at 0) -/
def wet : AdjectivalPredicateEntry where
  form := "wet"
  scaleType := .lowerBounded
  dimension := .wetness
  antonymForm := some "dry"
  antonymRelation := some .contradictory

/-- "dry" — upper-closed scale (maximum at top) -/
def dry : AdjectivalPredicateEntry where
  form := "dry"
  scaleType := .upperBounded
  dimension := .wetness
  antonymForm := some "wet"
  antonymRelation := some .contradictory


/-- "clean" — closed scale (maximally clean), contradictory to "dirty" -/
def clean : AdjectivalPredicateEntry where
  form := "clean"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "dirty"
  antonymRelation := some .contradictory

/-- "dirty" — closed scale (maximally dirty), contradictory to "clean" -/
def dirty : AdjectivalPredicateEntry where
  form := "dirty"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "clean"
  antonymRelation := some .contradictory
  evaluativeValence := some .negative

/-- "straight" — closed scale (maximally straight), contradictory to "bent" -/
def straight : AdjectivalPredicateEntry where
  form := "straight"
  scaleType := .closed
  dimension := .straightness
  antonymForm := some "bent"
  antonymRelation := some .contradictory

/-- "flat" — closed scale (maximally flat), contradictory to "bumpy" -/
def flat : AdjectivalPredicateEntry where
  form := "flat"
  scaleType := .closed
  dimension := .flatness
  antonymForm := some "bumpy"
  antonymRelation := some .contradictory
  spatialConfigType := some .surfaceOrient

/-- "open" — closed scale (maximally open), contradictory to "closed" -/
def open_ : AdjectivalPredicateEntry where
  form := "open"
  scaleType := .closed
  dimension := .openness
  antonymForm := some "closed"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "closed" — closed scale, contradictory to "open" -/
def closed_ : AdjectivalPredicateEntry where
  form := "closed"
  scaleType := .closed
  dimension := .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "shut" — closed scale, contradictory to "open" (near-synonym of "closed") -/
def shut : AdjectivalPredicateEntry where
  form := "shut"
  scaleType := .closed
  dimension := .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "free" — closed scale (maximally free = unattached), contradictory to "stuck" -/
def free_ : AdjectivalPredicateEntry where
  form := "free"
  scaleType := .closed
  dimension := .freedom
  antonymForm := some "stuck"
  antonymRelation := some .contradictory
  spatialConfigType := some .unattachment

/-- "loose" — closed scale (maximally loose), contradictory to "tight" -/
def loose : AdjectivalPredicateEntry where
  form := "loose"
  scaleType := .closed
  dimension := .tightness
  antonymForm := some "tight"
  antonymRelation := some .contradictory
  spatialConfigType := some .unattachment

/-- "tight" — closed scale (maximally tight), contradictory to "loose" -/
def tight : AdjectivalPredicateEntry where
  form := "tight"
  scaleType := .closed
  dimension := .tightness
  antonymForm := some "loose"
  antonymRelation := some .contradictory

/-- "bent" — lower-closed scale (minimum at 0 = straight), contradictory to "straight" -/
def bent : AdjectivalPredicateEntry where
  form := "bent"
  scaleType := .lowerBounded
  dimension := .straightness
  antonymForm := some "straight"
  antonymRelation := some .contradictory

/-- "smooth" — closed scale, contradictory to "rough" -/
def smooth : AdjectivalPredicateEntry where
  form := "smooth"
  scaleType := .closed
  dimension := .smoothness
  antonymForm := some "rough"
  antonymRelation := some .contradictory

/-- "rough" — closed scale, contradictory to "smooth" -/
def rough : AdjectivalPredicateEntry where
  form := "rough"
  scaleType := .closed
  dimension := .smoothness
  antonymForm := some "smooth"
  antonymRelation := some .contradictory

/-- "hard" — open scale, contrary to "soft" -/
def hard : AdjectivalPredicateEntry where
  form := "hard"
  scaleType := .open_
  dimension := .hardness
  antonymForm := some "soft"
  antonymRelation := some .contrary

/-- "soft" — open scale, contrary to "hard" -/
def soft : AdjectivalPredicateEntry where
  form := "soft"
  scaleType := .open_
  dimension := .hardness
  antonymForm := some "hard"
  antonymRelation := some .contrary

/-- "pure" — closed scale (maximally pure), contradictory to "impure" -/
def pure_ : AdjectivalPredicateEntry where
  form := "pure"
  scaleType := .closed
  dimension := .purity
  antonymForm := some "impure"
  antonymRelation := some .contradictory

/-- "dead" — closed scale (absolute: maximal endpoint), contradictory to "alive" -/
def dead : AdjectivalPredicateEntry where
  form := "dead"
  scaleType := .closed
  dimension := .alive
  antonymForm := some "alive"
  antonymRelation := some .contradictory

/-- "alive" — closed scale (absolute), contradictory to "dead" -/
def alive : AdjectivalPredicateEntry where
  form := "alive"
  scaleType := .closed
  dimension := .alive
  antonymForm := some "dead"
  antonymRelation := some .contradictory

/-- "large" — open scale, contrary to "small" -/
def large : AdjectivalPredicateEntry where
  form := "large"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "small"
  antonymRelation := some .contrary

/-- "small" — open scale, contrary to "large" -/
def small : AdjectivalPredicateEntry where
  form := "small"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "large"
  antonymRelation := some .contrary

/-- "gigantic" — open scale, contrary to "tiny", informationally stronger than "large" -/
def gigantic : AdjectivalPredicateEntry where
  form := "gigantic"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "tiny"
  antonymRelation := some .contrary

/-- "tiny" — open scale, contrary to "gigantic", informationally stronger than "small" -/
def tiny : AdjectivalPredicateEntry where
  form := "tiny"
  scaleType := .open_
  dimension := .generalSize
  antonymForm := some "gigantic"
  antonymRelation := some .contrary

/-- "pristine" — closed scale, contrary to "filthy" (extreme absolute: gap exists) -/
def pristine : AdjectivalPredicateEntry where
  form := "pristine"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "filthy"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "filthy" — closed scale, contrary to "pristine" (extreme absolute: gap exists) -/
def filthy : AdjectivalPredicateEntry where
  form := "filthy"
  scaleType := .closed
  dimension := .cleanliness
  antonymForm := some "pristine"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "long" — open scale, contrary to "short" (length dimension) -/
def long : AdjectivalPredicateEntry where
  form := "long"
  scaleType := .open_
  dimension := .length
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "wide" — open scale, contrary to "narrow" -/
def wide : AdjectivalPredicateEntry where
  form := "wide"
  scaleType := .open_
  dimension := .width
  antonymForm := some "narrow"
  antonymRelation := some .contrary

/-- "cool" — open scale, contrary to "warm" -/
def cool : AdjectivalPredicateEntry where
  form := "cool"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "warm"
  antonymRelation := some .contrary

/-- "warm" — open scale, contrary to "cool" -/
def warm : AdjectivalPredicateEntry where
  form := "warm"
  scaleType := .open_
  dimension := .temperature
  antonymForm := some "cool"
  antonymRelation := some .contrary

/-! ## Physical dimension adjectives -/

/-- "heavy" — open scale, contrary to "light" -/
def heavy : AdjectivalPredicateEntry where
  form := "heavy"
  scaleType := .open_
  dimension := .weight
  antonymForm := some "light"
  antonymRelation := some .contrary

/-- "light" — open scale, contrary to "heavy" -/
def light : AdjectivalPredicateEntry where
  form := "light"
  scaleType := .open_
  dimension := .weight
  antonymForm := some "heavy"
  antonymRelation := some .contrary

/-- "thick" — open scale, contrary to "thin" -/
def thick : AdjectivalPredicateEntry where
  form := "thick"
  scaleType := .open_
  dimension := .thickness
  antonymForm := some "thin"
  antonymRelation := some .contrary

/-- "thin" — open scale, contrary to "thick" -/
def thin : AdjectivalPredicateEntry where
  form := "thin"
  scaleType := .open_
  dimension := .thickness
  antonymForm := some "thick"
  antonymRelation := some .contrary

/-- "deep" — open scale, contrary to "shallow" -/
def deep : AdjectivalPredicateEntry where
  form := "deep"
  scaleType := .open_
  dimension := .depth
  antonymForm := some "shallow"
  antonymRelation := some .contrary

/-- "shallow" — open scale, contrary to "deep" -/
def shallow : AdjectivalPredicateEntry where
  form := "shallow"
  scaleType := .open_
  dimension := .depth
  antonymForm := some "deep"
  antonymRelation := some .contrary

/-- "strong" — open scale, contrary to "weak" -/
def strong : AdjectivalPredicateEntry where
  form := "strong"
  scaleType := .open_
  dimension := .strength
  antonymForm := some "weak"
  antonymRelation := some .contrary

/-- "weak" — open scale, contrary to "strong" -/
def weak : AdjectivalPredicateEntry where
  form := "weak"
  scaleType := .open_
  dimension := .strength
  antonymForm := some "strong"
  antonymRelation := some .contrary

/-- "fast" — open scale, contrary to "slow" -/
def fast : AdjectivalPredicateEntry where
  form := "fast"
  scaleType := .open_
  dimension := .speed
  antonymForm := some "slow"
  antonymRelation := some .contrary

/-- "slow" — open scale, contrary to "fast" -/
def slow : AdjectivalPredicateEntry where
  form := "slow"
  scaleType := .open_
  dimension := .speed
  antonymForm := some "fast"
  antonymRelation := some .contrary

/-- "old" — open scale, contrary to "young" -/
def old : AdjectivalPredicateEntry where
  form := "old"
  scaleType := .open_
  dimension := .age
  antonymForm := some "young"
  antonymRelation := some .contrary

/-- "young" — open scale, contrary to "old" -/
def young : AdjectivalPredicateEntry where
  form := "young"
  scaleType := .open_
  dimension := .age
  antonymForm := some "old"
  antonymRelation := some .contrary

/-! ## Sensory adjectives -/

/-- "bright" — open scale, contrary to "dark" -/
def bright : AdjectivalPredicateEntry where
  form := "bright"
  scaleType := .open_
  dimension := .brightness
  antonymForm := some "dark"
  antonymRelation := some .contrary

/-- "dark" — open scale, contrary to "bright" -/
def dark : AdjectivalPredicateEntry where
  form := "dark"
  scaleType := .open_
  dimension := .brightness
  antonymForm := some "bright"
  antonymRelation := some .contrary

/-- "loud" — open scale, contrary to "quiet" -/
def loud : AdjectivalPredicateEntry where
  form := "loud"
  scaleType := .open_
  dimension := .volume
  antonymForm := some "quiet"
  antonymRelation := some .contrary

/-- "quiet" — open scale, contrary to "loud" -/
def quiet : AdjectivalPredicateEntry where
  form := "quiet"
  scaleType := .open_
  dimension := .volume
  antonymForm := some "loud"
  antonymRelation := some .contrary

/-! ## Evaluative adjectives -/

/-- "good" — value scale (lower-bounded at 0 per @cite{wolfsdorf-2019}),
    contrary to "bad". Despite the lower bound, "good" receives a contextual
    standard (not minEndpoint): it patterns with relative adjectives
    (@cite{beltrama-2025} §3). -/
def good : AdjectivalPredicateEntry where
  form := "good"
  scaleType := .lowerBounded
  dimension := .value
  antonymForm := some "bad"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "bad" — value scale, contrary to "good" -/
def bad : AdjectivalPredicateEntry where
  form := "bad"
  scaleType := .lowerBounded
  dimension := .value
  antonymForm := some "good"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "beautiful" — open scale, contrary to "ugly" -/
def beautiful : AdjectivalPredicateEntry where
  form := "beautiful"
  scaleType := .open_
  dimension := .beauty
  antonymForm := some "ugly"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "ugly" — open scale, contrary to "beautiful" -/
def ugly : AdjectivalPredicateEntry where
  form := "ugly"
  scaleType := .open_
  dimension := .beauty
  antonymForm := some "beautiful"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "important" — open scale -/
def important : AdjectivalPredicateEntry where
  form := "important"
  scaleType := .open_
  dimension := .importance

/-- "safe" — open scale, contrary to "dangerous" -/
def safe : AdjectivalPredicateEntry where
  form := "safe"
  scaleType := .open_
  dimension := .safety
  antonymForm := some "dangerous"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "dangerous" — open scale, contrary to "safe" -/
def dangerous : AdjectivalPredicateEntry where
  form := "dangerous"
  scaleType := .open_
  dimension := .danger
  antonymForm := some "safe"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-! ## Physical disturbance deverbal adjectives

@cite{tham-2025}: physical disturbance predicates are associated with a totally
closed, multi-point scale. Lower bound = physical instantiation of disturbance;
upper bound = spatial extent of host entity. Gradable (*more cracked*, *badly
dented*), compatible with *completely* and *partially*. Contra
@cite{rappaport-hovav-2014} (two-point) and @cite{rotstein-winter-2004}
(lower-bounded only). -/

/-- "cracked" — closed scale, contradictory to "uncracked".
    Deverbal adjective from *crack* (Levin 45.1 Break verbs).
    NOT a two-point scale: accepts *more cracked*, *completely cracked*,
    *partially cracked*, *badly cracked* (@cite{tham-2025} §2.3–2.4). -/
def cracked : AdjectivalPredicateEntry where
  form := "cracked"
  scaleType := .closed
  dimension := .cracking

/-- "dented" — closed scale.
    Deverbal adjective from *dent*. Accepts *more dented*, *completely dented*,
    *badly dented* (@cite{tham-2025} (11a), (20b)). -/
def dented : AdjectivalPredicateEntry where
  form := "dented"
  scaleType := .closed
  dimension := .denting

/-- "scratched" — closed scale.
    Deverbal adjective from *scratch*. Accepts *more scratched*, *completely
    scratched*, *badly scratched* (@cite{tham-2025} (11b), (20c)). -/
def scratched : AdjectivalPredicateEntry where
  form := "scratched"
  scaleType := .closed
  dimension := .scratching

/-- "shattered" — closed scale, NON-GRADABLE.
    Deverbal adjective from *shatter* (Levin 45.1 Break verbs).
    Contrast: ??*more shattered*, punctual verb, no durative reading.
    Not a physical disturbance predicate (@cite{tham-2025} (12c)). -/
def shattered : AdjectivalPredicateEntry where
  form := "shattered"
  scaleType := .closed
  dimension := .shattering

/-! ## Mildly positive adjectives (MPAs)

@cite{beltrama-2025}: MPAs encode a necessity standard — the minimum value
required for pursuit. They share properties with both relative (context-sensitive,
gradable) and absolute (no zone of indifference, crisp judgments, *barely*
compatible) predicates. -/

/-- "nice" — open scale, positive evaluative (@cite{nouwen-2024}).
    Base for M-degree intensifier *nicely*. -/
def nice : AdjectivalPredicateEntry where
  form := "nice"
  scaleType := .open_
  dimension := .value
  evaluativeValence := some .positive

/-- "pleasant" — open scale, positive evaluative (@cite{nouwen-2024}).
    Base for M-degree intensifier *pleasantly*. -/
def pleasant : AdjectivalPredicateEntry where
  form := "pleasant"
  scaleType := .open_
  dimension := .value
  antonymForm := some "unpleasant"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "decent" — value scale, necessity standard (@cite{beltrama-2025}) -/
def decent : AdjectivalPredicateEntry where
  form := "decent"
  scaleType := .lowerBounded
  dimension := .value
  evaluativeValence := some .positive

/-- "acceptable" — value scale, necessity standard (@cite{beltrama-2025}).
    Deverbal *-able* form: modal suffix contributes functional standard. -/
def acceptable : AdjectivalPredicateEntry where
  form := "acceptable"
  scaleType := .lowerBounded
  dimension := .value
  evaluativeValence := some .positive

/-- "adequate" — value scale, necessity standard (@cite{beltrama-2025}) -/
def adequate : AdjectivalPredicateEntry where
  form := "adequate"
  scaleType := .lowerBounded
  dimension := .value
  evaluativeValence := some .positive

/-! ## Deadjectival intensifier bases (@cite{nouwen-2024})

Adjectival bases for deadjectival intensifiers. Evaluative adjectives
(horrible, wonderful) derive H-degree or M-degree intensifiers via the
Goldilocks effect. Mirative (unusual, surprising) and modal (possible,
impossible) bases follow Zwicky's generalization. -/

-- Negative-evaluative bases → H-degree intensifiers

/-- "horrible" — open scale, negative evaluative. Base for H-degree *horribly*. -/
def horrible : AdjectivalPredicateEntry where
  form := "horrible"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .negative

/-- "terrible" — open scale, negative evaluative. Base for H-degree *terribly*. -/
def terrible : AdjectivalPredicateEntry where
  form := "terrible"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .negative

/-- "awful" — open scale, negative evaluative. Base for H-degree *awfully*. -/
def awful : AdjectivalPredicateEntry where
  form := "awful"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .negative

/-- "dreadful" — open scale, negative evaluative. Base for H-degree *dreadfully*. -/
def dreadful : AdjectivalPredicateEntry where
  form := "dreadful"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .negative

/-- "frightening" — open scale, negative evaluative. Base for H-degree *frighteningly*. -/
def frightening : AdjectivalPredicateEntry where
  form := "frightening"
  scaleType := .open_
  dimension := .danger
  evaluativeValence := some .negative

/-- "disgusting" — open scale, negative evaluative. Base for H-degree *disgustingly*. -/
def disgusting : AdjectivalPredicateEntry where
  form := "disgusting"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .negative

/-- "annoying" — open scale, negative evaluative. Base for H-degree *annoyingly*. -/
def annoying : AdjectivalPredicateEntry where
  form := "annoying"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .negative

/-- "unpleasant" — open scale, negative evaluative, contrary to "pleasant". -/
def unpleasant : AdjectivalPredicateEntry where
  form := "unpleasant"
  scaleType := .open_
  dimension := .value
  antonymForm := some "pleasant"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "scary" — open scale, negative evaluative. Base for H-degree *scarily*. -/
def scary : AdjectivalPredicateEntry where
  form := "scary"
  scaleType := .open_
  dimension := .danger
  evaluativeValence := some .negative

-- Positive-evaluative bases → M-degree intensifiers

/-- "wonderful" — open scale, positive evaluative. Base for M-degree *wonderfully*. -/
def wonderful : AdjectivalPredicateEntry where
  form := "wonderful"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .positive

/-- "delightful" — open scale, positive evaluative. Base for M-degree *delightfully*. -/
def delightful : AdjectivalPredicateEntry where
  form := "delightful"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .positive

/-- "gorgeous" — open scale, positive evaluative. Base for M-degree *gorgeously*. -/
def gorgeous : AdjectivalPredicateEntry where
  form := "gorgeous"
  scaleType := .open_
  dimension := .beauty
  evaluativeValence := some .positive

-- Mirative bases → H-degree intensifiers (not evaluative; §2.4.2)

/-- "unusual" — open scale, neutral (mirative), contrary to "usual". -/
def unusual : AdjectivalPredicateEntry where
  form := "unusual"
  scaleType := .open_
  dimension := .expectation
  antonymForm := some "usual"
  antonymRelation := some .contrary
  evaluativeValence := some .neutral

/-- "surprising" — open scale, neutral (mirative). Base for H-degree *surprisingly*. -/
def surprising : AdjectivalPredicateEntry where
  form := "surprising"
  scaleType := .open_
  dimension := .expectation
  evaluativeValence := some .neutral

/-- "remarkable" — open scale, positive evaluative (§2.4.1). Extreme positive
    evaluation: H-degree *remarkably* despite positive valence (Goldilocks exception). -/
def remarkable : AdjectivalPredicateEntry where
  form := "remarkable"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .positive

/-- "stunning" — open scale, positive evaluative (Figure 2, upper-right quadrant).
    Extreme positive evaluation: H-degree *stunningly* (Goldilocks exception). -/
def stunning : AdjectivalPredicateEntry where
  form := "stunning"
  scaleType := .open_
  dimension := .quality
  evaluativeValence := some .positive

-- Modal bases (Zwicky's generalization)

/-- "usual" — open scale, neutral (modal), contrary to "unusual". -/
def usual : AdjectivalPredicateEntry where
  form := "usual"
  scaleType := .open_
  dimension := .expectation
  antonymForm := some "unusual"
  antonymRelation := some .contrary
  evaluativeValence := some .neutral

/-- "expected" — open scale, neutral (modal). Unattested as intensifier (*expectedly). -/
def expected : AdjectivalPredicateEntry where
  form := "expected"
  scaleType := .open_
  dimension := .expectation
  evaluativeValence := some .neutral

/-- "possible" — open scale, neutral (modal), contradictory to "impossible". -/
def possible : AdjectivalPredicateEntry where
  form := "possible"
  scaleType := .open_
  dimension := .possibility
  antonymForm := some "impossible"
  antonymRelation := some .contradictory
  evaluativeValence := some .neutral

/-- "impossible" — open scale, neutral (modal), contradictory to "possible". -/
def impossible : AdjectivalPredicateEntry where
  form := "impossible"
  scaleType := .open_
  dimension := .possibility
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
  -- State: physical disturbance (@cite{tham-2025})
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
  -- Mildly positive adjectives (@cite{beltrama-2025})
  decent, acceptable, adequate,
  -- Intensifier bases: negative-evaluative (@cite{nouwen-2024})
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

end Fragments.English.Predicates.Adjectival
