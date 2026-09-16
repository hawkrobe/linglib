import Linglib.Semantics.Degree.Adjective

/-!
# English adjectives

This file lists the English adjective lexemes as `Degree.GradableAdjective`
entries. An entry records the surface form, the scalar dimension, the
polarity, the antonym and the comparison paradigm: the comparative and
superlative forms with their root pattern, `Paradigm.abb` for *good – better –
best*. The scale shape, the positive standard and the Kennedy class are
derived from the dimension and the polarity, not stored.

## References

* [kennedy-2007]
* [bobaljik-2012]
* [tham-2025]
* [beltrama-2025]
* [nouwen-2024]
* [cariani-santorio-wellwood-2024]
* [rappaport-hovav-2014]
* [rotstein-winter-2004]
-/

namespace English.Adjectives

open Degree

/-- "tall" — open scale, contrary to "short" -/
def tall : GradableAdjective where
  form := "tall"
  comparison := { formComp := some "taller", formSuper := some "tallest" }
  polarity := .positive
  dimension := some .height
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "short" — open scale, contrary to "tall" -/
def short : GradableAdjective where
  form := "short"
  comparison := { formComp := some "shorter", formSuper := some "shortest" }
  polarity := .negative
  dimension := some .height
  antonymForm := some "tall"
  antonymRelation := some .contrary

/-- "high" — open scale, contrary to "low" -/
def high : GradableAdjective where
  form := "high"
  polarity := .positive
  dimension := some .height
  antonymForm := some "low"
  antonymRelation := some .contrary


/--
"happy" — open scale, contrary to "unhappy"

Note: This is the 1-place adjectival predicate "x is happy".
For the 2-place veridical-preferential attitude predicate
"x is happy that p", see `Studies/UegakiSudo2019.lean`.
-/
def happy : GradableAdjective where
  form := "happy"
  comparison := { formComp := some "happier", formSuper := some "happiest" }
  polarity := .positive
  dimension := some .happiness
  antonymForm := some "unhappy"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "unhappy" — open scale, contrary to "happy" -/
def unhappy : GradableAdjective where
  form := "unhappy"
  comparison := { formComp := some "unhappier", formSuper := some "unhappiest" }
  polarity := .negative
  dimension := some .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "sad" — open scale, contrary to "happy" (near-synonym of unhappy) -/
def sad : GradableAdjective where
  form := "sad"
  comparison := { formComp := some "sadder", formSuper := some "saddest" }
  dimension := some .happiness
  antonymForm := some "happy"
  antonymRelation := some .contrary
  evaluativeValence := some .negative


/-- "full" — closed scale, contradictory to "empty" -/
def full : GradableAdjective where
  form := "full"
  comparison := { formComp := some "fuller", formSuper := some "fullest" }
  dimension := some .fullness
  antonymForm := some "empty"
  antonymRelation := some .contradictory  -- Closed scales often contradictory

/-- "empty" — negative pole of the closed fullness scale ⇒ maximum standard (no contents),
    contradictory to "full". -/
def empty : GradableAdjective where
  form := "empty"
  comparison := { formComp := some "emptier", formSuper := some "emptiest" }
  polarity := .negative
  dimension := some .fullness
  antonymForm := some "full"
  antonymRelation := some .contradictory


/-- "hot" — open scale, contrary to "cold" -/
def hot : GradableAdjective where
  form := "hot"
  comparison := { formComp := some "hotter", formSuper := some "hottest" }
  dimension := some .temperature
  antonymForm := some "cold"
  antonymRelation := some .contrary

/-- "cold" — open scale, contrary to "hot" -/
def cold : GradableAdjective where
  form := "cold"
  comparison := { formComp := some "colder", formSuper := some "coldest" }
  dimension := some .temperature
  antonymForm := some "hot"
  antonymRelation := some .contrary


/-- "expensive" — open scale, contrary to "cheap" -/
def expensive : GradableAdjective where
  form := "expensive"
  comparison := { formComp := some "more expensive", formSuper := some "most expensive"
                , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }
  dimension := some .cost
  antonymForm := some "cheap"
  antonymRelation := some .contrary

/-- "cheap" — open scale, contrary to "expensive" -/
def cheap : GradableAdjective where
  form := "cheap"
  comparison := { formComp := some "cheaper", formSuper := some "cheapest" }
  dimension := some .cost
  antonymForm := some "expensive"
  antonymRelation := some .contrary

/-- "wet" — lower-closed wetness scale ⇒ minimum standard (true with any
    non-zero wetness). Shares the closed `.wetness` scale with "dry"; the two
    differ only in pole. -/
def wet : GradableAdjective where
  form := "wet"
  comparison := { formComp := some "wetter", formSuper := some "wettest" }
  dimension := some .wetness
  antonymForm := some "dry"
  antonymRelation := some .contradictory

/-- "dry" — negative pole of the wetness scale ⇒ maximum standard (true only at
    complete dryness). -/
def dry : GradableAdjective where
  form := "dry"
  comparison := { formComp := some "drier", formSuper := some "driest" }
  polarity := .negative
  dimension := some .wetness
  antonymForm := some "wet"
  antonymRelation := some .contradictory


/-- "clean" — closed scale (maximally clean), contradictory to "dirty" -/
def clean : GradableAdjective where
  form := "clean"
  dimension := some .cleanliness
  antonymForm := some "dirty"
  antonymRelation := some .contradictory

/-- "dirty" — closed scale (maximally dirty), contradictory to "clean" -/
def dirty : GradableAdjective where
  form := "dirty"
  polarity := .negative
  dimension := some .cleanliness
  antonymForm := some "clean"
  antonymRelation := some .contradictory
  evaluativeValence := some .negative

/-- "straight" — closed scale (maximally straight), contradictory to "bent" -/
def straight : GradableAdjective where
  form := "straight"
  dimension := some .straightness
  antonymForm := some "bent"
  antonymRelation := some .contradictory

/-- "flat" — closed scale (maximally flat), contradictory to "bumpy" -/
def flat : GradableAdjective where
  form := "flat"
  dimension := some .flatness
  antonymForm := some "bumpy"
  antonymRelation := some .contradictory
  spatialConfigType := some .surfaceOrient

/-- "open" — closed scale (maximally open), contradictory to "closed" -/
def open_ : GradableAdjective where
  form := "open"
  dimension := some .openness
  antonymForm := some "closed"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "closed" — closed scale, contradictory to "open" -/
def closed_ : GradableAdjective where
  form := "closed"
  polarity := .negative
  dimension := some .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "shut" — closed scale, contradictory to "open" (near-synonym of "closed") -/
def shut : GradableAdjective where
  form := "shut"
  polarity := .negative
  dimension := some .openness
  antonymForm := some "open"
  antonymRelation := some .contradictory
  spatialConfigType := some .barrierConfig

/-- "free" — closed scale (maximally free = unattached), contradictory to "stuck" -/
def free_ : GradableAdjective where
  form := "free"
  dimension := some .freedom
  antonymForm := some "stuck"
  antonymRelation := some .contradictory
  spatialConfigType := some .unattachment

/-- "loose" — closed scale (maximally loose), contradictory to "tight" -/
def loose : GradableAdjective where
  form := "loose"
  polarity := .negative
  dimension := some .tightness
  antonymForm := some "tight"
  antonymRelation := some .contradictory
  spatialConfigType := some .unattachment

/-- "tight" — closed scale (maximally tight), contradictory to "loose" -/
def tight : GradableAdjective where
  form := "tight"
  dimension := some .tightness
  antonymForm := some "loose"
  antonymRelation := some .contradictory

/-- "bent" — negative pole of the upper-closed straightness scale ⇒ minimum standard (true with
    any non-zero bend). Shares the closed `.straightness` scale with "straight". -/
def bent : GradableAdjective where
  form := "bent"
  polarity := .negative
  dimension := some .straightness
  antonymForm := some "straight"
  antonymRelation := some .contradictory

/-- "smooth" — closed scale, contradictory to "rough" -/
def smooth : GradableAdjective where
  form := "smooth"
  dimension := some .smoothness
  antonymForm := some "rough"
  antonymRelation := some .contradictory

/-- "rough" — closed scale, contradictory to "smooth" -/
def rough : GradableAdjective where
  form := "rough"
  polarity := .negative
  dimension := some .smoothness
  antonymForm := some "smooth"
  antonymRelation := some .contradictory

/-- "hard" — open scale, contrary to "soft" -/
def hard : GradableAdjective where
  form := "hard"
  dimension := some .hardness
  antonymForm := some "soft"
  antonymRelation := some .contrary

/-- "soft" — open scale, contrary to "hard" -/
def soft : GradableAdjective where
  form := "soft"
  dimension := some .hardness
  antonymForm := some "hard"
  antonymRelation := some .contrary

/-- "pure" — closed scale (maximally pure), contradictory to "impure" -/
def pure_ : GradableAdjective where
  form := "pure"
  dimension := some .purity
  antonymForm := some "impure"
  antonymRelation := some .contradictory

/-- "dead" — closed scale (absolute: maximal endpoint), contradictory to "alive" -/
def dead : GradableAdjective where
  form := "dead"
  dimension := some .alive
  antonymForm := some "alive"
  antonymRelation := some .contradictory

/-- "alive" — closed scale (absolute), contradictory to "dead" -/
def alive : GradableAdjective where
  form := "alive"
  dimension := some .alive
  antonymForm := some "dead"
  antonymRelation := some .contradictory

/-- "pregnant" — non-gradable: no scale -/
def pregnant : GradableAdjective where
  form := "pregnant"

/-- "large" — open scale, contrary to "small" -/
def large : GradableAdjective where
  form := "large"
  dimension := some .generalSize
  antonymForm := some "small"
  antonymRelation := some .contrary

/-- "small" — open scale, contrary to "large" -/
def small : GradableAdjective where
  form := "small"
  dimension := some .generalSize
  antonymForm := some "large"
  antonymRelation := some .contrary

/-- "gigantic" — open scale, contrary to "tiny", informationally stronger than "large" -/
def gigantic : GradableAdjective where
  form := "gigantic"
  dimension := some .generalSize
  antonymForm := some "tiny"
  antonymRelation := some .contrary

/-- "tiny" — open scale, contrary to "gigantic", informationally stronger than "small" -/
def tiny : GradableAdjective where
  form := "tiny"
  dimension := some .generalSize
  antonymForm := some "gigantic"
  antonymRelation := some .contrary

/-- "pristine" — closed scale, contrary to "filthy" (extreme absolute: gap exists) -/
def pristine : GradableAdjective where
  form := "pristine"
  dimension := some .cleanliness
  antonymForm := some "filthy"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "filthy" — closed scale, contrary to "pristine" (extreme absolute: gap exists) -/
def filthy : GradableAdjective where
  form := "filthy"
  polarity := .negative
  dimension := some .cleanliness
  antonymForm := some "pristine"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "long" — open scale, contrary to "short" (length dimension) -/
def long : GradableAdjective where
  form := "long"
  dimension := some .length
  antonymForm := some "short"
  antonymRelation := some .contrary

/-- "wide" — open scale, contrary to "narrow" -/
def wide : GradableAdjective where
  form := "wide"
  dimension := some .width
  antonymForm := some "narrow"
  antonymRelation := some .contrary

/-- "cool" — open scale, contrary to "warm" -/
def cool : GradableAdjective where
  form := "cool"
  dimension := some .temperature
  antonymForm := some "warm"
  antonymRelation := some .contrary

/-- "warm" — open scale, contrary to "cool" -/
def warm : GradableAdjective where
  form := "warm"
  dimension := some .temperature
  antonymForm := some "cool"
  antonymRelation := some .contrary

/-! ## Physical dimension adjectives -/

/-- "heavy" — open scale, contrary to "light" -/
def heavy : GradableAdjective where
  form := "heavy"
  dimension := some .weight
  antonymForm := some "light"
  antonymRelation := some .contrary

/-- "light" — open scale, contrary to "heavy" -/
def light : GradableAdjective where
  form := "light"
  dimension := some .weight
  antonymForm := some "heavy"
  antonymRelation := some .contrary

/-- "thick" — open scale, contrary to "thin" -/
def thick : GradableAdjective where
  form := "thick"
  dimension := some .thickness
  antonymForm := some "thin"
  antonymRelation := some .contrary

/-- "thin" — open scale, contrary to "thick" -/
def thin : GradableAdjective where
  form := "thin"
  dimension := some .thickness
  antonymForm := some "thick"
  antonymRelation := some .contrary

/-- "deep" — open scale, contrary to "shallow" -/
def deep : GradableAdjective where
  form := "deep"
  dimension := some .depth
  antonymForm := some "shallow"
  antonymRelation := some .contrary

/-- "shallow" — open scale, contrary to "deep" -/
def shallow : GradableAdjective where
  form := "shallow"
  dimension := some .depth
  antonymForm := some "deep"
  antonymRelation := some .contrary

/-- "strong" — open scale, contrary to "weak" -/
def strong : GradableAdjective where
  form := "strong"
  dimension := some .strength
  antonymForm := some "weak"
  antonymRelation := some .contrary

/-- "weak" — open scale, contrary to "strong" -/
def weak : GradableAdjective where
  form := "weak"
  dimension := some .strength
  antonymForm := some "strong"
  antonymRelation := some .contrary

/-- "fast" — open scale, contrary to "slow" -/
def fast : GradableAdjective where
  form := "fast"
  dimension := some .speed
  antonymForm := some "slow"
  antonymRelation := some .contrary

/-- "slow" — open scale, contrary to "fast" -/
def slow : GradableAdjective where
  form := "slow"
  dimension := some .speed
  antonymForm := some "fast"
  antonymRelation := some .contrary

/-- "old" — open scale, contrary to "young" -/
def old : GradableAdjective where
  form := "old"
  dimension := some .age
  antonymForm := some "young"
  antonymRelation := some .contrary

/-- "young" — open scale, contrary to "old" -/
def young : GradableAdjective where
  form := "young"
  dimension := some .age
  antonymForm := some "old"
  antonymRelation := some .contrary

/-! ## Sensory adjectives -/

/-- "bright" — open scale, contrary to "dark" -/
def bright : GradableAdjective where
  form := "bright"
  dimension := some .brightness
  antonymForm := some "dark"
  antonymRelation := some .contrary

/-- "dark" — open scale, contrary to "bright" -/
def dark : GradableAdjective where
  form := "dark"
  dimension := some .brightness
  antonymForm := some "bright"
  antonymRelation := some .contrary

/-- "loud" — open scale, contrary to "quiet" -/
def loud : GradableAdjective where
  form := "loud"
  dimension := some .volume
  antonymForm := some "quiet"
  antonymRelation := some .contrary

/-- "quiet" — open scale, contrary to "loud" -/
def quiet : GradableAdjective where
  form := "quiet"
  dimension := some .volume
  antonymForm := some "loud"
  antonymRelation := some .contrary

/-! ## Intelligence and confidence

The confidence adjectives are the gradable attitude adjectives of
[cariani-santorio-wellwood-2024]. They measure on an upper-bounded confidence
scale, with *certain* at its maximum and *doubtful*, *unsure* and *uncertain*
on its negative pole. -/

/-- "smart" — open scale, contrary to "dumb" -/
def smart : GradableAdjective where
  form := "smart"
  dimension := some .intelligence
  comparison := { formComp := some "smarter", formSuper := some "smartest" }
  antonymForm := some "dumb"
  antonymRelation := some .contrary

/-- "confident" — upper-bounded confidence scale -/
def confident : GradableAdjective where
  form := "confident"
  dimension := some .confidence
  comparison := { formComp := some "more confident", formSuper := some "most confident"
                , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }

/-- "certain" — the maximum of the confidence scale, contrary to "uncertain" -/
def certain : GradableAdjective where
  form := "certain"
  dimension := some .confidence
  comparison := { formComp := some "more certain", formSuper := some "most certain"
                , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }
  antonymForm := some "uncertain"
  antonymRelation := some .contrary

/-- "sure" — near-synonym of "confident", contrary to "unsure" -/
def sure : GradableAdjective where
  form := "sure"
  dimension := some .confidence
  comparison := { formComp := some "surer", formSuper := some "surest" }
  antonymForm := some "unsure"
  antonymRelation := some .contrary

/-- "doubtful" — negative pole of the confidence scale -/
def doubtful : GradableAdjective where
  form := "doubtful"
  polarity := .negative
  dimension := some .confidence
  comparison := { formComp := some "more doubtful", formSuper := some "most doubtful"
                , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }

/-- "unsure" — negative pole of the confidence scale, contrary to "sure" -/
def unsure : GradableAdjective where
  form := "unsure"
  polarity := .negative
  dimension := some .confidence
  comparison := { formComp := some "more unsure", formSuper := some "most unsure"
                , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }
  antonymForm := some "sure"
  antonymRelation := some .contrary

/-- "uncertain" — negative pole of the confidence scale, contrary to "certain" -/
def uncertain : GradableAdjective where
  form := "uncertain"
  polarity := .negative
  dimension := some .confidence
  comparison := { formComp := some "more uncertain", formSuper := some "most uncertain"
                , comparativeStrategy := .periphrastic, superlativeStrategy := .periphrastic }
  antonymForm := some "certain"
  antonymRelation := some .contrary

/-! ## Evaluative adjectives -/

/-- "good" — open value scale, contrary to "bad". "good" takes a contextual
    standard and patterns with relative adjectives ([beltrama-2025] §3); on the
    open `.value` scale this class is *derived* (open ⇒ contextual) rather than
    stipulated, so no `standardOverride` is needed. -/
def good : GradableAdjective where
  form := "good"
  comparison := { formComp := some "better", formSuper := some "best"
                , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive
                , suppletion := Morphology.Paradigm.abb }
  dimension := some .value
  antonymForm := some "bad"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "bad" — value scale, contrary to "good" -/
def bad : GradableAdjective where
  form := "bad"
  comparison := { formComp := some "worse", formSuper := some "worst"
                , comparativeStrategy := .suppletive, superlativeStrategy := .suppletive
                , suppletion := Morphology.Paradigm.abb }
  dimension := some .value
  antonymForm := some "good"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "beautiful" — open scale, contrary to "ugly" -/
def beautiful : GradableAdjective where
  form := "beautiful"
  dimension := some .beauty
  antonymForm := some "ugly"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "ugly" — open scale, contrary to "beautiful" -/
def ugly : GradableAdjective where
  form := "ugly"
  dimension := some .beauty
  antonymForm := some "beautiful"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "important" — open scale -/
def important : GradableAdjective where
  form := "important"
  dimension := some .importance

/-- "safe" — open scale, contrary to "dangerous" -/
def safe : GradableAdjective where
  form := "safe"
  dimension := some .safety
  antonymForm := some "dangerous"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "dangerous" — open scale, contrary to "safe" -/
def dangerous : GradableAdjective where
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
def cracked : GradableAdjective where
  form := "cracked"
  dimension := some .cracking

/-- "dented" — closed scale.
    Deverbal adjective from *dent*. Accepts *more dented*, *completely dented*,
    *badly dented* ([tham-2025] (11a), (20b)). -/
def dented : GradableAdjective where
  form := "dented"
  dimension := some .denting

/-- "scratched" — closed scale.
    Deverbal adjective from *scratch*. Accepts *more scratched*, *completely
    scratched*, *badly scratched* ([tham-2025] (11b), (20c)). -/
def scratched : GradableAdjective where
  form := "scratched"
  dimension := some .scratching

/-- "shattered" — closed scale, NON-GRADABLE.
    Deverbal adjective from *shatter* (Levin 45.1 Break verbs).
    Contrast: ??*more shattered*, punctual verb, no durative reading.
    Not a physical disturbance predicate ([tham-2025] (12c)). -/
def shattered : GradableAdjective where
  form := "shattered"
  dimension := some .shattering

/-! ## Mildly positive adjectives (MPAs)

[beltrama-2025]: MPAs encode a necessity standard — the minimum value
required for pursuit. They share properties with both relative (context-sensitive,
gradable) and absolute (no zone of indifference, crisp judgments, *barely*
compatible) predicates. -/

/-- "nice" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *nicely*. -/
def nice : GradableAdjective where
  form := "nice"
  dimension := some .value
  evaluativeValence := some .positive

/-- "pleasant" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *pleasantly*. -/
def pleasant : GradableAdjective where
  form := "pleasant"
  dimension := some .value
  antonymForm := some "unpleasant"
  antonymRelation := some .contrary
  evaluativeValence := some .positive

/-- "decent" — a mildly-positive adjective: open `.value` scale with a functional
    (necessity) standard ([beltrama-2025]), recorded via `standardOverride`. -/
def decent : GradableAdjective where
  form := "decent"
  dimension := some .value
  standardOverride := some .functional
  evaluativeValence := some .positive

/-- "acceptable" — mildly-positive adjective; open `.value` scale, functional
    standard ([beltrama-2025]). Deverbal *-able* form: the modal suffix
    contributes the functional standard. -/
def acceptable : GradableAdjective where
  form := "acceptable"
  dimension := some .value
  standardOverride := some .functional
  evaluativeValence := some .positive

/-- "adequate" — mildly-positive adjective; open `.value` scale, functional
    (necessity) standard ([beltrama-2025]). -/
def adequate : GradableAdjective where
  form := "adequate"
  dimension := some .value
  standardOverride := some .functional
  evaluativeValence := some .positive

/-! ## Deadjectival intensifier bases ([nouwen-2024])

Adjectival bases for deadjectival intensifiers. Evaluative adjectives
(horrible, wonderful) derive H-degree or M-degree intensifiers via the
Goldilocks effect. Mirative (unusual, surprising) and modal (possible,
impossible) bases follow Zwicky's generalization. -/

/-! ### Negative-evaluative bases: H-degree intensifiers -/

/-- "horrible" — open scale, negative evaluative. Base for H-degree *horribly*. -/
def horrible : GradableAdjective where
  form := "horrible"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "terrible" — open scale, negative evaluative. Base for H-degree *terribly*. -/
def terrible : GradableAdjective where
  form := "terrible"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "awful" — open scale, negative evaluative. Base for H-degree *awfully*. -/
def awful : GradableAdjective where
  form := "awful"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "dreadful" — open scale, negative evaluative. Base for H-degree *dreadfully*. -/
def dreadful : GradableAdjective where
  form := "dreadful"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "frightening" — open scale, negative evaluative. Base for H-degree *frighteningly*. -/
def frightening : GradableAdjective where
  form := "frightening"
  dimension := some .danger
  evaluativeValence := some .negative

/-- "disgusting" — open scale, negative evaluative. Base for H-degree *disgustingly*. -/
def disgusting : GradableAdjective where
  form := "disgusting"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "annoying" — open scale, negative evaluative. Base for H-degree *annoyingly*. -/
def annoying : GradableAdjective where
  form := "annoying"
  dimension := some .quality
  evaluativeValence := some .negative

/-- "unpleasant" — open scale, negative evaluative, contrary to "pleasant". -/
def unpleasant : GradableAdjective where
  form := "unpleasant"
  dimension := some .value
  antonymForm := some "pleasant"
  antonymRelation := some .contrary
  evaluativeValence := some .negative

/-- "scary" — open scale, negative evaluative. Base for H-degree *scarily*. -/
def scary : GradableAdjective where
  form := "scary"
  dimension := some .danger
  evaluativeValence := some .negative

/-! ### Positive-evaluative bases: M-degree intensifiers -/

/-- "wonderful" — open scale, positive evaluative. Base for M-degree *wonderfully*. -/
def wonderful : GradableAdjective where
  form := "wonderful"
  dimension := some .quality
  evaluativeValence := some .positive

/-- "delightful" — open scale, positive evaluative. Base for M-degree *delightfully*. -/
def delightful : GradableAdjective where
  form := "delightful"
  dimension := some .quality
  evaluativeValence := some .positive

/-- "gorgeous" — open scale, positive evaluative. Base for M-degree *gorgeously*. -/
def gorgeous : GradableAdjective where
  form := "gorgeous"
  dimension := some .beauty
  evaluativeValence := some .positive

/-! ### Mirative bases: H-degree intensifiers, not evaluative -/

/-- "unusual" — open scale, neutral (mirative), contrary to "usual". -/
def unusual : GradableAdjective where
  form := "unusual"
  dimension := some .expectation
  antonymForm := some "usual"
  antonymRelation := some .contrary
  evaluativeValence := some .neutral

/-- "surprising" — open scale, neutral (mirative). Base for H-degree *surprisingly*. -/
def surprising : GradableAdjective where
  form := "surprising"
  dimension := some .expectation
  evaluativeValence := some .neutral

/-- "remarkable" — open scale, positive evaluative (§2.4.1). Extreme positive
    evaluation: H-degree *remarkably* despite positive valence (Goldilocks exception). -/
def remarkable : GradableAdjective where
  form := "remarkable"
  dimension := some .quality
  evaluativeValence := some .positive

/-- "stunning" — open scale, positive evaluative (Figure 2, upper-right quadrant).
    Extreme positive evaluation: H-degree *stunningly* (Goldilocks exception). -/
def stunning : GradableAdjective where
  form := "stunning"
  dimension := some .quality
  evaluativeValence := some .positive

/-! ### Modal bases: Zwicky's generalization -/

/-- "usual" — open scale, neutral (modal), contrary to "unusual". -/
def usual : GradableAdjective where
  form := "usual"
  dimension := some .expectation
  antonymForm := some "unusual"
  antonymRelation := some .contrary
  evaluativeValence := some .neutral

/-- "expected" — open scale, neutral (modal). Unattested as intensifier (*expectedly). -/
def expected : GradableAdjective where
  form := "expected"
  dimension := some .expectation
  evaluativeValence := some .neutral

/-- "possible" — open scale, neutral (modal), contradictory to "impossible". -/
def possible : GradableAdjective where
  form := "possible"
  dimension := some .possibility
  antonymForm := some "impossible"
  antonymRelation := some .contradictory
  evaluativeValence := some .neutral

/-- "impossible" — open scale, neutral (modal), contradictory to "possible". -/
def impossible : GradableAdjective where
  form := "impossible"
  dimension := some .possibility
  antonymForm := some "possible"
  antonymRelation := some .contradictory
  evaluativeValence := some .neutral

/-- Every entry of the fragment. -/
def allEntries : List (GradableAdjective) := [
  -- Height / size
  tall, short, high, large, small, gigantic, tiny,
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
  hard, soft, pure_, dead, alive, pregnant,
  -- State: physical disturbance ([tham-2025])
  cracked, dented, scratched, shattered,
  -- Informationally strong
  pristine, filthy,
  -- Physical dimensions
  long, wide, heavy, light, thick, thin, deep, shallow,
  strong, weak, fast, slow, old, young,
  -- Sensory
  bright, dark, loud, quiet,
  -- Intelligence and confidence
  smart, confident, certain, sure, doubtful, unsure, uncertain,
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

/-- The entry with a given surface form. -/
def lookup (form : String) : Option (GradableAdjective) :=
  allEntries.find? (·.form == form)

end English.Adjectives
