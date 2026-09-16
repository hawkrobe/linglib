import Linglib.Semantics.Degree.Adjective

/-!
# English adjectives

This file lists the English adjective lexemes. An entry records the surface
form, the scalar dimension, the polarity, the antonym and the comparison
paradigm: the comparative and superlative forms with their root pattern,
`Paradigm.abb` for *good – better – best*. An antonym pair is entered once,
as an `AntonymPair` on its shared scale, and its two polar adjectives are the
pair's `pos` and `neg`.

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

def height : AntonymPair :=
  { dimension := .height, relation := .contrary, posForm := "tall", negForm := "short"
  , posComparison := .synthetic "taller" "tallest"
  , negComparison := .synthetic "shorter" "shortest" }

abbrev tall := height.pos

abbrev short := height.neg

def high : GradableAdjective :=
  { form := "high", dimension := some .height, antonymForm := some "low"
  , antonymRelation := some .contrary }

/-- Note: This is the 1-place adjectival predicate "x is happy".
For the 2-place veridical-preferential attitude predicate
"x is happy that p", see `Studies/UegakiSudo2019.lean`. -/
def happiness : AntonymPair :=
  { dimension := .happiness, relation := .contrary, posForm := "happy", negForm := "unhappy"
  , posComparison := .synthetic "happier" "happiest"
  , negComparison := .synthetic "unhappier" "unhappiest", evaluativeValence := some .positive }

abbrev happy := happiness.pos

abbrev unhappy := happiness.neg

def sad : GradableAdjective :=
  { form := "sad", polarity := .negative, dimension := some .happiness
  , comparison := .synthetic "sadder" "saddest"
  , antonymForm := some "happy", antonymRelation := some .contrary
  , evaluativeValence := some .negative }

/-- Both poles take the maximum standard, so a half-full glass is neither full nor empty
([kennedy-mcnally-2005] (28a)). -/
def fullness : AntonymPair :=
  { dimension := .fullness, relation := .contrary, posForm := "full", negForm := "empty"
  , posComparison := .synthetic "fuller" "fullest"
  , negComparison := .synthetic "emptier" "emptiest" }

abbrev full := fullness.pos

abbrev empty := fullness.neg

def heat : AntonymPair :=
  { dimension := .temperature, relation := .contrary, posForm := "hot", negForm := "cold"
  , posComparison := .synthetic "hotter" "hottest", negComparison := .synthetic "colder" "coldest" }

abbrev hot := heat.pos

abbrev cold := heat.neg

def cost : AntonymPair :=
  { dimension := .cost, relation := .contrary, posForm := "expensive", negForm := "cheap"
  , posComparison := .periphrastic "more expensive" "most expensive"
  , negComparison := .synthetic "cheaper" "cheapest" }

abbrev expensive := cost.pos

abbrev cheap := cost.neg

def wetness : AntonymPair :=
  { dimension := .wetness, relation := .contradictory, posForm := "wet", negForm := "dry"
  , posComparison := .synthetic "wetter" "wettest", negComparison := .synthetic "drier" "driest" }

abbrev wet := wetness.pos

abbrev dry := wetness.neg

def cleanliness : AntonymPair :=
  { dimension := .cleanliness, relation := .contradictory, posForm := "clean", negForm := "dirty" }

abbrev clean := cleanliness.pos

abbrev dirty := cleanliness.neg

def straightness : AntonymPair :=
  { dimension := .straightness, relation := .contradictory, posForm := "straight"
  , negForm := "bent" }

abbrev straight := straightness.pos

abbrev bent := straightness.neg

def flat : GradableAdjective :=
  { form := "flat", dimension := some .flatness, antonymForm := some "bumpy"
  , antonymRelation := some .contradictory, spatialConfigType := some .surfaceOrient }

/-- *open* takes the minimum standard, any amount of opening ([kennedy-2007] (68)); *closed* the
maximum. -/
def openness : AntonymPair :=
  { dimension := .openness, relation := .contradictory, posForm := "open", negForm := "closed"
  , posStandardOverride := some .minEndpoint, spatialConfigType := some .barrierConfig }

abbrev open_ := openness.pos

abbrev closed_ := openness.neg

def shut : GradableAdjective :=
  { form := "shut", polarity := .negative, dimension := some .openness, antonymForm := some "open"
  , antonymRelation := some .contradictory, spatialConfigType := some .barrierConfig }

def free_ : GradableAdjective :=
  { form := "free", dimension := some .freedom, antonymForm := some "stuck"
  , antonymRelation := some .contradictory, spatialConfigType := some .unattachment }

def loose : GradableAdjective :=
  { form := "loose", polarity := .negative, dimension := some .tightness
  , antonymForm := some "tight", antonymRelation := some .contradictory
  , spatialConfigType := some .unattachment }

def tight : GradableAdjective :=
  { form := "tight", dimension := some .tightness, antonymForm := some "loose"
  , antonymRelation := some .contradictory }

def smoothness : AntonymPair :=
  { dimension := .smoothness, relation := .contradictory, posForm := "smooth", negForm := "rough" }

abbrev smooth := smoothness.pos

abbrev rough := smoothness.neg

def hardness : AntonymPair :=
  { dimension := .hardness, relation := .contrary, posForm := "hard", negForm := "soft" }

abbrev hard := hardness.pos

abbrev soft := hardness.neg

def pure_ : GradableAdjective :=
  { form := "pure", dimension := some .purity, antonymForm := some "impure"
  , antonymRelation := some .contradictory }

/-- *dead* takes the maximum standard and is rarely used imprecisely ([kennedy-mcnally-2005]);
*alive* the minimum. -/
def life : AntonymPair :=
  { dimension := .alive, relation := .contradictory, posForm := "alive", negForm := "dead"
  , posStandardOverride := some .minEndpoint }

abbrev alive := life.pos

abbrev dead := life.neg

def pregnant : GradableAdjective :=
  { form := "pregnant" }

def size : AntonymPair :=
  { dimension := .generalSize, relation := .contrary, posForm := "large", negForm := "small" }

abbrev large := size.pos

abbrev small := size.neg

def extremeSize : AntonymPair :=
  { dimension := .generalSize, relation := .contrary, posForm := "gigantic", negForm := "tiny" }

abbrev gigantic := extremeSize.pos

abbrev tiny := extremeSize.neg

def pristineness : AntonymPair :=
  { dimension := .cleanliness, relation := .contrary, posForm := "pristine", negForm := "filthy"
  , evaluativeValence := some .positive }

abbrev pristine := pristineness.pos

abbrev filthy := pristineness.neg

def long : GradableAdjective :=
  { form := "long", dimension := some .length, antonymForm := some "short"
  , antonymRelation := some .contrary }

def wide : GradableAdjective :=
  { form := "wide", dimension := some .width, antonymForm := some "narrow"
  , antonymRelation := some .contrary }

def warmth : AntonymPair :=
  { dimension := .temperature, relation := .contrary, posForm := "warm", negForm := "cool" }

abbrev warm := warmth.pos

abbrev cool := warmth.neg

/-! ## Physical dimension adjectives -/

def weight : AntonymPair :=
  { dimension := .weight, relation := .contrary, posForm := "heavy", negForm := "light" }

abbrev heavy := weight.pos

abbrev light := weight.neg

def thickness : AntonymPair :=
  { dimension := .thickness, relation := .contrary, posForm := "thick", negForm := "thin" }

abbrev thick := thickness.pos

abbrev thin := thickness.neg

def depth : AntonymPair :=
  { dimension := .depth, relation := .contrary, posForm := "deep", negForm := "shallow" }

abbrev deep := depth.pos

abbrev shallow := depth.neg

def strength : AntonymPair :=
  { dimension := .strength, relation := .contrary, posForm := "strong", negForm := "weak" }

abbrev strong := strength.pos

abbrev weak := strength.neg

def speed : AntonymPair :=
  { dimension := .speed, relation := .contrary, posForm := "fast", negForm := "slow" }

abbrev fast := speed.pos

abbrev slow := speed.neg

def age : AntonymPair :=
  { dimension := .age, relation := .contrary, posForm := "old", negForm := "young" }

abbrev old := age.pos

abbrev young := age.neg

/-! ## Sensory adjectives -/

def brightness : AntonymPair :=
  { dimension := .brightness, relation := .contrary, posForm := "bright", negForm := "dark" }

abbrev bright := brightness.pos

abbrev dark := brightness.neg

def volume : AntonymPair :=
  { dimension := .volume, relation := .contrary, posForm := "loud", negForm := "quiet" }

abbrev loud := volume.pos

abbrev quiet := volume.neg

/-! ## Intelligence and confidence

The confidence adjectives are the gradable attitude adjectives of
[cariani-santorio-wellwood-2024]. They measure on an upper-bounded confidence
scale, with *certain* at its maximum and *doubtful*, *unsure* and *uncertain*
on its negative pole. -/

def smart : GradableAdjective :=
  { form := "smart", dimension := some .intelligence, comparison := .synthetic "smarter" "smartest"
  , antonymForm := some "dumb", antonymRelation := some .contrary }

def confident : GradableAdjective :=
  { form := "confident", dimension := some .confidence
  , comparison := .periphrastic "more confident" "most confident" }

def confidence : AntonymPair :=
  { dimension := .confidence, relation := .contrary, posForm := "certain", negForm := "uncertain"
  , posComparison := .periphrastic "more certain" "most certain"
  , negComparison := .periphrastic "more uncertain" "most uncertain" }

abbrev certain := confidence.pos

abbrev uncertain := confidence.neg

def sureness : AntonymPair :=
  { dimension := .confidence, relation := .contrary, posForm := "sure", negForm := "unsure"
  , posComparison := .synthetic "surer" "surest"
  , negComparison := .periphrastic "more unsure" "most unsure" }

abbrev sure := sureness.pos

abbrev unsure := sureness.neg

def doubtful : GradableAdjective :=
  { form := "doubtful", polarity := .negative, dimension := some .confidence
  , comparison := .periphrastic "more doubtful" "most doubtful" }

/-! ## Evaluative adjectives -/

/-- "good" — open value scale, contrary to "bad". "good" takes a contextual
    standard and patterns with relative adjectives ([beltrama-2025] §3); on the
    open `.value` scale this class is *derived* (open ⇒ contextual) rather than
    stipulated, so no `standardOverride` is needed. -/
def value : AntonymPair :=
  { dimension := .value, relation := .contrary, posForm := "good", negForm := "bad"
  , posComparison := .suppletive "better" "best", negComparison := .suppletive "worse" "worst"
  , evaluativeValence := some .positive }

abbrev good := value.pos

abbrev bad := value.neg

def beauty : AntonymPair :=
  { dimension := .beauty, relation := .contrary, posForm := "beautiful", negForm := "ugly"
  , evaluativeValence := some .positive }

abbrev beautiful := beauty.pos

abbrev ugly := beauty.neg

def important : GradableAdjective :=
  { form := "important", dimension := some .importance }

/-- *completely safe* but *??completely dangerous*: an upper-closed scale
([kennedy-mcnally-2005] (27c)). -/
def safety : AntonymPair :=
  { dimension := .safety, relation := .contradictory, posForm := "safe", negForm := "dangerous"
  , evaluativeValence := some .positive }

abbrev safe := safety.pos

abbrev dangerous := safety.neg

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
def cracked : GradableAdjective :=
  { form := "cracked", dimension := some .cracking, standardOverride := some .minEndpoint }

/-- "dented" — closed scale.
    Deverbal adjective from *dent*. Accepts *more dented*, *completely dented*,
    *badly dented* ([tham-2025] (11a), (20b)). -/
def dented : GradableAdjective :=
  { form := "dented", dimension := some .denting, standardOverride := some .minEndpoint }

/-- "scratched" — closed scale.
    Deverbal adjective from *scratch*. Accepts *more scratched*, *completely
    scratched*, *badly scratched* ([tham-2025] (11b), (20c)). -/
def scratched : GradableAdjective :=
  { form := "scratched", dimension := some .scratching, standardOverride := some .minEndpoint }

/-- "shattered" — closed scale, NON-GRADABLE.
    Deverbal adjective from *shatter* (Levin 45.1 Break verbs).
    Contrast: ??*more shattered*, punctual verb, no durative reading.
    Not a physical disturbance predicate ([tham-2025] (12c)). -/
def shattered : GradableAdjective :=
  { form := "shattered" }

/-! ## Mildly positive adjectives (MPAs)

[beltrama-2025]: MPAs encode a necessity standard — the minimum value
required for pursuit. They share properties with both relative (context-sensitive,
gradable) and absolute (no zone of indifference, crisp judgments, *barely*
compatible) predicates. -/

/-- "nice" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *nicely*. -/
def nice : GradableAdjective :=
  { form := "nice", dimension := some .value, evaluativeValence := some .positive }

/-- "pleasant" — open scale, positive evaluative ([nouwen-2024]).
    Base for M-degree intensifier *pleasantly*. -/
def pleasantness : AntonymPair :=
  { dimension := .value, relation := .contrary, posForm := "pleasant", negForm := "unpleasant"
  , evaluativeValence := some .positive }

abbrev pleasant := pleasantness.pos

abbrev unpleasant := pleasantness.neg

/-- "decent" — a mildly-positive adjective: open `.value` scale with a functional
    (necessity) standard ([beltrama-2025]), recorded via `standardOverride`. -/
def decent : GradableAdjective :=
  { form := "decent", dimension := some .value, evaluativeValence := some .positive
  , standardOverride := some .necessity }

/-- "acceptable" — mildly-positive adjective; open `.value` scale, functional
    standard ([beltrama-2025]). Deverbal *-able* form: the modal suffix
    contributes the functional standard. -/
def acceptable : GradableAdjective :=
  { form := "acceptable", dimension := some .value, evaluativeValence := some .positive
  , standardOverride := some .necessity }

/-- "adequate" — mildly-positive adjective; open `.value` scale, functional
    (necessity) standard ([beltrama-2025]). -/
def adequate : GradableAdjective :=
  { form := "adequate", dimension := some .value, evaluativeValence := some .positive
  , standardOverride := some .necessity }

/-! ## Deadjectival intensifier bases ([nouwen-2024])

Adjectival bases for deadjectival intensifiers. Evaluative adjectives
(horrible, wonderful) derive H-degree or M-degree intensifiers via the
Goldilocks effect. Mirative (unusual, surprising) and modal (possible,
impossible) bases follow Zwicky's generalization. -/

/-! ### Negative-evaluative bases: H-degree intensifiers -/

/-- "horrible" — open scale, negative evaluative. Base for H-degree *horribly*. -/
def horrible : GradableAdjective :=
  { form := "horrible", dimension := some .quality, evaluativeValence := some .negative }

/-- "terrible" — open scale, negative evaluative. Base for H-degree *terribly*. -/
def terrible : GradableAdjective :=
  { form := "terrible", dimension := some .quality, evaluativeValence := some .negative }

/-- "awful" — open scale, negative evaluative. Base for H-degree *awfully*. -/
def awful : GradableAdjective :=
  { form := "awful", dimension := some .quality, evaluativeValence := some .negative }

/-- "dreadful" — open scale, negative evaluative. Base for H-degree *dreadfully*. -/
def dreadful : GradableAdjective :=
  { form := "dreadful", dimension := some .quality, evaluativeValence := some .negative }

/-- "frightening" — open scale, negative evaluative. Base for H-degree *frighteningly*. -/
def frightening : GradableAdjective :=
  { form := "frightening", dimension := some .danger, evaluativeValence := some .negative }

/-- "disgusting" — open scale, negative evaluative. Base for H-degree *disgustingly*. -/
def disgusting : GradableAdjective :=
  { form := "disgusting", dimension := some .quality, evaluativeValence := some .negative }

/-- "annoying" — open scale, negative evaluative. Base for H-degree *annoyingly*. -/
def annoying : GradableAdjective :=
  { form := "annoying", dimension := some .quality, evaluativeValence := some .negative }

/-- "scary" — open scale, negative evaluative. Base for H-degree *scarily*. -/
def scary : GradableAdjective :=
  { form := "scary", dimension := some .danger, evaluativeValence := some .negative }

/-! ### Positive-evaluative bases: M-degree intensifiers -/

/-- "wonderful" — open scale, positive evaluative. Base for M-degree *wonderfully*. -/
def wonderful : GradableAdjective :=
  { form := "wonderful", dimension := some .quality, evaluativeValence := some .positive }

/-- "delightful" — open scale, positive evaluative. Base for M-degree *delightfully*. -/
def delightful : GradableAdjective :=
  { form := "delightful", dimension := some .quality, evaluativeValence := some .positive }

/-- "gorgeous" — open scale, positive evaluative. Base for M-degree *gorgeously*. -/
def gorgeous : GradableAdjective :=
  { form := "gorgeous", dimension := some .beauty, evaluativeValence := some .positive }

/-! ### Mirative bases: H-degree intensifiers, not evaluative -/

def expectation : AntonymPair :=
  { dimension := .expectation, relation := .contrary, posForm := "usual", negForm := "unusual"
  , evaluativeValence := some .neutral }

abbrev usual := expectation.pos

abbrev unusual := expectation.neg

/-- "surprising" — open scale, neutral (mirative). Base for H-degree *surprisingly*. -/
def surprising : GradableAdjective :=
  { form := "surprising", dimension := some .expectation, evaluativeValence := some .neutral }

/-- "remarkable" — open scale, positive evaluative (§2.4.1). Extreme positive
    evaluation: H-degree *remarkably* despite positive valence (Goldilocks exception). -/
def remarkable : GradableAdjective :=
  { form := "remarkable", dimension := some .quality, evaluativeValence := some .positive }

/-- "stunning" — open scale, positive evaluative (Figure 2, upper-right quadrant).
    Extreme positive evaluation: H-degree *stunningly* (Goldilocks exception). -/
def stunning : GradableAdjective :=
  { form := "stunning", dimension := some .quality, evaluativeValence := some .positive }

/-! ### Modal bases: Zwicky's generalization -/

/-- "expected" — open scale, neutral (modal). Unattested as intensifier (*expectedly). -/
def expected : GradableAdjective :=
  { form := "expected", dimension := some .expectation, evaluativeValence := some .neutral }

def possibility : AntonymPair :=
  { dimension := .possibility, relation := .contradictory, posForm := "possible"
  , negForm := "impossible", evaluativeValence := some .neutral }

abbrev possible := possibility.pos

abbrev impossible := possibility.neg

/-! ### Inventory -/

/-- The antonym pairs of the fragment. -/
def pairs : List AntonymPair := [
  height, happiness, fullness, heat, cost, wetness, cleanliness, straightness, openness,
  smoothness, hardness, life, size, extremeSize, pristineness, warmth, weight, thickness, depth,
  strength, speed, age, brightness, volume, confidence, sureness, value, beauty, pleasantness,
  expectation, possibility, safety]

/-- The entries outside an antonym pair. -/
def singletons : List GradableAdjective := [
  high, sad, flat, shut, free_, loose, tight, pure_, pregnant, long, wide, smart, confident,
  doubtful, important, cracked, dented, scratched, shattered, nice, decent,
  acceptable, adequate, horrible, terrible, awful, dreadful, frightening, disgusting, annoying,
  scary, wonderful, delightful, gorgeous, surprising, remarkable, stunning, expected]

/-- Every entry of the fragment. -/
def allEntries : List GradableAdjective :=
  pairs.flatMap (fun p ↦ [p.pos, p.neg]) ++ singletons

/-- The entry with a given surface form. -/
def lookup (form : String) : Option GradableAdjective :=
  allEntries.find? (·.form == form)

end English.Adjectives
