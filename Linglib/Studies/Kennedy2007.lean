import Linglib.Semantics.Degree.Adjective
import Linglib.Semantics.Degree.Basic
import Linglib.Fragments.English.Predicates.Adjectival

/-!
# Kennedy 2007: relative and absolute gradable adjectives

The positive form of a gradable adjective is true of what *stands out* relative to the kind of
measurement the adjective encodes: `⟦pos⟧ = λg λx. g(x) ≥ s(g)` (27), with the standard `s`
fixed by the scale rather than by a comparison class (§2). Relative adjectives (*tall*, *long*)
take a contextual standard; absolute adjectives take an endpoint, minimum (*wet*, *bent*) or
maximum (*full*, *dry*) (§3.1). Four diagnostics separate the two (§3.2): definite descriptions
pick out the one object that stands out only for relative adjectives; the Sorites second premise
is judged false for absolutes; comparatives entail the positive form for absolutes, in the
direction the standard fixes, and not at all for relatives; and maximizers and minimizers
distribute by the endpoints of the adjective's scale, the antonym using the same scale with the
ends exchanged (61). Interpretive Economy (66) derives the standard from scale structure: an
endpoint standard is available exactly where the scale has that endpoint, and a totally closed
scale admits both (67)–(68).

[kennedy-mcnally-2005] [rotstein-winter-2004]

## References

* [kennedy-2007]
-/

namespace Kennedy2007

open Degree

variable {Entity D : Type*} [LinearOrder D]

/-! ### The positive form (§2.3, §3.1) -/

/-- Minimum-standard absolute: *x is wet* iff its degree is above the scale minimum. -/
def MinStandardPos [OrderBot D] (μ : Entity → D) (x : Entity) : Prop := ⊥ < μ x

/-- Maximum-standard absolute: *x is dry* iff its degree is the scale maximum. -/
def MaxStandardPos [OrderTop D] (μ : Entity → D) (x : Entity) : Prop := μ x = ⊤

/-- Relative: *x is long* iff its degree exceeds a contextual threshold. -/
def RelativePos (μ : Entity → D) (θ : D) (x : Entity) : Prop := θ < μ x

/-! ### Definite descriptions (§3.2, (53)–(54)) -/

/-- *The long one*: two objects of different length can always be told apart by a contextual
standard, so the definite description succeeds. -/
theorem exists_relativePos_of_lt (μ : Entity → D) {a b : Entity} (h : μ b < μ a) :
    ∃ θ, RelativePos μ θ a ∧ ¬ RelativePos μ θ b :=
  ⟨μ b, h, lt_irrefl _⟩

/-- *The full one* (54): a maximum-standard adjective tells two objects apart only when one is
at the maximum and the other is not — two partially full jars leave nothing to pick out. -/
theorem maxStandardPos_and_not_iff [OrderTop D] (μ : Entity → D) (a b : Entity) :
    MaxStandardPos μ a ∧ ¬ MaxStandardPos μ b ↔ μ a = ⊤ ∧ μ b ≠ ⊤ :=
  Iff.rfl

/-! ### The Sorites second premise (§3.2, (57)–(58)) -/

/-- (57): a theater with one fewer occupied seat than a full one is not full — any degree
below the maximum fails a maximum standard. -/
theorem not_maxStandardPos_of_lt_top [OrderTop D] {μ : Entity → D} {x : Entity}
    (h : μ x < ⊤) : ¬ MaxStandardPos μ x :=
  h.ne

/-- (58): a rod with no bend is not bent — exactly the minimum fails a minimum standard. -/
theorem not_minStandardPos_iff [OrderBot D] (μ : Entity → D) (x : Entity) :
    ¬ MinStandardPos μ x ↔ μ x = ⊥ :=
  not_lt.trans le_bot_iff

/-! ### Comparatives (§3.2, (49)–(52)) -/

/-- (49): *the floor is wetter than the countertop* entails *the floor is wet*. -/
theorem minStandardPos_of_comparative [OrderBot D] {μ : Entity → D} {a b : Entity}
    (h : comparativeSem μ a b .positive) : MinStandardPos μ a :=
  bot_le.trans_lt h

/-- (50): *the floor is drier than the countertop* entails *the countertop is not dry*. -/
theorem not_maxStandardPos_of_comparative [OrderTop D] {μ : Entity → D} {a b : Entity}
    (h : comparativeSem μ a b .positive) : ¬ MaxStandardPos μ b :=
  not_maxStandardPos_of_lt_top (h.trans_le le_top)

/-- (51): *rod A is longer than rod B* entails neither that A is long nor that it is not. -/
theorem relativePos_undetermined_of_comparative (μ : Entity → D) {a b : Entity}
    (h : comparativeSem μ a b .positive) :
    (∃ θ, RelativePos μ θ a) ∧ ∃ θ, ¬ RelativePos μ θ a :=
  ⟨⟨μ b, h⟩, μ a, lt_irrefl _⟩

/-! ### Degree modifiers (§3.2, (61)) -/

/-- Maximizers (*completely*, *fully*) and minimizers (*slightly*, *partially*). -/
inductive DegreeModifier
  | maximizer
  | minimizer
  deriving DecidableEq

/-- A modifier is licensed on a scale that has the endpoint it picks out. -/
def Licenses : DegreeModifier → Boundedness → Prop
  | .maximizer, b => b.HasMax
  | .minimizer, b => b.HasMin

instance : ∀ (m : DegreeModifier) (b : Boundedness), Decidable (Licenses m b)
  | .maximizer, b => inferInstanceAs (Decidable b.HasMax)
  | .minimizer, b => inferInstanceAs (Decidable b.HasMin)

/-- Table (61) as printed: whether a maximizer or minimizer is acceptable with the positive or
negative member of an antonym pair, by the pair's scale type. -/
def table61 : ScalePolarity → Boundedness → DegreeModifier → Bool
  | .positive, .open_, _ => false
  | .positive, .lowerBounded, .maximizer => false
  | .positive, .lowerBounded, .minimizer => true
  | .positive, .upperBounded, .maximizer => true
  | .positive, .upperBounded, .minimizer => false
  | .positive, .closed, _ => true
  | .negative, .open_, _ => false
  | .negative, .lowerBounded, .maximizer => true
  | .negative, .lowerBounded, .minimizer => false
  | .negative, .upperBounded, .maximizer => false
  | .negative, .upperBounded, .minimizer => true
  | .negative, .closed, _ => true

/-- Every cell of (61) is the endpoint structure of the adjective's own scale. -/
theorem table61_iff_licenses (p : ScalePolarity) (b : Boundedness) (m : DegreeModifier) :
    table61 p b m = true ↔ Licenses m (b.ofPolarity p) := by
  cases p <;> cases b <;> cases m <;> decide

open English.Predicates.Adjectival in
/-- The Fragment's antonym pairs fill (61): *completely full/empty*, *slightly wet* but
*??completely wet*, *completely dry* but *??slightly dry*, *slightly bent* but *??fully bent*,
*fully straight*, and nothing on the open height scale. -/
theorem fragment_pairs_table61 :
    Licenses .maximizer full.scaleType ∧ Licenses .maximizer empty.scaleType ∧
    Licenses .minimizer wet.scaleType ∧ ¬ Licenses .maximizer wet.scaleType ∧
    Licenses .maximizer dry.scaleType ∧ ¬ Licenses .minimizer dry.scaleType ∧
    Licenses .minimizer bent.scaleType ∧ ¬ Licenses .maximizer bent.scaleType ∧
    Licenses .maximizer straight.scaleType ∧
    ¬ Licenses .maximizer tall.scaleType ∧ ¬ Licenses .minimizer short.scaleType := by
  decide

/-! ### Interpretive Economy (§4.2–§4.3) -/

/-- An open scale offers no endpoint, so its standard is contextual and the adjective needs a
comparison class. -/
theorem open_requires_comparison_class :
    Boundedness.IsRelative .open_ :=
  trivial

/-- A totally closed scale is interpretively variable: both endpoint standards are admitted
((67)–(68), *opaque/transparent*, *open/exposed*); the maximum is only the default. -/
theorem closed_admits_both_endpoints :
    Boundedness.closed.Admits .minEndpoint ∧ Boundedness.closed.Admits .maxEndpoint :=
  ⟨trivial, trivial⟩

end Kennedy2007
