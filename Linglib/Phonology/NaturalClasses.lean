import Linglib.Phonology.Features

/-!
# Natural-Class Predicates on Segments

Language-neutral natural-class membership predicates over `Phonology.Segment`,
defined by the SPE feature decompositions standard since [chomsky-halle-1968]
and codified in textbook form by [hayes-2009] Table 4.1 (sonority hierarchy
columns).

These predicates are pure substrate: they project information already encoded
in a segment's feature bundle. Per-language Fragment files (e.g.
`Fragments/Latin/Phonology.lean`, `Fragments/English/Phonology.lean`) consume
them rather than redefining the same definitions locally.

## Main declarations

* `Segment.IsVowel` — [+syllabic]
* `Segment.IsConsonant` — [+consonantal]
* `Segment.IsStop` — [+cons, -son, -cont]
* `Segment.IsFricative` — [+cons, -son, +cont]
* `Segment.IsNasal` — [+nasal]
* `Segment.IsLiquid` — [+cons, +son] and one of [+lateral], [+trill], [+tap]
* `Segment.IsGlide` — [-cons, -syllabic, +approximant]

## Implementation notes

Each predicate is a `Prop` (not `Bool`) following the project Bool→Prop
discipline. `Decidable` instances are derived via `by unfold; infer_instance`
so consumers can use `decide` on universally-quantified statements over
finite segment lists.

The liquid decomposition uses the disjunction [+lateral] ∨ [+trill] ∨ [+tap]
to admit both the alveolar lateral /l/, the trilled /r/ of Latin and Spanish,
and the flapped /ɾ/ of Japanese/American English under a single class. A
language that wants to refine the class (e.g. only [+lateral, -trill]) can
add a stricter local predicate; this one stays at the textbook level.
-/

namespace Phonology

/-! ### Major classes -/

/-- A segment is a vowel iff it is [+syllabic]. -/
def Segment.IsVowel (s : Segment) : Prop := s.HasValue .syllabic true

instance (s : Segment) : Decidable s.IsVowel := by
  unfold Segment.IsVowel; infer_instance

/-- A segment is a consonant iff it is [+consonantal]. -/
def Segment.IsConsonant (s : Segment) : Prop := s.HasValue .consonantal true

instance (s : Segment) : Decidable s.IsConsonant := by
  unfold Segment.IsConsonant; infer_instance

/-! ### Manner classes -/

/-- A segment is an oral stop iff it is [+cons, -son, -cont]. -/
def Segment.IsStop (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant false

instance (s : Segment) : Decidable s.IsStop := by
  unfold Segment.IsStop; infer_instance

/-- A segment is a fricative iff it is [+cons, -son, +cont]. -/
def Segment.IsFricative (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant false ∧
    s.HasValue .continuant true

instance (s : Segment) : Decidable s.IsFricative := by
  unfold Segment.IsFricative; infer_instance

/-- A segment is a nasal iff it is [+nasal]. -/
def Segment.IsNasal (s : Segment) : Prop := s.HasValue .nasal true

instance (s : Segment) : Decidable s.IsNasal := by
  unfold Segment.IsNasal; infer_instance

/-- A segment is a liquid iff it is [+cons, +son] and one of
[+lateral], [+trill], [+tap]. -/
def Segment.IsLiquid (s : Segment) : Prop :=
  s.HasValue .consonantal true ∧ s.HasValue .sonorant true ∧
    (s.HasValue .lateral true ∨ s.HasValue .trill true ∨ s.HasValue .tap true)

instance (s : Segment) : Decidable s.IsLiquid := by
  unfold Segment.IsLiquid; infer_instance

/-- A segment is a glide iff it is [-cons, -syllabic, +approximant]. -/
def Segment.IsGlide (s : Segment) : Prop :=
  s.HasValue .consonantal false ∧ s.HasValue .syllabic false ∧
    s.HasValue .approximant true

instance (s : Segment) : Decidable s.IsGlide := by
  unfold Segment.IsGlide; infer_instance

end Phonology
