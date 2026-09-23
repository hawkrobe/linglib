module

public import Linglib.Semantics.Polarity.Marking
public import Linglib.Semantics.Polarity.Sentence
public import Linglib.Fragments.Dutch.Particles
public import Linglib.Fragments.German.PolarityMarking
public import Linglib.Data.Examples.TurcoBraunDimroth2014

/-!
# Turco, Braun and Dimroth (2014): When Contrasting Polarity, the Dutch Use Particles, Germans Intonation

This file formalizes [turco-braun-dimroth-2014], a production study of how Dutch and German
mark a switch from a negative to a positive polarity in two discourse contexts. A polarity
contrast, (1), asserts the positive claim of a different topic situation, in the sense of
[klein-2008], than the negative claim, so the two claims are compatible; a polarity correction,
(2), asserts it of the same topic situation, so the two claims exclude each other, the contrast
and correction of [umbach-2004]: `Sentence`, `Switch`, `IsContrast`, `IsCorrection`,
`Switch.disjoint_iff`, `IsCorrection.disjoint`, `exists_isContrast_not_disjoint`. In both
contexts German speakers produced Verum focus, a high-falling pitch accent on the finite verb,
[hohle-1992], and never a sentence-internal affirmative particle, whereas Dutch speakers mostly
produced the accented affirmative particle *wel*, the entries `German.PolarityMarking.verumFocus`
and `Dutch.Particles.wel`. The paper's theoretical claim is that the two devices, though
functionally equivalent, operate on different levels: a sentence contains a polarity operator
and, above it, an assertion operator carried by the finite verb; *wel* is the overt affirmative
value of the polarity operator, the counterpart of *niet*, [sudhoff-2012], whereas Verum focus
highlights the assertion operator, `PolarityOperator`, `Sentence.verumFocus`, `Level`,
`strategyLevel`. Truth conditions do not depend on Verum focus or on whether affirmation is
overt, `denotation_verumFocus` and `denotation_affirmation`, the functional equivalence; Verum
focus but not *wel* can occur in a negated sentence, `exists_verumFocus_negative` and
`pol_of_affirmation`, which is why the assertion operator takes effect above polarity, as in
[bluhdorn-2012].

## Implementation notes

The polarity operator is a single slot of the sentence, so a sentence with the affirmative
particle is positive by construction and *Het kind heeft wel niet gehuild* is not a `Sentence`.
The production results are not formalized. Dutch speakers used *wel* in most utterances of both
contexts, fewer in correction, an effect the paper leaves unexplained, and Verum focus never in
contrast and rarely in correction; German speakers used Verum focus in more than two thirds of
the utterances of both contexts, never a sentence-internal particle, and *doch* as a separate
utterance before a Verum focus utterance in correction only, the entry
`German.PolarityMarking.dochPreUtterance`. *Wel* was mostly accented, as a downstepped fall in
contrast and as a fall in correction, and the pitch range of German Verum focus was larger in
correction than in contrast; the paper attributes the greater prominence of correction either to
the strength of undoing a denial, [hogeweg-2009], or to the absence of a contrastive topic accent
before the comment. The examples are the rows of `Data.Examples.TurcoBraunDimroth2014`.

## References

* [turco-braun-dimroth-2014]
* [umbach-2004]
* [klein-2008]
* [hohle-1992]
* [sudhoff-2012]
* [bluhdorn-2012]
* [hogeweg-2009]
* [dimroth-etal-2010]
-/

@[expose] public section

namespace TurcoBraunDimroth2014

open Polarity.Marking

/-! ### The polarity operator and the assertion operator -/

/-- The value of a sentence's polarity operator: negation, an overt affirmative particle such
as Dutch *wel*, or the unmarked default affirmation. -/
inductive PolarityOperator where
  | negation
  | affirmation
  | unmarked
  deriving DecidableEq, Repr

/-- The polarity a polarity operator expresses. -/
def PolarityOperator.value : PolarityOperator → SentencePolarity
  | .negation => .negative
  | .affirmation | .unmarked => .positive

/-- A sentence predicates a descriptive property, given per topic situation as the set of worlds
where it holds there, of a topic situation, through a polarity operator and, above it, the
assertion operator carried by the finite verb, which Verum focus accents. -/
structure Sentence (S W : Type*) where
  property : S → Set W
  situation : S
  polarityOp : PolarityOperator
  verumFocus : Bool

variable {S W : Type*}

namespace Sentence

/-- The polarity of a sentence, the value of its polarity operator. -/
def pol (s : Sentence S W) : SentencePolarity := s.polarityOp.value

/-- The proposition a sentence asserts. -/
def denotation (s : Sentence S W) : Set W :=
  match s.pol with
  | .positive => s.property s.situation
  | .negative => (s.property s.situation)ᶜ

/-- Accenting the assertion operator leaves the truth conditions unchanged. -/
theorem denotation_verumFocus (s : Sentence S W) (b : Bool) :
    { s with verumFocus := b }.denotation = s.denotation := rfl

/-- An overt affirmative particle leaves the truth conditions of the unmarked affirmative
sentence unchanged: *wel* and Verum focus are functionally equivalent on a positive sentence. -/
theorem denotation_affirmation (s : Sentence S W) :
    { s with polarityOp := .affirmation }.denotation =
      { s with polarityOp := .unmarked }.denotation := rfl

/-- A sentence with an affirmative particle is positive: the particle is the polarity
operator, so it cannot occur in a negated sentence. -/
theorem pol_of_affirmation {s : Sentence S W} (h : s.polarityOp = .affirmation) :
    s.pol = .positive := by
  simp only [pol, h, PolarityOperator.value]

/-- Verum focus can occur in a negated sentence, *Das Kind HAT nicht geweint*. -/
theorem exists_verumFocus_negative [Nonempty S] :
    ∃ s : Sentence S W, s.verumFocus = true ∧ s.pol = .negative :=
  ⟨⟨λ _ => ∅, Classical.arbitrary S, .negation, true⟩, rfl, rfl⟩

end Sentence

/-- The two levels of meaning at which a polarity-marking device operates. -/
inductive Level where
  | polarity
  | assertion
  deriving DecidableEq, Repr

/-- The level of a marking strategy: affirmative and polarity-reversing particles are values of
the polarity operator, Verum focus highlights the assertion operator. -/
def strategyLevel : Strategy → Option Level
  | .particle | .polarityReversal => some .polarity
  | .verumFocus => some .assertion
  | .other | .unmarked => none

/-- Dutch *wel* and German Verum focus operate at different levels. -/
theorem strategyLevel_wel_ne_verumFocus :
    strategyLevel Dutch.Particles.wel.strategy ≠
      strategyLevel German.PolarityMarking.verumFocus.strategy := by
  decide

/-! ### Polarity contrast and polarity correction -/

/-- A polarity switch from `a` to `b`: a negative claim followed by a positive claim of the same
descriptive property. -/
def Switch (a b : Sentence S W) : Prop :=
  a.property = b.property ∧ a.pol = .negative ∧ b.pol = .positive

/-- A polarity contrast: a switch between claims about different topic situations. -/
def IsContrast (a b : Sentence S W) : Prop := Switch a b ∧ a.situation ≠ b.situation

/-- A polarity correction: a switch between claims about the same topic situation. -/
def IsCorrection (a b : Sentence S W) : Prop := Switch a b ∧ a.situation = b.situation

/-- The claims of a switch exclude each other exactly when the property's holding of the second
topic situation entails its holding of the first. -/
theorem Switch.disjoint_iff {a b : Sentence S W} (h : Switch a b) :
    Disjoint a.denotation b.denotation ↔ b.property b.situation ⊆ a.property a.situation := by
  obtain ⟨hP, ha, hb⟩ := h
  simp only [Sentence.denotation, ha, hb, hP, Set.disjoint_compl_left_iff_subset]

/-- The claims of a correction exclude each other. -/
theorem IsCorrection.disjoint {a b : Sentence S W} (h : IsCorrection a b) :
    Disjoint a.denotation b.denotation :=
  h.1.disjoint_iff.2 (by rw [h.1.1, h.2])

/-- The claims of a contrast need not exclude each other: any two topic situations carry a
contrast whose claims are jointly true. -/
theorem exists_isContrast_not_disjoint [Nonempty W] {s₁ s₂ : S} (h : s₁ ≠ s₂) :
    ∃ a b : Sentence S W, IsContrast a b ∧ ¬ Disjoint a.denotation b.denotation := by
  refine ⟨⟨λ s => {_w | s = s₂}, s₁, .negation, false⟩,
    ⟨λ s => {_w | s = s₂}, s₂, .unmarked, false⟩, ⟨⟨rfl, rfl, rfl⟩, h⟩, ?_⟩
  exact Set.not_disjoint_iff.2 ⟨Classical.arbitrary W, h, rfl⟩

end TurcoBraunDimroth2014
