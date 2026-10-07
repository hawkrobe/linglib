module

public import Mathlib.Data.Finset.Prod
public import Linglib.Semantics.Degree.Antonymy
public import Linglib.Pragmatics.Bidirectional

/-!
# Krifka (2007): Negated Antonyms: Creating and Filling the Gap

Krifka accounts for antonym quadruplets such as *happy*, *not happy*, *unhappy*, *not unhappy*,
and in particular for the double negative, which reports a mild state of happiness rather than
the middle ground that Horn's contrary analysis of antonyms predicts. The border between an
antonym pair is sharp but its location is not fixed, as on Williamson's epistemic view of
vagueness; the pair exhausts its scale, so *happy* and *unhappy* are literally contradictories;
and the M principle reserves the more complex of two equivalent expressions for the
non-stereotypical cases. Speakers use the simple forms only where every admissible border agrees,
which opens the gap, and the complex forms where the simple form is true at the speaker's border
but not safely usable, which fills it. The M principle is derived within Blutner's bidirectional
optimality theory on McCawley's *kill* example, and the same evaluation over the quadruplet
yields Krifka's assignment.

## Main statements

* `marked_both`: between two admissible borders a degree is *not unhappy* for one speaker and
  *not happy* for another, so the two have no fixed border between them.
* `superoptimal_mccawley`: weak optimality pairs *kill* with direct and *cause to die* with
  indirect killing.

## Implementation notes

* Literal meanings are the substrate's single-threshold `AntonymForm.contradictoryDenotation`;
  the admissible borders form a set of thresholds on a linear order, and the diagrams are read
  relative to a speaker's border within that set.
* Bidirectional evaluation is the substrate's `superoptimal`, the weak optimality of (14).
  The quadruplet game is built from the literal semantics (a form and a region on the same
  side of the border), form complexity (`AntonymForm.complexity`) and the markedness of the
  border regions.
* The other uses of double negatives the paper sets aside (denial, irony, amplification) and
  the local strengthening of *neither happy nor unhappy* are not formalized.

## References

* [krifka-2007b]
* [horn-1989]
* [horn-1984]
* [williamson-1994]
* [levinson-2000]
* [blutner-2000]
* [mccawley-1978]
-/

@[expose] public section

namespace Krifka2007b

open Degree BidirectionalOT

variable {D : Type*} [LinearOrder D]

/-! ### Safe and marked uses -/

/-- The simpler form with the same literal meaning is *happy* for *not unhappy* and *unhappy*
for *not happy*. -/
def simple : AntonymForm → AntonymForm
  | .notNegative => .positive
  | .notPositive => .negative
  | f => f

/-- At a border `θ` antonyms literally denote contradictories (16). -/
abbrev literal (θ : D) (f : AntonymForm) : Set D := AntonymForm.contradictoryDenotation θ f

/-- A use is safe (18) when it is true under every admissible border, so that speaker and
addressee agree on it whichever border they set. -/
def Safe (Θ : Set D) (f : AntonymForm) (d : D) : Prop := ∀ θ ∈ Θ, d ∈ literal θ f

/-- A use of a complex form is marked ((19), (20)) when it is literally true at the speaker's
border, where the simpler form with the same literal meaning is not safe. -/
def Marked (Θ : Set D) (θ : D) (f : AntonymForm) (d : D) : Prop :=
  d ∈ literal θ f ∧ ¬ Safe Θ (simple f) d

variable {Θ : Set D} {θ θ₁ θ₂ d d₁ d₂ : D}

/-- The literal meanings exhaust the scale, so *neither happy nor unhappy* (21) is a
contradiction, and an unconditional over the pair (22) covers everyone. -/
theorem literal_positive_or_negative (θ d : D) :
    d ∈ literal θ .positive ∨ d ∈ literal θ .negative :=
  lt_or_ge θ d

/-- Two admissible borders open a gap, since a degree between them is safely neither *happy* nor
*unhappy*, which is how *neither happy nor unhappy* comes to be sayable. -/
theorem not_safe_of_between (h₂ : θ₂ ∈ Θ) (h₁ : θ₁ ∈ Θ) (hd : θ₁ < d) (hd' : d ≤ θ₂) :
    ¬ Safe Θ .positive d ∧ ¬ Safe Θ .negative d :=
  ⟨fun h ↦ absurd (h θ₂ h₂) (not_lt.2 hd'), fun h ↦ absurd (h θ₁ h₁) (not_le.2 hd)⟩

/-- A marked *not unhappy* is a mild state of happiness ((3), (19)), happy at the speaker's
border but not safely so. -/
theorem marked_notNegative_iff : Marked Θ θ .notNegative d ↔ θ < d ∧ ∃ θ' ∈ Θ, d ≤ θ' := by
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun ⟨θ', hθ', hle⟩ h ↦ absurd (h θ' hθ') (not_lt.2 hle)⟩
  by_contra hn
  exact h fun θ' hθ' ↦ lt_of_not_ge fun hle ↦ hn ⟨θ', hθ', hle⟩

/-- A marked *not happy* is a mild state of unhappiness ((9), (20)), unhappy at the speaker's
border but not safely so. -/
theorem marked_notPositive_iff : Marked Θ θ .notPositive d ↔ d ≤ θ ∧ ∃ θ' ∈ Θ, θ' < d := by
  refine and_congr Iff.rfl ⟨fun h ↦ ?_, fun ⟨θ', hθ', hlt⟩ h ↦ absurd (h θ' hθ') (not_le.2 hlt)⟩
  by_contra hn
  exact h fun θ' hθ' ↦ le_of_not_gt fun hlt ↦ hn ⟨θ', hθ', hlt⟩

/-- At a given border, *not unhappy* reports higher states than *not happy* (20). -/
theorem lt_of_marked (h₁ : Marked Θ θ .notPositive d₁) (h₂ : Marked Θ θ .notNegative d₂) :
    d₁ < d₂ :=
  lt_of_le_of_lt h₁.1 h₂.1

/-- Between two admissible borders a degree is *not unhappy* for a speaker with the lower
border and *not happy* for one with the higher, so the two expressions are not exhaustive and
have no fixed border between them (20). -/
theorem marked_both (h₁ : θ₁ ∈ Θ) (h₂ : θ₂ ∈ Θ) (hlt : θ₁ < θ₂) :
    Marked Θ θ₁ .notNegative θ₂ ∧ Marked Θ θ₂ .notPositive θ₂ :=
  ⟨marked_notNegative_iff.2 ⟨hlt, θ₂, h₂, le_rfl⟩, marked_notPositive_iff.2 ⟨le_rfl, θ₁, h₁, hlt⟩⟩

/-! ### The M principle in bidirectional optimality theory -/

/-- The two forms of (13). -/
inductive Form
  | killed
  | causedToDie
  deriving DecidableEq, Repr

/-- The two interpretations of (13). -/
inductive Interp
  | direct
  | indirect
  deriving DecidableEq, Repr

/-- The four form-interpretation pairs of (13). -/
def mccawleyPairs : Finset (Form × Interp) :=
  {(.killed, .direct), (.killed, .indirect), (.causedToDie, .direct), (.causedToDie, .indirect)}

/-- The preference for the simpler form. -/
def formCost : Form × Interp → ℕ
  | (.killed, _) => 0
  | (.causedToDie, _) => 1

/-- The preference for the stereotypical interpretation. -/
def interpCost : Form × Interp → ℕ
  | (_, .direct) => 0
  | (_, .indirect) => 1

/-- Under weak optimality ((14), (15)) *kill* pairs with direct killing and *cause to die* with
indirect killing, the M principle. -/
theorem superoptimal_mccawley :
    superoptimal mccawleyPairs (profile [formCost, interpCost]) =
      {(.killed, .direct), (.causedToDie, .indirect)} := by
  decide

/-- After strengthening ((18)–(20)) the scale divides into the regions safely happy, mildly
happy, mildly unhappy and safely unhappy. -/
inductive Region
  | positive
  | plateauHigh
  | plateauLow
  | negative
  deriving DecidableEq, Repr

/-- Mirror image of a region under the polarity flip. -/
def Region.flip : Region → Region
  | .positive => .negative
  | .negative => .positive
  | .plateauHigh => .plateauLow
  | .plateauLow => .plateauHigh

@[simp] theorem Region.flip_flip (r : Region) : r.flip.flip = r := by cases r <;> rfl

/-- The regions above the border. -/
def Region.above : Region → Bool
  | .positive | .plateauHigh => true
  | .plateauLow | .negative => false

/-- The border regions are the non-stereotypical interpretations. -/
def Region.markedness : Region → ℕ
  | .plateauHigh | .plateauLow => 1
  | .positive | .negative => 0

/-- The forms literally true above the border (16). -/
def formAbove : AntonymForm → Bool
  | .positive | .notNegative => true
  | .notPositive | .negative => false

/-- The literal semantics admits the pairs of a form and a region on the same side of the
border. -/
def quadrupletPairs : Finset (AntonymForm × Region) :=
  ([.positive, .notPositive, .negative, .notNegative].toFinset ×ˢ
      [.positive, .plateauHigh, .plateauLow, .negative].toFinset).filter
    fun p ↦ formAbove p.1 = p.2.above

/-- Krifka's assignment gives the simple forms the safe regions and the complex forms the border
regions on their side. -/
def krifkaQuadruplet : Finset (AntonymForm × Region) :=
  {(.positive, .positive), (.notNegative, .plateauHigh),
    (.negative, .negative), (.notPositive, .plateauLow)}

/-- Weak optimality over the quadruplet, with markedness and form complexity in either order,
yields Krifka's assignment. -/
theorem superoptimal_quadruplet :
    superoptimal quadrupletPairs (profile [(·.2.markedness), (·.1.complexity)]) =
        krifkaQuadruplet ∧
      superoptimal quadrupletPairs (profile [(·.1.complexity), (·.2.markedness)]) =
        krifkaQuadruplet := by
  decide

end Krifka2007b
