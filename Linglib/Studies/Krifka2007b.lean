import Linglib.Semantics.Degree.Antonymy
import Linglib.Pragmatics.Superoptimal

/-!
# Krifka (2007): Negated Antonyms: Creating and Filling the Gap

This file formalizes [krifka-2007b]'s account of antonym quadruplets such as *happy*, *not
happy*, *unhappy*, *not unhappy*, and in particular of the double negative, which reports a
mild state of happiness rather than the middle ground between happiness and unhappiness that
the received contrary analysis of antonyms ([horn-1989]) predicts. The paper's three
hypotheses: the border between an antonym pair is sharp but its location is not fixed, the
epistemic view of vagueness of [williamson-1994]; the pair exhausts its scale, so *happy*
and *unhappy* are literally contradictories; and the M principle ([horn-1984],
[levinson-2000]), on which the more complex of two equivalent expressions is reserved for
the non-stereotypical cases. Speakers use the simple forms only where every admissible border
agrees (`Safe`), which opens the gap, and the complex forms where the simple form is
literally true at the speaker's border but not safely usable (`Marked`), which fills it: *not
happy* below the border and *not unhappy* above it, with no fixed border between the two
(`lt_of_marked`, `marked_both`). The M principle is derived within bidirectional optimality
theory ([blutner-2000]) on the two-form, two-interpretation example of [mccawley-1978], and
the same evaluation over the quadruplet's forms and regions yields Krifka's assignment
(`krifkaQuadruplet`).

## Implementation notes

* Literal meanings are the substrate's single-threshold `AntonymForm.contradictoryDenot`;
  the admissible borders form a finite set of thresholds, and the paper's diagrams are read
  relative to a speaker's border within that set.
* Bidirectional evaluation is the substrate's `superoptimal`, the weak optimality of (14).
  The quadruplet game is built from the literal semantics (a form and a region on the same
  side of the border), form complexity (`AntonymForm.complexity`) and the markedness of the
  border regions.
* The other uses of double negatives the paper sets aside (denial, irony, amplification) and
  the local strengthening of *neither happy nor unhappy* are not formalized.

## References

* [krifka-2007b]
* [horn-1989], [horn-1984] — the contrary analysis and the division of pragmatic labor
* [williamson-1994] — the epistemic theory of vagueness
* [levinson-2000] — the M principle
* [blutner-2000] — weak bidirectional optimality
* [mccawley-1978] — *kill* and *cause to die*
-/

namespace Krifka2007b

open Degree Pragmatics.Bidirectional

variable {max : ℕ}

/-! ### Safe and marked uses -/

/-- The simpler form with the same literal meaning: *happy* for *not unhappy* and *unhappy*
for *not happy*. -/
def simple : AntonymForm → AntonymForm
  | .notNegative => .positive
  | .notPositive => .negative
  | f => f

/-- The literal meaning at a border `θ`: antonyms are contradictories (16). -/
abbrev literal (θ : Threshold max) (f : AntonymForm) (d : Bounded max) : Prop :=
  AntonymForm.contradictoryDenot θ f d

/-- A safe use (18): true under every admissible border, so that speaker and addressee agree
on it whichever border they set. -/
def Safe (Θ : Finset (Threshold max)) (f : AntonymForm) (d : Bounded max) : Prop :=
  ∀ θ ∈ Θ, literal θ f d

/-- A marked use of a complex form ((19), (20)): literally true at the speaker's border, where
the simpler form with the same literal meaning is not safe. -/
def Marked (Θ : Finset (Threshold max)) (θ : Threshold max) (f : AntonymForm)
    (d : Bounded max) : Prop :=
  literal θ f d ∧ ¬ Safe Θ (simple f) d

variable {Θ : Finset (Threshold max)} {θ θ₁ θ₂ : Threshold max} {d d₁ d₂ : Bounded max}

/-- The literal meanings exhaust the scale: *neither happy nor unhappy* (21) is a
contradiction, and an unconditional over the pair (22) covers everyone. -/
theorem literal_positive_or_negative (θ : Threshold max) (d : Bounded max) :
    literal θ .positive d ∨ literal θ .negative d :=
  em _

/-- Two admissible borders open a gap: a degree between them is safely neither *happy* nor
*unhappy*, which is how *neither happy nor unhappy* comes to be sayable. -/
theorem not_safe_of_between (h₂ : θ₂ ∈ Θ) (h₁ : θ₁ ∈ Θ) (hd : (θ₁ : Bounded max) < d)
    (hd' : d ≤ θ₂) : ¬ Safe Θ .positive d ∧ ¬ Safe Θ .negative d :=
  ⟨λ h => absurd (h θ₂ h₂) (not_lt.2 hd'), λ h => h θ₁ h₁ hd⟩

/-- A marked *not unhappy* is a mild state of happiness ((3), (19)): happy at the speaker's
border, but not safely so. -/
theorem marked_notNegative_iff :
    Marked Θ θ .notNegative d ↔ (θ : Bounded max) < d ∧ ∃ θ' ∈ Θ, d ≤ θ' := by
  refine and_congr Iff.rfl ⟨λ h => ?_, λ ⟨θ', hθ', hle⟩ h => absurd (h θ' hθ') (not_lt.2 hle)⟩
  by_contra hn
  exact h λ θ' hθ' => lt_of_not_ge λ hle => hn ⟨θ', hθ', hle⟩

/-- A marked *not happy* is a mild state of unhappiness ((9), (20)): unhappy at the speaker's
border, but not safely so. -/
theorem marked_notPositive_iff :
    Marked Θ θ .notPositive d ↔ d ≤ θ ∧ ∃ θ' ∈ Θ, (θ' : Bounded max) < d := by
  refine and_congr (not_lt (a := (θ : Bounded max)) (b := d))
    ⟨λ h => ?_, λ ⟨θ', hθ', hlt⟩ h => h θ' hθ' hlt⟩
  by_contra hn
  exact h λ θ' hθ' hlt => hn ⟨θ', hθ', hlt⟩

/-- At a given border, *not unhappy* reports higher states than *not happy* (20). -/
theorem lt_of_marked (h₁ : Marked Θ θ .notPositive d₁) (h₂ : Marked Θ θ .notNegative d₂) :
    d₁ < d₂ :=
  lt_of_le_of_lt (not_lt.1 h₁.1) h₂.1

/-- Between two admissible borders a degree is *not unhappy* for a speaker with the lower
border and *not happy* for one with the higher: the two expressions are not exhaustive and
have no fixed border between them (20). -/
theorem marked_both (h₁ : θ₁ ∈ Θ) (h₂ : θ₂ ∈ Θ) (hlt : (θ₁ : Bounded max) < θ₂) :
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

/-- Weak optimality ((14), (15)): *kill* pairs with direct killing and *cause to die* with
indirect killing, the M principle. -/
theorem superoptimal_mccawley :
    superoptimal mccawleyPairs (profile [formCost, interpCost]) =
      {(.killed, .direct), (.causedToDie, .indirect)} := by
  decide

/-- The regions of the scale after strengthening ((18)–(20)): safely happy, mildly happy,
mildly unhappy, safely unhappy. -/
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

/-- The pairs the literal semantics admits: a form and a region on the same side of the
border. -/
def quadrupletPairs : Finset (AntonymForm × Region) :=
  ([.positive, .notPositive, .negative, .notNegative].toFinset ×ˢ
      [.positive, .plateauHigh, .plateauLow, .negative].toFinset).filter
    λ p => formAbove p.1 = p.2.above

/-- Krifka's assignment: the simple forms take the safe regions, the complex forms the border
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
