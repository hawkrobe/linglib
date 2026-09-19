import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

/-!
# The subjectivity cline

This file defines the synchronic cline of (inter)subjectivity of Traugott and Dasher as an ordered
type. Expressions range from nonsubjective, ideational and propositional, through subjective,
expressing the speaker's attitude or belief, to intersubjective, attending to the addressee's
face and self-image. The diachronic hypothesis is that coded (inter)subjective meanings arise
later than nonsubjective ones, and that subjectification precedes intersubjectification. The
file also defines the performative ~ descriptive distinction, which Narrog argues the cline
conflates with speaker orientation.

## References

* [traugott-dasher-2002]
* [traugott-2010]
* [narrog-2012]
-/

namespace Modality

/-- The levels of the subjectivity cline. Subjective meanings arise historically later than
nonsubjective ones, and intersubjective meanings later than subjective ones. -/
inductive SubjectivityLevel where
  /-- The expression describes properties of the world or of an event. -/
  | nonSubjective
  /-- The expression conveys the speaker's attitude, belief or evaluation. -/
  | subjective
  /-- The expression attends to the addressee's face or self-image. -/
  | intersubjective
  deriving DecidableEq, Repr, Inhabited

/-- The position of a level on the cline, counted from the nonsubjective end. -/
def SubjectivityLevel.toNat : SubjectivityLevel → Nat
  | .nonSubjective => 0
  | .subjective => 1
  | .intersubjective => 2

instance : LinearOrder SubjectivityLevel :=
  LinearOrder.lift' SubjectivityLevel.toNat
    (fun a b h ↦ by cases a <;> cases b <;> simp_all [SubjectivityLevel.toNat])

/-- The subjective level lies below the intersubjective level. -/
theorem intersubjective_ge_subjective :
    SubjectivityLevel.subjective ≤ SubjectivityLevel.intersubjective := by decide

/-- The nonsubjective level is the least level. -/
theorem nonSubjective_le (l : SubjectivityLevel) :
    SubjectivityLevel.nonSubjective ≤ l := by
  cases l <;> decide

/-! ### Performativity -/

/-- An utterance is performative when it constitutes the act it describes, and descriptive when
it reports a state that already holds. *You must go* can create an obligation, while *He must
be home* only assesses a situation. -/
inductive Performativity where
  /-- The utterance constitutes the act, as in imposing an obligation or making a promise. -/
  | performative
  /-- The utterance describes an existing state, as in an assessment or a report. -/
  | descriptive
  deriving DecidableEq, Repr, Inhabited

end Modality
