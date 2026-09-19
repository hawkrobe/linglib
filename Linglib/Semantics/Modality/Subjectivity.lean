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

/-- Synchronic subjectivity scale ([traugott-dasher-2002] Table 1,
    [traugott-2010] cline 2). Diachronic work shows that subjective
    polysemies arise later than ideational ones, and intersubjective
    polysemies arise later than subjective ones. -/
inductive SubjectivityLevel where
  | nonSubjective   -- ideational: describes world/event properties
  | subjective      -- speaker attitude, belief, evaluation
  | intersubjective -- attention to addressee face/self-image
  deriving DecidableEq, Repr, Inhabited

/-- Numeric encoding for ordering. -/
def SubjectivityLevel.toNat : SubjectivityLevel → Nat
  | .nonSubjective => 0
  | .subjective => 1
  | .intersubjective => 2

instance : LinearOrder SubjectivityLevel :=
  LinearOrder.lift' SubjectivityLevel.toNat
    (fun a b h => by cases a <;> cases b <;> simp_all [SubjectivityLevel.toNat])

/-- Intersubjectivity presupposes subjectivity ([traugott-2010] section 2). -/
theorem intersubjective_ge_subjective :
    SubjectivityLevel.subjective ≤ SubjectivityLevel.intersubjective := by decide

/-- Non-subjective is the minimum. -/
theorem nonSubjective_le (l : SubjectivityLevel) :
    SubjectivityLevel.nonSubjective ≤ l := by
  cases l <;> decide

/-! ### Performativity -/

/-- Whether the utterance constitutes the act it describes or merely reports it.

    The performative/descriptive distinction originates with Austin (1962) and
    cross-cuts subjectivity: a speaker-oriented utterance can be performative
    ("You must go" — creates the obligation) or descriptive ("He must be home"
    — assesses without creating). [narrog-2012] §2.4 argues that
    Traugott's subjectivity cline conflates speaker-orientation with
    performativity, collapsing distinctions that matter for face-threat,
    person restrictions, and diachronic change paths.

    This dimension connects to:
    - Modal semantics: deontic = performative; epistemic = descriptive
    - Politeness: performative + volitive = face-threatening (Brown & Levinson)
    - Speech acts: performatives (Austin) vs constatives -/
inductive Performativity where
  | performative   -- utterance constitutes the act (deontic imposition, promise)
  | descriptive    -- utterance describes an existing state (assessment, report)
  deriving DecidableEq, Repr, Inhabited

end Modality
