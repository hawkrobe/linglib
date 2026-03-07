import Linglib.Core.Discourse.Epistemicity

/-!
# Subjectivity Cline
@cite{traugott-dasher-2002} @cite{traugott-2010}

Traugott & Dasher's synchronic cline of (inter)subjectivity, formalized as an
ordered type. Expressions range from **nonsubjective** (ideational, propositional)
through **subjective** (speaker attitude/belief) to **intersubjective** (addressee
face/self-image). The diachronic hypothesis is that coded (inter)subjective
meanings arise later than non-subjective ones; subjectification precedes
intersubjectification.

## Bridges

- `EpistemicAuthority` to `SubjectivityLevel`: ego = subjective,
  allocutive = intersubjective, nonparticipant = nonSubjective.
- The cline connects modal semantics (speaker assessment = subjective),
  politeness (addressee face = intersubjective), and RSA (speaker model =
  subjectified speaker).
-/

namespace Core.Subjectivity

open Core.Epistemicity (EpistemicAuthority)

/-- Synchronic subjectivity scale (@cite{traugott-dasher-2002} Table 1,
    @cite{traugott-2010} cline 2). Diachronic work shows that subjective
    polysemies arise later than ideational ones, and intersubjective
    polysemies arise later than subjective ones. -/
inductive SubjectivityLevel where
  | nonSubjective   -- ideational: describes world/event properties
  | subjective      -- speaker attitude, belief, evaluation
  | intersubjective -- attention to addressee face/self-image
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Numeric encoding for ordering. -/
def SubjectivityLevel.toNat : SubjectivityLevel → Nat
  | .nonSubjective => 0
  | .subjective => 1
  | .intersubjective => 2

instance : LE SubjectivityLevel where
  le a b := a.toNat ≤ b.toNat

instance : LT SubjectivityLevel where
  lt a b := a.toNat < b.toNat

instance (a b : SubjectivityLevel) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

instance (a b : SubjectivityLevel) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNat < b.toNat))

/-- The cline is totally ordered. -/
theorem le_total (a b : SubjectivityLevel) : a ≤ b ∨ b ≤ a :=
  Nat.le_total a.toNat b.toNat

/-- Bridge: epistemic authority to subjectivity level.

    - ego (speaker has privileged access) maps to subjective
    - allocutive (addressee has privileged access) maps to intersubjective
    - nonparticipant maps to nonSubjective -/
def SubjectivityLevel.ofEpistemicAuthority : EpistemicAuthority → SubjectivityLevel
  | .ego => .subjective
  | .allocutive => .intersubjective
  | .nonparticipant => .nonSubjective

/-- Intersubjectivity presupposes subjectivity (@cite{traugott-2010} section 2). -/
theorem intersubjective_ge_subjective :
    SubjectivityLevel.subjective ≤ SubjectivityLevel.intersubjective := by decide

/-- Non-subjective is the minimum. -/
theorem nonSubjective_le (l : SubjectivityLevel) :
    SubjectivityLevel.nonSubjective ≤ l := by
  cases l <;> decide

-- ============================================================================
-- §2. Performativity
-- ============================================================================

/-- Whether the utterance constitutes the act it describes or merely reports it.

    The performative/descriptive distinction originates with Austin (1962) and
    cross-cuts subjectivity: a speaker-oriented utterance can be performative
    ("You must go" — creates the obligation) or descriptive ("He must be home"
    — assesses without creating). @cite{narrog-2012} §2.4 argues that
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
  deriving DecidableEq, Repr, BEq, Inhabited

end Core.Subjectivity
