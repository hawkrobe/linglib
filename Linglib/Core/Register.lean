import Mathlib.Data.Rat.Defs

/-!
# Register

Sociolinguistic register as a lexical feature. Register encodes the
formality level of a linguistic form — whether it belongs to formal
(literary, careful) speech, neutral (unmarked) speech, or informal
(colloquial, casual) speech.

Register is currently stipulated as a lexical property of individual
forms. A future direction is to derive register effects from pragmatic
factors (e.g., RSA models where formality emerges from competing social
goals, as in Yoon et al. 2020 for politeness).

## Connections

* `Core.Pronouns.PronounEntry.register`: pronoun register (T/V/honorific)
* `Core.Pronouns.AllocutiveEntry.register`: allocutive marker register
* `Fragments.English.FunctionWords.AuxEntry.register`: modal register
* `Semantics.Lexical.Expressives.CIContext.formality`: context formality (ℚ)

Binary T/V systems (Basque, Tamil, Galician, Punjabi) use `.informal`/`.formal`.
Ternary honorific systems (Hindi, Magahi, Maithili, Korean) use all three levels.

## References

* Dieuleveut, Hsu & Bhatt (2025). A Register Approach to Modal Non-Concord.
* Biber & Conrad (2009). Register, Genre, and Style.
-/

namespace Core.Register

/-- Register level: the formality of a linguistic form.

    Three levels suffice for the phenomena currently formalized
    (modal concord, T/V pronouns, honorific systems). Finer-grained scales are
    possible (Biber's multi-dimensional analysis uses continuous
    features) but not yet needed. -/
inductive Level where
  | formal    -- literary, written, careful speech (e.g., *must*, *shall*, *aap*)
  | neutral   -- unmarked (e.g., *can*, *will*, *tum*, *gayo*)
  | informal  -- colloquial, casual speech (e.g., *have to*, *tuu*, *boku*)
  deriving DecidableEq, BEq, Repr, Inhabited

instance : ToString Level where
  toString
    | .formal => "formal"
    | .neutral => "neutral"
    | .informal => "informal"

/-- All register levels, ordered from informal to formal. -/
def Level.all : List Level := [.informal, .neutral, .formal]

/-- Numeric encoding: informal=0 < neutral=1 < formal=2. -/
def Level.toNat : Level → Nat
  | .informal => 0
  | .neutral  => 1
  | .formal   => 2

/-- Inverse of `toNat`: 0 → informal, 1 → neutral, 2+ → formal. -/
def Level.fromNat : Nat → Level
  | 0 => .informal
  | 1 => .neutral
  | _ => .formal

/-- Ordering: informal < neutral < formal. -/
instance : Ord Level where
  compare a b := compare a.toNat b.toNat

instance : LT Level where
  lt a b := a.toNat < b.toNat

instance : LE Level where
  le a b := a.toNat ≤ b.toNat

instance (a b : Level) : Decidable (a < b) := Nat.decLt a.toNat b.toNat
instance (a b : Level) : Decidable (a ≤ b) := Nat.decLe a.toNat b.toNat

theorem informal_lt_neutral : Level.informal < Level.neutral := by decide
theorem neutral_lt_formal : Level.neutral < Level.formal := by decide
theorem informal_lt_formal : Level.informal < Level.formal := by decide

/-- Round-trip: `ofNat` inverts `toNat`. -/
theorem ofNat_toNat (l : Level) : Level.fromNat l.toNat = l := by cases l <;> decide

/-- Rational-valued encoding: informal=0, neutral=1/2, formal=1.
    Bridges to `CIContext.formality : ℚ` (0=casual, 1=formal). -/
def Level.toRat : Level → ℚ
  | .informal => 0
  | .neutral  => 1/2
  | .formal   => 1

/-- Two forms are **register variants** if they differ in register
    level. This is the structural precondition for register mixing
    and split-register constructions (Dieuleveut et al. 2025). -/
def areVariants (a b : Level) : Bool := a != b

/-! ## Social indexation -/

/-- Social indexation of grammatical doubling.

    Concord phenomena carry social meaning along a competence/solidarity
    axis (drawing on the competence/warmth dichotomy in social cognition;
    Fiske, Cuddy, Glick & Xu 2002).

    * `competence`: standard dialect, educated, formal, high-SES, confident.
    * `solidarity`: non-standard, friendly, warm, in-group, casual. -/
inductive SocialIndex where
  | competence
  | solidarity
  deriving DecidableEq, BEq, Repr, Inhabited

end Core.Register
