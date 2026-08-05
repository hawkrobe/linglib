import Linglib.Features.Complementation
import Linglib.Features.ClauseForm
import Linglib.Features.Case.Basic

/-! # Complement frames — typed complement positions

A predicate's complement frame as a list of typed `Complement.Position`s,
factoring the flat `ComplementType` enum cells into their axes:
syntactic category, clause form, [noonan-2007] coding, and
embedded-subject requirement (genitive subjects of nominalized clauses,
[noonan-2007] §1.3.5, [bondarenko-2022]). The flat enum survives as a
round-trip view (`ComplementType.toFrame` / `Frame.toComplementType`).

## Main declarations

* `Complement.Position`, with its `Complement.Cat` and
  `Complement.EmbeddedSubject` axes — one complement position: category
  plus optional clausal axes
* `Frame` + `Frame.np`, `Frame.finiteClause`, … — a frame is a list of
  complement positions; the flat enum cells as smart constructors
* `ComplementType` + `toFrame` / `Frame.toComplementType` — the flat
  enum and its round-trip view
* `ComplementType.toCoding` + `codings_toFrame` — the enum's
  [noonan-2007] coding and its agreement with the typed frames

## Implementation notes

Complement-taking is cross-categorial ([noonan-2007]'s CTPs include
adjectives and nouns), so the position record lives in the `Complement`
namespace beside `Complement.Coding`, not under `Verb`;
`Adposition.Complement` is the P-specific counterpart of
`Complement.Cat`. Frame-conditioned readings (attitude, opacity,
control) are not per-position data — they live on `Verb.Reading`
(`Syntax/Category/Verb/Defs.lean`), keyed to the verb's frames. The
selection relation between verb frames and clause-typers
(`Verb.realizes`) lives in `Syntax/Category/Verb/Selection.lean`.
[deal-2026]'s CP-external shell inventory lives with its consumer in
`Studies/Deal2026.lean`.
-/

namespace Complement

/-! ### Complement-position axes -/

/-- Syntactic category of a complement position. -/
inductive Cat where
  | nominal
  | adpositional
  | clausal
  deriving DecidableEq, Repr

/-- Embedded-subject requirement of a clausal complement: obligatorily
    null (as in control complements) or overt, optionally with a fixed
    case. Genitive marking on the subject is [noonan-2007]'s criterion
    for the nominalization coding (§1.3.5); [bondarenko-2022] ch. 4 is
    the modern instance (Buryat genitive subjects of nominalized
    clauses). -/
inductive EmbeddedSubject where
  | obligatorilyNull
  | overt (subjCase : Option Case)
  deriving DecidableEq, Repr

/-! ### The frame object -/

/-- One complement position of a predicate's frame: its category plus,
    for clausal complements, the recorded clausal axes. On clausal
    complements `none` means unrecorded; non-clausal complements leave
    the clausal axes at their `none` defaults. Frame-conditioned
    readings and control are not per-position data — they live on
    `Verb.Reading`. -/
structure Position where
  /-- Syntactic category of the complement. -/
  cat : Cat
  /-- Clause form (declarative vs embedded question). -/
  clauseForm : Option Features.ClauseForm := none
  /-- [noonan-2007] coding of the complement clause. -/
  coding : Option Coding := none
  /-- Embedded-subject requirement. -/
  embeddedSubject : Option EmbeddedSubject := none
  deriving DecidableEq, Repr

end Complement

/-- A complement frame: the predicate's selected complement positions in
    order. Intransitive = `[]`; double object = two positions. The
    external argument is not a frame position — it lives on
    `Verb.voiceType`. -/
abbrev Frame := List Complement.Position

namespace Frame

/-- The [noonan-2007] codings recorded across the frame's positions. -/
def codings (fr : Frame) : List Complement.Coding := fr.filterMap (·.coding)

/-- Some position of the frame records clause form `cf`. -/
def hasClauseForm (fr : Frame) (cf : Features.ClauseForm) : Prop :=
  ∃ s ∈ fr, s.clauseForm = some cf

instance (fr : Frame) (cf : Features.ClauseForm) :
    Decidable (fr.hasClauseForm cf) :=
  inferInstanceAs (Decidable (∃ s ∈ fr, _))

/-! ### Smart constructors — the flat `ComplementType` cells -/

/-- Transitive: one nominal position. -/
def np : Frame := [{ cat := .nominal }]

/-- Double object: two nominal positions. -/
def np_np : Frame := [{ cat := .nominal }, { cat := .nominal }]

/-- NP + PP: a nominal plus an adpositional position. -/
def np_pp : Frame := [{ cat := .nominal }, { cat := .adpositional }]

/-- Finite declarative clause. -/
def finiteClause : Frame :=
  [{ cat := .clausal, coding := some .indicative,
     clauseForm := some .declarative }]

/-- Infinitival clause. The embedded-subject requirement varies by verb
    (equi-deletion, raising, or adposition-marked overt subjects,
    [noonan-2007] §1.3.4), so it lives on the verb's reading, not here. -/
def infinitival : Frame := [{ cat := .clausal, coding := some .infinitive }]

/-- Gerund / nominalized clause. -/
def gerund : Frame := [{ cat := .clausal, coding := some .nominalized }]

/-- Small clause (*consider X happy*; causative *make X leave*). Outside
    [noonan-2007]'s coding inventory, which classifies complements by
    the part of speech of their predicate, so `coding` stays `none`. -/
def smallClause : Frame := [{ cat := .clausal }]

/-- Embedded question. Interrogativity is a clause-form distinction
    orthogonal to [noonan-2007] coding, so `coding` stays `none`. -/
def question : Frame :=
  [{ cat := .clausal, clauseForm := some .embeddedQuestion }]

end Frame

/-! ### The flat enum view -/

/--
Complement type that the verb selects — the flat view over the typed
`Frame`.

- Finite: "that" clauses ("John knows that Mary left")
- Infinitival: "to" complements ("John managed to leave")
- Gerund: "-ing" complements ("John stopped smoking")
- NP: Direct object ("John kicked the ball")
- None: Intransitive ("John slept")
-/
inductive ComplementType where
  | none            -- Intransitive
  | np              -- Transitive with NP object
  | np_np           -- Ditransitive: "give X Y"
  | np_pp           -- NP + PP: "put X on Y"
  | finiteClause    -- "that" clause
  | infinitival     -- "to" VP
  | gerund          -- "-ing" VP
  | smallClause     -- "consider X happy"
  | question        -- Embedded question "wonder who"
  deriving DecidableEq, Repr

/-- Is this complement type finite (i.e., does it contain a tense head)?

    Finite complements (.finiteClause,.question) have independent tense
    morphology; non-finite complements (.infinitival,.gerund,.smallClause)
    do not. -/
def ComplementType.isFinite : ComplementType → Bool
  | .finiteClause | .question => true
  | _ => false

/-- Is this complement type a nominal (DP) argument?

    Nominal complements project DP: the verb selects a noun phrase
    in object position. Relevant to c-selection in coordination:
    a verb that only selects nominal complements cannot independently
    license a CP conjunct ([schwarzer-2026]). -/
def ComplementType.isNominal : ComplementType → Bool
  | .np | .np_np | .np_pp => true
  | _ => false

/-- Is this complement type a clausal (CP) argument?

    Clausal complements project CP or reduced clausal structure.
    This covers finite clauses (*dass*-clauses), infinitivals,
    gerunds, small clauses, and embedded questions. -/
def ComplementType.isClausal : ComplementType → Bool
  | .finiteClause | .infinitival | .gerund | .smallClause | .question => true
  | _ => false

/-- The `Frame` cell of a flat `ComplementType` (`.none` ↦ `[]`). -/
def ComplementType.toFrame : ComplementType → Frame
  | .none => []
  | .np => Frame.np
  | .np_np => Frame.np_np
  | .np_pp => Frame.np_pp
  | .finiteClause => Frame.finiteClause
  | .infinitival => Frame.infinitival
  | .gerund => Frame.gerund
  | .smallClause => Frame.smallClause
  | .question => Frame.question

/-- Partial inverse of `ComplementType.toFrame`: the flat enum cell a
    frame instantiates, `none` on frames richer than any cell. -/
def Frame.toComplementType (fr : Frame) : Option ComplementType :=
  [ComplementType.none, .np, .np_np, .np_pp, .finiteClause, .infinitival,
    .gerund, .smallClause, .question].find? (·.toFrame == fr)

/-- The enum view round-trips over the smart-constructor cells. -/
@[simp]
theorem toComplementType_toFrame (ct : ComplementType) :
    ct.toFrame.toComplementType = some ct := by cases ct <;> rfl

theorem ComplementType.toFrame_injective :
    Function.Injective ComplementType.toFrame := by
  intro a b h
  have ha := toComplementType_toFrame a
  rw [h, toComplementType_toFrame b] at ha
  exact (Option.some.inj ha).symm

/-- The [noonan-2007] coding of a complement frame: `none` for
non-clausal frames, for small clauses (outside the coding inventory),
and for embedded questions (interrogativity is a clause-form axis, not
a coding). -/
def ComplementType.toCoding : ComplementType → Option Complement.Coding
  | .finiteClause => some .indicative
  | .infinitival => some .infinitive
  | .gerund => some .nominalized
  | .smallClause => Option.none
  | .none => Option.none
  | .np => Option.none
  | .np_np => Option.none
  | .np_pp => Option.none
  | .question => Option.none

/-- The enum view and the typed frames record the same coding: a cell's
    frame carries exactly the codings `toCoding` assigns it. -/
theorem ComplementType.codings_toFrame (ct : ComplementType) :
    ct.toFrame.codings = ct.toCoding.toList := by cases ct <;> rfl
