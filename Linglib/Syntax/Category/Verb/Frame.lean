import Linglib.Syntax.Clause.Basic

/-! # Complement frames — typed complement positions

A predicate's complement frame as a list of typed
`Complement.Position`s: nominal, adpositional, or clausal, the clausal
case carrying the axes the predicate selects for. The flat
`ComplementType` enum survives as a round-trip view
(`ComplementType.toFrame` / `Frame.toComplementType`).

## Main definitions

* `Complement.Position` — one complement position; a clausal position
  carries its selectional axes by construction
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
`Adposition.Complement` is the P-specific counterpart of the position
categories. Frame-conditioned readings (attitude, opacity, control)
are not per-position data — they live on `Verb.Reading`
(`Syntax/Category/Verb/Defs.lean`), keyed to the verb's frames. The
selection relation between verb frames and clause-typers
(`Verb.takes`) lives in `Syntax/Category/Verb/Takes.lean`.
[deal-2026]'s CP-external shell inventory lives with its consumer in
`Studies/Deal2026.lean`.
-/

namespace Complement

/-- One complement position of a predicate's frame: nominal,
    adpositional, or clausal with the axes the predicate selects for —
    [noonan-2007] coding, illocutionary force, and subject requirement,
    `none` = unselective. Non-clausal positions carry no clausal axes
    by construction. -/
inductive Position where
  | nominal
  | adpositional
  | clausal (coding : Option Coding := none)
      (force : Option Mood.Illocutionary := none)
      (embeddedSubject : Option Clause.EmbeddedSubject := none)
  deriving DecidableEq, Repr

namespace Position

/-- The position's recorded [noonan-2007] coding, if clausal. -/
def coding? : Position → Option Coding
  | clausal c _ _ => c
  | _ => none

/-- The position's recorded force, if clausal. -/
def force? : Position → Option Mood.Illocutionary
  | clausal _ cf _ => cf
  | _ => none

/-- The position's recorded subject requirement, if clausal. -/
def embeddedSubject? : Position → Option Clause.EmbeddedSubject
  | clausal _ _ es => es
  | _ => none

end Position

end Complement

/-- A complement frame: the predicate's selected complement positions in
    order. Intransitive = `[]`; double object = two positions. The
    external argument is not a frame position — it lives on
    `Verb.voiceType`. -/
abbrev Frame := List Complement.Position

namespace Frame

/-- The [noonan-2007] codings recorded across the frame's positions. -/
def codings (fr : Frame) : List Complement.Coding :=
  fr.filterMap (·.coding?)

/-- Some position of the frame records force `f`. -/
def hasForce (fr : Frame) (f : Mood.Illocutionary) : Prop :=
  ∃ p ∈ fr, p.force? = some f

instance (fr : Frame) (f : Mood.Illocutionary) :
    Decidable (fr.hasForce f) :=
  inferInstanceAs (Decidable (∃ p ∈ fr, _))

/-! ### Smart constructors — the flat `ComplementType` cells -/

/-- Transitive: one nominal position. -/
def np : Frame := [.nominal]

/-- Double object: two nominal positions. -/
def np_np : Frame := [.nominal, .nominal]

/-- NP + PP: a nominal plus an adpositional position. -/
def np_pp : Frame := [.nominal, .adpositional]

/-- Finite declarative clause. -/
def finiteClause : Frame :=
  [.clausal (coding := some .indicative) (force := some .declarative)]

/-- Infinitival clause. The embedded-subject requirement varies by verb
    (equi-deletion, raising, or adposition-marked overt subjects,
    [noonan-2007] §1.3.4), so it lives on the verb's reading, not here. -/
def infinitival : Frame := [.clausal (coding := some .infinitive)]

/-- Gerund / nominalized clause. -/
def gerund : Frame := [.clausal (coding := some .nominalized)]

/-- Small clause (*consider X happy*; causative *make X leave*). Outside
    [noonan-2007]'s coding inventory, which classifies complements by
    the part of speech of their predicate, so the position records
    nothing. -/
def smallClause : Frame := [.clausal]

/-- Embedded question. Interrogativity is a force distinction
    orthogonal to [noonan-2007] coding, so `coding` stays `none`. -/
def question : Frame :=
  [.clausal (force := some .interrogative)]

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
