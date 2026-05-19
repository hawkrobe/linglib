/-!
# Pustejovsky (1995): Generative Lexicon — qualia-derived complement coercion
@cite{pustejovsky-1995}

GL §7.1 introduces *type coercion*: a semantic operation that
converts an argument to the type expected by a function, "where it
would otherwise result in a type error" (paper p. 111, def. 16). The
coercion is selected from a set `Σ_α` of shifting operators
*available for the source expression α*, derived from the noun's
qualia structure (TELIC, AGENTIVE: paper §6.2).

**Why not Lean `Coe`.** Lean's `Coe` matches GL's *subtype coercion*
(§7.1.2: Honda ≤ car ≤ vehicle) but not *true complement coercion*
(§7.1.3). Three reasons it would be wrong here:

1. *Multiple shifters per noun.* `begin a book` admits BOTH the
   TELIC reading (begin reading) AND the AGENTIVE reading (begin
   writing) — paper p. 86. A single Coe instance commits prematurely
   to one. The verb selects among the available shifters; coercion
   is genuinely ambiguous before selection.

2. *Meaning-changing.* Pustejovsky distinguishes complement coercion
   from subsumption: the source value is *mapped to a different
   entity* (book ↦ reading-event), not viewed as a member of a
   supertype. The coercion must be visible in proofs, not implicitly
   inserted.

3. *Σ_α as first-class data.* Theorems quantify over the available
   shifters for a noun (e.g., "any noun with a non-trivial TELIC
   admits a use-event coercion"). Lean instance databases are not
   introspectable; we need `Σ : NounMeaning → Finset Shifter` as
   data.

## Main definitions

* `Qualia`, `NounMeaning`: paper §6.2 (eq. 31 for `book`).
* `Shifter`: a qualia-source-tagged coercion from a noun to a
  target type. Concrete shifters are derived from TELIC and AGENTIVE.
* `complementCoerce`: explicit application of a shifter (not
  Lean-native Coe — coercion is meaning-changing and must be
  visible).
* `bookMeaning`: paper §6.2 eq. 31 (CONST=pages, FORMAL=physobj,
  TELIC=read, AGENTIVE=write).
* Paradigm theorems exposing BOTH TELIC and AGENTIVE readings of
  "John began a book" (paper p. 86).

## References

* @cite{pustejovsky-1995} §6.2 (qualia structure), §7.1.3
  (true complement coercion), p. 86 (book's two coercion readings).
-/

namespace Pustejovsky1995

/-! ### Paper §6.2: qualia structure -/

/-- The four qualia roles (paper §6.1 "Modes of Explanation"). -/
inductive QualeRole where
  | constitutive
  | formal
  | telic
  | agentive
  deriving DecidableEq, Repr

/-- A qualia structure: each role maps to a "logical parameter"
    (paper p. 76). Here flattened to a target type per role; the
    paper's relational forms (e.g., TELIC = read(P,w,x)) collapse
    to the target-type-of-the-relation at this fidelity. `none`
    means the role is unspecified (paper §6.2: not all nouns
    instantiate all four). -/
structure Qualia where
  constitutive : Option Type
  formal       : Option Type
  telic        : Option Type
  agentive     : Option Type

/-- A noun lexical entry under GL: extension + qualia (paper §5.1
    "Levels of Representation"). -/
structure NounMeaning where
  extension : Type
  qualia    : Qualia

/-! ### Paper §6.2 eq. 31: book

`book` = ⟨ARG1 = x:information, ARG2 = y:phys_obj⟩ with qualia
CONST=pages, FORMAL=hold(y,x), TELIC=read(e,w,x,y), AGENTIVE=write(e',v,x,y).
At our fidelity: TELIC = reading-event, AGENTIVE = writing-event. -/

inductive Book where | warAndPeace | hamlet | mobyDick
  deriving DecidableEq, Repr

inductive ReadingEvent where | reading : Book → ReadingEvent
  deriving DecidableEq, Repr

inductive WritingEvent where | writing : Book → WritingEvent
  deriving DecidableEq, Repr

/-- Paper eq. 31 for `book`. -/
def bookMeaning : NounMeaning where
  extension := Book
  qualia :=
    { constitutive := none      -- "pages" (informational composition); not modelled
      formal       := some Book
      telic        := some ReadingEvent
      agentive     := some WritingEvent }

/-! ### Shifters: qualia-derived coercions

A `Shifter` records both the target type and the qualia role that
*licenses* the coercion. Paper's Σ_α is the set of shifters derived
from α's qualia. -/

/-- A coercion shifter: target type plus the qualia role that
    licenses it. -/
structure Shifter (N : NounMeaning) where
  role   : QualeRole
  target : Type
  shift  : N.extension → target

/-- The set of shifters derived from a noun's qualia (paper FAC's
    Σ_α). For each role with a defined quale-target, there is one
    shifter (the structural projection onto that quale). The actual
    quale-projection function (e.g., `Book → ReadingEvent`) is
    declared per-noun, since the relationship is lexical, not
    structural. -/
def Qualia.targets (q : Qualia) : List (QualeRole × Type) :=
  let opt (r : QualeRole) (t : Option Type) : List (QualeRole × Type) :=
    match t with | none => [] | some τ => [(r, τ)]
  opt .constitutive q.constitutive ++
  opt .formal       q.formal       ++
  opt .telic        q.telic        ++
  opt .agentive     q.agentive

/-- The TELIC shifter for `book`: book ↦ reading-event (paper §7.1.3
    "begin a novel" = begin reading a novel, p. 84 eq. 19). -/
def bookTelicShifter : Shifter bookMeaning where
  role   := .telic
  target := ReadingEvent
  shift  := ReadingEvent.reading

/-- The AGENTIVE shifter for `book`: book ↦ writing-event (paper
    p. 86: book has TWO event types via TELIC and AGENTIVE; either
    is available for a coerce-to-event verb). -/
def bookAgentiveShifter : Shifter bookMeaning where
  role   := .agentive
  target := WritingEvent
  shift  := WritingEvent.writing

/-! ### Explicit complement-coercion application

Coercion is meaning-changing (paper §7.1.3) and must be visible in
the term, NOT silently inserted by the elaborator. Hence `complementCoerce`
is an explicit function, not a Lean `Coe` instance. -/

/-- Apply a shifter to a value of the noun's extension. The result
    lives in the shifter's target type. -/
def complementCoerce {N : NounMeaning} (σ : Shifter N) (a : N.extension) : σ.target :=
  σ.shift a

/-! ### Paradigm: "John began a book" (paper p. 86)

The paper's central case: `begin` expects an event-typed argument;
`a book` is a Book; the type mismatch triggers FAC; book's qualia
offer BOTH TELIC (reading) AND AGENTIVE (writing) shifters, so the
sentence is **genuinely ambiguous** between two readings. The verb
or context resolves. -/

def begin_read : ReadingEvent → Prop := fun _ => True
def begin_write : WritingEvent → Prop := fun _ => True

/-- TELIC reading: `begin a book` = begin reading a book. -/
theorem began_book_telic_reading :
    begin_read (complementCoerce bookTelicShifter Book.warAndPeace) :=
  trivial

/-- AGENTIVE reading: `begin a book` = begin writing a book. -/
theorem began_book_agentive_reading :
    begin_write (complementCoerce bookAgentiveShifter Book.warAndPeace) :=
  trivial

/-- **Paper p. 86 thesis**: `book` admits at least two distinct
    qualia-derived shifters (TELIC and AGENTIVE), one targeting
    reading-events and one targeting writing-events. Both readings
    are available for `begin a book`; pragmatic context resolves. -/
theorem book_admits_two_shifters :
    bookTelicShifter.role = QualeRole.telic ∧
    bookAgentiveShifter.role = QualeRole.agentive ∧
    bookTelicShifter.target = ReadingEvent ∧
    bookAgentiveShifter.target = WritingEvent :=
  ⟨rfl, rfl, rfl, rfl⟩

end Pustejovsky1995
