import Linglib.Data.UD.Basic
import Linglib.Features.Prominence
import Linglib.Morphology.Word.Basic
import Linglib.Features.Number.Capabilities
import Linglib.Features.Person.Capabilities

open Morphology (Word)

/-!
# Agreement paradigms — the descriptive realization table
[corbett-1998] [scott-2023]

A **theory-neutral** representation of an agreement paradigm: the descriptive
table mapping agreement-feature cells to their surface exponents, in the sense
of [corbett-1998] (*Morphology and Agreement*, Handbook of Morphology) and
the grammar-sketch chapters of descriptive work like [scott-2023] (Ch. 2:
Set A / Set B person–number inflection).

## Theory-neutrality

This file records *what forms realize which feature cells* — the paradigm table
a reference grammar lists. It deliberately commits to **no** generative account
of *how* the table arises. Syncretism is recorded as a plain fact (two cells, one
form — a non-injective table), not explained. The competing realizational
analyses — Distributed Morphology (vocabulary insertion + impoverishment;
[scott-2023] Ch. 4), Paradigm Function Morphology, HPSG type-hierarchy
unification — are *theories of* this table and belong in `Studies/`, not here.

## One φ-space with pronouns

Per [corbett-1998] (§1), agreement in the wider sense *includes* pronouns —
diachronically, agreement morphology grammaticalizes from pronouns. The three
indisputable agreement features (§2) are exactly **person, number, gender**
(case is government, not agreement). So an `Cell` is the canonical φ-subspace
a `Pronoun`/`Word` already carries: `Word.agrCell` projects a word's φ-features
into a paradigm index, so the *same* feature space drives pronoun reference and
agreement realization — no parallel person/number enum.

## Main declarations

* `Cell` — an agreement-feature cell (person × number × gender), in the
  canonical `UD` feature types.
* `Paradigm Exp` — a descriptive table: agreement cells to exponents.
* `Paradigm.realize` — look up the exponent for a cell (exact match).
* `Word.agrCell` / `Paradigm.realizeFor` — index a paradigm by a word's φ.
-/

namespace Agreement


/-- An agreement-feature cell: the canonical φ-features that may be realized by
    agreement ([corbett-1998] §2 — person, number, gender; case excluded as
    government). Uses the same `UD` feature types a `Pronoun`/`Word` carries, so a
    controller's φ projects directly into the index (`Word.agrCell`). A `none`
    field is a feature the paradigm does not distinguish. -/
structure Cell where
  person : Option UD.Person := none
  number : Option UD.Number := none
  gender : Option UD.Gender := none
  deriving DecidableEq, Repr, BEq

/-- Build a person–number cell (the common case: no gender agreement). -/
def Cell.pn (p : UD.Person) (n : UD.Number) : Cell :=
  { person := some p, number := some n }

/-- Is this a speech-act-participant (1st/2nd person) cell? Drives
    person-conditioned phenomena like differential indexing ([corbett-1998]). -/
def Cell.isSAP (c : Cell) : Bool :=
  c.person == some .first || c.person == some .second

/-- The person level of a cell, on the `Person` scale
    (an unspecified or 0-person cell maps to `.third`). Adapts a φ-cell to
    consumers that reason on person prominence (decomposition, indexing). -/
def Cell.toPerson (c : Cell) : Person :=
  match c.person with
  | some .first => .first
  | some .second => .second
  | _ => .third

/-- Is this a plural cell? -/
def Cell.isPlural (c : Cell) : Bool := c.number == some .Plur

/-- A cell bears the number its UD slot ingests (`Number.fromUD`); an
    undistinguished slot leaves the cell unvalued (wildcard). -/
instance : HasNumber Cell := ⟨fun c => c.number.bind Number.fromUD⟩

instance : HasPerson Cell := ⟨fun c => c.person.map Person.fromUD⟩

/-- The basic 3-person × {singular, plural} inventory of φ-cells — the cells a
    person/number agreement paradigm ranges over. -/
def Cell.pnCells : List Cell :=
  [.pn .first .Sing, .pn .second .Sing, .pn .third .Sing,
   .pn .first .Plur, .pn .second .Plur, .pn .third .Plur]

/-- The φ-cell of a word: its person/number/gender features, as an agreement
    index. The bridge that lets a pronoun (or any controller) drive an agreement
    paradigm in the *same* feature space ([corbett-1998] §1). -/
def _root_.Morphology.Word.agrCell (w : Word) : Cell :=
  { person := w.features.person, number := w.features.number,
    gender := w.features.gender }

/-- An agreement paradigm: the descriptive table of (cell, exponent) entries.
    `Exp` is the exponent type (a surface string, a structured affix, …).
    A non-injective table records syncretism as a fact; a partial table (a cell
    with no entry) records defectiveness. -/
abbrev Paradigm (Exp : Type _) := List (Cell × Exp)

namespace Paradigm

variable {Exp : Type _}

/-- The exponent realizing a given cell, by exact match (the first entry whose
    cell equals `c`). `none` if the paradigm has no entry for the cell. -/
def realize [DecidableEq Exp] (p : Paradigm Exp) (c : Cell) : Option Exp :=
  (p.find? (·.1 == c)).map (·.2)

/-- Realize the exponent agreeing with a controller word, via its `agrCell`. -/
def realizeFor [DecidableEq Exp] (p : Paradigm Exp) (controller : Word) : Option Exp :=
  p.realize controller.agrCell

/-- The cells the paradigm distinguishes (in declaration order). -/
def cells (p : Paradigm Exp) : List Cell := p.map (·.1)

end Paradigm

end Agreement
