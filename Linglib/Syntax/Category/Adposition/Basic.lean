import Mathlib.Tactic.DeriveFintype

/-!
# Adposition: the function-marking relator
[hagege-2010] [dryer-2013] [svenonius-2010]

The P-head word class — a **function-marking relator** — as a theory-neutral
object, sibling to `Syntax/Category/Pronoun` in the closed-class function-word family.
The base encodes only the cross-framework criteria that *define* the category;
every framework (Minimalist cartography, HPSG, CCG, Dependency Grammar,
cognitive grammar) and every semantic theory (Pantcheva direction, Zwarts path
algebra, the Svenonius `AxPart` decomposition in `Adposition/Spatial.lean`)
*plugs into* this base rather than defining it — exactly as Caha's containment
refines `Case` without being `Case`.

## Defining criteria (typological tradition: [hagege-2010], [dryer-2013])

1. **governs a complement** (the Ground/régime) — a relator; `[]` is the
   intransitive/particle limit;
2. **marks the function** of that complement — a `RelationType`;
3. **closed-class grammatical** element (a category fact; may inflect/agree —
   Celtic, Uralic, Hebrew);
4. **fixed linearization** relative to the complement (a *set*: a lexeme may be
   both pre- and post-positional, e.g. Dutch *op*);
5. **exponence** on the grammaticalization cline (the case-affix boundary).

## Main declarations

* `Adposition` — the category object (the five criteria as fields)
* `Adposition.RelationType` / `Linearization` / `Complement` / `Exponence` /
  `Form` — the criterion vocabularies
* `Adposition.isIntransitive` / `isComplex` / `isAmbipositional`
-/

namespace Adposition

/-- The relation an adposition marks (criterion 2) — coarse only. A spatial
    relation's internal structure (`AxPart × Region × PathDir × Bound`) is a
    *theory* (`Adposition/Spatial.lean`), never part of the category. -/
inductive RelationType where
  /-- Spatial: in/on/under/to/from. Refined by the cartographic decomposition. -/
  | spatial
  /-- Temporal: before/after/during/until. -/
  | temporal
  /-- Grammatical/relational: of/by/with — function-marking (agent, instrument,
      comitative). The marked role is a Study-level refinement, not a base field. -/
  | grammatical
  /-- Logical/abstract: because-of/despite/concerning. -/
  | logical
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- A linearization of an adposition with respect to its complement
    (criterion 4). The per-lexeme companion to the language-level
    `Adposition.AdpositionOrder`. -/
inductive Linearization where
  /-- Preposition: P precedes the complement. -/
  | pre
  /-- Postposition: P follows the complement. -/
  | post
  /-- Circumposition: P brackets the complement (two exponents). -/
  | circum
  /-- Inposition: P appears inside/second-position in the complement. -/
  | inposition
  deriving DecidableEq, Repr, Fintype

/-- What an adposition governs (criterion 1) — P-specific complement types
    (NOT the verb-argument `Features.Complementation.ComplementType`, which
    carries ditransitive frames an adposition never selects). -/
inductive Complement where
  | np
  | pp
  | clause
  /-- Adjectival complement (Dutch *tot voor kort* 'until recently'). -/
  | ap
  deriving DecidableEq, Repr, Fintype

/-- Exponence on the grammaticalization cline (criterion 5). `affix` is the
    boundary at which the adposition becomes a `Case` exponent — the point where
    this object and `Case` meet on the cline (`Features/Case/Grammaticalization.lean`). -/
inductive Exponence where
  | free
  | clitic
  | affix
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- The form of an adposition: a single word, or a complex/multi-word adposition
    (*in front of*, *on top of*). -/
inductive Form where
  | simple (s : String)
  | complex (parts : List String)
  deriving DecidableEq, Repr

/-- The surface string of a form (complex forms joined by spaces). -/
def Form.text : Form → String
  | .simple s => s
  | .complex parts => " ".intercalate parts

end Adposition

/-- An adposition: the five defining criteria as fields. Theory-neutral —
    spatial/grammatical refinements and framework analyses consume it. -/
structure Adposition where
  form : Adposition.Form
  /-- Criterion 2: the relation marked. -/
  relation : Adposition.RelationType
  /-- Criterion 1: complement types selected. `[]` = intransitive (particle). -/
  complement : List Adposition.Complement
  /-- Criterion 4: allowed linearizations (set semantics; may be several). -/
  linearization : List Adposition.Linearization
  /-- Criterion 5: exponence on the cline. -/
  exponence : Adposition.Exponence := .free
  /-- Criterion 3 refinement: inflects/agrees with the complement's φ-features
      (Celtic *agam*, Hungarian, Hebrew). -/
  agreesWithComplement : Bool := false
  deriving Repr, DecidableEq

namespace Adposition

/-- Intransitive (the particle limit): governs no complement. -/
def isIntransitive (a : Adposition) : Bool := a.complement.isEmpty

/-- Complex/multi-word adposition (*in front of*). -/
def isComplex (a : Adposition) : Bool :=
  match a.form with
  | .complex _ => true
  | .simple _ => false

/-- Ambipositional: allows both pre- and post-positional order (Dutch *op*). -/
def isAmbipositional (a : Adposition) : Bool :=
  a.linearization.contains .pre && a.linearization.contains .post

/-! ### Smoke tests — the mature fields exercised (stress-test seeds) -/

/-- English *in*: simple spatial preposition over an NP. -/
def english_in : Adposition :=
  { form := .simple "in", relation := .spatial, complement := [.np],
    linearization := [.pre] }

/-- English *in front of*: a complex/multi-word spatial preposition. -/
def english_inFrontOf : Adposition :=
  { form := .complex ["in", "front", "of"], relation := .spatial,
    complement := [.np], linearization := [.pre] }

/-- Dutch *op*: ambipositional (both pre- and post-positional). -/
def dutch_op : Adposition :=
  { form := .simple "op", relation := .spatial, complement := [.np],
    linearization := [.pre, .post] }

/-- Irish *ag* 'at': a grammatical preposition that **inflects** for its
    complement (*agam* 'at-me', *agat* 'at-you'). -/
def irish_ag : Adposition :=
  { form := .simple "ag", relation := .grammatical, complement := [.np],
    linearization := [.pre], agreesWithComplement := true }

example : english_inFrontOf.isComplex = true := by decide
example : dutch_op.isAmbipositional = true := by decide
example : irish_ag.agreesWithComplement = true := by decide
example : english_in.isIntransitive = false := by decide

end Adposition
