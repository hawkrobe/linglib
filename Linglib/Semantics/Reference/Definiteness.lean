/-!
# Definiteness

The Frame-free vocabulary of definiteness: whether a nominal is definite or indefinite
([heim-1982]), the two strengths of a definite article, uniqueness and familiarity
([schwarz-2009]), the kinds of description an inventory can realize, and the typologies of
article systems built on the strengths. The strength a use of a definite calls for
([hawkins-1978], [schwarz-2013]) and the strength of a bridging relation are recorded as data
here; which cell a language's determiner inventory falls in is derived in
`Syntax/Category/Determiner/Basic.lean`, and the descriptions themselves denote in
`Semantics/Reference/Description.lean`.

## Main definitions

* `Reference.Definiteness`: definite or indefinite.
* `Reference.Description.Strength`, `Reference.Description.Kind`: the strength of a definite
  article and the kind of a description, with `Strength.toKind` and `Kind.strength`.
* `Reference.DefiniteUse`, `Reference.Bridging`: the uses of a definite and the bridging
  relations, each with the strength it calls for.
* `Reference.ArticleType`, `Reference.MarkingStrategy`: the three-cell and four-cell article
  typologies of [schwarz-2009] and [jenks-2018] with [moroney-2021]'s unmarked cell, and the
  coarsening `MarkingStrategy.articleType`.

## References

* [schwarz-2009]
* [schwarz-2013]
* [hawkins-1978]
* [heim-1982]
* [jenks-2018]
* [moroney-2021]
* [patel-grosz-grosz-2017]
-/

namespace Reference

/-- Definite or indefinite: a definite retrieves a unique or familiar referent, an indefinite
introduces a new one ([heim-1982]). -/
inductive Definiteness where
  | indefinite
  | definite
  deriving DecidableEq, Repr

namespace Description

/-- The strength of a definite article ([schwarz-2009]): the weak article presupposes
uniqueness, the strong article familiarity. -/
inductive Strength where
  | uniqueness
  | familiarity
  deriving DecidableEq, Repr

/-- The kind of a nominal description: a constructor of `Description` with its payload erased,
together with the indefinite, which denotes no partial individual but which an inventory may
realize. -/
inductive Kind where
  | bare
  | indefinite
  | unique
  | anaphoric
  | demonstrative
  | possessive
  deriving DecidableEq, Repr

/-- The kind of description an article strength realizes: the weak article the unique
description, the strong article the anaphoric one. -/
def Strength.toKind : Strength → Kind
  | .uniqueness  => .unique
  | .familiarity => .anaphoric

/-- The strength a kind of description presupposes, where it is definite. -/
def Kind.strength : Kind → Option Strength
  | .bare | .indefinite         => none
  | .unique | .possessive       => some .uniqueness
  | .anaphoric | .demonstrative => some .familiarity

@[simp] theorem Strength.strength_toKind (p : Strength) : p.toKind.strength = some p := by
  cases p <;> rfl

end Description

/-- [hawkins-1978]'s uses of a definite description, with the donkey use of [schwarz-2009]. -/
inductive DefiniteUse where
  | anaphoric
  | immediateSituation
  | largerSituation
  | bridging
  | donkey
  deriving DecidableEq, Repr

/-- The article strength a use calls for ([schwarz-2013]): the anaphoric and donkey uses the
strong article, the situational uses the weak one, bridging the weak one by default. -/
def DefiniteUse.strength : DefiniteUse → Description.Strength
  | .anaphoric | .donkey => .familiarity
  | .immediateSituation | .largerSituation | .bridging => .uniqueness

/-- The bridging relations ([schwarz-2013]): part–whole bridging, the fridge and its crisper,
and relational bridging, the play and its author. -/
inductive Bridging where
  | partWhole
  | relational
  deriving DecidableEq, Repr

/-- The article strength a bridging relation calls for ([schwarz-2013]): part–whole bridging
the weak article, relational bridging the strong one. -/
def Bridging.strength : Bridging → Description.Strength
  | .partWhole  => .uniqueness
  | .relational => .familiarity

/-- The article systems of [schwarz-2009] and [patel-grosz-grosz-2017]: no article, a weak
article only, or weak and strong articles. -/
inductive ArticleType where
  | articleless
  | weakOnly
  | weakAndStrong
  deriving DecidableEq, Repr

/-- The definiteness-marking strategies of [jenks-2018], with [moroney-2021]'s unmarked cell:
one form marks both strengths, two forms mark them apart, only the anaphoric strength is
obligatorily marked, or neither is. A language's cell is derived from its determiner inventory
by `Determiner.Inventory.markingStrategy`. -/
inductive MarkingStrategy where
  | generallyMarked
  | bipartite
  | markedAnaphoric
  | unmarked
  deriving DecidableEq, Repr

/-- The article system of a marking strategy, which collapses the generally-marked and
marked-anaphoric cells to a single weak article. -/
def MarkingStrategy.articleType : MarkingStrategy → ArticleType
  | .generallyMarked | .markedAnaphoric => .weakOnly
  | .bipartite => .weakAndStrong
  | .unmarked  => .articleless

end Reference
