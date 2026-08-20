import Mathlib.Tactic.TypeStar

/-!
# Roots, categorizers, vocabulary items, and allosemes

The objects of Distributed Morphology ([halle-marantz-1993]): acategorial
roots individuated by arbitrary indices, the categorizing heads n/v/a, and
the rule types of the two interpretive lists — `VI.VocabItem` (List 2, form)
and `Allosemy.AllosemicEntry` (List 3, meaning), the latter conditioned by
`Allosemy.SyntacticContext`. The shared selection-engine instances live in
`DistributedMorphology/Basic.lean`.
-/

namespace DistributedMorphology

/-- A Root terminal node, individuated by an arbitrary index alone — with
deliberately no form or meaning fields, following [harley-2014]'s answer to
what roots are. It receives its form at Vocabulary Insertion. A different
object from the comparative-concept root of `Morphology/Root/Basic.lean`,
which is a contentful morph. -/
structure Root where
  /-- The individuating index. -/
  index : Nat
  deriving DecidableEq, Repr

/-- A categorizing head that merges with an acategorial root to project
    syntactic structure. The three options correspond to the functional
    heads n, v, a in Distributed Morphology ([marantz-1997], [harley-2014] §2). -/
inductive Categorizer where
  | n  -- nominal categorizer
  | v  -- verbal categorizer
  | a  -- adjectival categorizer
  deriving DecidableEq, Repr

namespace VI

/-- A Vocabulary Item: a rule mapping morphosyntactic context to a
    phonological exponent.

    - `Ctx`: the type of morphosyntactic contexts (e.g., feature bundles)
    - `Root`: the type of root identifiers (for root-specific rules)

    The `specificity` field encodes the Elsewhere Condition: when
    multiple rules match, the highest-specificity rule wins. In
    practice, specificity equals the number of features the context
    checks — a rule conditioned on [ACC, +animate] (specificity 2) beats
    a default rule with no feature requirements (specificity 0). -/
structure VocabItem (Ctx Root : Type*) where
  /-- The phonological exponent inserted at the terminal. -/
  exponent : String
  /-- Context check: does the terminal's feature bundle match? -/
  contextMatch : Ctx → Bool
  /-- Root restriction: which roots this rule applies to.
      `none` means the rule is unrestricted (default/elsewhere). -/
  rootMatch : Option (Root → Bool) := none
  /-- Specificity for Elsewhere Condition resolution. Higher = more
      specific. When two rules both match, the higher-specificity
      rule wins. -/
  specificity : Nat := 0

/-- Does a Vocabulary Item match at a given terminal node?
    Checks both the morphosyntactic context and the root restriction. -/
def VocabItem.matches {Ctx Root : Type*}
    (vi : VocabItem Ctx Root) (ctx : Ctx) (root : Root) : Bool :=
  vi.contextMatch ctx &&
  match vi.rootMatch with
  | none => true
  | some f => f root

end VI

namespace Allosemy

/-- A syntactic context that conditions alloseme selection.

    §2.4 of [benz-2025]: allosemy is conditioned by the semantics of a
    previously interpreted domain (below) or the syntactic features of the
    next higher head (above). Both cyclic locality and linear adjacency
    play a role, but the exact locality conditions are an open question.

    We represent context minimally as what is structurally below and
    above the allosemic head. -/
structure SyntacticContext where
  /-- Category of the complement (below). `none` = no complement. -/
  belowCat : Option Categorizer := none
  /-- Category of the embedding head (above). `none` = root context. -/
  aboveCat : Option Categorizer := none
  /-- Does the complement denote an event? -/
  complementIsEventive : Bool := false
  /-- Does the complement denote a state? ([kratzer-1996] §2.3: the
      stative-vs-dynamic split conditions the Voice alloseme.) -/
  complementIsStative : Bool := false
  deriving DecidableEq, Repr

/-- A partial context specification `spec` **matches** a fully-specified
query context `c` when every non-wildcard field of `spec` agrees with
`c`. A field at its default (`none` / `false`) is a **wildcard**,
constraining nothing; a set field must agree. More specified contexts
match strictly fewer queries — the applicability-set inclusion that
orders exponence rules ([kiparsky-1973]). -/
def SyntacticContext.matches (spec c : SyntacticContext) : Bool :=
  (spec.belowCat == none || spec.belowCat == c.belowCat) &&
  (spec.aboveCat == none || spec.aboveCat == c.aboveCat) &&
  (!spec.complementIsEventive || c.complementIsEventive) &&
  (!spec.complementIsStative || c.complementIsStative)

/-- The specificity **score**: the number of non-wildcard fields. Higher
score = more specified = strictly smaller applicability set, so the score
reflects the specificity preorder contravariantly
(`SyntacticContext.specificity_le_of_matches_subset`). -/
def SyntacticContext.specificity (c : SyntacticContext) : Nat :=
  (if c.belowCat.isSome then 1 else 0) + (if c.aboveCat.isSome then 1 else 0)
    + (if c.complementIsEventive then 1 else 0) + (if c.complementIsStative then 1 else 0)

/-- A single alloseme: a labeled meaning available in a particular context. -/
structure AllosemicEntry (Sem : Type) where
  /-- Human-readable label for this alloseme. -/
  label : String
  /-- The semantic contribution. -/
  denotation : Sem
  /-- The conditioning context. -/
  context : SyntacticContext
  deriving BEq, Repr

/-- An allosemic head: a functional morpheme with multiple
    context-dependent meanings.

    §2.6 of [benz-2025]: "This dissertation is about examining the
    principal promise of allosemy as a tool in syntactic theory." -/
structure AllosemicHead (Sem : Type) where
  /-- Which functional head (n, v, a). -/
  morpheme : Categorizer
  /-- The available allosemes in their contexts. -/
  entries : List (AllosemicEntry Sem)
  deriving Repr

/-- Number of distinct meanings available for this head. -/
def AllosemicHead.allosemeCount {Sem : Type} (h : AllosemicHead Sem) : Nat :=
  h.entries.length

/-- The denotations licensed for the head in context `c` — the entries whose
conditioning context matches `c`. Alloseme ambiguity in a context is
non-singleton licensing, and the canonical default among the licensed
entries is the Elsewhere winner (`selectBy_score_isElsewhereWinner`). -/
def AllosemicHead.licensed {Sem : Type} (h : AllosemicHead Sem)
    (c : SyntacticContext) : List Sem :=
  (h.entries.filter (·.context.matches c)).map (·.denotation)

end Allosemy

end DistributedMorphology
