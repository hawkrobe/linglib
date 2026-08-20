import Linglib.Morphology.DistributedMorphology.Categorizer.Basic

/-!
# Vocabulary items and allosemes

The rule types of Distributed Morphology's two interpretive lists:
`VI.VocabItem` pairs a phonological exponent with the context that
licenses it (List 2), and `Allosemy.AllosemicEntry` pairs a meaning with
the conditioning `Allosemy.SyntacticContext` (List 3). The shared
selection-engine instances live in `DistributedMorphology/Basic.lean`.

## References

* [M. Halle and A. Marantz, *Distributed Morphology and the pieces of
  inflection*][halle-marantz-1993]
* [J. Benz, *Structure and interpretation across categories*][benz-2025]
-/

namespace DistributedMorphology

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

/-- A single alloseme: a meaning available in a particular context. A
head's List-3 inventory is its alloseme *vocabulary*, a bare
`List (AllosemicEntry Sem)` — any functional morpheme can carry one
(the categorizers, Voice, prefixes), so no head type is baked in. -/
structure AllosemicEntry (Sem : Type) where
  /-- The semantic contribution. -/
  denotation : Sem
  /-- The conditioning context. -/
  context : SyntacticContext
  deriving BEq, Repr

/-- The denotations an alloseme vocabulary licenses in context `c` — the
entries whose conditioning context matches `c`. Alloseme ambiguity in a
context is non-singleton licensing, and the canonical default among the
licensed entries is the Elsewhere winner
(`selectBy_score_isElsewhereWinner`). -/
def licensed {Sem : Type} (v : List (AllosemicEntry Sem))
    (c : SyntacticContext) : List Sem :=
  (v.filter (·.context.matches c)).map (·.denotation)

end Allosemy

end DistributedMorphology
