import Mathlib.Order.Nat
import Mathlib.Tactic.DeriveFintype

/-!
# Agreement Target Hierarchy [corbett-1991]

[corbett-1991]'s Agreement Hierarchy has four positions —
attributive > predicate > relative pronoun > personal pronoun — along which
the likelihood of *semantic* (rather than syntactic) agreement increases
monotonically from left to right.

The `AgreementTarget` enum below additionally carries a `verb` target, ranked
below personal pronoun, for languages with verbal gender/number agreement.
Corbett subsumes verbal agreement under the predicate position, so `verb` is
a linglib refinement, not a fifth position of Corbett's hierarchy.

This type is shared by gender typology (`Linglib/Morphology/Gender.lean` and
`Studies/Corbett1991.lean`) and number agreement
(`Studies/Corbett2000.lean`).
-/

namespace Agreement

/-- Morphosyntactic targets where agreement can surface, ranked by
    [corbett-1991]'s Agreement Hierarchy (with `verb` as a linglib
    refinement below personal pronoun — see the module docstring).

    Higher rank = closer to the controller, agreement more syntactic.
    Lower rank = further from the controller, agreement more semantic. -/
inductive AgreementTarget where
  | attributive       -- attributive adjective (e.g. French *un bon livre*)
  | predicate         -- predicate adjective/verb (e.g. Russian *kniga interesnaja*)
  | relativePronoun   -- relative pronoun (e.g. German *der/die/das*)
  | personalPronoun   -- personal pronoun (e.g. English *he/she/it*)
  | verb              -- verb (e.g. Hindi *laRkaa aayaa / laRkii aayii*)
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Numeric rank in the Agreement Hierarchy: higher = more likely to show
    agreement (more syntactic); lower = less likely (more semantic). -/
def AgreementTarget.rank : AgreementTarget → Nat
  | .attributive     => 4
  | .predicate       => 3
  | .relativePronoun => 2
  | .personalPronoun => 1
  | .verb            => 0

/-- The Agreement Hierarchy is a `LinearOrder` lifted from the rank.
    Provides `≤`, `<`, `min`, `max`, `Finset.sort`, etc. for free. -/
instance : LinearOrder AgreementTarget :=
  LinearOrder.lift' AgreementTarget.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [AgreementTarget.rank])

/-- The hierarchy rank is injective — derivable from the `LinearOrder`
    instance, restated here as a named lemma for direct invocation. -/
theorem AgreementTarget.rank_injective :
    Function.Injective AgreementTarget.rank :=
  fun a b h => by cases a <;> cases b <;> simp_all [AgreementTarget.rank]

-- ============================================================================
-- § 2: Predicate Hierarchy ([comrie-1975]; [corbett-2000] Ch 6)
-- ============================================================================

/-- The Predicate Hierarchy ([comrie-1975], systematised by
    [corbett-2000]) decomposes the predicate position on the Agreement
    Hierarchy into a sub-hierarchy:
    verb < participle < adjective < noun.

    Semantic agreement increases monotonically along this sub-hierarchy:
    if semantic agreement is possible on a verb, it is possible on a
    participle; if on a participle, then on an adjective; etc.

    This is orthogonal to `AgreementTarget`, which treats `.predicate` and
    `.verb` as two positions on the main hierarchy. The Predicate Hierarchy
    provides finer resolution *within* the predicate position. -/
inductive PredicateTarget where
  | verb         -- finite verb agreement (= AgreementTarget.verb)
  | participle   -- participial agreement
  | adjective    -- predicate adjective (= AgreementTarget.predicate)
  | noun         -- predicate noun ("she is a doctor")
  deriving DecidableEq, Repr, Inhabited

/-- Rank in the Predicate Hierarchy: higher = more likely to show
    semantic agreement. verb (0) < participle (1) < adjective (2) < noun (3). -/
def PredicateTarget.rank : PredicateTarget → Nat
  | .verb       => 0
  | .participle => 1
  | .adjective  => 2
  | .noun       => 3

/-- The Predicate Hierarchy is a `LinearOrder` lifted from the rank. -/
instance : LinearOrder PredicateTarget :=
  LinearOrder.lift' PredicateTarget.rank
    (fun a b h => by cases a <;> cases b <;> simp_all [PredicateTarget.rank])

/-- The Predicate Hierarchy rank is injective. -/
theorem PredicateTarget.rank_injective :
    Function.Injective PredicateTarget.rank :=
  fun a b h => by cases a <;> cases b <;> simp_all [PredicateTarget.rank]

/-- Map a `PredicateTarget` to the corresponding `AgreementTarget`.
    Verb maps to `.verb`; participle/adjective/noun all map to
    `.predicate`. Many-to-one, monotone (preserves the `≤` order
    once you account for rank collapsing inside `.predicate`). -/
def PredicateTarget.toAgreementTarget : PredicateTarget → AgreementTarget
  | .verb       => .verb
  | .participle => .predicate
  | .adjective  => .predicate
  | .noun       => .predicate

-- ============================================================================
-- § 3: Agreement Type ([bickel-nichols-2001])
-- ============================================================================

/-- Whether agreement markers have referential autonomy.
    [bickel-nichols-2001]

    - **grammatical**: pure agreement — the marker cannot stand alone as
      an argument; an independent NP is required (English *she walk-s*,
      the *-s* cannot replace *she*)
    - **pronominal**: cross-referencing — the marker can function as the
      sole expression of the argument; an independent NP is optional
      (Swahili *a-li-ki-soma (kitabu)* — the prefixes suffice without
      the noun)

    This distinction is orthogonal to the Agreement Hierarchy: a language
    can have pronominal agreement on verbs but grammatical agreement on
    adjectives, or vice versa. -/
inductive AgreementType where
  | grammatical   -- pure agreement (cannot stand alone as argument)
  | pronominal    -- cross-referencing (can be sole argument expression)
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 4: Agreement Direction ([bickel-nichols-2001])
-- ============================================================================

/-- Direction of agreement: which element originates ("drives") the features.
    [bickel-nichols-2001] §9

    - **headDriven**: the phrasal head provides features that percolate to
      its dependents — dependents carry the agreement morphology.
      (German/Watam NP concord: noun's gender/number → adjective, det;
      = dependent marking in the sense of §3.)
    - **dependentDriven**: a dependent provides features that the head
      matches — the head carries the agreement morphology.
      (Belhare/Swahili verb agreement: subject's person/number → verb;
      = head marking in the sense of §3.)

    Related to but distinct from `Morphology.LocusOfMarking`: locus
    is a language-level WALS typological parameter classifying where *all*
    grammatical relations are marked (head, dependent, double, zero).
    `AgreementDirection` is phenomenon-specific — a language can be
    overall head-marking (`LocusOfMarking.headMarking`) yet have specific
    head-driven agreement (e.g., NP concord in an otherwise head-marking
    language). -/
inductive AgreementDirection where
  | headDriven       -- head drives features → dependents carry morphology (NP concord)
  | dependentDriven  -- dependent drives features → head carries morphology (verb agreement)
  deriving DecidableEq, Repr, Inhabited

end Agreement
