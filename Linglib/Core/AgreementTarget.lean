/-!
# Agreement Target Hierarchy @cite{corbett-1991}

The Agreement Hierarchy (@cite{corbett-1991}) ranks morphosyntactic targets
by likelihood of showing agreement: attributive adjectives are most likely,
verbs least likely. If a language shows gender/number agreement on a lower
target, it shows agreement on all higher targets.

This type is shared by gender typology (`Phenomena/Gender/Typology.lean`)
and number agreement (`Phenomena/Agreement/Studies/Corbett2000.lean`).
-/

namespace Core

/-- Morphosyntactic targets where agreement can surface, ordered by the
    Agreement Hierarchy (@cite{corbett-1991}).

    Higher rank = more likely to show agreement (closer to controller).
    Lower rank = less likely (further from controller, more semantic). -/
inductive AgreementTarget where
  | attributive       -- attributive adjective (e.g. French *un bon livre*)
  | predicate         -- predicate adjective/verb (e.g. Russian *kniga interesnaja*)
  | relativePronoun   -- relative pronoun (e.g. German *der/die/das*)
  | personalPronoun   -- personal pronoun (e.g. English *he/she/it*)
  | verbTarget        -- verb (e.g. Hindi *laRkaa aayaa / laRkii aayii*)
  deriving DecidableEq, Repr

/-- Numeric rank in the Agreement Hierarchy: higher = more likely to show
    agreement (more syntactic); lower = less likely (more semantic). -/
def AgreementTarget.rank : AgreementTarget → Nat
  | .attributive     => 4
  | .predicate       => 3
  | .relativePronoun => 2
  | .personalPronoun => 1
  | .verbTarget      => 0

/-- The hierarchy rank is injective — no two positions share a rank.
    This guarantees the Agreement Hierarchy is a total (not just partial) order:
    for any two targets, one strictly outranks the other. -/
theorem agreement_rank_injective (a b : AgreementTarget) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [AgreementTarget.rank]

-- ============================================================================
-- § 2: Predicate Hierarchy (@cite{corbett-2000} Ch 6)
-- ============================================================================

/-- The Predicate Hierarchy (@cite{corbett-2000}) decomposes the predicate
    position on the Agreement Hierarchy into a sub-hierarchy:
    verb < participle < adjective < noun.

    Semantic agreement increases monotonically along this sub-hierarchy:
    if semantic agreement is possible on a verb, it is possible on a
    participle; if on a participle, then on an adjective; etc.

    This is orthogonal to `AgreementTarget`, which treats `.predicate` and
    `.verbTarget` as two positions on the main hierarchy. The Predicate
    Hierarchy provides finer resolution *within* the predicate position. -/
inductive PredicateTarget where
  | verb         -- finite verb agreement (= AgreementTarget.verbTarget)
  | participle   -- participial agreement
  | adjective    -- predicate adjective (= AgreementTarget.predicate)
  | noun         -- predicate noun ("she is a doctor")
  deriving DecidableEq, Repr

/-- Rank in the Predicate Hierarchy: higher = more likely to show
    semantic agreement. verb (0) < participle (1) < adjective (2) < noun (3). -/
def PredicateTarget.rank : PredicateTarget → Nat
  | .verb       => 0
  | .participle => 1
  | .adjective  => 2
  | .noun       => 3

/-- The Predicate Hierarchy rank is injective — a total order on predicate
    positions. Semantic agreement increases monotonically along the hierarchy. -/
theorem predicate_rank_injective (a b : PredicateTarget) (h : a.rank = b.rank) : a = b := by
  cases a <;> cases b <;> simp_all [PredicateTarget.rank]

/-- Map a PredicateTarget to the corresponding AgreementTarget.
    The predicate sub-positions map to either `.predicate` or `.verbTarget`. -/
def PredicateTarget.toAgreementTarget : PredicateTarget → AgreementTarget
  | .verb       => .verbTarget
  | .participle => .predicate  -- participial agreement ≈ predicate position
  | .adjective  => .predicate
  | .noun       => .predicate

-- ============================================================================
-- § 3: Agreement Type (@cite{bickel-nichols-2001})
-- ============================================================================

/-- Whether agreement markers have referential autonomy.
    @cite{bickel-nichols-2001}

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
  deriving DecidableEq, Repr

-- ============================================================================
-- § 4: Agreement Direction (@cite{bickel-nichols-2001})
-- ============================================================================

/-- Direction of agreement: which element originates ("drives") the features.
    @cite{bickel-nichols-2001} §9

    - **headDriven**: the phrasal head provides features that percolate to
      its dependents — dependents carry the agreement morphology.
      (German/Watam NP concord: noun's gender/number → adjective, det;
      = dependent marking in the sense of §3.)
    - **dependentDriven**: a dependent provides features that the head
      matches — the head carries the agreement morphology.
      (Belhare/Swahili verb agreement: subject's person/number → verb;
      = head marking in the sense of §3.)

    Related to but distinct from `Core.Morphology.LocusOfMarking`: locus
    is a language-level WALS typological parameter classifying where *all*
    grammatical relations are marked (head, dependent, double, zero).
    `AgreementDirection` is phenomenon-specific — a language can be
    overall head-marking (`LocusOfMarking.headMarking`) yet have specific
    head-driven agreement (e.g., NP concord in an otherwise head-marking
    language). -/
inductive AgreementDirection where
  | headDriven       -- head drives features → dependents carry morphology (NP concord)
  | dependentDriven  -- dependent drives features → head carries morphology (verb agreement)
  deriving DecidableEq, Repr

end Core
