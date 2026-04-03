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

/-- The hierarchy is strictly ordered. -/
theorem agreement_hierarchy_strict :
    AgreementTarget.attributive.rank > AgreementTarget.predicate.rank ∧
    AgreementTarget.predicate.rank > AgreementTarget.relativePronoun.rank ∧
    AgreementTarget.relativePronoun.rank > AgreementTarget.personalPronoun.rank ∧
    AgreementTarget.personalPronoun.rank > AgreementTarget.verbTarget.rank := by
  native_decide

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

/-- The Predicate Hierarchy is strictly ordered. -/
theorem predicate_hierarchy_strict :
    PredicateTarget.verb.rank < PredicateTarget.participle.rank ∧
    PredicateTarget.participle.rank < PredicateTarget.adjective.rank ∧
    PredicateTarget.adjective.rank < PredicateTarget.noun.rank := by
  native_decide

/-- Map a PredicateTarget to the corresponding AgreementTarget.
    The predicate sub-positions map to either `.predicate` or `.verbTarget`. -/
def PredicateTarget.toAgreementTarget : PredicateTarget → AgreementTarget
  | .verb       => .verbTarget
  | .participle => .predicate  -- participial agreement ≈ predicate position
  | .adjective  => .predicate
  | .noun       => .predicate

end Core
