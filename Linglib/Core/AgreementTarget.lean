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
  deriving DecidableEq, BEq, Repr

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

end Core
