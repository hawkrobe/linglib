import Linglib.Data.Examples.BeckOdaSugisaki2004
import Linglib.Semantics.Degree.Basic

/-!
# Beck, Oda & Sugisaki 2004: Parametric Variation in the Semantics of Comparison

[beck-oda-sugisaki-2004] argue that Japanese *yori*-constructions are not
English-style degree comparatives: the *yori*-constituent is a free relative
denoting an individual ((34): ⟦John-ga kaita⟧ = what John wrote), which sets
the context for a positive or contextual comparative in the main clause,
rather than a *than*-clause denoting a set of degrees. Japanese, they
conjecture, lacks binding of degree variables in the syntax — their Degree
Abstraction Parameter — while English has it. Three empirical differences
follow, recorded in `Data/Examples/BeckOdaSugisaki2004.json`: variable
acceptability of degree (vs amount) *yori*-comparatives ((3)–(4)), the absence
of subcomparatives ((5-a) vs (5-b) — the English side is
`Degree.subcomparative`), and the absence of English-like negative-island
effects ((6)).
-/

namespace BeckOdaSugisaki2004

open Data.Examples (LinguisticExample)

/-- The standard clause of this construction only has a well-formed LF if the
language abstracts over degree variables in the syntax. -/
def standardRequiresAbstraction (e : LinguisticExample) : Prop :=
  e.feature? "standard_requires_degree_abstraction" = some "true"

instance (e : LinguisticExample) : Decidable (standardRequiresAbstraction e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The Japanese rows of (3)–(6). -/
def japaneseRows : List LinguisticExample :=
  [ Examples.amount_yori, Examples.subcomp_ja, Examples.negisland_ja ]

/-- The paper's parameter at work in Japanese: a construction whose standard
clause requires syntactic degree abstraction is ungrammatical, and every
other recorded construction is acceptable. The degraded-but-not-star (4-a)
is excluded — its variability is the paper's separate explanandum. -/
theorem japanese_lacks_degree_abstraction :
    ∀ e ∈ japaneseRows,
      e.judgment = .ungrammatical ↔ standardRequiresAbstraction e := by
  decide

/-- The English controls: both degree-abstraction constructions are
well-formed LFs, and (6-b)'s ungrammaticality is instead Rullmann-style
maximality failure over the degree set — undefined, not unbuildable. -/
def englishRows : List LinguisticExample :=
  [ Examples.subcomp_en, Examples.negisland_en ]

/-- English has degree abstraction: the subcomparative (5-b) is acceptable
even though its standard requires it. -/
theorem english_subcomparative_available :
    Examples.subcomp_en.judgment = .acceptable ∧
      standardRequiresAbstraction Examples.subcomp_en := by
  decide

end BeckOdaSugisaki2004
