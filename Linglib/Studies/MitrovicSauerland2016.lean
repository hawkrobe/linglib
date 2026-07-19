import Linglib.Studies.Haspelmath2007

/-!
# Mitrović & Sauerland (2016): Two conjunctions are better than one
[mitrovic-sauerland-2016] [mitrovic-sauerland-2014] [mitrovic-2021]
[haspelmath-2007]

Moreno Mitrović & Uli Sauerland. "Two conjunctions are better than one."
*Acta Linguistica Hungarica* 63 (2016) 4, 471–494.
DOI: 10.1556/064.2016.63.4.5

The paper proposes a universal **J-μ system** for DP coordination: μ is an
e-type head (combines with a single individual) and J is a t-type head
(combines two truth-value-typed arguments). Languages parametrise which
heads are overtly pronounced; the predictions are:

- **J-type coordinators** (e.g. English *and*) have propositional uses, do not
  double, and lack additive/quantificational uses.
- **μ-type coordinators** (e.g. Japanese *mo*) combine DPs, can double, and
  may have additive/quantificational uses.
- Some languages overtly realise both heads, giving triadic exponency
  (J + two μ): [mitrovic-sauerland-2016] §3.1 lists SE Macedonian,
  Hungarian, and Avar as their attested cases (with SerBo-Croatian
  approaching the pattern with adversative J).

## Main declarations

* `hasAllThreeStrategies` — propositional predicate for triadic exponency.
* `mu_additive_generalization` — every language with a μ morpheme has a μ
  morpheme that also serves as the additive particle (§3).
* `j_is_universal` — every M&S focus language has a J-only strategy (§1).
* `all_three_is_rare` — within the focus sample, only Hungarian and Georgian
  show triadic exponency; the paper's own sample uses SE Macedonian, Avar,
  Hungarian (none of SE Macedonian / Avar / SerBo-Croatian is encoded here,
  so the formalised claim is restricted to the M&S focus sub-sample).
* `mu_kind_asymmetry` — Georgian μ is bound, Hungarian μ is free; [bill-etal-2025]
  link this morphological asymmetry to acquisition difficulty.

## Implementation notes

* Language records (`english`, `japanese`, `hungarian`, `georgian`, `latin`,
  `korean`, `slovenian`) are defined in `Studies/Haspelmath2007.lean` and
  reused here unchanged. Triadic-exponency classification of Georgian
  follows [mitrovic-2021]; [mitrovic-sauerland-2016] itself
  does not include Georgian.
* The original paper's languages SE Macedonian, Avar, and SerBo-Croatian
  are not yet in the sample.
-/

namespace MitrovicSauerland2016

open Syntax.Coordination
open Haspelmath2007

/-! ### Triadic-exponency predicate -/

/-- A language exhibits **triadic exponency** when all three M&S strategies
    (J-only, MU-only, J-MU) are attested. The paper's strongest synchronic
    typological observation (§3.1). -/
def hasAllThreeStrategies (sys : ConjunctionSystem) : Prop :=
  sys.hasStrategy .jOnly ∧ sys.hasStrategy .muOnly ∧ sys.hasStrategy .jMu

instance (sys : ConjunctionSystem) : Decidable (hasAllThreeStrategies sys) := by
  unfold hasAllThreeStrategies; infer_instance

/-! ### M&S 2016 generalisations -/

/-- **MU is additive.** Every language with a MU conjunction particle uses
    the same morpheme as its additive ("also/too") particle ([mitrovic-sauerland-2016]
    §3). MU is a single lexical item with subset semantics that appears in
    both conjunction and additive contexts. -/
theorem mu_additive_generalization :
    ∀ sys ∈ allLanguages,
      (∃ m ∈ sys.morphemes, m.entry.role = .mu) → sys.muIsAdditive := by
  decide

/-- **J is universal in the M&S focus sample.** Every M&S-classified language
    has at least the J-only strategy ([mitrovic-sauerland-2016] §3). -/
theorem j_is_universal : ∀ sys ∈ msLanguages, sys.hasStrategy .jOnly := by
  decide

/-- **Triadic exponency is rare.** Within the 19-language sample, the only
    languages exhibiting all three M&S strategies (J, MU, J-MU) are Hungarian
    and Georgian (iso codes "hun", "kat"). The biconditional pins which
    languages have the rare pattern and which do not. -/
theorem all_three_is_rare :
    ∀ sys ∈ allLanguages,
      hasAllThreeStrategies sys ↔ sys.iso = "kat" ∨ sys.iso = "hun" := by
  decide

/-- **MU attachment asymmetry.** Georgian MU (*-c*) is a bound enclitic;
    Hungarian MU (*is*) is free. [bill-etal-2025] (with [mitrovic-2021])
    propose this morphological difference may explain the acquisition
    asymmetry: bound morphemes are harder to segment. -/
theorem mu_kind_asymmetry :
    georgian.muKind = some (.bound .after .clitic) ∧
    hungarian.muKind = some .free := by
  decide

end MitrovicSauerland2016
