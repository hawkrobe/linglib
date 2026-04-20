import Linglib.Theories.Semantics.Exhaustification.FreeChoice
import Linglib.Phenomena.Focus.AdditiveParticles.Data
import Mathlib.Data.Set.Basic

/-!
# Ahn (2015): The Semantics of Additive *Either*
@cite{ahn-2015}

Proceedings of Sinn und Bedeutung 19, pp. 20–35.

## Key Proposal

*Too* and *either* are two-place predicates taking the host proposition p
and a silent propositional anaphor q as arguments:
- ⟦**too**⟧(q)(p) = q ⊓ p (meet in the Boolean algebra of propositions)
- ⟦**either**⟧(q)(p) = q ⊔ p (join)

The propositional anaphor q must be a distinct focus alternative of p
(@cite{rooth-1985}), capturing three properties shared by both particles:
1. **Antecedent Requirement**: q must be salient in discourse
2. **Focus Sensitivity**: q must be a focus alternative of p
3. **Distinctness**: q must be distinct from p

This replaces the traditional fully presuppositional account
(@cite{heim-1992}, Rullmann 2003) with an assertive one. The key
advantage is that it handles cases where *too*'s additive meaning does
not seem fully presupposed (e.g., "I don't know if Mary is in the
elevator, but if John is in the elevator too, we will go over the weight
limit").

## NPI Distribution via Boolean Algebra

`Set World` is a `BooleanAlgebra` (via Mathlib's pointwise instances),
and the entire NPI asymmetry falls out of the ⊓/⊔ duality:

- **⊓ entails its components** (`inf_le_left`, `inf_le_right`), so
  exhaustification of *too* is always vacuous — not an NPI.
- **⊔ does not entail its components**, so exhaustification of *either*
  negates them. In positive contexts this yields ⊥ (`inf_compl_eq_bot`
  via De Morgan). In negative contexts, complementation reverses the
  ordering (`compl_le_compl`), making all alternatives entailed — vacuous.

The ∨/∧ scale parallels ∃/∀: *either* (⊔, weak) is an NPI for exactly
the same structural reason as *any* (∃, weak). The bridge theorem
`either_npi_via_chierchia` instantiates @cite{chierchia-2013}'s SI–NPI
generalization.

Note: the full NPI derivation uses the naive exhaustification operator
O_ALT (which negates ALL non-entailed alternatives including domain
alternatives), not the more conservative exh_IE (which only negates
innocently excludable alternatives). Under exh_IE, the domain
alternatives q and p are not both innocently excludable (negating both
is inconsistent with q ∨ p), so exh_IE yields exclusive disjunction
rather than contradiction. The NPI result requires Chierchia's assumption
that NPIs obligatorily activate domain alternatives exhaustified by O_ALT.
-/

namespace Ahn2015

open Exhaustification

variable {World : Type*}

-- ═══════════════════════════════════════════════════════════════════════════
-- Core Semantic Proposal: too = ⊓, either = ⊔
-- ═══════════════════════════════════════════════════════════════════════════

/-- ⟦**too**⟧(q)(p) = q ⊓ p — meet in the Boolean algebra of propositions. -/
abbrev tooDenotation (q p : Set World) : Set World := q ⊓ p

/-- ⟦**either**⟧(q)(p) = q ⊔ p — join in the Boolean algebra of propositions. -/
abbrev eitherDenotation (q p : Set World) : Set World := q ⊔ p

-- ═══════════════════════════════════════════════════════════════════════════
-- De Morgan: negation-scope interactions
-- ═══════════════════════════════════════════════════════════════════════════

/-- ¬(q ⊓ p) = qᶜ ⊔ pᶜ — De Morgan for *too*. -/
theorem too_demorgan (q p : Set World) : (tooDenotation q p)ᶜ = qᶜ ⊔ pᶜ := compl_inf

/-- ¬(q ⊔ p) = qᶜ ⊓ pᶜ — De Morgan for *either*. -/
theorem either_demorgan (q p : Set World) : (eitherDenotation q p)ᶜ = qᶜ ⊓ pᶜ := compl_sup

-- ═══════════════════════════════════════════════════════════════════════════
-- NPI asymmetry: ⊓ entails components, ⊔ does not
-- ═══════════════════════════════════════════════════════════════════════════

/-- *Too* entails all alternatives — exhaustification always vacuous (not NPI).
    q ⊓ p ≤ q, q ⊓ p ≤ p, q ⊓ p ≤ q ⊔ p. -/
theorem too_entails_all_alts (q p : Set World) :
    tooDenotation q p ≤ q ∧ tooDenotation q p ≤ p
      ∧ tooDenotation q p ≤ eitherDenotation q p :=
  ⟨inf_le_left, inf_le_right, inf_le_left.trans le_sup_left⟩

/-- *Either* in positive context: O_ALT(q ⊔ p) = (q ⊔ p) ⊓ qᶜ ⊓ pᶜ = ⊥.
    By De Morgan, qᶜ ⊓ pᶜ = (q ⊔ p)ᶜ, so this is a ⊓ aᶜ = ⊥. -/
theorem either_positive_contradiction (q p : Set World) :
    eitherDenotation q p ⊓ qᶜ ⊓ pᶜ = ⊥ := by
  rw [inf_assoc, ← compl_sup, inf_compl_eq_bot]

/-- *Either* under negation: all alternatives entailed (vacuous).
    (q ⊔ p)ᶜ ≤ qᶜ ⊓ pᶜ ⊓ (q ⊓ p)ᶜ by `compl_le_compl`. -/
theorem either_negative_vacuous (q p : Set World) :
    (eitherDenotation q p)ᶜ ≤ qᶜ ⊓ pᶜ ⊓ (q ⊓ p)ᶜ :=
  le_inf (le_inf (compl_le_compl le_sup_left) (compl_le_compl le_sup_right))
    (compl_le_compl (inf_le_left.trans le_sup_left))

-- ═══════════════════════════════════════════════════════════════════════════
-- Bridge: @cite{chierchia-2013} SI–NPI Generalization
-- ═══════════════════════════════════════════════════════════════════════════

/-- *Either*'s NPI behavior as an instance of @cite{chierchia-2013}'s
    SI–NPI generalization: for any antitone (DE) context C,
    C(q ⊔ p) ∧ ¬C(q ⊓ p) is vacuous. -/
theorem either_npi_via_chierchia (C : FreeChoice.Ctx World)
    (hDE : Antitone C) (q p : Set World) :
    FreeChoice.siVacuous C (eitherDenotation q p) (q ⊓ p) :=
  FreeChoice.si_vacuous_in_de C hDE _ _
    (inf_le_left.trans le_sup_left : q ⊓ p ≤ q ⊔ p)

-- ═══════════════════════════════════════════════════════════════════════════
-- Data
-- ═══════════════════════════════════════════════════════════════════════════

open Phenomena.Focus.AdditiveParticles (AdditiveParticleDatum)

/-- "either" with parallel negation — licensed (negative context). -/
def eitherBasic : AdditiveParticleDatum :=
  { sentence := "John didn't come. Mary didn't come either."
  , antecedent := "John didn't come"
  , prejacent := "Mary didn't come"
  , particle := "either"
  , resolvedQuestion := some "Who didn't come?"
  , felicity := .ok
  , useType := .standard
  , notes := "Negative context: ¬(q ∨ p) → exhaustification vacuous"
  , source := "Ahn (2015)" }

/-- Verb focus with "either" — licensed. -/
def eitherVerb : AdditiveParticleDatum :=
  { sentence := "John doesn't sing. He doesn't dance either."
  , antecedent := "John doesn't sing"
  , prejacent := "John doesn't dance"
  , particle := "either"
  , resolvedQuestion := some "What doesn't John do?"
  , felicity := .ok
  , useType := .standard
  , notes := "Negative context with verb focus"
  , source := "Ahn (2015)" }

/-- "either" in positive context — ungrammatical (Ahn's (41)). -/
def eitherPositiveUngrammatical : AdditiveParticleDatum :=
  { sentence := "*John left either."
  , antecedent := "Mary left"
  , prejacent := "John left"
  , particle := "either"
  , resolvedQuestion := some "Who left?"
  , felicity := .odd
  , useType := .standard
  , notes := "Positive context: O_ALT(q ∨ p) = ⊥ (see either_positive_contradiction)"
  , source := "Ahn (2015)" }

/-- "too" under negation — grammatical (Ahn's (24)–(25)). -/
def tooUnderNegation : AdditiveParticleDatum :=
  { sentence := "Sue bought some books. Mary didn't buy them too."
  , antecedent := "Sue bought some books"
  , prejacent := "Mary bought them"
  , particle := "too"
  , resolvedQuestion := some "Who bought the books?"
  , felicity := .ok
  , useType := .standard
  , notes := "Negation scopes over too: ¬(q ⊓ p) = qᶜ ⊔ pᶜ (see too_demorgan)"
  , source := "Ahn (2015)" }

/-- "almost" does not license "either" (Ahn's (45)).
    Rullmann's licensing condition wrongly predicts *almost* licenses
    *either*. The exhaustification account correctly rules it out. -/
def almostDoesNotLicenseEither : AdditiveParticleDatum :=
  { sentence := "*The paper is almost finished either."
  , antecedent := ""
  , prejacent := "The paper is finished"
  , particle := "either"
  , resolvedQuestion := none
  , felicity := .odd
  , useType := .standard
  , notes := "Almost is DE but exhaustification still contradicts (Ahn's advantage over Rullmann)"
  , source := "Ahn (2015)" }

/-- Rullmann's problem case: *either* blocked after positive antecedent (Ahn's (5)). -/
def rullmannProblem : AdditiveParticleDatum :=
  { sentence := "John washed the dishes. *He shouldn't do the laundry either."
  , antecedent := "John washed the dishes"
  , prejacent := "He does the laundry"
  , particle := "either"
  , resolvedQuestion := some "What should he do?"
  , felicity := .odd
  , useType := .standard
  , notes := "Positive antecedent incompatible with either"
  , source := "Ahn (2015), Rullmann (2003)" }

/-- Negative antecedent with parallel structure — basic "either" (Ahn's (32)). -/
def eitherNegAntecedent : AdditiveParticleDatum :=
  { sentence := "Bill didn't leave. John didn't leave either."
  , antecedent := "Bill didn't leave"
  , prejacent := "John didn't leave"
  , particle := "either"
  , resolvedQuestion := some "Who didn't leave?"
  , felicity := .ok
  , useType := .standard
  , notes := "¬⟦either⟧(q)(p) = ¬(q ⊔ p) = qᶜ ⊓ pᶜ"
  , source := "Ahn (2015)" }

/-- Non-presuppositional "too" — the elevator example (Ahn's intro).
    Under the conjunctive account, *too* asserts q ⊓ p, and the whole
    assertion is entailed, so q need not be presupposed. -/
def elevatorToo : AdditiveParticleDatum :=
  { sentence := "I don't know if Mary is in the elevator. But if John is in the elevator too, we will go over the weight limit."
  , antecedent := "Mary is in the elevator"
  , prejacent := "John is in the elevator"
  , particle := "too"
  , resolvedQuestion := some "Will we go over the weight limit?"
  , felicity := .ok
  , useType := .standard
  , notes := "Additive meaning not fully presupposed — motivates conjunctive account"
  , source := "Ahn (2015)" }

def examples : List AdditiveParticleDatum :=
  [ eitherBasic, eitherVerb, eitherPositiveUngrammatical
  , tooUnderNegation, almostDoesNotLicenseEither, rullmannProblem
  , eitherNegAntecedent, elevatorToo ]

end Ahn2015
