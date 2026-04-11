import Linglib.Theories.Semantics.Lexical.Determiner.ChoiceFunction
import Linglib.Theories.Semantics.Lexical.Determiner.Definite
import Linglib.Theories.Semantics.Lexical.Determiner.UnifiedUniversal
import Linglib.Core.Definiteness

/-!
# Akan (Kwa) Determiners
@cite{zimmermann-2026} @cite{owusu-2022} @cite{bombi-2018} @cite{philipp-2022}

Fragment entries for the Akan (Kwa, Niger-Congo) determiner system,
covering definiteness markers, indefinites, and universal quantifiers.

## Definiteness

Akan has an overt DEF-marker *nó* whose analysis is disputed:

| Analysis            | Source                    | DefPresupType       |
|---------------------|--------------------------|---------------------|
| Strong (familiarity)| @cite{schwarz-2013}      | familiarity         |
| Weak (uniqueness)   | @cite{bombi-2018}        | uniqueness          |
| Demonstrative       | @cite{owusu-2022}        | familiarity + ¬uniq |

All analyses agree that bare NPs (without *nó*) can receive definite
readings in Akan, making Akan a `WeakArticleStrategy.bareNominal`
language. The bare NP handles uniqueness-based definiteness covertly,
while *nó* overtly marks familiarity.

Key empirical facts (@cite{owusu-2022}, @cite{zimmermann-2026} §3.1):
- *nó* is infelicitous with globally unique NPs (*ewia* 'sun') → ¬uniqueness
- *nó* requires a discourse-familiar antecedent → familiarity
- *nó* is obligatory in larger-situation contexts (ex. 4a) → previous reference

## Indefiniteness

Akan *bí* is analysed as a skolemized choice function by @cite{owusu-2022},
explaining its obligatory wide scope under negation. Hausa *wani/wata*
by contrast is an ∃-quantifier with flexible scope. This contrast provides
cross-linguistic evidence for the choice function vs ∃-quantifier distinction
that English alone cannot disambiguate.

## Universal Quantification

Akan *bi-ara* shows flexible interpretation: universal (✓every), NPI
(✓nobody), and free choice (✓any), depending on structural context.
@cite{philipp-2022} proposes a structural ambiguity account via the
alternative-sensitive scalar operator *ara*.
-/

namespace Fragments.Akan.Determiners

open Semantics.Lexical.Determiner.ChoiceFunction
open Semantics.Lexical.Determiner.Definite
open Semantics.Lexical.Determiner.UnifiedUniversal
open Core.Definiteness
open Core.Presupposition

-- ════════════════════════════════════════════════════
-- § 1. Definiteness: *nó*
-- ════════════════════════════════════════════════════

/-- Analysis options for Akan *nó*, reflecting the current debate.
    @cite{zimmermann-2026} §3.1 surveys all three positions. -/
inductive NoAnalysis where
  | strong        -- @cite{schwarz-2013}: anaphoric familiarity (strong DEF)
  | weak          -- @cite{bombi-2018}: situational uniqueness (weak DEF)
  | demonstrative -- @cite{owusu-2022}: familiarity + non-uniqueness
  deriving DecidableEq, Repr

/-- Each analysis predicts a different presupposition type. -/
def NoAnalysis.toPresupType : NoAnalysis → DefPresupType
  | .strong        => .familiarity
  | .weak          => .uniqueness
  | .demonstrative => .familiarity

/-- Bombi's (2018) uniqueness-based analysis captures the most empirical
    data: it explains why *nó* occurs on non-uniquely-referring NPs (in
    familiarity contexts where uniqueness is evaluated against the context
    of a preceding clause), the different distribution of *nó* and
    demonstrative *saa...nó*, and the non-occurrence on proper names.
    @cite{zimmermann-2026} §3.1 concludes Bombi's analysis fares better
    than Owusu's demonstrative analysis. -/
def preferredAnalysis : NoAnalysis := .weak

/-- ⟦nó⟧ under the familiarity analysis: presupposes a unique salient
    discourse referent matching the restrictor. Grounded in `the_fam`
    from `Definite.lean` — the theory-layer denotation for Schwarz's
    strong article.

    Under Bombi's preferred uniqueness analysis, the same denotation
    applies but evaluated against a discourse-restricted situation
    rather than the full evaluation world. -/
def noSem {E : Type} [DecidableEq E]
    (dc : DiscourseContext E)
    (restrictor : E → Bool) (scope : E → Bool) :=
  the_fam dc restrictor scope

-- ════════════════════════════════════════════════════
-- § 2. Bare NPs
-- ════════════════════════════════════════════════════

/-- Akan bare NP interpretation depends on context:

    - Globally unique NPs (*ewia* 'sun'): definite reading without *nó*
      → covert uniqueness-based iota
    - Non-singleton-denoting NPs: indefinite / ∃-quantifier reading
      → covert ∃ or type-shift

    @cite{owusu-2022}, @cite{philipp-2022}. Akan is classified as
    `WeakArticleStrategy.bareNominal` in `Core/Definiteness.lean`. -/
inductive BareNPReading where
  | definite    -- covert ι: globally unique referent
  | indefinite  -- covert ∃: non-singleton denotation
  deriving DecidableEq, Repr

/-- When a bare NP gets an indefinite reading, it is a covert
    ∃-quantifier — hence narrow scope only. -/
def bareNPIndefType : IndefType := .existential

-- ════════════════════════════════════════════════════
-- § 3. Indefinite *bí*: Choice Function Semantics
-- ════════════════════════════════════════════════════

/-- *bí* is analysed as a choice function, not an ∃-quantifier.
    @cite{owusu-2022}, following @cite{mirrazi-2024}. -/
def biIndefType : IndefType := .choiceFunction

/-- ⟦bí⟧ = λs.λP. CH(f_s). f_s(P(s))

    @cite{owusu-2022} analyses *bí* as denoting a skolemized choice
    function with individual and world/situation indices.

    The choice function `f_s` selects a single individual of type *e*
    from the set of P-individuals in situation `s`. The key consequence:
    since negation is not an intensional operator, it cannot shift the
    situation argument, so *bí*-NPs always take wide scope over negation.

    ⟦Me-n-ni fish bí⟧ = ¬eat(speaker, f_s(fish))
    = 'I don't eat a certain (kind of) fish'  (∃ > ¬)
    ≠ 'I don't eat any fish'  (*¬ > ∃)

    @cite{zimmermann-2026} §3.3 exx. (15–16). -/
def biSem (S E : Type*) := SkolemCF S E

-- ════════════════════════════════════════════════════
-- § 4. Universal Quantifier *bi-ara*
-- ════════════════════════════════════════════════════

/-- *bi-ara* exhibits flexible surface interpretations depending on
    its structural environment. @cite{philipp-2022} proposes that the
    three readings arise from different structural combinations of
    the INDEF marker *bí* and the alternative-sensitive scalar
    operator *ara*:

    - INDEF + *ara* at NP level → universal (✓every)
    - INDEF + *ara* at clause level → NPI (nobody) / FC (any)

    @cite{zimmermann-2026} §4.1.2 ex. (27). -/
inductive BiaraReading where
  | universal   -- 'every student read a book' (INDEF + ara at NP)
  | npi         -- 'no sibling came' (INDEF + ara at clause, under NEG)
  | freeChoice  -- 'fix any chair' (INDEF + ara at clause, FC context)
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 5. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- *bí* is a choice function indefinite.
    @cite{owusu-2022}, @cite{zimmermann-2026} §3.3 ex. (15). -/
theorem bi_is_cf : biIndefType = .choiceFunction := rfl

/-- Bare NPs are ∃-quantifier indefinites. -/
theorem bareNP_is_existential : bareNPIndefType = .existential := rfl

/-- Strong analysis of *nó* predicts familiarity presupposition.
    @cite{schwarz-2013}. -/
theorem strong_presup_familiarity :
    NoAnalysis.strong.toPresupType = .familiarity := rfl

/-- Demonstrative analysis of *nó* also predicts familiarity.
    @cite{owusu-2022}. -/
theorem demonstrative_presup_familiarity :
    NoAnalysis.demonstrative.toPresupType = .familiarity := rfl

/-- Akan's article system: overt DEF marker (*nó*) for familiarity,
    bare NP for uniqueness-based definiteness. This is the reverse of
    English (one overt form for both) and German (two overt forms).
    @cite{schwarz-2013}, @cite{zimmermann-2026} §3.1. -/
def akanArticleStrategy : WeakArticleStrategy := .bareNominal

end Fragments.Akan.Determiners
