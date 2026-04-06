import Linglib.Theories.Semantics.Lexical.Determiner.ChoiceFunction
import Linglib.Theories.Semantics.Lexical.Determiner.UnifiedUniversal
import Linglib.Core.Definiteness
import Linglib.Core.Semantics.Presupposition

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

/-- ⟦nó⟧ contributes a presupposition (familiarity or uniqueness,
    depending on the analysis) and passes through the NP assertion.

    Under Bombi's preferred analysis, *nó* presupposes uniqueness
    evaluated relative to the context of a preceding clause.
    Under Schwarz/Owusu's analysis, it presupposes familiarity. -/
def noSem {W : Type*} (presupHolds : W → Bool) (assertion : W → Bool) :
    PrProp W :=
  { presup := presupHolds
  , assertion := assertion }

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

/-- Akan bare NPs take narrow scope obligatorily (like Hausa bare NPs).
    @cite{philipp-2022}: Akan bare NPs do not show the characteristic
    properties of pseudo-noun incorporation. -/
def bareNPHasWideScope : Bool := false

-- ════════════════════════════════════════════════════
-- § 3. Indefinite *bí*: Choice Function Semantics
-- ════════════════════════════════════════════════════

/-- ⟦bí⟧ = λs.λP. CH(f_s). f_s(P(s))

    @cite{owusu-2022} analyses *bí* as denoting a skolemized choice
    function with individual and world/situation indices (following
    @cite{mirrazi-2024}).

    The choice function `f_s` selects a single individual of type *e*
    from the set of P-individuals in situation `s`. The key consequence:
    since negation is not an intensional operator, it cannot shift the
    situation argument, so *bí*-NPs always take wide scope over negation.

    ⟦Me-n-ni fish bí⟧ = ¬eat(speaker, f_s(fish))
    = 'I don't eat a certain (kind of) fish'  (∃ > ¬)
    ≠ 'I don't eat any fish'  (*¬ > ∃)

    @cite{zimmermann-2026} §3.3 exx. (15–16). -/
def biSem (S E : Type*) := SkolemCF S E

/-- *bí* takes obligatory wide scope under negation.
    This contrasts with Hausa *wani/wata* which allows narrow scope.
    @cite{owusu-2022}, @cite{zimmermann-2026} §3.3 ex. (15). -/
def biHasWideScope : Bool := true

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

/-- Unlike Ga *ko*, Akan *bí* (and by extension *bi-ara*) is analysed
    as a choice function, not an ∃-quantifier. This means the universal
    reading of *bi-ara* cannot be from a simple FC ∃-quantifier.
    @cite{owusu-2022}, @cite{zimmermann-2026} §3.3. -/
def biaraUsesChoiceFunction : Bool := true

-- ════════════════════════════════════════════════════
-- § 5. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- *nó* contributes familiarity regardless of the chosen analysis:
    both the strong and demonstrative analyses predict familiarity;
    Bombi's weak analysis predicts uniqueness but evaluated against
    a discourse-restricted situation (functionally similar). -/
theorem no_requires_discourse_link :
    NoAnalysis.strong.toPresupType = .familiarity ∧
    NoAnalysis.demonstrative.toPresupType = .familiarity :=
  ⟨rfl, rfl⟩

/-- *bí*-marked indefinites take wide scope; bare NPs take narrow scope.
    This is the Akan analogue of the Hausa *wani* vs bare NP contrast,
    but with a different mechanism: choice function binding (Akan) vs
    QR (Hausa). @cite{zimmermann-2026} §3.3. -/
theorem bi_vs_bare_scope :
    biHasWideScope = true ∧ bareNPHasWideScope = false :=
  ⟨rfl, rfl⟩

/-- Akan's article system: overt DEF marker (*nó*) for familiarity,
    bare NP for uniqueness-based definiteness. This is the reverse of
    English (one overt form for both) and German (two overt forms).
    @cite{schwarz-2013}, @cite{zimmermann-2026} §3.1. -/
def akanArticleStrategy : WeakArticleStrategy := .bareNominal

end Fragments.Akan.Determiners
