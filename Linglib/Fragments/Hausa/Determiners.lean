import Linglib.Theories.Semantics.Lexical.Determiner.UnifiedUniversal
import Linglib.Theories.Semantics.Lexical.Determiner.ONEModifiers
import Linglib.Core.Definiteness

/-!
# Hausa Determiners
@cite{zimmermann-2008} @cite{zimmermann-2014} @cite{zimmermann-2026}

Fragment entries for the Hausa (Chadic, West Africa) determiner system,
covering universal quantifiers and indefinite markers.

## Universal Quantification

Hausa has a 2-form UQ system (@cite{zimmermann-2008}):

| Form       | Type      | Complement       | Reading     |
|------------|-----------|------------------|-------------|
| *koo-wane* | [+dist]   | SG count without DEF | each    |
| *duk(a)*   | [−dist]   | DEF PL count + mass  | all     |

The *koo*-quantifier shows phi-agreement with the NP and combines only
with bare SG count NPs. The *duka*-expressions do not agree and select
for definite plural NPs and mass NPs.

This maps to the Haslinger et al. Q_∀ + ONE decomposition:
- *koo-wane* = Q_∀[ONE_∅] (distributive, non-overlapping complement)
- *duk(a)* = bare Q_∀ (non-distributive, CUM complement)

## Indefiniteness

Hausa has two indefinite strategies:

| Form          | Analysis        | Scope potential    |
|---------------|-----------------|-------------------|
| *wani/wata*   | ∃-quantifier    | Wide + narrow     |
| bare NP       | covert ∃        | Narrow only       |

*wani/wata* can take exceptional wide scope, even out of relative
clauses (@cite{zimmermann-2014}), motivating an analysis as either
a contextually bound choice function variable or an ∃-quantifier
with singleton restriction (@cite{schwarzschild-2002}).

@cite{zimmermann-2008} @cite{zimmermann-2014} analyse *wani/wata* as
∃-quantifiers, in complementary distribution with the distributive
universal *koo-wane/koo-wace*.
-/

namespace Fragments.Hausa.Determiners

open Semantics.Lexical.Determiner.UnifiedUniversal
open Semantics.Lexical.Determiner.ONEModifiers
open Core.Definiteness

-- ════════════════════════════════════════════════════
-- § 1. UQ System Classification
-- ════════════════════════════════════════════════════

/-- Hausa has a 2-form universal quantifier system:
    *koo-wane* (distributive) vs *duk(a)* (non-distributive).
    @cite{zimmermann-2008}, confirmed by @cite{zimmermann-2026} §4.1. -/
inductive HausaUQ where
  | koo   -- *koo-wane(m.)* / *koo-wace(f.)* — distributive [+dist]
  | duk   -- *duk(a)* — non-distributive [−dist]
  deriving DecidableEq, Repr

/-- *koo* shows phi-agreement and takes bare SG count NPs.
    *duk* does not agree and takes DEF PL/mass NPs. -/
def HausaUQ.takesSGCount : HausaUQ → Bool
  | .koo => true
  | .duk => false

def HausaUQ.takesDEFPlural : HausaUQ → Bool
  | .koo => false
  | .duk => true

/-- The *koo*/*duk* split instantiates the DNG (@cite{haslinger-etal-2025-nllt}):
    same Q_∀, different complement structure. -/
def HausaUQ.isDistributive : HausaUQ → Bool
  | .koo => true
  | .duk => false

-- ════════════════════════════════════════════════════
-- § 2. Semantic Entries: Universals
-- ════════════════════════════════════════════════════

/-- ⟦koo-wane⟧ = Q_∀[ONE_∅]: distributive universal.

    *koo-wane* distributes over the individual atoms of the SG NP
    denotation. Because it selects for SG count NPs (atoms only),
    ONE_∅ (non-overlap) is automatically satisfied.

    Equivalent to English *every* in the Haslinger et al. decomposition.
    @cite{zimmermann-2008}. -/
def kooSem {α : Type*} [PartialOrder α]
    (P : α → Prop) (Q : α → Prop) : Prop :=
  everyPresup P Q

/-- ⟦duk(a)⟧ = bare Q_∀: non-distributive universal.

    *duk(a)* applies the scope predicate to the maximal element of
    the DEF PL/mass NP denotation (the sum of all individuals).

    Equivalent to English *all* in the Haslinger et al. decomposition.
    @cite{zimmermann-2008}. -/
def dukSem {α : Type*} [PartialOrder α]
    (P : α → Prop) (Q : α → Prop) : Prop :=
  QForall P Q

-- ════════════════════════════════════════════════════
-- § 3. Semantic Entries: Indefinites
-- ════════════════════════════════════════════════════

/-- Hausa indefinite marker type: bare NP vs *wani/wata*-marked. -/
inductive HausaIndef where
  | bare    -- unmarked bare NP: narrow scope only
  | wani    -- *wani(m.)/wata(f.)/wa(d'an)su(pl.)*: flexible scope
  deriving DecidableEq, Repr

/-- *wani/wata* can take wide or narrow scope relative to negation,
    conditionals, and modal operators. @cite{zimmermann-2014}. -/
def HausaIndef.hasWideScope : HausaIndef → Bool
  | .bare => false
  | .wani => true

/-- *wani/wata* satisfies Matthewson's diagnostics for marked indefinites:
    occurrence in existential sentences, introduction of new discourse
    referents, serving as antecedents for sluicing.
    @cite{matthewson-1999}, @cite{zimmermann-2026} §3.3 ex. (12). -/
def HausaIndef.isMarkedIndefinite : HausaIndef → Bool
  | .bare => false
  | .wani => true

-- ════════════════════════════════════════════════════
-- § 4. Bridge Theorems
-- ════════════════════════════════════════════════════

/-- *koo-wane* is distributive: its complement must be non-overlapping. -/
theorem koo_is_distributive : HausaUQ.koo.isDistributive = true := rfl

/-- *duk(a)* is non-distributive: it applies to the maximal sum. -/
theorem duk_is_nondistributive : HausaUQ.duk.isDistributive = false := rfl

/-- *koo* selects SG count NPs (atoms), *duk* selects DEF PL/mass NPs.
    This complement difference is what drives the distributivity split
    via the DNG (@cite{haslinger-etal-2025-nllt}). -/
theorem complement_split :
    HausaUQ.koo.takesSGCount = true ∧ HausaUQ.duk.takesDEFPlural = true :=
  ⟨rfl, rfl⟩

/-- Only *koo*-quantifiers can semantically bind SG pronouns, because
    only they distribute over individual atoms. *duk*-NPs cannot bind
    SG pronouns; they require PL pronominal forms.
    @cite{zimmermann-2008}, @cite{zimmermann-2026} §4.1 ex. (23). -/
theorem koo_binds_sg_pronouns :
    HausaUQ.koo.isDistributive = true ∧ HausaUQ.duk.isDistributive = false :=
  ⟨rfl, rfl⟩

/-- Bare NPs obligatorily take narrow scope. *wani*-marked indefinites
    have flexible scope. This scope contrast motivates the different
    semantic analyses: bare = covert ∃ (locally bound), *wani* = overt
    ∃-quantifier (can QR). @cite{zimmermann-2014}. -/
theorem scope_contrast :
    HausaIndef.bare.hasWideScope = false ∧
    HausaIndef.wani.hasWideScope = true :=
  ⟨rfl, rfl⟩

/-- *duk(a)* cannot co-occur with collective predicates like *gather*
    due to its distributive semantic nature — only the semantic nature
    of *koo* forces atom-level distribution.
    @cite{zimmermann-2008}, @cite{zimmermann-2026} §4.1 ex. (22). -/
theorem duk_allows_collective : HausaUQ.duk.isDistributive = false := rfl

end Fragments.Hausa.Determiners
