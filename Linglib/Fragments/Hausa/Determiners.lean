import Linglib.Theories.Semantics.Quantification.UnifiedUniversal
import Linglib.Theories.Semantics.Quantification.ONEModifiers
import Linglib.Theories.Semantics.Quantification.ChoiceFunction
import Linglib.Features.Definiteness

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

open Semantics.Quantification.UnifiedUniversal
open Semantics.Quantification.ONEModifiers
open Semantics.Quantification.ChoiceFunction
open Features.Definiteness

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
-- § 3. Indefinites: Analysis Type → Scope
-- ════════════════════════════════════════════════════

/-- Hausa indefinite marker type: bare NP vs *wani/wata*-marked.

    Both are ∃-quantifiers (@cite{zimmermann-2014}). The difference
    is that *wani* is an overt ∃ that can QR, while bare NPs have
    a covert ∃ that is locally bound. -/
inductive HausaIndef where
  | bare    -- unmarked bare NP: covert ∃, narrow scope
  | wani    -- *wani(m.)/wata(f.)*: overt ∃, flexible scope
  deriving DecidableEq, Repr

/-- Both Hausa indefinite strategies use ∃-quantification, not
    choice functions. @cite{zimmermann-2014}. -/
def HausaIndef.indefType : HausaIndef → IndefType
  | .bare => .existential
  | .wani => .existential

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

/-- *koo* selects SG count NPs (atoms).
    @cite{zimmermann-2008}, @cite{haslinger-etal-2025-nllt}. -/
theorem koo_takes_sg_count : HausaUQ.koo.takesSGCount = true := rfl

/-- *duk* selects DEF PL/mass NPs.
    @cite{zimmermann-2008}, @cite{haslinger-etal-2025-nllt}. -/
theorem duk_takes_def_plural : HausaUQ.duk.takesDEFPlural = true := rfl

/-- Bare NPs are ∃-quantifier indefinites. @cite{zimmermann-2014}. -/
theorem bare_is_existential : HausaIndef.bare.indefType = .existential := rfl

/-- *wani/wata* are ∃-quantifier indefinites. @cite{zimmermann-2014}. -/
theorem wani_is_existential : HausaIndef.wani.indefType = .existential := rfl

end Fragments.Hausa.Determiners
