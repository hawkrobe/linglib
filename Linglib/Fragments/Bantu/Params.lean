/-!
# Bantu Language Family: Shared Parameters

@cite{carstens-1991} @cite{kramer-2015} @cite{carstens-2026}

Shared types for Bantu language fragments, capturing cross-Bantu structural
regularities in the noun class system. Individual Bantu languages (Swahili,
Xhosa, Shona) import these types and specialize them with language-specific
class inventories and morphological forms.

## Key shared structure

- Noun classes come in singular/plural pairs that define **genders**
  (@cite{carstens-1991}, @cite{kramer-2015})
- A small number of genders have **semantic cores** — salient associations
  with entity classes like [human], [animal], [inanimate]
  (@cite{carstens-2026} §4.2)
- The semantic core determines whether a gender is **interpretable**
  (bears an i[entity] flavor) or **uninterpretable** (purely formal)

## Design

This file stores pure data — types, inventories, and status classifications.
Resolution logic (percolation, intersection) lives in the Theory layer
(`GenderResolution.lean`); study files connect the two.
-/

namespace Fragments.Bantu

-- ============================================================================
-- § 1: Semantic Cores
-- ============================================================================

/-- Semantic cores of Bantu gender: salient associations between
    genders and entity classes (@cite{carstens-2026} §4.2, (71)).

    Not all Bantu genders have a semantic core. Those that do have
    an interpretable i[entity] flavor at their innermost nP layer.
    Those that don't are purely formal (uninterpretable).

    Xhosa has three cores — [human], [animal], [inanimate] — reflecting
    a three-way entity split. Shona collapses [animal] and [inanimate]
    into a single [non-human] default, adding a fourth constructor.
    The Xhosa distinction is the parametric maximum. -/
inductive SemanticCore where
  | human     -- [human]: canonically classes 1/2
  | animal    -- [animal]: canonically classes 9/10 (Xhosa)
  | inanimate -- [inanimate]: canonically classes 7/8 (Xhosa)
  | nonhuman  -- [non-human]: Shona's 7/8 default for all non-humans
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- § 2: Gender Interpretability
-- ============================================================================

/-- Gender interpretability status (@cite{carstens-2026} §4.2).

    An **interpretable** gender has an i[entity] flavor associated with
    a salient class of countable entities. An **uninterpretable** gender
    has no such association — its members are semantically arbitrary.

    This distinction directly controls agreement with conjoined singulars:
    gender-matching plural agreement succeeds with uniform conjuncts
    only for interpretable genders (@cite{carstens-2026} (52), (54)). -/
inductive GenderStatus where
  | interpretable : SemanticCore → GenderStatus
  | uninterpretable : GenderStatus
  deriving DecidableEq, BEq, Repr

def GenderStatus.isInterpretable : GenderStatus → Bool
  | .interpretable _ => true
  | .uninterpretable => false

def GenderStatus.core : GenderStatus → Option SemanticCore
  | .interpretable c => some c
  | .uninterpretable => none

-- ============================================================================
-- § 3: nP Stacking
-- ============================================================================

/-- Stacked nP structure for Bantu nominals (@cite{carstens-2026} §4, (72)–(73)).

    Bantu nouns have an inner semantic nP (bearing the i-core gender)
    wrapped by zero or more outer nPs (determining the visible noun class).
    For nouns in their canonical class, visible = core; for nouns
    appearing in non-canonical classes (e.g. [human] nouns in classes
    3/4 or 5/6), the outer nP differs from the inner core.

    `visibleClass` is the outer noun class number (determines morphological
    agreement with non-conjoined DPs). `coreClass` is the inner class
    determined by the semantic core (or equal to `visibleClass` if no
    stacking). -/
structure NPStack where
  visibleClass : Nat
  coreClass : Nat
  status : GenderStatus
  deriving DecidableEq, BEq, Repr

def NPStack.isCanonical (s : NPStack) : Bool :=
  s.visibleClass == s.coreClass

-- ============================================================================
-- § 4: Default Agreement Classes
-- ============================================================================

/-- Default agreement class for a semantic core (@cite{carstens-2026} (52c)).
    Class 2 *ba-* for [human], class 8 *zi-* for [inanimate] and [animal]. -/
def SemanticCore.defaultPluralClass : SemanticCore → Nat
  | .human     => 2
  | .animal    => 8
  | .inanimate => 8
  | .nonhuman  => 8

end Fragments.Bantu
