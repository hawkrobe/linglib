import Linglib.Core.RootDimensions

/-!
# Root: Cross-Cutting Primitive Types

Framework-agnostic types for characterizing verb roots across theoretical
modules. These types are used by Semantics (event structure, denotations),
Syntax (argument structure, Voice), and Morphology (categorization, DM).

The theoretical content — why these types are what they are, and what
they predict — lives in `Theories/Morphology/RootTypology.lean` (Beavers
et al. 2021) and `Theories/Morphology/DM/Categorizer.lean` (Harley 2014).
-/

-- ════════════════════════════════════════════════════
-- § 1. Root Type: Change Entailment
-- ════════════════════════════════════════════════════

/-- Two types of change-of-state verb roots (Beavers et al. 2021 §3.1).

    **Property concept (PC) roots** (Dixon 1982, Thompson 1988): underlie
    deadjectival CoS verbs. The root describes a gradable property
    (dimension, color, value, etc.). Examples: flat, red, long, warm.

    **Result roots**: underlie non-deadjectival CoS verbs. The root describes
    a specific result state that arises from a particular kind of event
    (breaking, cooking, killing, etc.). Examples: crack, break, shatter. -/
inductive RootType where
  | propertyConcept  -- flat, red, long — deadjectival CoS (flatten, redden)
  | result           -- crack, break, shatter — non-deadjectival CoS
  deriving DecidableEq, Repr, BEq

/-- Whether a root lexically entails prior change (Beavers et al. 2021 §3.6).

    PC roots denote simple states that can hold without any prior change event.
    Result roots denote states that entail a prior change event. -/
def RootType.entailsChange : RootType → Bool
  | .propertyConcept => false
  | .result => true

-- ════════════════════════════════════════════════════
-- § 2. Root Arity: Internal Argument Selection
-- ════════════════════════════════════════════════════

/-- Whether a root selects an internal (theme) argument.

    Coon (2019): the central division of labor is that **roots determine
    internal arguments** while **functional heads (v/Voice⁰) determine
    external arguments**. This is orthogonal to change entailment. -/
inductive RootArity where
  | selectsTheme  -- root obligatorily takes internal argument (Coon's √TV)
  | noTheme       -- no internal argument selection (Coon's √ITV, √NOM, √POS)
  deriving DecidableEq, Repr, BEq

/-- Does this root arity entail an obligatory internal argument? -/
def RootArity.hasInternalArg : RootArity → Bool
  | .selectsTheme => true
  | .noTheme => false

-- ════════════════════════════════════════════════════
-- § 3. Root Denotation Type
-- ════════════════════════════════════════════════════

/-- The semantic denotation domain of a root (Coon 2019, (3)).

    - **eventPred** ⟨e, ⟨s,t⟩⟩: entity → event → truth-value (√TV, √ITV)
    - **measureFn** ⟨e, ⟨s,d⟩⟩: entity → event → degree (√POS; Henderson 2017)
    - **entityPred** ⟨e,t⟩: entity → truth-value, no event (√NOM) -/
inductive RootDenotationType where
  | eventPred   -- ⟨e, ⟨s,t⟩⟩ (√TV, √ITV)
  | measureFn   -- ⟨e, ⟨s,d⟩⟩ (√POS; Henderson 2017)
  | entityPred  -- ⟨e,t⟩ (√NOM)
  deriving DecidableEq, BEq, Repr

-- ════════════════════════════════════════════════════
-- § 4. Unified Root Structure
-- ════════════════════════════════════════════════════

/-- Unified root characterization bundling all classification dimensions.

    A root is characterized along five independent axes:
    1. **Arity** (Coon 2019): does it select an internal argument?
    2. **Change entailment** (Beavers et al. 2021): does it lexically
       entail a prior change event?
    3. **Denotation type** (Coon 2019, (3)): event predicate, measure
       function, or entity predicate.
    4. **Quality dimensions** (Spalek & McNally): within-class root content
    5. **Class membership** (Levin 1993): verb class taxonomy

    Axes 1, 2, and 3 cross-classify: Coon's four Chuj root classes are
    recovered as (arity × denotationType) pairs:
    √TV = selectsTheme + eventPred, √ITV = noTheme + eventPred,
    √POS = noTheme + measureFn, √NOM = noTheme + entityPred. -/
structure Root where
  /-- Does this root select an internal argument? (Coon 2019) -/
  arity : RootArity
  /-- Does this root lexically entail prior change? (Beavers et al. 2021) -/
  changeType : RootType
  /-- Semantic denotation domain (Coon 2019, (3)). Optional — not all
      roots have been annotated. -/
  denotationType : Option RootDenotationType := none
  /-- Within-class quality dimensions (Spalek & McNally) -/
  profile : RootProfile := {}
  /-- Verb class membership (Levin 1993) -/
  levinClass : Option LevinClass := none
  deriving BEq, Repr

/-- Does this root lexically entail prior change? -/
def Root.entailsChange (r : Root) : Bool := r.changeType.entailsChange
