import Linglib.Semantics.Verb.Root.Arity
import Linglib.Semantics.ArgumentStructure.LevinTheory

/-!
# Root classification: change type, denotation type, and cross-classification

The cross-linguistic classification dimensions a change-of-state verb root is
typed by: whether it lexically entails change (`ChangeType`), its semantic
denotation domain (`DenotationType`), Dixon's property-concept categories
(`PCClass`), Levin's result-verb categories (`ResultClass`), and the bundled
`Classification` cross-classifying arity against change entailment.

## Anchoring and provenance

* `ChangeType` — the property-concept vs. result split of [levin-1993]'s
  deadjectival typology. The reading that result roots *lexically entail
  change* (`entailsChange`, `allowsRestitutiveAgain`) is the
  [beavers-etal-2021]/[beavers-koontz-garboden-2020] account and is contested
  by the Distributed-Morphology camp, for whom change is templatic; the split
  itself is theory-neutral.
* `DenotationType` — the four denotation domains of [coon-2019]'s Chuj root
  classes (3), extended by [hanink-koontz-garboden-2025]. A single-account
  type earning substrate status by consumer count (Chuj fragment, Coon 2019,
  Hanink & Koontz-Garboden 2025).
* `PCClass` — [dixon-1982]'s seven property-concept categories (consensus).
* `ResultClass` — [levin-1993]'s result-verb categories (consensus), except
  `inherentlyDirectedMotion`, a formaliser addition not on Levin's list.

## Main definitions

* `ChangeType`, `ChangeType.entailsChange`, `ChangeType.allowsRestitutiveAgain`
* `DenotationType`, `DenotationType.hasIndivArg`
* `PCClass`, `ResultClass`
* `Classification` bundling arity × change entailment × denotation type

## Main results

* `arity_changeType_orthogonal`, `change_does_not_determine_arity` — the arity
  and change-entailment dimensions are independent (all four cells inhabited).
* `theme_persistence` — a theme-selecting root keeps its internal argument
  regardless of the functional head ([coon-2019]).
-/

open ArgumentStructure

namespace Verb.Root

/-- Two types of change-of-state verb roots ([beavers-etal-2021] §3.1).

    **Property concept (PC) roots** underlie deadjectival CoS verbs: the root
    describes a gradable property (flat, red, long, warm). **Result roots**
    underlie non-deadjectival CoS verbs: the root describes a specific result
    state arising from a particular event (crack, break, shatter). -/
inductive ChangeType where
  | propertyConcept  -- flat, red, long — deadjectival CoS (flatten, redden)
  | result           -- crack, break, shatter — non-deadjectival CoS
  deriving DecidableEq, Repr

/-- Whether a root lexically entails prior change ([beavers-etal-2021] §3.6).
    PC roots denote simple states holding without prior change; result roots
    denote states entailing a prior change event. The entailment reading is the
    B&KG account, contested by the DM camp. -/
def ChangeType.entailsChange : ChangeType → Bool
  | .propertyConcept => false
  | .result => true

/-- PC roots allow restitutive *again* (scope over root only); result roots
    allow only repetitive *again* (scope over BECOME) ([beavers-etal-2021]
    §3.4). Since a result root's state itself entails change, *again* over the
    root still entails a prior change event, collapsing into the repetitive
    reading. -/
def ChangeType.allowsRestitutiveAgain : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- The semantic denotation domain of a root ([coon-2019] (3); extended by
    [hanink-koontz-garboden-2025]).

    - `indivStatePred` ⟨e, ⟨v,t⟩⟩: individual/state relation (√TV, √ITV; also PC
      Class 1/3 roots per [hanink-koontz-garboden-2025])
    - `statePred` ⟨v,t⟩: predicate of states, no individual argument (PC Class 2)
    - `measureFn` ⟨e, ⟨s,d⟩⟩: entity → event → degree (√POS in [coon-2019] (3),
      following [henderson-2019]'s measure functions)
    - `entityPred` ⟨e,t⟩: entity → truth-value, no event (√NOM) -/
inductive DenotationType where
  | indivStatePred  -- ⟨e, ⟨v,t⟩⟩ (√TV, √ITV; PC Class 1/3)
  | statePred       -- ⟨v,t⟩ (PC Class 2: quality-type)
  | measureFn       -- ⟨e, ⟨s,d⟩⟩ (√POS; [coon-2019] (3), following [henderson-2019])
  | entityPred      -- ⟨e,t⟩ (√NOM)
  deriving DecidableEq, Repr

/-- Whether a root denotation type includes an individual argument.

    Types with an individual argument (⟨e, ...⟩) compose directly with v_become
    (which requires ⟨e, ⟨v,t⟩⟩). Types without one (⟨v,t⟩) cause a type mismatch
    and require type-shifting (∇) or possessive semantics (v_have) to predicate
    of individuals ([hanink-koontz-garboden-2025] §5.1). -/
def DenotationType.hasIndivArg : DenotationType → Bool
  | .indivStatePred => true   -- ⟨e, ⟨v,t⟩⟩
  | .statePred      => false  -- ⟨v,t⟩
  | .measureFn      => true   -- ⟨e, ⟨s,d⟩⟩
  | .entityPred     => true   -- ⟨e,t⟩

/-- Property concept root subclasses ([dixon-1982]; [beavers-etal-2021] ex. 5).

    [dixon-1982] identifies seven semantic categories. [beavers-etal-2021]
    omits HUMAN PROPENSITY from their Table 2 sample, but the category is
    attested crosslinguistically ([hanink-koontz-garboden-2025] Table A1). -/
inductive PCClass where
  | dimension         -- large/big, small, long, short, deep, wide, tall/high
  | age               -- old/aged
  | value             -- bad/worse, good/improved
  | color             -- white, black, red, green, blue, brown
  | physicalProperty  -- cool/cold, warm/hot, dry/wet, soft/hard, smooth/rough
  | humanPropensity   -- hungry, afraid, sick, brave, generous ([dixon-1982])
  | speed             -- fast, slow
  deriving DecidableEq, Repr

/-- Result root subclasses ([levin-1993]; [beavers-etal-2021] ex. 6).
    `inherentlyDirectedMotion` is a formaliser addition, not on Levin's list. -/
inductive ResultClass where
  | entitySpecificCoS          -- burned, melted, frozen, decayed, bloomed, rusted
  | cooking                    -- cooked, baked, fried, roasted, boiled
  | breaking                   -- broken, cracked, crushed, shattered, split, torn
  | bending                    -- bent, folded, wrinkled, creased
  | killing                    -- dead, killed, murdered, drowned
  | destroying                 -- destroyed, ruined
  | calibratableCoS            -- go up, increase, go down, decrease, differ
  | inherentlyDirectedMotion   -- come, go, enter, exit, return (formaliser addition)
  deriving DecidableEq, Repr

/-- Unified root characterization bundling the classification dimensions.

    A root is characterized along independent axes: arity (does it select an
    internal argument?), change entailment (does it lexically entail prior
    change?), denotation type ([coon-2019] (3)), within-class quality
    dimensions, and verb-class membership. Arity, change entailment, and
    denotation type cross-classify: [coon-2019]'s four Chuj root classes are
    recovered as (arity × denotationType) pairs — √TV = selectsTheme +
    indivStatePred, √ITV = noTheme + indivStatePred, √POS = noTheme + measureFn,
    √NOM = noTheme + entityPred. -/
structure Classification where
  /-- Does this root select an internal argument? -/
  arity : Arity
  /-- Does this root lexically entail prior change? -/
  changeType : ChangeType
  /-- Semantic denotation domain ([coon-2019] (3)). Optional — not all roots
      have been annotated. -/
  denotationType : Option DenotationType := none
  /-- Within-class quality dimensions ([spalek-mcnally-2026]). -/
  profile : Profile := {}
  /-- Verb class membership. -/
  levinClass : Option LevinClass := none
  deriving BEq, Repr

/-- Does this root lexically entail prior change? -/
def Classification.entailsChange (r : Classification) : Bool := r.changeType.entailsChange

/-! ### Cross-classification: arity × change entailment -/

-- Witnesses for all four cells of the 2×2 cross-classification.

/-- √BREAK: selects theme + entails change (result root, [levin-1993] 45.1). -/
def Classification.break_ : Classification :=
  { arity := .selectsTheme, changeType := .result,
    denotationType := some .indivStatePred, levinClass := some .break_ }

/-- √HIT: selects theme + does not entail change ([levin-1993] 18.1).
    `.propertyConcept` is used broadly: the formal content
    (`entailsChange = false`) is what matters, not the label. -/
def Classification.hit : Classification :=
  { arity := .selectsTheme, changeType := .propertyConcept,
    denotationType := some .indivStatePred, levinClass := some .hit }

/-- √DIE: no theme + entails change. The dying entity is introduced by
    functional structure (unaccusative vGO/vBE), not selected by the root;
    dying lexically entails a prior change (becoming dead). -/
def Classification.die : Classification :=
  { arity := .noTheme, changeType := .result,
    denotationType := some .indivStatePred }

/-- √SIT: no theme + does not entail change (positional root, Coon's √POS
    class). Denotes a measure function ⟨e,⟨s,d⟩⟩ ([coon-2019] (3), following
    [henderson-2019]). -/
def Classification.sit : Classification :=
  { arity := .noTheme, changeType := .propertyConcept,
    denotationType := some .measureFn, levinClass := some .assumePosition }

/-- **Orthogonality of arity and change entailment.** All four cells of the 2×2
    cross-classification are inhabited: knowing that a root selects a theme
    tells you nothing about whether it entails change, and vice versa. -/
theorem arity_changeType_orthogonal :
    (∃ r : Classification, r.arity = .selectsTheme ∧ r.changeType = .result) ∧
    (∃ r : Classification, r.arity = .selectsTheme ∧ r.changeType = .propertyConcept) ∧
    (∃ r : Classification, r.arity = .noTheme ∧ r.changeType = .result) ∧
    (∃ r : Classification, r.arity = .noTheme ∧ r.changeType = .propertyConcept) :=
  ⟨⟨.break_, rfl, rfl⟩, ⟨.hit, rfl, rfl⟩, ⟨.die, rfl, rfl⟩, ⟨.sit, rfl, rfl⟩⟩

/-- **Change entailment does not determine arity** (and vice versa).
    Change entailment fixes all morphosyntactic correlates (markedness, simple
    stative, again readings) but nothing about internal argument selection —
    [coon-2019]'s arity is an independent dimension. -/
theorem change_does_not_determine_arity :
    (∃ r : Classification, r.entailsChange = true ∧ r.arity = .selectsTheme) ∧
    (∃ r : Classification, r.entailsChange = true ∧ r.arity = .noTheme) ∧
    (∃ r : Classification, r.entailsChange = false ∧ r.arity = .selectsTheme) ∧
    (∃ r : Classification, r.entailsChange = false ∧ r.arity = .noTheme) :=
  ⟨⟨.break_, rfl, rfl⟩, ⟨.die, rfl, rfl⟩, ⟨.hit, rfl, rfl⟩, ⟨.sit, rfl, rfl⟩⟩

/-- **Theme persistence** ([coon-2019] main empirical claim). If a root selects
    a theme, the internal argument persists regardless of the v/Voice⁰ head. In
    Chuj, √TV roots surface with an internal argument in transitive, passive,
    and antipassive constructions alike. Expressed by design: `arity` is a
    field of `Classification`, not of the derived verb. -/
theorem theme_persistence (r : Classification) (h : r.arity = .selectsTheme) :
    r.arity.hasInternalArg = true := by
  simp [h, Arity.hasInternalArg]

end Verb.Root
