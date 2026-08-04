import Linglib.Semantics.Verb.Root.Kinds
import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Semantics.ArgumentStructure.SalienceClass

/-!
# Root classification: change type, denotation type, and the annotation record

The cross-linguistic classification dimensions a change-of-state verb root
is typed by: whether it lexically entails change (`ChangeType`), its
semantic denotation domain (`DenotationType`), Dixon's property-concept
categories (`PCClass`), and the `Classification` annotation record over
(valency × change type × denotation type) for annotation-first fragments.

## Anchoring and provenance

* `ChangeType` — [dixon-1982]'s (p. 50) split between property-concept
  states and "states that are the result of some action", recast at root
  level by [beavers-koontz-garboden-2020] and [beavers-etal-2021] (the
  term "property concept" is later than Dixon —
  [beavers-koontz-garboden-2020] fn. 2 credit it to Thompson).
  [levin-1993] supplies the English deadjectival vs non-deadjectival
  verb inventory. The reading that result roots *lexically entail*
  change is the Beavers et al. account, contested by the
  Distributed-Morphology camp; the split itself is theory-neutral.
* `DenotationType` — the four denotation domains of [coon-2019] (3),
  extended by [hanink-koontz-garboden-2025].
* `PCClass` — [dixon-1982]'s seven categories.

## Main definitions

* `ChangeType`, `ChangeType.ofKinds` — the axis and its projection from
  kind signatures
* `DenotationType`, `DenotationType.hasIndivArg`
* `Classification` — the annotation record
* `Classification.salienceClass` — the annotation-level salience hom

## Main results

* `Classification.salienceClass_ofKinds` — on manner-free signatures the
  annotation-level classifier agrees with the signature-level
  `SalienceClass.ofKinds`
-/

open ArgumentStructure

namespace Verb.Root

/-- Two types of change-of-state verb roots ([beavers-etal-2021] §3.1;
    [dixon-1982] p. 50).

    **Property concept (PC) roots** underlie deadjectival CoS verbs: the root
    describes a gradable property (flat, red, long, warm). **Result roots**
    underlie non-deadjectival CoS verbs: the root describes a specific result
    state arising from a particular event (crack, break, shatter). -/
inductive ChangeType where
  /-- flat, red, long — deadjectival CoS (flatten, redden). -/
  | propertyConcept
  /-- crack, break, shatter — non-deadjectival CoS. -/
  | result
  deriving DecidableEq, Repr

/-- Whether a root lexically entails prior change ([beavers-etal-2021] §3.6).
    PC roots denote simple states holding without prior change; result roots
    denote states entailing a prior change event. The change entailment is
    categorical; the morphological correlates (markedness, simple stative
    forms) are crosslinguistic tendencies with flagged exceptions. -/
def ChangeType.entailsChange : ChangeType → Bool
  | .propertyConcept => false
  | .result => true

/-- PC roots allow restitutive *again* (scope over root only); result roots
    allow only repetitive *again* (scope over BECOME) ([beavers-etal-2021]
    §3.4). Since a result root's state itself entails change, *again* over the
    root still entails a prior change event, collapsing into the repetitive
    reading. Their fn. 9 records speaker variation for particular result
    roots (*thaw*, *return*). -/
def ChangeType.allowsRestitutiveAgain : ChangeType → Bool
  | .propertyConcept => true
  | .result => false

/-- The change-entailment type of a kind signature: a root entails change
    iff its signature carries `result` ([beavers-etal-2021]). The
    projection is manner-blind — see `Classification.salienceClass_ofKinds`
    for what survives it. -/
def ChangeType.ofKinds (s : Root.Kinds) : ChangeType :=
  if LexKind.result ∈ s then .result else .propertyConcept

/-- The semantic denotation domain of a root ([coon-2019] (3); extended by
    [hanink-koontz-garboden-2025]). -/
inductive DenotationType where
  /-- ⟨e,⟨s,t⟩⟩: individual/state relation (√TV and √ITV in [coon-2019]
      (3); PC Class 1/3 roots per [hanink-koontz-garboden-2025]). -/
  | indivStatePred
  /-- ⟨s,t⟩: predicate of states, no individual argument (PC Class 2). -/
  | statePred
  /-- ⟨e,⟨s,d⟩⟩: entity → state → degree (√POS, per [coon-2019] (3);
      [henderson-2019]'s published analysis types positional-root measure
      functions ⟨e,d⟩ — the state argument is Coon's). -/
  | measureFn
  /-- ⟨e,t⟩: entity predicate with no eventuality argument (√NOM). -/
  | entityPred
  deriving DecidableEq, Repr

/-- Whether a root denotation type includes an individual argument.

    Types with an individual argument (⟨e, …⟩) compose directly with v_become
    (which requires ⟨e,⟨s,t⟩⟩). A bare state predicate (⟨s,t⟩) cannot, and is
    predicated of individuals via possession instead — the *-iʔ* possessive
    verbalizer of [hanink-koontz-garboden-2025] (their analysis of the *ʔil-*
    prefix, §5.2), following [francez-koontz-garboden-2017]'s possessive
    analysis of property concepts. -/
def DenotationType.hasIndivArg : DenotationType → Bool
  | .indivStatePred => true   -- ⟨e,⟨s,t⟩⟩
  | .statePred      => false  -- ⟨s,t⟩
  | .measureFn      => true   -- ⟨e,⟨s,d⟩⟩
  | .entityPred     => true   -- ⟨e,t⟩

/-- Property concept root subclasses ([dixon-1982]; [beavers-etal-2021]
    ex. 5). [beavers-etal-2021] exclude human propensity from their sample
    (fn. 5 to ex. 5): many of its verbal forms are stative, and their study
    targets change of state. -/
inductive PCClass where
  /-- large/big, small, long, short, deep, wide, tall/high. -/
  | dimension
  /-- old/aged. -/
  | age
  /-- bad/worse, good/improved. -/
  | value
  /-- white, black, red, green, blue, brown. -/
  | color
  /-- cool/cold, warm/hot, dry/wet, soft/hard, smooth/rough. -/
  | physicalProperty
  /-- angry, embarrassed ([beavers-etal-2021] fn. 5). -/
  | humanPropensity
  /-- fast, slow. -/
  | speed
  deriving DecidableEq, Repr

/-- Annotation record for roots with no atom decomposition: stipulated
    coordinates over valency × change type × denotation type, the
    annotation-first counterpart of the derived projections off
    `Root.kinds`. The stipulated and derived coordinates agree only by
    theorem (`salienceClass_ofKinds`), never by construction.

    [coon-2019]'s √TV vs √ITV distinction is *not* recovered by these
    coordinates: her §3.3 gives both classes type ⟨e,⟨s,t⟩⟩, with √ITV
    unaccusative, and separates them by compatibility with the
    external-argument-introducing v ~ Voice head — a coordinate she
    declines to formalize and this record does not yet carry. -/
structure Classification where
  /-- The core-argument positions the root introduces ([coon-2019]:
      at most the internal argument — `Valency.IsRootValency`). -/
  valency : Valency
  /-- Does this root lexically entail prior change? -/
  changeType : ChangeType
  /-- Semantic denotation domain ([coon-2019] (3)). Optional — not all roots
      have been annotated. -/
  denotationType : Option DenotationType := none
  deriving DecidableEq, Repr

/-- Does this root lexically entail prior change? -/
def Classification.entailsChange (r : Classification) : Bool := r.changeType.entailsChange

/-! ### Salience through the annotation coordinates -/

variable (s : Root.Kinds) (v : Valency)

/-- The salience class determined by the annotation coordinates
    (valency × change type). Partial where the coordinates underdetermine
    the class: `ChangeType` is manner-blind, so an internal-argument-free
    property-concept annotation cannot distinguish an agent-salient
    manner root from an unclassified stative. -/
def Classification.salienceClass (c : Classification) : Option SalienceClass :=
  if .internal ∈ c.valency then some .agentPatient
  else match c.changeType with
    | .result => some .patient
    | .propertyConcept => none

/-- On manner-free signatures the annotation-level classifier agrees with
    the signature-level one (`SalienceClass.ofKinds`) — the agree-by-theorem
    link between the stipulated and derived coordinates. The hypothesis is
    necessary: a manner root maps to `.propertyConcept` under
    `ChangeType.ofKinds`, where the annotation coordinates return `none`
    but the signature classifier sees agent salience. -/
theorem Classification.salienceClass_ofKinds (h : LexKind.manner ∉ s) :
    ({ valency := v, changeType := .ofKinds s } : Classification).salienceClass =
      SalienceClass.ofKinds s v := by
  revert s v; decide

end Verb.Root
