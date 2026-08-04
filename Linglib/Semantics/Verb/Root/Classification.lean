import Linglib.Semantics.Verb.Root.Kinds
import Linglib.Semantics.ArgumentStructure.Valency
import Linglib.Semantics.ArgumentStructure.SalienceClass
import Linglib.Semantics.Intensional.Defs

/-!
# Root classification: change type, semantic type, and the annotation record

The cross-linguistic classification dimensions a change-of-state verb root
is typed by: whether it lexically entails change (`ChangeType`), its
semantic type (an `Intensional.Ty` — [coon-2019] (3) types Chuj roots
⟨e,⟨s,t⟩⟩, ⟨e,⟨s,d⟩⟩, ⟨e,t⟩), Dixon's property-concept categories
(`PCClass`), and the `Classification` annotation record for
annotation-first fragments.

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
* denotation types — actual semantic types (`Intensional.Ty`), not a
  bespoke enum: [coon-2019] (3)'s four Chuj domains and
  [hanink-koontz-garboden-2025]'s three Wáshiw PC classes are finite
  inventories the anchoring studies state over concrete `Ty` values.
* `PCClass` — [dixon-1982]'s seven categories.

## Main definitions

* `ChangeType`, `ChangeType.ofKinds` — the axis and its projection from
  kind signatures
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
    coordinates over valency × change type × semantic type ×
    transitive-Voice licensing, the annotation-first counterpart of the
    derived projections off `Root.kinds`. The stipulated and derived
    coordinates agree only by theorem (`salienceClass_ofKinds`), never by
    construction. -/
structure Classification where
  /-- The core-argument positions the root introduces ([coon-2019]:
      at most the internal argument — `Valency.IsRootValency`). -/
  valency : Valency
  /-- Does this root lexically entail prior change? -/
  changeType : ChangeType
  /-- The root's semantic type ([coon-2019] (3)). Optional — not all
      roots have been annotated. -/
  denotationType : Option Intensional.Ty := none
  /-- Whether the root may combine with the transitive-forming v ~ Voice⁰
      head that merges an agent — the coordinate separating [coon-2019]'s
      √TV from her unaccusative √ITV (§3.3), which share both semantic
      type and internal-argument valency. Coon expressly declines to
      formalize its source ("I do not take a particular stance on the
      source of this distinction"). -/
  licensesTransitiveVoice : Bool := false
  deriving DecidableEq, Repr

/-- Does this root lexically entail prior change? -/
def Classification.entailsChange (r : Classification) : Bool := r.changeType.entailsChange

/-! ### Salience through the annotation coordinates -/

variable (s : Root.Kinds) (v : Valency)

/-- The salience class determined by the annotation coordinates.
    Agent-patient salience is transitive-Voice licensing — [lucy-1994]'s
    `=∅` roots form transitive stems bare — not internal-argument
    introduction, which unaccusatives also have ([coon-2019] §3.3).
    Partial where the coordinates underdetermine the class: `ChangeType`
    is manner-blind, so a non-transitivizing property-concept annotation
    cannot distinguish an agent-salient manner root from an unclassified
    stative. -/
def Classification.salienceClass (c : Classification) : Option SalienceClass :=
  if c.licensesTransitiveVoice then some .agentPatient
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
    ({ valency := v, changeType := .ofKinds s,
       licensesTransitiveVoice := decide (.internal ∈ v) } :
      Classification).salienceClass = SalienceClass.ofKinds s v := by
  revert s v; decide

end Verb.Root
