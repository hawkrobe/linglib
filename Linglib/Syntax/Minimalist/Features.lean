import Linglib.Features.Basic
import Linglib.Features.Case.Basic
import Linglib.Data.UD.Basic
import Linglib.Features.Prominence
import Linglib.Features.Number.Basic
import Linglib.Features.Slot

/-!
# Feature Infrastructure for Minimalist Agree
[adger-2003] [chomsky-1995] [chomsky-2000] [chomsky-2001] [alok-2020] [alok-bhalla-2026] [lobeck-1995] [panagiotidis-2015] [pollock-1989]

Phi-features, case values, and feature bundles — the shared infrastructure
underlying all Agree-based operations. Extracted from `Agree.lean` to
separate the feature *types* (what can be checked) from the Agree
*operation* (how checking works) and the *failure model* (what happens
when checking fails — a `Probe.outcome` of `unvalued`; see `Probe/Basic.lean`).

## ±Interpretable Features ([chomsky-1995] Ch 4 §4.5)

The ±Interpretable distinction is orthogonal to valued/unvalued:

- **+Interpretable**: contributes to meaning, survives to LF.
  Categorial features ([N], [V], [D], [C]) and φ-features of nouns.
- **–Interpretable**: must be checked and deleted before LF.
  Case features, φ-features of T/v, strong [nominal-] features.

Interpretability is determined by the combination of feature type and
host category: person on N is +Interpretable, person on T is
–Interpretable. `isInterpretableOn` encodes this mapping.

## Design Decision: `Person` replaces `Nat`

`PhiFeature.person` uses `Person` (`.first |.second
|.third`) rather than a raw `Nat`. This eliminates the possibility of
meaningless person values (e.g., `person 47`) and grounds the feature
inventory in the same canonical type used across the library:

- `Person` — framework-agnostic person hierarchy
- `Phi.Geometry.DecomposedPerson` — [preminger-2014]'s [±participant,
  ±author] decomposition, now mapping from `Person`
- `DifferentialIndexing.IndexingPersonLevel` — [just-2024]'s SAP/3rd
  binary split, bridged to `Person`

For unvalued (probe) features, the value is irrelevant —
`FeatureVal.sameType` matches any `.person _` against any `.person _`
and any `.number _` against any `.number _`, ignoring specific values.
Use `.person .third` and `.number .sg` as conventional placeholders
for probes.

-/


namespace Minimalist

open Features.Prominence

-- ============================================================================
-- § 1: Phi-Features
-- ============================================================================

/-- Phi-features (agreement features). -/
inductive PhiFeature where
  | person : Person → PhiFeature
  | number : Number → PhiFeature         -- grammatical number (canonical inventory)
  | gender : Nat → PhiFeature        -- language-specific encoding
  deriving Repr, DecidableEq

-- ============================================================================
-- § 2: Honorific Features
-- ============================================================================

/-- Honorific level: social ordering between speaker and referent.
    Relational, not absolute.
    ⟦iHON⟧ = λx. S_i ≺ x, where ≺ encodes social hierarchy. -/
inductive HonLevel where
  | nh    -- nonhonorific: S ≥ referent
  | h     -- honorific: S < referent
  | hh    -- high honorific: S << referent
  deriving Repr, DecidableEq

-- ============================================================================
-- § 3: Feature Values
-- ============================================================================

/-- Feature values that can be checked via Agree -/
inductive FeatureVal where
  | phi : PhiFeature → FeatureVal
  | case : Case → FeatureVal
  | wh : Bool → FeatureVal           -- [±wh]
  | q : Bool → FeatureVal            -- [±Q] (question)
  | epp : Bool → FeatureVal          -- EPP (needs specifier)
  | tense : Bool → FeatureVal        -- [±tense]
  | hon : HonLevel → FeatureVal      -- [iHON] ([alok-bhalla-2026])
  | finite : Bool → FeatureVal       -- [±finite] (Fin head, [rizzi-1997])
  | factive : Bool → FeatureVal      -- [±factive] (clause-typing)
  | neg : Bool → FeatureVal          -- [±neg] (NegP, [pollock-1989])
  | rel : Bool → FeatureVal          -- [±rel] (relative clause typing, [rizzi-1997])
  | oblique : Bool → FeatureVal     -- [±oblique] (extraction tracking, [elkins-torrence-brown-2026])
  | ellipsis : Bool → FeatureVal   -- [E] feature licensing NP-ellipsis ([lobeck-1995], [saab-2026])
  | catN : Bool → FeatureVal       -- [N] referentiality ([panagiotidis-2015])
  | catV : Bool → FeatureVal       -- [V] temporal predication ([panagiotidis-2015])
  | foc : Bool → FeatureVal       -- [±FOC] information structure ([westergaard-2009])
  | pol : Bool → FeatureVal       -- [±Pol] polarity ([laka-1990]; [holmberg-2016])
  | pov : Bool → FeatureVal      -- [±d] point-of-view ([chou-2012]; [chan-shen-2026])
  -- Harbour decompositional features for person/number; distinct from the
  -- `phi` constructors above so postsyntactic rules can target them
  -- individually without colliding with existing person/number/gender
  -- pattern-matching elsewhere in the library.
  | atomic : Bool → FeatureVal     -- [±atomic] number lattice ([harbour-2014])
  | minimal : Bool → FeatureVal    -- [±minimal] number lattice ([harbour-2014])
  | participant : Bool → FeatureVal -- [±participant] person lattice ([harbour-2016])
  | author : Bool → FeatureVal     -- [±author] person lattice ([harbour-2016])
  deriving Repr, DecidableEq

/-- Do two feature values have the same type, ignoring specific values?

    This is the correct matching predicate for Agree: a probe with
    [uPerson] should match any goal with [Person:x], regardless of
    the specific person value x. In contrast, `DecidableEq` (`==`)
    compares both type and value, which is wrong for Agree matching
    where the probe carries a placeholder value. -/
def FeatureVal.sameType : FeatureVal → FeatureVal → Bool
  | .phi p1, .phi p2 => match p1, p2 with
    | .person _, .person _ => true
    | .number _, .number _ => true
    | .gender _, .gender _ => true
    | _, _ => false
  | .case _, .case _ => true
  | .wh _, .wh _ => true
  | .q _, .q _ => true
  | .epp _, .epp _ => true
  | .tense _, .tense _ => true
  | .hon _, .hon _ => true
  | .finite _, .finite _ => true
  | .factive _, .factive _ => true
  | .neg _, .neg _ => true
  | .rel _, .rel _ => true
  | .oblique _, .oblique _ => true
  | .ellipsis _, .ellipsis _ => true
  | .catN _, .catN _ => true
  | .catV _, .catV _ => true
  | .foc _, .foc _ => true
  | .pol _, .pol _ => true
  | .pov _, .pov _ => true
  | .atomic _, .atomic _ => true
  | .minimal _, .minimal _ => true
  | .participant _, .participant _ => true
  | .author _, .author _ => true
  | _, _ => false

-- ============================================================================
-- § 4: Grammatical Features (Valued / Unvalued)
-- ============================================================================

/-- A grammatical feature: either valued or unvalued.

    **Valued vs unvalued** is about whether the feature carries a specific
    value (person:3) or just a type placeholder (person:_). This is
    orthogonal to ±Interpretable (see `Interpretability` below):

    |                 | +Interpretable          | –Interpretable               |
    |-----------------|------------------------|-------------------------------|
    | **Valued**      | φ of N (person:3)      | —                             |
    | **Unvalued**    | —                      | φ of T/v, Case of N           |

    Unvalued features act as probes; valued features can be goals.
    But interpretability determines whether a feature *must be checked
    and deleted* before LF — a separate question from whether it
    currently carries a value. -/
inductive GramFeature where
  | valued : FeatureVal → GramFeature
  | unvalued : FeatureVal → GramFeature  -- The FeatureVal indicates feature TYPE
  deriving Repr, DecidableEq

/-- Is this feature valued? -/
def GramFeature.isValued : GramFeature → Bool
  | .valued _ => true
  | .unvalued _ => false

/-- Is this feature unvalued (a potential probe)? -/
def GramFeature.isUnvalued : GramFeature → Bool
  | .valued _ => false
  | .unvalued _ => true

/-- Get the feature type (ignoring valued/unvalued distinction) -/
def GramFeature.featureType : GramFeature → FeatureVal
  | .valued v => v
  | .unvalued v => v

/-- Do two features match in type? (for Agree)
    Delegates to `FeatureVal.sameType`, ignoring specific values. -/
def featuresMatch (f1 f2 : GramFeature) : Bool :=
  f1.featureType.sameType f2.featureType

-- ============================================================================
-- § 5: Feature Bundles as Assignments ([marcolli-chomsky-berwick-2025])
-- ============================================================================

/-! A feature bundle is a **total assignment** from feature dimensions to
three-state checking slots (`Features.FeatureSlot`): one slot per dimension,
`absent` / `unvalued` (probe) / `valued v`. This replaces the earlier list
representation (`List GramFeature`), which admitted junk — duplicate
dimensions, conflicting values — and was not extensional, so it could not be
a `LawfulBundleLike` (the `Features/Basic.lean` Todo).

This is the Agree-layer structure; per [marcolli-chomsky-berwick-2025] (book
p. 13) the free-Merge core keeps `SO₀` features atomic, so the slot apparatus
is decoupled from the `SyntacticObject` carrier and lives in
`Features/Slot.lean`.

`GramFeature` survives as a literal-builder DSL: `ofGramFeatures` folds a list
of valued/unvalued features into the assignment, the list head winning on
duplicate dimensions. -/

/-- The feature *dimensions* checked via Agree — the equivalence classes of
`FeatureVal.sameType`. φ-features split into their three sub-dimensions
(`person`, `number`, `gender`) so each is a slot in its own right. -/
inductive FeatureType where
  | person | number | gender
  | case | wh | q | epp | tense | hon | finite | factive | neg | rel
  | oblique | ellipsis | catN | catV | foc | pol | pov
  | atomic | minimal | participant | author
  deriving Repr, DecidableEq, Fintype

/-- All feature dimensions, for computable enumeration
(`Finset.univ.toList` is noncomputable). -/
def FeatureType.all : List FeatureType :=
  [.person, .number, .gender, .case, .wh, .q, .epp, .tense, .hon, .finite,
   .factive, .neg, .rel, .oblique, .ellipsis, .catN, .catV, .foc, .pol, .pov,
   .atomic, .minimal, .participant, .author]

/-- The dimension a feature value belongs to. Two values share a dimension
iff `FeatureVal.sameType` holds. -/
def FeatureVal.dimension : FeatureVal → FeatureType
  | .phi (.person _) => .person
  | .phi (.number _) => .number
  | .phi (.gender _) => .gender
  | .case _ => .case
  | .wh _ => .wh
  | .q _ => .q
  | .epp _ => .epp
  | .tense _ => .tense
  | .hon _ => .hon
  | .finite _ => .finite
  | .factive _ => .factive
  | .neg _ => .neg
  | .rel _ => .rel
  | .oblique _ => .oblique
  | .ellipsis _ => .ellipsis
  | .catN _ => .catN
  | .catV _ => .catV
  | .foc _ => .foc
  | .pol _ => .pol
  | .pov _ => .pov
  | .atomic _ => .atomic
  | .minimal _ => .minimal
  | .participant _ => .participant
  | .author _ => .author

/-- The value space of a dimension: the canonical type a slot at that
dimension carries (`person ↦ Person`, `number ↦ Number`, `gender ↦ Nat`,
`case ↦ Case`, `hon ↦ HonLevel`, every binary dimension `↦ Bool`). -/
@[reducible] def FeatureType.ValueOf : FeatureType → Type
  | .person => Person
  | .number => Number
  | .gender => Nat
  | .case => Case
  | .hon => HonLevel
  | .wh | .q | .epp | .tense | .finite | .factive | .neg | .rel
  | .oblique | .ellipsis | .catN | .catV | .foc | .pol | .pov
  | .atomic | .minimal | .participant | .author => Bool

instance (t : FeatureType) : DecidableEq t.ValueOf := by
  cases t <;> exact inferInstance

instance (t : FeatureType) : Repr t.ValueOf := by
  cases t <;> exact inferInstance

/-- The value carried by a feature value, in its dimension's value space. -/
def FeatureVal.value : (fv : FeatureVal) → fv.dimension.ValueOf
  | .phi (.person p) => p
  | .phi (.number n) => n
  | .phi (.gender g) => g
  | .case c => c
  | .wh b => b
  | .q b => b
  | .epp b => b
  | .tense b => b
  | .hon hl => hl
  | .finite b => b
  | .factive b => b
  | .neg b => b
  | .rel b => b
  | .oblique b => b
  | .ellipsis b => b
  | .catN b => b
  | .catV b => b
  | .foc b => b
  | .pol b => b
  | .pov b => b
  | .atomic b => b
  | .minimal b => b
  | .participant b => b
  | .author b => b

/-- A feature bundle as a total assignment: each dimension maps to a
three-state checking slot. The canonical extensional carrier — replacing
`List GramFeature` — that is `LawfulBundleLike`. -/
abbrev FeatureBundle := (t : FeatureType) → Features.FeatureSlot t.ValueOf

namespace FeatureBundle

instance : BundleLike FeatureBundle FeatureType (λ t => Features.FeatureSlot t.ValueOf) :=
  ⟨λ b => b⟩

instance : LawfulBundleLike FeatureBundle :=
  ⟨λ _ _ h => h⟩

/-- The bundle has a valued feature of the given dimension. -/
def hasValuedFeature (a : FeatureBundle) (t : FeatureType) : Bool :=
  (a t).isValued

/-- The bundle has an unvalued (probe) feature of the given dimension. -/
def hasUnvaluedFeature (a : FeatureBundle) (t : FeatureType) : Bool :=
  (a t).isUnvalued

/-- The value at the given dimension, when valued. -/
def getValuedFeature (a : FeatureBundle) (t : FeatureType) : Option t.ValueOf :=
  (a t).value?

/-- The assignment specifying exactly one valued dimension, all others absent. -/
def single (t : FeatureType) (v : t.ValueOf) : FeatureBundle :=
  Function.update (⊥ : FeatureBundle) t (.valued v)

@[simp] theorem single_self (t : FeatureType) (v : t.ValueOf) :
    single t v t = .valued v := by
  simp [single]

/-- The everywhere-`absent` bundle is the default. -/
instance : Inhabited FeatureBundle := ⟨⊥⟩

instance : DecidableEq FeatureBundle :=
  inferInstanceAs (DecidableEq ((t : FeatureType) → Features.FeatureSlot t.ValueOf))

/-- Render a bundle by its specified (non-`absent`) dimensions. The function
carrier has no structural `Repr`, so containing structures that `deriving Repr`
rely on this. -/
instance : Repr FeatureBundle where
  reprPrec fb _ :=
    repr <| FeatureType.all.filterMap λ t =>
      if (fb t).isSpecified then some (reprStr t, reprStr (fb t)) else none

end FeatureBundle

/-- The checking slot a single grammatical feature contributes at its own
dimension: `valued v ↦ valued v.value`, `unvalued _ ↦ unvalued`. -/
def GramFeature.toSlot : (gf : GramFeature) → Features.FeatureSlot gf.featureType.dimension.ValueOf
  | .valued v => .valued v.value
  | .unvalued _ => .unvalued

/-- Bridge from the legacy list representation: fold each feature into its
dimension's slot, the list head taking precedence on duplicate dimensions
(matching `getValuedFeature`/`find?` first-match semantics). -/
def FeatureBundle.ofGramFeatures (l : List GramFeature) : FeatureBundle :=
  l.foldr (λ gf a => Function.update a gf.featureType.dimension gf.toSlot) ⊥

/-- Reconstruct a `FeatureVal` at dimension `t` from a value. -/
def FeatureType.toFeatureVal : (t : FeatureType) → t.ValueOf → FeatureVal
  | .person, p => .phi (.person p)
  | .number, n => .phi (.number n)
  | .gender, g => .phi (.gender g)
  | .case, c => .case c
  | .hon, hl => .hon hl
  | .wh, b => .wh b
  | .q, b => .q b
  | .epp, b => .epp b
  | .tense, b => .tense b
  | .finite, b => .finite b
  | .factive, b => .factive b
  | .neg, b => .neg b
  | .rel, b => .rel b
  | .oblique, b => .oblique b
  | .ellipsis, b => .ellipsis b
  | .catN, b => .catN b
  | .catV, b => .catV b
  | .foc, b => .foc b
  | .pol, b => .pol b
  | .pov, b => .pov b
  | .atomic, b => .atomic b
  | .minimal, b => .minimal b
  | .participant, b => .participant b
  | .author, b => .author b

/-- A conventional placeholder value per dimension (for `unvalued`-feature
reconstruction, where the value is semantically irrelevant). -/
def FeatureType.placeholderValue : (t : FeatureType) → t.ValueOf
  | .person => .third
  | .number => .singular
  | .gender => 0
  | .case => .nom
  | .hon => .nh
  | .wh | .q | .epp | .tense | .finite | .factive | .neg | .rel
  | .oblique | .ellipsis | .catN | .catV | .foc | .pol | .pov
  | .atomic | .minimal | .participant | .author => false

/-- Bridge back to the legacy list representation: one `GramFeature` per
specified dimension. The placeholder value on `unvalued` features is
semantically inert (`ofGramFeatures` discards it via `toSlot`), so
`ofGramFeatures ∘ toGramFeatures` round-trips. -/
def FeatureBundle.toGramFeatures (fb : FeatureBundle) : List GramFeature :=
  FeatureType.all.filterMap λ t =>
    match fb t with
    | .absent => none
    | .unvalued => some (.unvalued (t.toFeatureVal t.placeholderValue))
    | .valued v => some (.valued (t.toFeatureVal v))

/-! ### `FeatureVal`-keyed query wrappers

Convenience over the `FeatureType`-keyed methods: pass a sample `FeatureVal`
(its carried value is ignored, only the dimension matters — the old
`sameType` semantics). These keep probe-spec call sites that pass a
placeholder feature (`.phi (.person .third)`) unchanged. -/

/-- The bundle has a valued feature of `fv`'s dimension. -/
def hasValuedFeature (fb : FeatureBundle) (fv : FeatureVal) : Bool :=
  FeatureBundle.hasValuedFeature fb fv.dimension

/-- The bundle has an unvalued (probe) feature of `fv`'s dimension. -/
def hasUnvaluedFeature (fb : FeatureBundle) (fv : FeatureVal) : Bool :=
  FeatureBundle.hasUnvaluedFeature fb fv.dimension

/-- The value at `fv`'s dimension, when valued. -/
def getValuedFeature (fb : FeatureBundle) (fv : FeatureVal) : Option fv.dimension.ValueOf :=
  FeatureBundle.getValuedFeature fb fv.dimension

-- ============================================================================
-- § 6: ±Interpretable Features
-- ============================================================================

/-- Whether a feature is interpretable (contributes to LF) or
    uninterpretable (must be checked and deleted before LF).

    This is the central distinction of [chomsky-1995] Ch 4 §4.5.
    It is orthogonal to valued/unvalued: a feature can be interpretable
    but unvalued (rare), or uninterpretable but valued (never, in the
    standard theory). The typical pairings are:

    - +Interpretable, valued: φ-features on nouns, categorial features
    - –Interpretable, unvalued: φ-features on T/v, Case on nouns

    `AgreeSOT.lean` uses `Interpretability` directly for tense features.
    `GenderResolution.lean`'s `AnnotatedFeature.interp` uses `Interpretability`
    directly; `CoordinateResolution.lean`, `AdamsonAnagnostopoulou2025.lean`,
    and `Carstens2026.lean` all use it via `open _root_.Minimalist`. -/
inductive Interpretability where
  | interpretable    -- +Interp: contributes to LF, survives
  | uninterpretable  -- –Interp: must be checked and deleted
  deriving Repr, DecidableEq

/-- Whether a feature is inherently interpretable regardless of host.

    Some features are always interpretable (categorial, honorific,
    factive) or always uninterpretable (Case, EPP, ellipsis).
    For features whose interpretability depends on host category
    (phi, wh, tense), see `isInterpretableOn` in `Checking.lean`. -/
def FeatureVal.inherentInterpretability : FeatureVal → Option Interpretability
  | .catN _ | .catV _ => some .interpretable
  | .case _ => some .uninterpretable
  | .epp _ => some .uninterpretable
  | .ellipsis _ => some .uninterpretable
  | .oblique _ => some .uninterpretable
  | .hon _ => some .interpretable
  | .neg _ => some .interpretable
  | .factive _ | .pol _ | .pov _ => some .interpretable
  | _ => none  -- host-dependent: phi, wh, q, tense, finite, foc, rel

/-- Case is always uninterpretable. -/
theorem case_always_uninterpretable (c : Case) :
    FeatureVal.inherentInterpretability (.case c) = some .uninterpretable := rfl

/-- Categorial [N] is always interpretable. -/
theorem catN_always_interpretable (b : Bool) :
    FeatureVal.inherentInterpretability (.catN b) = some .interpretable := rfl

end Minimalist
