import Linglib.Theories.Semantics.Noun.Kind.Mendia2020
import Linglib.Fragments.Dutch.Adjectives
import Linglib.Phenomena.Morphology.CategoryChanging

/-!
# Inflection and Derivation: How Adjectives and Nouns Refer to Abstract Objects
@cite{mcnally-deswart-2011}

@cite{mcnally-deswart-2011} (Proceedings of the 18th Amsterdam Colloquium,
425-434) analyses three morphologically distinct ways Dutch refers to
abstract objects (colors, tastes, properties), illustrated with the colour
*rood* 'red':

| Form               | Example                       | Semantic type        |
|--------------------|-------------------------------|----------------------|
| Uninflected nominal | `het rood (van de aardbeien)` | kind / set of subkinds |
| Derived `-heid`    | `de roodheid (van de huid)`   | kind / set of subkinds (of property correlate) |
| Inflected `-e` + `het` | `het rode van de aardbeien` | trope (entity correlate of relational property) |

The paper's central morphosyntactic claim is that Dutch *het* is polysemous:
with neuter nouns it denotes the iota operator, but when embedding an
inflected adjective in a DP it denotes @cite{chierchia-1984}'s ∩
nominalization operator. The inflectional suffix `-e` is *not* a
category-changing nominalizer; rather it is a valence-increasing operator
that turns the adjective into a relation `Pasp(y)(x)` between an object `y`
(saturated by the PP complement) and the `P` aspect `x` of that object.

The key empirical contrasts (paper §2.3):

* The inflected form admits adverbial but not adjectival modification (13)
  — evidence it remains adjectival, not nominal.
* The inflected form does not tolerate determiners other than *het* (14).
* The inflected form does not occur generically (15).
* The derived `-heid` form admits all determiners and pluralizes (9, 11).
* The uninflected form behaves as a regular neuter mass noun (6-8).

## Substrate reuse

* **Lexical data**: `Fragments/Dutch/Adjectives.lean` provides the consensus
  Dutch adjective lexicon — the three morphological forms (uninflected,
  inflected with `-e`, derived nominalisation in `-heid`), gender-driven
  alternation, and the exception class (forms in /ə/, `-a`, `-en`). The
  formalisation here derives its colour and taste roots from that Fragment
  rather than enumerating them inline.
* **Kind/subkind ontology**: @cite{zamparelli-1995}'s layered DP plus
  @cite{carlson-1977} kinds. The subkind relation is exactly what
  `Theories/Semantics/Noun/Kind/Mendia2020.lean` provides: a salient
  equivalence relation on shade-atoms partitions them into colour subkinds,
  and McNally & de Swart's `subkind(xk, red)` is precisely
  `Mendia2020.subkindOf kfShade (canonicalShade rood)`. Carlson's
  Disjointness Condition follows.

This file is the second consumer of `Mendia2020.subkindOf`, alongside
`Phenomena/Numerals/Studies/Snyder2026.lean`. Together they witness that
the Mendia substrate is genuinely cross-domain (numerals + colours), not
paper-specific scaffolding for one analysis.

## Cross-references

* `Phenomena/Morphology/CategoryChanging.lean` (`RootFamily`) formalises
  the @cite{marantz-1997} uncategorised-roots pattern that
  @cite{mcnally-deswart-2011} §3.1 explicitly invokes: `[[rood]] = red`
  is an entity-denoting root that *both* the noun `rood_N` and the
  adjective `rood_A` project from. The Dutch Fragment's `AdjEntry` plays
  the role of `RootFamily` for the colour and taste sub-paradigms;
  the connection is documented but not yet bridged formally (a
  `AdjEntry → RootFamily` adapter is plausible future work).
* `Phenomena/Morphology/Studies/Panagiotidis2015.lean` engages this file
  via a *diagnostic-alignment* bridge in its own §6 (`namespace MdSBridge`):
  Panagiotidis's §6.7.1 modifier-distribution diagnostic for SWITCH
  placement (geometric reasoning: SWITCH-dominated constituent projects
  nominally, takes adjectival mod; non-dominated constituent stays
  verbal/adjectival, takes adverbial mod) is shown to make the same
  predictions on each `InflectedAnalysis` rival as the M&deS-side
  `PredictsAdverbialModOnly`. Both diagnostics are inherited from
  Ackema & Neeleman 2004 (Beyond Morphology); the alignment is shared-
  source consequence rather than independent rediscovery. The bridge
  jointly motivates rejecting the `nominalisation` rival and supporting
  the adopted `hetAsCap` analysis.

## Cross-framework note

@cite{snyder-2026} §6-7 conjectures that *colour* terms admit the same
Polymorphic-Contextualism analysis as numerals: `[[red]] = λxα. red(x)`,
all forms via type-shifting. McNally & de Swart 2011 takes a different
route — they distinguish category-projections of the root (rood_N vs
rood_A) at the syntactic level, and use Chierchia ∩ for nominalisation
rather than pure Partee shifters. The two analyses *agree* on the kind-
formation substrate (both are Zamparelli/Carlson/Mendia subkind structure)
and on iota for definites; they *disagree* on whether nominalisation is
∩ (this paper) or NOM-as-Partee-shifter (Snyder Polymorphic Contextualism).
This is a genuine theoretical incompatibility surfaced by sharing
substrate.
-/

namespace Phenomena.Morphology.Studies.McNallyDeSwart2011

open Semantics.Noun.Kind.Mendia2020 (subkindOf disjointness_condition
  subkindOf_ne mem_subkindOf)
open Fragments.Dutch.Adjectives (AdjEntry Domain rood wit vreemd gezond leuk dicht)

/-! ## §3.1: Uncategorised roots and the Dutch lexicon

@cite{mcnally-deswart-2011} (18) posits entity-denoting roots: `[[rood]] =
red`, `[[zuur]] = acid`. Both nominal and adjectival uses project from the
same root. The roots themselves are the consensus Dutch lexical entries
in `Fragments/Dutch/Adjectives.lean`; this file uses those entries as the
carrier identifying each colour or taste subkind.

The @cite{marantz-1997} uncategorised-roots framework — formalised in
`Phenomena/Morphology/CategoryChanging.lean` as `RootFamily` — is the
substrate for the same idea. Each Dutch `AdjEntry` projects to a
`RootFamily` whose `forms` list records the three category-stamped surface
forms (uninflected adjective, inflected adjective per M&deS §3.4, derived
noun in `-heid`). The adapter `AdjEntry.toRootFamily` below makes the
connection code-level, not just docstring. -/

end Phenomena.Morphology.Studies.McNallyDeSwart2011

/-- Lift a Dutch `AdjEntry` into a @cite{marantz-1997}-style
    `RootFamily` (`Phenomena/Morphology/CategoryChanging.lean`). The
    uninflected and inflected forms are both adjectival per
    @cite{mcnally-deswart-2011} §2.3, §3.4 (the inflected form remains
    adjectival under the het-as-∩ analysis); the `-heid` derivative is a
    noun. Forms absent from the entry (no inflected variant for the
    schwa-, -a-, -en- final exception class; no -heid for the same) are
    omitted from the `forms` list. This adapter exercises the previously
    unread `.form` and `.formInfl` Fragment fields. Defined in the
    Fragment's namespace so dot notation `a.toRootFamily` works. -/
def Fragments.Dutch.Adjectives.AdjEntry.toRootFamily
    (a : Fragments.Dutch.Adjectives.AdjEntry) :
    Phenomena.Morphology.CategoryChanging.RootFamily :=
  let inflForms := match a.formInfl with
    | none   => []
    | some s => [(s, Phenomena.Morphology.CategoryChanging.LexCat.adjective)]
  let nominalForms := match a.nominalHeid with
    | none   => []
    | some s => [(s, Phenomena.Morphology.CategoryChanging.LexCat.noun)]
  { rootLabel := a.form
    forms := (a.form, .adjective) :: inflForms ++ nominalForms }

namespace Phenomena.Morphology.Studies.McNallyDeSwart2011

open Semantics.Noun.Kind.Mendia2020 (subkindOf disjointness_condition
  subkindOf_ne mem_subkindOf)
open Fragments.Dutch.Adjectives (AdjEntry Domain rood wit vreemd gezond leuk dicht)

/-- The `RootFamily` derived from `rood` records all three Dutch forms
    (uninflected adj, inflected adj, derived noun). -/
example : rood.toRootFamily.forms.length = 3 := by decide

/-- Adjectives in the inflection-exception class (e.g., `roze`) project
    to a single-form `RootFamily` (only the uninflected form), reflecting
    the morphological gap. -/
example : Fragments.Dutch.Adjectives.roze.toRootFamily.forms.length = 1 := by
  decide

/-- Adjectives spanning category projections always include the
    uninflected adjectival form. -/
theorem toRootFamily_includes_uninflected (a : AdjEntry) :
    (a.form, Phenomena.Morphology.CategoryChanging.LexCat.adjective)
      ∈ a.toRootFamily.forms := by
  unfold Fragments.Dutch.Adjectives.AdjEntry.toRootFamily
  cases a.formInfl <;> cases a.nominalHeid <;> simp

/-! ## §3.1, §3.2: Shades, colour partition, and Mendia substrate

@cite{mcnally-deswart-2011} follows @cite{zamparelli-1995}'s layered DP:
the noun `rood_N` denotes the *set of subkinds* (shades) of the colour
red. The subkind relation is @cite{mendia-2020}'s kind-formation framework
— partition the domain of shade-atoms by the salient equivalence relation
`belongs to the same colour root`. -/

/-- A shade-atom: an adjective entry from the Dutch Fragment paired with a
    distinguishing index. The pair lets multiple shade-tokens belong to
    the same colour subkind (e.g., crimson and scarlet both belong to
    `rood`), so the @cite{mendia-2020} partition is exercised non-trivially. -/
structure Shade where
  /-- The adjective entry classifying this shade — drawn from the Dutch
      Fragment (e.g., `Fragments.Dutch.Adjectives.rood`). -/
  root : AdjEntry
  /-- Distinguishing index for multiple shade-tokens of the same root. -/
  idx  : Nat
  deriving DecidableEq, Repr

/-- The salient @cite{mendia-2020} kind-formation for shades: partitioned
    by their adjective-entry root. Each equivalence class is a subkind
    (set of shade-tokens for one Dutch adjective entry). The same setoid
    works for both colours and tastes — only the chosen entries differ. -/
def kfShade : Setoid Shade where
  r s₁ s₂ := s₁.root = s₂.root
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- Canonical witness shade for an adjective entry. -/
def canonicalShade (a : AdjEntry) : Shade := ⟨a, 0⟩

/-- @cite{mcnally-deswart-2011} (19): the uninflected nominal `rood_N`
    denotes the set of subkinds (shades) of the colour `red`. Implemented
    as `Mendia2020.subkindOf kfShade (canonicalShade rood)` — the
    equivalence class of any canonical witness. The Dutch Fragment entry
    `Fragments.Dutch.Adjectives.rood` is the actual lexical anchor. -/
def uninflectedNominal (a : AdjEntry) : Set Shade :=
  subkindOf kfShade (canonicalShade a)

/-- The uninflected nominal of `a` is exactly the set of shades whose root
    is `a`. -/
theorem uninflectedNominal_iff (a : AdjEntry) (s : Shade) :
    s ∈ uninflectedNominal a ↔ s.root = a :=
  ⟨Eq.symm, Eq.symm⟩

/-- Distinct adjective entries project to disjoint uninflected nominals —
    a direct consequence of @cite{carlson-1977}'s Disjointness Condition
    derived from the Mendia partition. -/
theorem uninflectedNominal_disjoint {a₁ a₂ : AdjEntry} (h : a₁ ≠ a₂) :
    Disjoint (uninflectedNominal a₁) (uninflectedNominal a₂) :=
  disjointness_condition kfShade (a := canonicalShade a₁)
    (b := canonicalShade a₂) h

/-- Concrete witness: `rood` and `wit` denote disjoint subkinds. The Dutch
    Fragment entries are non-equal as `AdjEntry` records, so the Mendia
    Disjointness Condition gives disjoint shade-sets directly. -/
theorem rood_disjoint_from_wit :
    Disjoint (uninflectedNominal rood) (uninflectedNominal wit) :=
  uninflectedNominal_disjoint (by decide)

/-! ## §3.2: PP modification and `het` as iota (uninflected case)

@cite{mcnally-deswart-2011} (20): the PP `van de aardbeien` introduces a
contextual relation `R_i(x_k, s)` where `s` is the PP-complement entity.
Combined via predicate-modification with the noun's set of subkinds, then
selected by `het` as iota, it picks out the unique strawberry-related
shade of red. -/

/-- @cite{mcnally-deswart-2011} (20): a PP modifier introduces a contextual
    relation between subkinds and the PP-complement entity. Modelled here
    as a predicate-restriction on shades. -/
def ppModifier {Entity : Type*} (R : Shade → Entity → Prop) (s : Entity)
    (P : Set Shade) : Set Shade :=
  {x | x ∈ P ∧ R x s}

/-- @cite{mcnally-deswart-2011} (21a): `rood van de aardbeien` denotes the
    set of red-shades that stand in `R_i` to the strawberries. -/
def uninflectedNominalWithPP {Entity : Type*} (a : AdjEntry)
    (R : Shade → Entity → Prop) (s : Entity) : Set Shade :=
  ppModifier R s (uninflectedNominal a)

/-! ## §3.3: Derived `-heid` form

@cite{mcnally-deswart-2011} (24a-c): the derivational suffix `-heid`
operates on a property `P` (the adjective's denotation) and returns the
set of subkinds of its entity correlate (Chierchia ∩P). Modelled here at
the kind-of-subkinds layer. -/

/-- The adjectival denotation of a Dutch adjective entry, abbreviated as
    `[[rood_A]] = λy. Red(y)` per @cite{mcnally-deswart-2011} (23c). The
    paper distinguishes a gradable measure-function reading (23a, after
    @cite{kennedy-mcnally-2010}) from a non-gradable proxy reading (23b);
    we abbreviate as the paper does, and identify each adjective with its
    Dutch Fragment entry. -/
def adjectivalProperty (a : AdjEntry) : Shade → Prop :=
  fun s => s.root = a

/-- @cite{mcnally-deswart-2011} (24b): `roodheid_N` denotes the set of
    subkinds of the entity correlate (Chierchia ∩) of the property
    `λy. Red(y)`. The substantive Chierchia ∩ operator lives in
    `Theories/Semantics/Noun/Kind/Chierchia1998.lean` (`down`/`up` for
    intensional kinds) and `Theories/Semantics/Composition/TypeShifting.lean`
    (`NOM` extensional counterpart, with `NOM = iota` in the finite
    setting); we do not call them here because the extensional collapse
    means the only Fragment-visible distinction is whether the adjective
    *has* a `-heid` form at all.

    The construction is *partial*: when `a` lacks a `-heid` form (e.g.,
    `roze`, `mauve` per @cite{mcnally-deswart-2011} §1), the derived
    nominal is *outside the scope* of the analysis — `none`, not `some ∅`.
    This matches the paper's framing (p. 426, set aside): "Not all
    adjectives allow modification by `-heid` to form a nominalization,
    or have uninflected nominal counterparts. We will focus on triplets…". -/
def derivedNominal (a : AdjEntry) : Option (Set Shade) :=
  a.nominalHeid.map fun _ => subkindOf kfShade (canonicalShade a)

/-- When `a` admits a `-heid` form, the derived nominal coincides
    extensionally with the uninflected nominal — both denote the same
    Mendia subkind. This is the empirical convergence
    @cite{mcnally-deswart-2011} §3.2-3.3 establishes between the two
    kind-denoting routes; the formal divergence (∩ vs root projection)
    is suppressed in the extensional model. -/
theorem derivedNominal_eq_uninflected_of_heid {a : AdjEntry}
    (h : a.nominalHeid.isSome) :
    derivedNominal a = some (uninflectedNominal a) := by
  unfold derivedNominal
  cases hh : a.nominalHeid with
  | none => simp [hh] at h
  | some _ => rfl

/-- When `a` has no `-heid` form (e.g., `roze`), the derived-nominal
    construction is *outside the scope* of the analysis. -/
theorem derivedNominal_none_of_no_heid {a : AdjEntry}
    (h : a.nominalHeid = none) : derivedNominal a = none := by
  unfold derivedNominal; rw [h]; rfl

/-- Concrete witness using the Fragment's exception class: `roze` 'pink'
    has no `-heid` form per @cite{mcnally-deswart-2011} §1, so its derived
    nominal is outside scope. -/
theorem roze_derivedNominal_none :
    derivedNominal Fragments.Dutch.Adjectives.roze = none :=
  derivedNominal_none_of_no_heid (by decide)

/-! ## §1: Domain-driven felicity of inflected nominalisation

@cite{mcnally-deswart-2011} §1 observes that the inflected nominalisation
construction (`het rode van X`, `het vreemde van X`) is *frequent with
abstract adjectives* (`vreemd`, `gezond`, `leuk`, `bijzonder`) but
*rare with concrete adjectives* — the cited contrast being
`?*het dichte van deze doos` 'the closed of this box'. We project this
asymmetry off the Fragment's `Domain` field. -/

/-- Frequency of the inflected nominalisation construction by domain.
    @cite{mcnally-deswart-2011} §1 + §3.4 reports a graded scale, not a
    binary contrast: abstract adjectives admit the construction *most
    freely*, colour and taste are the focal cases (admit all three forms
    productively), and concrete adjectives are *marginal* (only `dicht`
    is cited, with `?*het dichte van deze doos` flagged). -/
inductive Frequency where
  /-- Most freely admitted (abstract: `het vreemde van X`, paper §3.4). -/
  | high
  /-- Productively admitted (colour, taste: `het rode van X`, paper §3.1). -/
  | medium
  /-- Marginally admitted (concrete: `?*het dichte van deze doos`, §1). -/
  | marginal
  deriving DecidableEq, Repr

/-- The frequency-of-inflected-nominalisation predicted by a semantic
    `Domain`. Per @cite{mcnally-deswart-2011} §1 + §3.4. -/
def inflectedNominalisationFrequency : Domain → Frequency
  | .color    => .medium
  | .taste    => .medium
  | .abstract => .high
  | .concrete => .marginal

/-- The §1 abstract/concrete asymmetry, formalised on Fragment entries
    along the graded `Frequency` scale. Abstract adjectives (`vreemd`,
    `gezond`, `leuk`) score `.high`; colours and tastes (`rood`)
    score `.medium`; the concrete adjective `dicht` scores `.marginal`.
    The proof reads `.domain` on each Fragment entry. -/
theorem domain_frequency_split :
    inflectedNominalisationFrequency rood.domain   = .medium ∧
    inflectedNominalisationFrequency vreemd.domain = .high   ∧
    inflectedNominalisationFrequency gezond.domain = .high   ∧
    inflectedNominalisationFrequency leuk.domain   = .high   ∧
    inflectedNominalisationFrequency dicht.domain  = .marginal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [inflectedNominalisationFrequency,
      Fragments.Dutch.Adjectives.rood, Fragments.Dutch.Adjectives.vreemd,
      Fragments.Dutch.Adjectives.gezond, Fragments.Dutch.Adjectives.leuk,
      Fragments.Dutch.Adjectives.dicht]

/-! ## §3.4: Inflected `-e` form — relational trope semantics

@cite{mcnally-deswart-2011} (25): the inflectional suffix `-e` increases
the adjective's valence by one, introducing a relation `P_asp(y)(x)`
between an external entity `y` (saturated by PP) and the `P` aspect `x`
of `y`. The `het` article then applies @cite{chierchia-1984}'s ∩ to
reify the resulting property as a trope (an entity correlate of a
property *uniquely instantiated in one individual*).

The crucial type-theoretic distinction: uninflected/derived denote
*kinds* (sets of subkinds); inflected denotes a *trope* (a single
property-aspect of a specific entity), which is *not* a kind. -/

/-- An `AspectOf` instance records, for each adjectival property `P`, the
    "P-aspect" relation the language pairs with `P`. This makes
    @cite{mcnally-deswart-2011}'s `P_asp` derivation explicit: the suffix
    `-e` does not introduce an arbitrary new relation; it produces *the*
    aspect-relation contextually associated with `P` (analogous to the
    `cor` function relating the proxy adjective to its associated property
    in (23b)). -/
def AspectOf (Entity : Type*) := (Shade → Prop) → Entity → Shade → Prop

/-- @cite{mcnally-deswart-2011} (25a): `[[-e]] = λPλyλx. P_asp(y)(x)`.
    The `-e` inflection takes a property `P` and produces `P_asp` via the
    contextual aspect-of mapping. Crucially `P_asp` is *derived from* `P`
    (not an independent input), so substituting a different property
    yields a different aspect relation. -/
def inflectAdjective {Entity : Type*}
    (asp : AspectOf Entity) (P : Shade → Prop) :
    Entity → Shade → Prop := asp P

/-- @cite{mcnally-deswart-2011} (26b): saturating the `-e`-inflected
    adjective with a PP-complement entity yields a *property* (the
    aspect-of-`s` property), not a set of kinds. -/
def inflectedWithPP {Entity : Type*}
    (Pasp : Entity → Shade → Prop) (s : Entity) : Shade → Prop :=
  Pasp s

-- (NOTE: a previous `inflectAdjective_respects_property` theorem was
-- deleted as η-identity. Genuine pinning of the `asp` ↔ `P` relationship
-- requires a `LawfulAspectOf` typeclass with injectivity laws, which is
-- not warranted by a single-paper consumer; promote when needed.)

/-! @cite{moltmann-2004} **trope**: the entity correlate of a property
    uniquely instantiated in one specific individual. We do *not*
    introduce a dedicated `Trope` struct — the inflected-form denotation
    is the bare pair `(Shade → Prop) × Entity`, with `.fst` recording the
    property aspect and `.snd` recording the bearer. A full
    @cite{moltmann-2004} / @cite{moltmann-2013} formalisation would
    additionally individuate by spatiotemporal location and carry a
    uniqueness-presupposition witness; promote to substrate
    (`Theories/Semantics/Reference/Trope.lean` or similar) when a second
    consumer arrives. No prior `Trope` type exists in linglib. -/

/-- The denotation of a `het`-reified inflected adjective: the bare pair
    `(property-aspect, bearer)`. -/
abbrev TropePair (Entity : Type*) := (Shade → Prop) × Entity

/-- @cite{mcnally-deswart-2011} (26c): `het rode van de aardbeien`
    denotes the trope obtained by reifying (Chierchia ∩) the property
    `λx. Red_asp(strawberries)(x)`. The result is *not* a kind; it is a
    trope — an entity correlate uniquely tied to a specific bearer. The
    full pipeline (`-e` inflection + PP saturation + het-as-∩) composes
    `inflectAdjective` and `inflectedWithPP`. -/
def inflectedWithHet {Entity : Type*}
    (asp : AspectOf Entity) (P : Shade → Prop) (s : Entity) :
    TropePair Entity :=
  (inflectedWithPP (inflectAdjective asp P) s, s)

/-! ## §3.4-3.5: Type-theoretic contrast between the three forms

The architectural payoff of the paper: uninflected and derived forms
denote sets of subkinds (kind-level); the inflected form denotes a trope
(individual-level). The Lean types make this explicit. -/

/-- The three Dutch forms are typologically distinct in their *Lean
    return types*: uninflected and derived return `Set Shade` (kinds);
    the inflected form returns `TropePair Entity`. This is the core
    contrast @cite{mcnally-deswart-2011} establishes. -/
inductive Form where
  /-- `het rood (van X)` — uninflected nominal, neuter mass noun. -/
  | uninflected
  /-- `de roodheid (van X)` — derived nominal via -heid, count or mass. -/
  | derived
  /-- `het rode van X` — inflected adjective + het-as-∩. -/
  | inflected
  deriving DecidableEq, Repr

/-- Whether a form's denotation is a *kind* (set of subkinds) or a *trope*
    (entity correlate of a uniquely instantiated property). -/
inductive AbstractObjectKind where
  | kind   -- Set of subkinds
  | trope  -- Entity correlate uniquely instantiated
  deriving DecidableEq, Repr

/-- @cite{mcnally-deswart-2011}'s central typological claim: each Dutch
    form maps to a determinate kind of abstract object. -/
def Form.denotationType : Form → AbstractObjectKind
  | .uninflected => .kind
  | .derived     => .kind
  | .inflected   => .trope

/-- Uninflected and derived both denote *kinds*; inflected is the unique
    *trope*-denoting form. This is the empirically motivated three-way
    distinction the paper argues for (§3.4 + §5 conclusion). -/
theorem two_kinds_one_trope :
    Form.uninflected.denotationType = .kind ∧
    Form.derived.denotationType     = .kind ∧
    Form.inflected.denotationType   = .trope := ⟨rfl, rfl, rfl⟩

/-! ## §2.3: Rival analyses of the inflected form

@cite{mcnally-deswart-2011} §2.3 considers two rival analyses of `het rode
van X` and rejects both, in favour of the third (`het` as Chierchia ∩):

1. **Nominalisation analysis**: the inflected `rode` IS a noun (changed
   category via `-e`). Rejected because nouns admit adjectival modification
   and other determiners (paper §2.3 (13)-(14)).
2. **Ellipsis analysis**: the inflected `rode` is an adjective hiding an
   empty/elided noun. Rejected because (a) determiner restrictions (14)
   and lack of generic readings (15) are unexplained, and (b) no plausible
   noun can be inserted (paper §2.3 (16): `de` is required for `kleur`,
   `smaak`).
3. **Het-as-∩ analysis**: `het` carries Chierchia ∩, embedding the AP
   directly under DP. The adjective remains adjectival (taking adverbial
   mod), and only `het` (the default ∩-marker for non-nominal categories)
   is licensed.

Following the @cite{snyder-2026} `PolymorphicAnalysis` pattern, we encode
all three rivals and their predictions for the §2.3 diagnostics. The
substantive theorem `only_hetAsCap_matches_diagnostics` shows only the
adopted analysis matches the actual data — the other two would predict
the wrong distribution. -/

/-- The three rival analyses of Dutch `het rode van X` considered in
    @cite{mcnally-deswart-2011} §2.3. -/
inductive InflectedAnalysis where
  /-- The inflected adjective is a noun (category-changing). Rejected. -/
  | nominalisation
  /-- The inflected adjective hides an empty/elided noun. Rejected. -/
  | ellipsis
  /-- `het` = Chierchia ∩, embedding the inflected AP under DP. Adopted. -/
  | hetAsCap
  deriving DecidableEq, Repr

/-- Does the analysis predict that the form admits adverbial (rather than
    adjectival) modification? Per §2.3 (13). The three rivals diverge
    here: only `nominalisation` (which makes the form a noun) predicts
    adjectival mod is licensed and adverbial mod blocked. Under
    `ellipsis`, the visible element remains an adjective pre-ellipsis,
    so adverbial mod IS licensed. -/
def InflectedAnalysis.PredictsAdverbialModOnly : InflectedAnalysis → Prop
  | .nominalisation => False  -- nouns take adjectival modification
  | .ellipsis       => True   -- visible adjective remains adjectival pre-ellipsis
  | .hetAsCap       => True   -- AP under DP, takes adverbial mod

instance : DecidablePred InflectedAnalysis.PredictsAdverbialModOnly :=
  fun a => by cases a <;> unfold InflectedAnalysis.PredictsAdverbialModOnly <;> exact inferInstance

/-- Does the analysis predict that *only* `het` (no other determiners)
    licenses the form? Per §2.3 (14). -/
def InflectedAnalysis.PredictsHetOnlyDeterminer : InflectedAnalysis → Prop
  | .nominalisation => False
  | .ellipsis       => False
  | .hetAsCap       => True

instance : DecidablePred InflectedAnalysis.PredictsHetOnlyDeterminer :=
  fun a => by cases a <;> unfold InflectedAnalysis.PredictsHetOnlyDeterminer <;> exact inferInstance

/-- Does the analysis predict that the form rejects generic readings?
    Per §2.3 (15). -/
def InflectedAnalysis.PredictsNoGeneric : InflectedAnalysis → Prop
  | .nominalisation => False
  | .ellipsis       => False
  | .hetAsCap       => True

instance : DecidablePred InflectedAnalysis.PredictsNoGeneric :=
  fun a => by cases a <;> unfold InflectedAnalysis.PredictsNoGeneric <;> exact inferInstance

/-- @cite{mcnally-deswart-2011}'s §2.3 argument made formal: only the
    `hetAsCap` analysis predicts the actual distribution (adverbial-mod
    only, het-only determiner, no generics). Each predicate is decided
    on the rival's own theoretical commitments; the conjunction
    discriminates rivals from data. -/
theorem only_hetAsCap_matches_diagnostics (a : InflectedAnalysis) :
    (a.PredictsAdverbialModOnly ∧
     a.PredictsHetOnlyDeterminer ∧
     a.PredictsNoGeneric) ↔ a = .hetAsCap := by
  cases a <;> simp [InflectedAnalysis.PredictsAdverbialModOnly,
    InflectedAnalysis.PredictsHetOnlyDeterminer,
    InflectedAnalysis.PredictsNoGeneric]

/-! ## §2.3: Form-level distribution facts

The morphosyntactic facts (13)-(15) about each Dutch form: only the
inflected form is restricted to *het*, to adverbial modification, and
rejects generic uses. -/

/-- Whether a form admits non-`het` determiners (a, this, his, no, many).
    @cite{mcnally-deswart-2011} (14): only inflected refuses. -/
def Form.AdmitsDetOtherThanHet : Form → Prop
  | .uninflected => True   -- (7)
  | .derived     => True   -- (11)
  | .inflected   => False  -- (14a-b): *een/dit/zijn/geen/veel rode

instance : DecidablePred Form.AdmitsDetOtherThanHet :=
  fun f => by cases f <;> unfold Form.AdmitsDetOtherThanHet <;> exact inferInstance

/-- Whether a form admits adjectival modification (vs only adverbial).
    @cite{mcnally-deswart-2011} (13): only inflected refuses. -/
def Form.AdmitsAdjectivalModification : Form → Prop
  | .uninflected => True   -- (6a)
  | .derived     => True   -- (10)
  | .inflected   => False  -- (13): adverbial only

instance : DecidablePred Form.AdmitsAdjectivalModification :=
  fun f => by cases f <;> unfold Form.AdmitsAdjectivalModification <;> exact inferInstance

/-- Whether a form admits a generic interpretation. (8), (12) vs (15). -/
def Form.AdmitsGeneric : Form → Prop
  | .uninflected => True   -- (8): Rood is een krachtige kleur.
  | .derived     => True   -- (12): Blijvende roodheid is...
  | .inflected   => False  -- (15): *Rode is...

instance : DecidablePred Form.AdmitsGeneric :=
  fun f => by cases f <;> unfold Form.AdmitsGeneric <;> exact inferInstance

/-- The morphosyntactic distribution (§2.3 — three diagnostics) and the
    semantic-type column (`denotationType`) are cross-aligned: a form
    fails any one of the three diagnostics iff it denotes a trope. This
    is the substantive content of the paper's claim that the
    morphosyntactic restrictions on `het rode van X` are *because of* its
    trope semantics — two independently-stated tables coincide. -/
theorem morphosyntax_aligns_with_trope_semantics (f : Form) :
    (¬ f.AdmitsDetOtherThanHet ∨
     ¬ f.AdmitsAdjectivalModification ∨
     ¬ f.AdmitsGeneric)
    ↔ f.denotationType = .trope := by
  cases f <;> simp [Form.denotationType, Form.AdmitsDetOtherThanHet,
    Form.AdmitsAdjectivalModification, Form.AdmitsGeneric]

/-- Equivalent biconditional: a form denotes a trope iff it is the
    inflected form. -/
theorem trope_iff_inflected (f : Form) :
    f.denotationType = .trope ↔ f = .inflected := by
  cases f <;> simp [Form.denotationType]

/-! ## §3.5, §4: Cross-linguistic parallels

@cite{mcnally-deswart-2011} §3.5 places the inflected construction in
parallel with Dutch *het*-nominalised infinitives (`het zingen van Jan`,
§3.5 (28a)). For the semantics, the paper invokes @cite{chierchia-1984}
on infinitives and gerunds, and @cite{hamm-vanlambalgen-2002} on formal
foundations of nominalisation. @cite{pullum-1991}'s "NP with VP head"
analysis treats the *syntax* of English `-ing` separately and is *not*
itself a Chierchia-∩ analysis.

§4 considers Spanish *lo*-nominals (`lo blanco de las dunas`). Crucially,
@cite{villalba-2009}'s own analysis uses Moltmann's properties/qualities
ontology (introducing a *quality* sort distinct from properties), *not*
Chierchia ∩. McNally & de Swart §4 *propose* extending their ∩-analysis
to Spanish, against Villalba — the ∩-extension is M&deS's, not Villalba's.

The paper's central general claim (§5): natural languages exploit the
inflection / derivation distinction to create subtle nuances in reference
to abstract objects, all derivable from a parsimonious kind+token
ontology — no separate "quality" sort is needed (contra Villalba).

The cross-linguistic cluster — Dutch *het* (inflected adjective AND
*het*-nominalised infinitive), English `-ing` gerund (Chierchia 1984 +
Hamm & van Lambalgen 2002 semantics, Pullum 1991 syntax), Spanish *lo*
(M&deS extension, against Villalba) — is documented here in prose
because none of the analogues besides Dutch inflected-adjective is
currently formalised in linglib. Promote to a typed cluster when
the second case lands. -/

/-! ## §5: Cross-paper substrate alignment with Snyder 2026

`Phenomena/Numerals/Studies/Snyder2026.lean` (Polymorphic Contextualism)
and this file (McNally & de Swart 2011) both consume the same substrate:
* `Mendia2020.subkindOf` for kind formation by salient equivalence
  relation (numerals partition by mathematical system; colours partition
  by chromatic root).
* IOTA-as-definite for selecting a unique subkind from a modified noun
  predicate.

They *disagree* on:
* Whether nominalisation is Chierchia ∩ (this paper) or Partee NOM as a
  pure type-shifter (Snyder Polymorphic Contextualism, §2 (10a)). In the
  finite extensional setting these collapse (cf.
  `Composition/TypeShifting.lean` `NOM = iota`), but conceptually they
  diverge: ∩ is *substantive* (entity-correlate-of-property), NOM is
  *formal* (Partee-shifter combinator).
* Whether the lexical entry is unitary (Snyder: one `λxα. two(x)`) or
  category-projected (McNally & de Swart: distinct `rood_N` vs `rood_A`
  built from a shared root via different morphological projections).

The shared substrate (Mendia subkinds + IOTA) is genuine; the divergence
on nominalisation and lexical-projection architecture is genuine theoretical
incompatibility. This is exactly the kind of cross-framework engagement
linglib is designed to surface.
-/

end Phenomena.Morphology.Studies.McNallyDeSwart2011
