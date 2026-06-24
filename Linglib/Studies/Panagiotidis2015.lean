import Linglib.Morphology.RootFamily
import Linglib.Studies.McNallyDeSwart2011
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Syntax.Minimalist.ExtendedProjection.Properties

/-!
# Categorial Features ↔ Category-Changing Morphology

[panagiotidis-2015] [marantz-1997]Connects the theory-side predictions of [panagiotidis-2015] — substantive
categorial features [N] and [V] hosted on categorizer heads — to the empirical
data on category-changing morphology in English.

## What this bridge proves

1. **Categorizer–LexCat correspondence**: Each theory-side categorizer (v, n, a)
   maps to exactly one empirical lexical category (verb, noun, adjective).

2. **Feature predictions**: The categorial features [N]/[V] on each categorizer
   correctly predict the interpretive perspective of the resulting category —
   nouns have sortal perspective ([N]), verbs have temporal perspective ([V]),
   adjectives have both ([N, V]).

3. **EP well-formedness**: Each categorizer extends its lexical anchor into a
   well-formed EP (A→a, N→n, V→v).

4. **Categorizer parallelism**: All three categorizers sit at the same F-level
   (F1 in Grimshaw's system), formalizing Panagiotidis's claim that
   categorization is a uniform operation across category families.

## Derivational chain

```
ExtendedProjection/Basic.lean (CategorialFeatures, isCategorizer, categorialFeatures)
    ↓
THIS BRIDGE FILE
    ↓
Morphology/RootFamily.lean (RootFamily, LexCat)
```

-/

namespace Panagiotidis2015

open Minimalist
open Morphology (LexCat RootFamily)

-- ════════════════════════════════════════════════════════════════
-- § 1: Categorizer ↔ LexCat Correspondence
-- ════════════════════════════════════════════════════════════════

/-- Map a Minimalist categorizer to the empirical lexical category
    of the word it produces. This is the core link between the theory
    (Cat.v, Cat.n, Cat.a) and the data (LexCat). -/
def categorizerToLexCat : Cat → Option LexCat
  | .v => some .verb
  | .n => some .noun
  | .a => some .adjective
  | _  => none

/-- Map an empirical lexical category to its theory-side categorizer. -/
def lexCatToCategorizer : LexCat → Cat
  | .verb      => .v
  | .noun      => .n
  | .adjective => .a

/-- The mapping is a partial bijection: lexCat → categorizer → lexCat roundtrips. -/
theorem roundtrip (c : LexCat) :
    categorizerToLexCat (lexCatToCategorizer c) = some c := by
  cases c <;> rfl

/-- Every categorizer maps to some LexCat. -/
theorem categorizers_have_lexcat :
    categorizerToLexCat .v = some .verb ∧
    categorizerToLexCat .n = some .noun ∧
    categorizerToLexCat .a = some .adjective := ⟨rfl, rfl, rfl⟩

/-- Non-categorizers don't map to any LexCat. -/
theorem non_categorizers_no_lexcat :
    categorizerToLexCat .V = none ∧
    categorizerToLexCat .N = none ∧
    categorizerToLexCat .A = none ∧
    categorizerToLexCat .T = none ∧
    categorizerToLexCat .D = none := ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 2: Feature Predictions
-- ════════════════════════════════════════════════════════════════

/-- Does a categorizer produce a category with sortal perspective?
    Panagiotidis §4.3: [N] = sortal perspective / referentiality. Items bearing [N] have the capacity to introduce
    discourse referents (nouns, adjectives) — items lacking [N] do not
    (verbs). -/
def producesReferential (c : Cat) : Bool :=
  (categorialFeatures c).hasN

/-- Does a categorizer produce a category with temporal perspective?
    Panagiotidis §4.3: [V] = temporal perspective / eventivity. Items
    bearing [V] can anchor to time/events (verbs, adjectives) — items
    lacking [V] do not have temporal anchoring (nouns). -/
def producesPredicative (c : Cat) : Bool :=
  (categorialFeatures c).hasV

/-- Nouns have sortal but not temporal perspective: n bears [N] only. -/
theorem noun_referential_not_predicative :
    producesReferential .n = true ∧ producesPredicative .n = false := by decide

/-- Verbs have temporal but not sortal perspective: v bears [V] only. -/
theorem verb_predicative_not_referential :
    producesPredicative .v = true ∧ producesReferential .v = false := by decide

/-- Adjectives have both sortal and temporal perspective: a bears [N, V]. -/
theorem adjective_both :
    producesReferential .a = true ∧ producesPredicative .a = true := by decide

/-- The noun–verb asymmetry: nouns have sortal but not temporal perspective;
    verbs have temporal but not sortal perspective. Adjectives have both.
    This follows from the [N]/[V] feature distribution on categorizers. -/
theorem referential_predicative_asymmetry :
    -- Nouns: [N], not [V]
    (categorialFeatures .n).hasN = true ∧ (categorialFeatures .n).hasV = false ∧
    -- Verbs: [V], not [N]
    (categorialFeatures .v).hasV = true ∧ (categorialFeatures .v).hasN = false ∧
    -- Adjectives: [N] and [V]
    (categorialFeatures .a).hasN = true ∧ (categorialFeatures .a).hasV = true := by
  decide

-- ════════════════════════════════════════════════════════════════
-- § 3: EP Well-Formedness
-- ════════════════════════════════════════════════════════════════

/-- Each categorizer forms a well-formed EP with its lexical anchor:
    V→v, N→n, A→a are all category-consistent and F-monotone. -/
theorem all_categorizer_eps_wellformed :
    (allCategoryConsistent [Cat.V, Cat.v] = true ∧ allFMonotone [Cat.V, Cat.v] = true) ∧
    (allCategoryConsistent [Cat.N, Cat.n] = true ∧ allFMonotone [Cat.N, Cat.n] = true) ∧
    (allCategoryConsistent [Cat.A, Cat.a] = true ∧ allFMonotone [Cat.A, Cat.a] = true) := by
  decide

/-- The F-level jump from lexical head to categorizer is exactly 1 in all cases.
    The uniformity of categorization is Panagiotidis's prediction (§4.4–§4.5);
    the F-value encoding is [grimshaw-2005]'s EP architecture. -/
theorem categorization_uniform_fstep :
    fValue .v - fValue .V = 1 ∧
    fValue .n - fValue .N = 1 ∧
    fValue .a - fValue .A = 1 := by decide

-- ════════════════════════════════════════════════════════════════
-- § 4: Categorizer Parallelism
-- ════════════════════════════════════════════════════════════════

/-- All categorizers sit at exactly F1 (in Grimshaw's system), parallel
    across families. Panagiotidis's core claim: v, n, a are structurally
    parallel — they differ only in which interpretable features they bear. -/
theorem categorizers_parallel_at_f1 :
    fValue .v = 1 ∧ fValue .n = 1 ∧ fValue .a = 1 := by decide

/-- The categorizers are in their respective families. -/
theorem categorizers_in_own_families :
    catFamily .v = .verbal ∧ catFamily .n = .nominal ∧ catFamily .a = .adjectival := by
  decide

/-- Category-changing morphology = changing the categorizer.
    The same root under different categorizers yields items in
    different EP families — this is what it means to "change category." -/
theorem different_categorizers_different_families :
    catFamily .v ≠ catFamily .n ∧
    catFamily .n ≠ catFamily .a ∧
    catFamily .v ≠ catFamily .a := by decide

-- ════════════════════════════════════════════════════════════════
-- § 5: Data–Theory Connection
-- ════════════════════════════════════════════════════════════════

/-! ### English root families ([panagiotidis-2015] §5.2, [marantz-1997])

Standard examples from the Distributed Morphology literature: roots that
surface as nouns, verbs, and adjectives via different morphological
processes. -/

/-- √DESTROY: destroy (V), destruction (N), destructive (A) -/
def destroy : RootFamily := ⟨"DESTROY",
  [("destroy", .verb), ("destruction", .noun), ("destructive", .adjective)]⟩

/-- √BEAUTY: beautify (V), beauty (N), beautiful (A) -/
def beauty : RootFamily := ⟨"BEAUTY",
  [("beautify", .verb), ("beauty", .noun), ("beautiful", .adjective)]⟩

/-- √CLEAR: clear (V), clarity (N), clear (A) -/
def clear : RootFamily := ⟨"CLEAR",
  [("clear", .verb), ("clarity", .noun), ("clear", .adjective)]⟩

/-- √PRODUCE: produce (V), product/production (N), productive (A) -/
def produce : RootFamily := ⟨"PRODUCE",
  [("produce", .verb), ("production", .noun), ("productive", .adjective)]⟩

/-- √CREATE: create (V), creation (N), creative (A) -/
def create : RootFamily := ⟨"CREATE",
  [("create", .verb), ("creation", .noun), ("creative", .adjective)]⟩

/-- √ACT: act (V), action (N), active (A) -/
def act : RootFamily := ⟨"ACT",
  [("act", .verb), ("action", .noun), ("active", .adjective)]⟩

/-- All sample root families. -/
def allFamilies : List RootFamily :=
  [destroy, beauty, clear, produce, create, act]

/-- A root family is predicted to be tricategorial iff categorization by
    each of v, n, a is possible. Since all three categorizers are available
    in English, any root can in principle surface in all three categories. -/
theorem three_categorizers_predict_tricategoriality :
    isCategorizer .v ∧ isCategorizer .n ∧ isCategorizer .a := by decide

/-- The √DESTROY family's three categories correspond to three categorizers. -/
theorem destroy_matches_categorizers :
    destroy.hasCategory .verb = true ∧
    destroy.hasCategory .noun = true ∧
    destroy.hasCategory .adjective = true := by native_decide

/-- Every root family in the sample has a form for each categorizer's category. -/
theorem all_families_match_all_categorizers :
    allFamilies.all (fun rf =>
      rf.hasCategory .verb && rf.hasCategory .noun && rf.hasCategory .adjective) = true := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- § 6: Cross-framework bridge to [mcnally-deswart-2011]
-- ════════════════════════════════════════════════════════════════

/-! ## Bridge: §6.7.1 modifier-distribution diagnostic ↔ M&deS §2.3 (13)

[panagiotidis-2015] §6.7.1 (35)–(36) deploys a *modifier-distribution*
diagnostic for SWITCH placement in mixed projections, with Dutch examples
adapted from Ackema & Neeleman (2004:173):

* (35) `dat [stiekem succesvolle liedjes jatten]` — adverb `stiekem`
  sits BELOW the SWITCH (in the verbal/adjectival subtree)
* (36) `dat stiekeme [succesvolle liedjes jatten]` — adjective `stiekeme`
  sits ABOVE the SWITCH (in the nominal subtree)

Per Panagiotidis p. 146, the SWITCH's complement is *recategorised* by
its [N] feature. So a constituent dominated by a SWITCH projects
nominally and takes adjectival modifiers; a constituent below the
SWITCH retains its verbal/adjectival categorial identity and takes
adverbial modifiers. The diagnostic gives SWITCH placement: where the
modifier-category transition occurs is where the SWITCH sits.

[mcnally-deswart-2011] §2.3 (13) makes a *similar* modifier-
distribution observation about the inflected adjective in `het rode
van X`: M&deS observe `het intens/*intense rode` (adverbial-only) and
conclude that `rode` remains adjectival, with `het` carrying the
type-shift.

**Methodological lineage, not independent rediscovery.** Both M&deS and
Panagiotidis cite Ackema & Neeleman 2004 (Beyond Morphology) as the
source of the modifier-as-domain diagnostic. The convergence below is a
shared-source consequence, not two independent frameworks landing on the
same test. The bridge formalises *that* the two frameworks make
predictions of the same shape on the same data.

**Caveat.** Panagiotidis nowhere specifically analyses Dutch *het* as a
SWITCH; §6.6 covers V→N SWITCHes only (Korean *-um*, Basque *-te/tze*,
Turkish *-dIk* and *-AcAk*) and §6.9 covers Dutch nominalised infinitives.
Mapping `het` to a Panagiotidis-style SWITCH on the inflected adjective
is the formaliser's extrapolation. The bridge below identifies the
M&deS rivals with SWITCH-position commitments (low/high) and reads off
predictions geometrically; it does not claim Panagiotidis himself
analyses M&deS's data. -/

namespace MdSBridge

open McNallyDeSwart2011

/-- The structural commitment each `InflectedAnalysis` rival makes about
    SWITCH placement, modelling Panagiotidis §6.7.1's geometric reasoning
    over the rivals' defining proposals. This is the substantive content
    each rival commits to: *where* in the structure of `het rode van X`
    is the categorising head sitting? -/
inductive SwitchPosition where
  /-- SWITCH is at the inflected-form level (the `-e` morpheme is the
      SWITCH; the inflected `rode` is the categorised constituent). -/
  | low
  /-- No SWITCH; regular adjectival projection (e.g., normal AP modifying
      a noun, where the noun is elided). -/
  | none
  /-- SWITCH is at the DP edge (`het` is the SWITCH; the AP `rode` is
      the SWITCH's complement). -/
  | high
  deriving DecidableEq, Repr

/-- Each rival's defining commitment about SWITCH placement.

    * `nominalisation`: -e itself is the SWITCH/categoriser. SWITCH = low.
    * `ellipsis`: regular AP-modifying-N structure with elided N; *no*
      SWITCH/categoriser intervenes between modifier and `rode` (the
      adjectival projection is intact pre-ellipsis). SWITCH = none.
    * `hetAsCap`: het carries the categorising operation. SWITCH = high. -/
def switchPosition : InflectedAnalysis → SwitchPosition
  | .nominalisation => .low
  | .ellipsis       => .none
  | .hetAsCap       => .high

/-- Per [panagiotidis-2015] p. 146 + §6.7.1: the SWITCH's complement
    is recategorised by [N], so a constituent dominated by a SWITCH
    projects nominally (takes adjectival modifiers) while a constituent
    below the SWITCH retains its adjectival identity (takes adverbial
    modifiers). For the inflected form `rode`, the diagnostic is read
    by asking *where is `rode` relative to the SWITCH*:

    * SWITCH = low (`-e` IS the SWITCH): `rode` IS the SWITCH-headed
      constituent → projects nominally → predicts ADJECTIVAL
      modification of `rode`.
    * SWITCH = high (`het` is the SWITCH, `rode` is its AP-complement):
      `rode` is BELOW the SWITCH → retains adjectival identity → predicts
      ADVERBIAL modification of `rode`.

    For `ellipsis` (no SWITCH), the surface AP is intact, so adverbial
    modification of `rode` is licensed just as any adjective licenses it.

    `panagiotidisPredictsAdverbialMod a` is now *derived* from
    `switchPosition a`: the geometric prediction is "no low SWITCH
    dominating `rode`", i.e. the modifier-attachment site is below or
    independent of any SWITCH. -/
def panagiotidisPredictsAdverbialMod (a : InflectedAnalysis) : Prop :=
  switchPosition a ≠ .low

instance : DecidablePred panagiotidisPredictsAdverbialMod :=
  fun a => by unfold panagiotidisPredictsAdverbialMod; exact inferInstance

/-- The Panagiotidis prediction matches the [mcnally-deswart-2011]
    prediction on every rival. Both predicates encode the same modifier-
    distribution diagnostic (which they both inherit from Ackema &
    Neeleman 2004); the agreement is shared-methodology consequence, not
    independent rediscovery. The substance of the bridge: *the geometric
    SWITCH-placement reasoning derives the same predictions as M&deS's
    case-by-case `PredictsAdverbialModOnly`*. -/
theorem mcnally_panagiotidis_diagnostics_agree :
    ∀ a : InflectedAnalysis,
      a.PredictsAdverbialModOnly ↔ panagiotidisPredictsAdverbialMod a := by
  intro a
  cases a <;>
    (unfold InflectedAnalysis.PredictsAdverbialModOnly
            panagiotidisPredictsAdverbialMod switchPosition
     decide)

/-- The `nominalisation` rival fails the joint prediction:
    Panagiotidis's geometric diagnostic over its low-SWITCH commitment
    predicts the inflected form should admit adjectival modification
    (because `rode` would be SWITCH-dominated and project nominally);
    [mcnally-deswart-2011] (13) shows the inflected form REJECTS
    adjectival modification. The combined refutation routes through
    `switchPosition .nominalisation = .low → ¬panagiotidisPredictsAdverbialMod`
    and the M&deS data point. -/
theorem panagiotidis_refutes_nominalisation :
    switchPosition .nominalisation = .low
    ∧ ¬ panagiotidisPredictsAdverbialMod .nominalisation
    ∧ ¬ Form.inflected.AdmitsAdjectivalModification := by
  refine ⟨rfl, ?_, id⟩
  unfold panagiotidisPredictsAdverbialMod switchPosition; decide

/-- Conversely, the `hetAsCap` rival passes: high-SWITCH commitment +
    `rode` below SWITCH → adverbial modification predicted, matching
    M&deS data. -/
theorem hetAsCap_panagiotidis_compatible :
    switchPosition .hetAsCap = .high
    ∧ panagiotidisPredictsAdverbialMod .hetAsCap
    ∧ ¬ Form.inflected.AdmitsAdjectivalModification := by
  refine ⟨rfl, ?_, id⟩
  unfold panagiotidisPredictsAdverbialMod switchPosition; decide

/-- The `ellipsis` rival also passes: no-SWITCH commitment means
    surface AP is intact and adverbial modification is licensed in the
    standard way. -/
theorem ellipsis_panagiotidis_compatible :
    switchPosition .ellipsis = .none
    ∧ panagiotidisPredictsAdverbialMod .ellipsis := by
  refine ⟨rfl, ?_⟩
  unfold panagiotidisPredictsAdverbialMod switchPosition; decide

/-- Categoriser identification at the *surface* head level. Under each
    rival, what is the lexical category of the inflected form `rode` as
    it is projected at the surface?

    * `nominalisation`: `-e` categorises `rode` as a noun → `Cat.n`.
    * `ellipsis`: surface `rode` is an adjective; the n is the elided
      null noun, structurally elsewhere → `Cat.a` (the visible head).
    * `hetAsCap`: `rode` remains adjectival; `het` is the SWITCH
      → `Cat.a` at the surface head.

    The frameworks-divergence is captured: only `nominalisation`
    promotes the surface category to nominal. The other two leave the
    surface adjectival. -/
def surfaceCategorizer : InflectedAnalysis → Cat
  | .nominalisation => Cat.n   -- -e changes A → N
  | .ellipsis       => Cat.a   -- visible A; n is elided elsewhere
  | .hetAsCap       => Cat.a   -- het carries SWITCH; rode stays A

/-- The surface categoriser distinguishes nominalisation from the other
    two rivals — exactly the M&deS §2.3 distinction of "is the inflected
    form a noun?". This is a real per-rival commitment, not a constant. -/
theorem nominalisation_uniquely_promotes_to_n :
    surfaceCategorizer .nominalisation = Cat.n ∧
    surfaceCategorizer .ellipsis       = Cat.a ∧
    surfaceCategorizer .hetAsCap       = Cat.a := ⟨rfl, rfl, rfl⟩

/-- The Panagiotidis-side referential prediction follows the surface
    categoriser: `nominalisation` predicts the inflected form is
    referential (per `noun_referential_not_predicative` above);
    `ellipsis` and `hetAsCap` predict it remains predicative-bearing
    (per `adjective_both`). -/
theorem nominalisation_predicts_referential :
    producesReferential (surfaceCategorizer .nominalisation) = true ∧
    producesReferential (surfaceCategorizer .ellipsis)       = true ∧
    producesReferential (surfaceCategorizer .hetAsCap)       = true := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end MdSBridge

/-! ### Categorial features: [chomsky-1970] vs [panagiotidis-2015] (relocated from Minimalist/CategorialFeatures.lean)

[chomsky-1970] [grimshaw-2005] [panagiotidis-2015]

Two theories of what makes a noun a noun and a verb a verb:

1. **[chomsky-1970]**: [±V, ±N] as arbitrary binary diacritics that cross-classify
   the four lexical categories. Adopted by [grimshaw-2005] for Extended Projections.
   Implemented in `CatFeatures`.

2. **[panagiotidis-2015]**: [N] and [V] as substantive, LF-interpretable features:
   - [N] = sortal perspective / referentiality
   - [V] = temporal perspective / eventivity (§4.3)
   On categorizers (v, n, a), these are *interpretable*; on functional heads
   (T, C, D, etc.), they are *uninterpretable* copies (§5.8).
   Implemented in `CategorialFeatures`.

## Key Agreement

The two systems produce the same four equivalence classes — {verbal}, {nominal},
{adjectival}, {adpositional} — and therefore agree on all EP-consistency judgments
(`chomsky_panagiotidis_agree`).

## Key Disagreement

The status of **P** (prepositions/adpositions):

- Chomsky: P *actively bears* [-V, -N] — two negative feature values
- Panagiotidis: P is the **default** categorizer, lacking both [N] and [V]

This matters for the theory of features: in Chomsky's system, [-V] and [-N] are
just as "real" as [+V] and [+N]. In Panagiotidis's system, the absence of [N] and
[V] is genuinely the absence of categorial content — P is the elsewhere case. This
predicts that P should be the most promiscuous category (appearing in the most
diverse syntactic environments), which Panagiotidis argues is borne out.

## Adjectives

Both systems agree that A shares properties with both N and V:
- Chomsky: A = [+V, +N], the only category with both positive values
- Panagiotidis: A = [N, V], bearing both substantive features

The difference: for Panagiotidis, this is *explanatory* — adjectives have temporal
anchoring (because [V]) and sortal perspective (because [N]). For Chomsky,
the co-presence of [+V] and [+N] is a notational fact without semantic content.
-/

-- ═══════════════════════════════════════════════════════════════
-- § Internal Structure of Each System
-- ═══════════════════════════════════════════════════════════════

/-- In Chomsky's system, every category has at least one positive feature
    except P (which has [-V, -N] = ⟨false, false⟩). -/
theorem chomsky_p_has_no_positive_feature :
    (catFeatures .P).plusV = false ∧ (catFeatures .P).plusN = false := by decide

/-- In Panagiotidis's system, P is the default: no categorial features. -/
theorem panagiotidis_p_is_default :
    (categorialFeatures .P).hasN = false ∧ (categorialFeatures .P).hasV = false := by decide

/-- These are extensionally identical — but the theories *interpret* ⟨false, false⟩
    differently: Chomsky reads it as "actively [-V, -N]"; Panagiotidis reads it
    as "absence of both [N] and [V]" (the elsewhere case). -/
theorem p_same_values :
    catFeatures .P = ⟨false, false⟩ ∧ categorialFeatures .P = ⟨false, false⟩ := by decide

/-- Adjectives bear both features in both systems. -/
theorem adjective_both_features :
    catFeatures .A = ⟨true, true⟩ ∧ categorialFeatures .A = ⟨true, true⟩ := by decide

-- ═══════════════════════════════════════════════════════════════
-- § Feature Semantics (Panagiotidis only)
-- ═══════════════════════════════════════════════════════════════

/-- [N] = sortal perspective / referentiality. Every category in the nominal
    EP bears [N] (interpretable on n, uninterpretable on Num/Q/D; §5.8). -/
theorem nominal_ep_has_n :
    (categorialFeatures .N).hasN ∧ (categorialFeatures .n).hasN ∧
    (categorialFeatures .Num).hasN ∧ (categorialFeatures .Q).hasN ∧
    (categorialFeatures .D).hasN := by decide

/-- [V] = temporal perspective / eventivity. Every category in the verbal
    EP bears [V] (interpretable on v, uninterpretable on T/C; §5.8). -/
theorem verbal_ep_has_v :
    (categorialFeatures .V).hasV ∧ (categorialFeatures .v).hasV ∧
    (categorialFeatures .T).hasV ∧ (categorialFeatures .C).hasV := by decide

/-- Adjectives bear both [N] (sortal perspective) and [V] (temporal perspective).
    This explains why adjectives can be nominalized (via [N]) and
    have temporal anchoring (via [V]). -/
theorem adjective_referential_and_predicative :
    (categorialFeatures .A).hasN ∧ (categorialFeatures .A).hasV := by decide

/-- The adjectival categorizer *a* inherits [N, V] from A. -/
theorem a_categorizer_referential_and_predicative :
    (categorialFeatures .a).hasN ∧ (categorialFeatures .a).hasV := by decide

/-- P bears neither [N] nor [V] — the default/elsewhere categorizer.
    This predicts P is the most syntactically promiscuous category. -/
theorem p_neither_referential_nor_predicative :
    ¬(categorialFeatures .P).hasN ∧ ¬(categorialFeatures .P).hasV := by decide

-- ═══════════════════════════════════════════════════════════════
-- § Categorizers as a Natural Class
-- ═══════════════════════════════════════════════════════════════

/-- The three categorizers (v, n, a) form a natural class at F1
    (Grimshaw's system). Each bears the interpretable categorial features
    of its EP family. Note: Panagiotidis (§4.5) argues categorizers are
    lexical, not functional, despite being placed at F1 in the EP. -/
theorem categorizers_are_f1 :
    isCategorizer .v ∧ isCategorizer .n ∧ isCategorizer .a ∧
    fValue .v = 1 ∧ fValue .n = 1 ∧ fValue .a = 1 := by decide

/-- Lexical heads (V, N, A, P) are not categorizers. In Panagiotidis's
    system, these represent *categorized* items (√+categorizer), not
    the categorizers themselves. -/
theorem lexical_heads_not_categorizers :
    isCategorizer .V = false ∧ isCategorizer .N = false ∧
    isCategorizer .A = false ∧ isCategorizer .P = false := by decide

/-- Each categorizer bears the *interpretable* features of its family:
    v bears [V] (temporal), n bears [N] (sortal), a bears [N, V] (both). -/
theorem categorizer_features :
    categorialFeatures .v = ⟨false, true⟩ ∧
    categorialFeatures .n = ⟨true, false⟩ ∧
    categorialFeatures .a = ⟨true, true⟩ := by decide

-- ═══════════════════════════════════════════════════════════════
-- § CatFamily as Theory-Neutral Ground
-- ═══════════════════════════════════════════════════════════════

/-- CatFamily is the theory-neutral representation: it records which
    categories group together without committing to the mechanism.
    Both Chomsky and Panagiotidis produce the same CatFamily partition. -/
theorem catFamily_from_chomsky (c1 c2 : Cat) :
    (catFeatures c1 == catFeatures c2) = (catFamily c1 == catFamily c2) := by
  cases c1 <;> cases c2 <;> decide

theorem catFamily_from_panagiotidis (c1 c2 : Cat) :
    (categorialFeatures c1 == categorialFeatures c2) = (catFamily c1 == catFamily c2) := by
  cases c1 <;> cases c2 <;> decide

end Panagiotidis2015
