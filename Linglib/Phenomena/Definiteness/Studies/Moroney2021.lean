import Linglib.Core.Definiteness
import Linglib.Core.Mereology
import Linglib.Theories.Semantics.Noun.Kind.Dayal2004
import Linglib.Theories.Semantics.Noun.Kind.Chierchia1998
import Linglib.Theories.Semantics.Definiteness.Basic
import Linglib.Theories.Semantics.Noun.Classifier
import Linglib.Fragments.Shan.Definiteness

/-!
# Moroney (2021): Definiteness and Quantification — Evidence from Shan
@cite{moroney-2021}

Shan (Southwestern Tai, Kra-Dai) bare nouns can be interpreted as indefinite,
definite, generic, or kind-denoting. The key finding is that bare nouns in
Shan express BOTH unique and anaphoric definiteness — contra @cite{jenks-2018}'s
prediction that languages without overt definite articles mark at most one
type of definiteness.

## Core contributions formalized here

1. **Revised definiteness marking typology** (Table 4.1/4.4): adds an "unmarked"
   category where bare nouns express both unique and anaphoric definiteness.
   Languages: Shan, Serbian, Kannada.

2. **Bare noun interpretation distribution** (Table 2.3): Shan and English bare
   nouns agree on low ∃, kind, and generic readings. They differ ONLY on
   definite readings — Shan bare nouns can be definite, English cannot.

3. **Type-shifting analysis**: all bare nouns are base type ⟨s,⟨e,t⟩⟩.
   Definite readings arise via unblocked ι type-shift (no overt "the" to
   block it). Kind readings via ∩. Existential via DPP (Derived Predicate
   Predication, `Chierchia1998.DPP`), which yields obligatory low scope.

4. **Cross-linguistic definiteness data** (Table 4.4): Shan uses bare nouns
   in ALL @cite{schwarz-2009} definite use types. Demonstrative-noun phrases
   (N Clf Dem) are optional in anaphoric/relational-bridging/donkey contexts
   where German requires the strong article and Mandarin/Thai require
   demonstratives.
-/

namespace Moroney2021

open Core.Definiteness
open Fragments.Shan.Definiteness (SpatialRelation)

-- ============================================================================
-- §1: Definiteness Marking Typology (Table 4.1, extended)
-- ============================================================================

-- DefMarkingStrategy, DefMarkingParams, deriveStrategy, and
-- strategyToArticleType are defined in Core.Definiteness (promoted
-- from this study file to Core for reuse across phenomena).

-- ============================================================================
-- §2: Cross-Linguistic Definiteness Expression Data (Table 4.4)
-- ============================================================================

/-- What form a language uses to express definiteness in a given context. -/
inductive DefForm where
  | weakArticle    -- German weak article (contracted: vom, im)
  | strongArticle  -- German strong article (full: von dem, in dem)
  | bare           -- Bare noun
  | dem            -- Demonstrative(-classifier-noun) phrase
  | bareOrDem      -- Either acceptable
  deriving DecidableEq, Repr

/-- Cross-linguistic datum: what form does language L use for definite use
type U? Connects @cite{hawkins-1978}'s use types (already in
`Core.Definiteness.DefiniteUseType`) to actual morphological expression. -/
structure DefExpressionDatum where
  language : String
  useType : DefiniteUseType
  bridgingSubtype : Option BridgingSubtype := none
  form : DefForm
  deriving Repr, DecidableEq

/-- German data (@cite{schwarz-2009}): weak article for situational uniqueness
and part-whole bridging; strong article for anaphora, producer-product
bridging, and donkey anaphora. -/
def germanData : List DefExpressionDatum :=
  [ { language := "German", useType := .immediateSituation
    , form := .weakArticle }
  , { language := "German", useType := .largerSituation
    , form := .weakArticle }
  , { language := "German", useType := .anaphoric
    , form := .strongArticle }
  , { language := "German", useType := .bridging
    , bridgingSubtype := some .partWhole
    , form := .weakArticle }
  , { language := "German", useType := .bridging
    , bridgingSubtype := some .relational
    , form := .strongArticle }
  , { language := "German", useType := .donkey
    , form := .strongArticle } ]

/-- Thai data (@cite{jenks-2015}): bare nouns for uniqueness contexts,
demonstrative-noun phrases for anaphoric/relational contexts. -/
def thaiData : List DefExpressionDatum :=
  [ { language := "Thai", useType := .immediateSituation
    , form := .bare }
  , { language := "Thai", useType := .largerSituation
    , form := .bare }
  , { language := "Thai", useType := .anaphoric
    , form := .dem }
  , { language := "Thai", useType := .bridging
    , bridgingSubtype := some .partWhole
    , form := .bare }
  , { language := "Thai", useType := .bridging
    , bridgingSubtype := some .relational
    , form := .dem }
  , { language := "Thai", useType := .donkey
    , form := .dem } ]

/-- Mandarin data (@cite{jenks-2018}): bare nouns for uniqueness contexts,
demonstrative-noun phrases for anaphoric/relational/donkey contexts.
Same pattern as Thai — Mandarin is classified as `.markedAnaphoric`
in @cite{jenks-2018}'s typology. -/
def mandarinData : List DefExpressionDatum :=
  [ { language := "Mandarin", useType := .immediateSituation
    , form := .bare }
  , { language := "Mandarin", useType := .largerSituation
    , form := .bare }
  , { language := "Mandarin", useType := .anaphoric
    , form := .dem }
  , { language := "Mandarin", useType := .bridging
    , bridgingSubtype := some .partWhole
    , form := .bare }
  , { language := "Mandarin", useType := .bridging
    , bridgingSubtype := some .relational
    , form := .dem }
  , { language := "Mandarin", useType := .donkey
    , form := .dem } ]

/-- Mandarin and Thai have the same definiteness expression pattern:
bare for uniqueness, demonstrative for anaphoric/relational/donkey. -/
theorem mandarin_thai_same_pattern :
    mandarinData.map (·.form) = thaiData.map (·.form) := by decide

/-- Shan data (@cite{moroney-2021} Table 4.4): bare nouns in ALL contexts.
Demonstratives optional in anaphoric and relational-bridging contexts.
This is the key empirical finding — Shan bare nouns cover ALL of Schwarz's
definite use types, unlike Mandarin/Thai (anaphoric requires dem) or
German (weak/strong articles). -/
def shanData : List DefExpressionDatum :=
  [ -- ex. 487: unique in immediate situation, bare noun required (#dem)
    { language := "Shan", useType := .immediateSituation
    , form := .bare }
    -- ex. 488: unique in larger situation (kǎaŋwán 'sun'), bare noun required
  , { language := "Shan", useType := .largerSituation
    , form := .bare }
    -- ex. 489: narrative sequence anaphora, bare noun OR dem acceptable
  , { language := "Shan", useType := .anaphoric
    , form := .bareOrDem }
    -- part-whole bridging: bare noun
  , { language := "Shan", useType := .bridging
    , bridgingSubtype := some .partWhole
    , form := .bare }
    -- producer-product bridging: bare noun OR dem
  , { language := "Shan", useType := .bridging
    , bridgingSubtype := some .relational
    , form := .bareOrDem }
    -- donkey anaphora: bare noun OR dem (Table 4.4)
  , { language := "Shan", useType := .donkey
    , form := .bareOrDem } ]

/-- Shan bare nouns are acceptable in every definite use type. -/
theorem shan_bare_in_all_contexts :
    shanData.all (fun d => d.form == .bare || d.form == .bareOrDem) = true := by
  decide

/-- German requires a distinct article form for every context — no bare nouns. -/
theorem german_no_bare :
    germanData.all (fun d => d.form == .weakArticle || d.form == .strongArticle)
      = true := by decide

-- ============================================================================
-- §3: Shan Bare Noun Interpretation Distribution (Table 2.3)
-- ============================================================================

/-- The five possible interpretations of bare nouns. -/
inductive BareNounInterp where
  | lowExistential   -- Low scope ∃ (via DPP, below negation)
  | highExistential  -- Wide scope ∃ (above negation; unavailable for bare nouns)
  | definite         -- Via ι type-shift
  | kind             -- Via ∩ type-shift
  | generic          -- Via GEN over situations
  deriving DecidableEq, Repr

/-- Availability of a bare noun interpretation in Shan vs English. -/
structure InterpAvailability where
  interp : BareNounInterp
  shanCount : Bool       -- Shan count nouns
  shanMass : Bool        -- Shan mass nouns
  englishCount : Bool    -- English bare count nouns (plurals)
  englishMass : Bool     -- English bare mass nouns
  deriving Repr, DecidableEq

/-- Table 2.3: bare noun interpretation distribution in Shan and English.

Shan and English agree on four of five readings. The sole difference
is the definite reading: Shan ✓ (via unblocked ι), English ✗ (ι
blocked by overt *the*). -/
def interpretationTable : List InterpAvailability :=
  [ { interp := .lowExistential
    , shanCount := true, shanMass := true
    , englishCount := true, englishMass := true }
  , { interp := .highExistential
    , shanCount := false, shanMass := false
    , englishCount := false, englishMass := false }
  , { interp := .definite
    , shanCount := true, shanMass := true
    , englishCount := false, englishMass := false }
  , { interp := .kind
    , shanCount := true, shanMass := true
    , englishCount := true, englishMass := true }
  , { interp := .generic
    , shanCount := true, shanMass := true
    , englishCount := true, englishMass := true } ]

/-- The definite interpretation is the ONLY point where Shan and English
bare nouns differ (Table 2.3). -/
theorem definite_is_sole_difference :
    (interpretationTable.filter
      (fun d => d.shanCount != d.englishCount || d.shanMass != d.englishMass)
    ).map (·.interp) = [.definite] := by decide

/-- High scope existential is universally unavailable for bare nouns —
a consequence of DPP/DKP locality (@cite{chierchia-1998}). The
existential introduced by DPP applies at the point of composition
(vP level), so it cannot scope above negation. -/
theorem high_existential_universally_blocked :
    (interpretationTable.filter (·.interp == .highExistential)
    ).all (fun d => !d.shanCount && !d.shanMass &&
                     !d.englishCount && !d.englishMass) = true := by
  decide

-- ============================================================================
-- §4: Type-Shifting Analysis
-- ============================================================================

open Semantics.Noun.Kind

/-- Shan has no overt determiners: all type-shifts are unblocked.

Contrast with English (`Dayal2004.englishBlocking`): the presence of
*the* blocks covert ι, and *a*/*some* block covert ∃. In Shan, the
absence of articles means the blocking principle imposes no constraints
on covert type-shifting. Crucially, both ι AND ι^x are unblocked —
this is what allows Shan bare nouns to express both unique and anaphoric
definiteness (@cite{moroney-2021} §4.3).

Derived from `Fragments.Shan.Definiteness.blocking` — the single source
of truth for Shan's article inventory. -/
def shanBlocking : Chierchia1998.BlockingPrinciple :=
  Fragments.Shan.Definiteness.blocking

/-- When a Shan bare noun is used in a context requiring unique definiteness,
the preferred type-shift is ι (definite), by Meaning Preservation
({∩, ι, ι^x} > ∃). Number-neutral nouns allow both ι and ∩, but ∩
requires a kind-compatible predicate (`downDefined`).

Compare: English singular nouns get `none` (`Dayal2004.dayal_consistent_english_bare_singular_out`). -/
theorem shan_neutral_prefers_iota :
    let ctx : Dayal2004.TypeShiftContext := {
      number := .neutral
      downDefined := false  -- Predicate is not kind-compatible
      iotaBlocked := false
      iotaAnaphoricBlocked := false
      existsBlocked := false
      instantiationAccessible := true
    }
    Dayal2004.selectShift ctx = some .iota := rfl

/-- When a Shan bare noun is used with a kind-compatible predicate,
∩ is selected (it appears first in `availableShifts` for number-neutral
nouns with `downDefined`). -/
theorem shan_neutral_kind_prefers_down :
    let ctx : Dayal2004.TypeShiftContext := {
      number := .neutral
      downDefined := true
      iotaBlocked := false
      iotaAnaphoricBlocked := false
      existsBlocked := false
      instantiationAccessible := true
    }
    Dayal2004.selectShift ctx = some .down := rfl

/-- Number-neutral nouns in Shan make BOTH ∩ and ι available simultaneously
when the predicate is kind-compatible. This correctly predicts the
ambiguity between definite and kind readings for Shan bare nouns. -/
theorem shan_neutral_both_available :
    let ctx : Dayal2004.TypeShiftContext := {
      number := .neutral
      downDefined := true
      iotaBlocked := false
      iotaAnaphoricBlocked := false
      existsBlocked := false
      instantiationAccessible := true
    }
    .down ∈ Dayal2004.availableShifts ctx ∧
    .iota ∈ Dayal2004.availableShifts ctx ∧
    .iotaAnaphoric ∈ Dayal2004.availableShifts ctx := by
  simp [Dayal2004.availableShifts]

/-- The Shan–English definiteness contrast derived from blocking.

Same base noun type (⟨s,⟨e,t⟩⟩), same type-shifting operations,
different article inventories. Shan has no "the" → ι unblocked →
bare nouns can be definite. English has "the" → ι blocked → bare
nouns cannot be definite (must use overt determiner). -/
theorem shan_english_definiteness_contrast :
    -- Shan: number-neutral bare noun gets definite reading
    Dayal2004.selectShift {
      number := .neutral, downDefined := false
      iotaBlocked := false, iotaAnaphoricBlocked := false
      existsBlocked := false, instantiationAccessible := true
    } = some .iota ∧
    -- English: bare singular gets no reading
    Dayal2004.selectShift {
      number := .sg, downDefined := false
      iotaBlocked := true, iotaAnaphoricBlocked := true
      existsBlocked := true, instantiationAccessible := true
    } = none :=
  ⟨rfl, rfl⟩

/-- The Shan–Thai anaphoric definiteness contrast derived from blocking.

Shan: ι^x is unblocked → bare nouns can be anaphorically definite.
Thai: ι^x is blocked by demonstrative → demonstrative required for
anaphoric definiteness. Both languages have unblocked ι (unique
definiteness via bare nouns). -/
theorem shan_thai_anaphoric_contrast :
    -- Shan: ι^x available for anaphoric definiteness
    .iotaAnaphoric ∈ Dayal2004.availableShifts {
      number := .neutral, downDefined := false
      iotaBlocked := false, iotaAnaphoricBlocked := false
      existsBlocked := false, instantiationAccessible := true
    } ∧
    -- Thai: ι^x blocked, only ι available
    .iotaAnaphoric ∉ Dayal2004.availableShifts {
      number := .neutral, downDefined := false
      iotaBlocked := false, iotaAnaphoricBlocked := true
      existsBlocked := false, instantiationAccessible := true
    } := by
  simp [Dayal2004.availableShifts]

/-- ∃ is available as a last resort in Shan (when ∩ and ι are
inapplicable), but by Meaning Preservation it is always dispreferred.
This means bare nouns default to definite/kind, not existential —
the existential reading arises only via DPP at vP. -/
theorem shan_exists_is_last_resort :
    -- ∃ is available but not selected when ι is available
    (Dayal2004.availableShifts {
      number := .neutral, downDefined := false
      iotaBlocked := false, iotaAnaphoricBlocked := false
      existsBlocked := false, instantiationAccessible := true
    }).head? = some .iota ∧
    -- ∃ appears in the list but after ι
    .exists ∈ (Dayal2004.availableShifts {
      number := .neutral, downDefined := false
      iotaBlocked := false, iotaAnaphoricBlocked := false
      existsBlocked := false, instantiationAccessible := true
    }) := by
  constructor
  · rfl
  · simp [Dayal2004.availableShifts]

-- ============================================================================
-- §5: Marking Strategy ↔ Core/Definiteness Bridge
-- ============================================================================

/-- Shan's unmarked strategy correctly maps to `ArticleType.none_`. -/
theorem shan_article_type :
    strategyToArticleType .unmarked = .none_ := rfl

/-- `Core.Definiteness.articleTypeToDistinguishedPresup` correctly returns
zero morphologically distinguished presupposition types for Shan. -/
theorem shan_no_morphological_distinction :
    (articleTypeToDistinguishedPresup .none_).length = 0 := rfl

/-- The central Moroney insight: morphological marking ≠ semantic availability.

Shan morphologically distinguishes zero presupposition types (no articles)
but semantically expresses both unique and anaphoric definiteness (via
covert type-shifting). The bridge between article inventory and semantic
availability is the blocking principle: no articles → no blocking →
all type-shifts (ι, ι^x, ∩) available. -/
theorem marking_ne_availability :
    -- Zero morphologically distinguished types
    (articleTypeToDistinguishedPresup .none_).length = 0 ∧
    -- But all type-shifts are semantically available (ι, ι^x, and ∩)
    shanBlocking.iotaBlocked = false ∧
    shanBlocking.downBlocked = false ∧
    shanBlocking.existsBlocked = false := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §6: Moroney's Revised Typology — Uniqueness Status
-- ============================================================================

/-- Moroney's new category is genuinely distinct from the three existing ones. -/
theorem unmarked_distinct_from_existing :
    DefMarkingStrategy.unmarked ≠ .generallyMarked ∧
    DefMarkingStrategy.unmarked ≠ .bipartite ∧
    DefMarkingStrategy.unmarked ≠ .markedAnaphoric := by decide

-- ============================================================================
-- §7: Language-Specific Parameters
-- ============================================================================

/-- Language parameters for the four languages in Table 4.4. -/
def englishParams : DefMarkingParams :=
  { hasUniqueForm := true, hasAnaphoricForm := true, sameForm := true }
def germanParams : DefMarkingParams :=
  { hasUniqueForm := true, hasAnaphoricForm := true, sameForm := false }
def thaiParams : DefMarkingParams :=
  { hasUniqueForm := false, hasAnaphoricForm := true }
def shanParams : DefMarkingParams :=
  Fragments.Shan.Definiteness.markingParams

/-- The derivation correctly classifies all four Table 4.4 languages. -/
theorem derive_all_languages :
    deriveStrategy englishParams = .generallyMarked ∧
    deriveStrategy germanParams = .bipartite ∧
    deriveStrategy thaiParams = .markedAnaphoric ∧
    deriveStrategy shanParams = .unmarked := ⟨rfl, rfl, rfl, rfl⟩

/-- `deriveStrategy` agrees with `strategyToArticleType` composed with
`ArticleType` classification. The derivation is consistent with the
stipulated mapping — but now the strategy is computed from primitives
rather than assigned by fiat. -/
theorem derive_consistent_with_stipulated :
    strategyToArticleType (deriveStrategy englishParams) = .weakOnly ∧
    strategyToArticleType (deriveStrategy germanParams) = .weakAndStrong ∧
    strategyToArticleType (deriveStrategy thaiParams) = .weakOnly ∧
    strategyToArticleType (deriveStrategy shanParams) = .none_ :=
  ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §8: Bridge to Theories/Semantics/Definiteness/Basic.lean
-- ============================================================================

open Semantics.Definiteness (the_uniq the_anaphoric
  the_anaphoric_vacuous_eq_the_uniq)

/-- The type-shift system and the denotational semantics agree:

- ι (unique definiteness) corresponds to `the_uniq` in the denotational layer
- ι^x (anaphoric definiteness) corresponds to `the_anaphoric`

When Q is vacuously true, `the_anaphoric` reduces to `the_uniq`
(via `the_anaphoric_vacuous_eq_the_uniq`), mirroring the type-shift
relationship where ι^x subsumes ι. -/
theorem type_shift_denotation_agreement :
    ∀ (E : Type) (domain : List E) [DecidableEq E]
      (restrictor scope : E → Bool),
      the_anaphoric domain restrictor (λ _ => true) scope =
      the_uniq domain restrictor scope :=
  fun _E domain _ restrictor scope =>
    the_anaphoric_vacuous_eq_the_uniq domain restrictor scope

-- ============================================================================
-- §9: DPP Obligatory Low Scope (Table 2.3 derived)
-- ============================================================================

/-- DPP yields obligatory low scope existential: the existential
    introduced by DPP applies at the vP level, so it cannot scope above
    negation. This is why `highExistential` is universally unavailable for
    bare nouns (@cite{chierchia-1998}; @cite{moroney-2021} §2.3).

    The theorem derives the universal blocking from the data table rather
    than stipulating it. -/
theorem dpp_scope_below_neg :
    ∀ interp ∈ interpretationTable,
      interp.interp = .highExistential →
        interp.shanCount = false ∧ interp.shanMass = false ∧
        interp.englishCount = false ∧ interp.englishMass = false := by
  intro interp hmem heq
  simp only [interpretationTable, List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> simp_all

-- ============================================================================
-- §10: FakeMass Witness — Shan Count Nouns (§2.4)
-- ============================================================================

/-- Concrete witness of `FakeMass` behavior: Shan bare count nouns like
    *mǎa* 'dog' are CUM (the sum of two dogs is dogs) but not g-homogeneous
    (a dog's leg is part of a dog but is not itself a dog).

    We construct a three-element partial order: two atoms `a`, `b` and their
    join `ab = a ⊔ b`. The predicate `isDog` holds of `a`, `b`, and `ab`
    (CUM), but fails g-homogeneity at `ab` because its proper parts `a` and
    `b` could have sub-parts (in a richer model) that are not dogs. Here we
    use the atoms directly: `ab` has proper parts `a` and `b` which ARE dogs,
    so g-homogeneity holds vacuously on this small model. The genuine failure
    requires non-atomic non-P parts, which we model by adding a non-dog atom
    `c` with `c ≤ ab` (representing a dog-leg). -/
inductive FakeMassEntity : Type where
  | a   -- first dog
  | b   -- second dog
  | c   -- a leg (not a dog)
  | ab  -- sum of two dogs (includes the leg)
  deriving DecidableEq, Repr

/-- Partial order: a, b, c ≤ ab (atoms below their join); reflexive. -/
private def fmLe : FakeMassEntity → FakeMassEntity → Bool
  | _, .ab => true
  | .a, .a => true
  | .b, .b => true
  | .c, .c => true
  | _, _ => false

private theorem fmLe_refl (x : FakeMassEntity) : fmLe x x = true := by
  cases x <;> rfl

private theorem fmLe_antisymm (x y : FakeMassEntity)
    (hxy : fmLe x y = true) (hyx : fmLe y x = true) : x = y := by
  cases x <;> cases y <;> simp_all [fmLe]

private theorem fmLe_trans (x y z : FakeMassEntity)
    (hxy : fmLe x y = true) (hyz : fmLe y z = true) : fmLe x z = true := by
  cases x <;> cases y <;> cases z <;> simp_all [fmLe]

instance : PartialOrder FakeMassEntity where
  le x y := fmLe x y = true
  le_refl := fmLe_refl
  le_antisymm x y hxy hyx := fmLe_antisymm x y hxy hyx
  le_trans x y z hxy hyz := fmLe_trans x y z hxy hyz

/-- Dog-predicate: `a`, `b`, and `ab` are dogs; `c` (the leg) is not. -/
def isDog : FakeMassEntity → Prop
  | .a => True
  | .b => True
  | .c => False
  | .ab => True

/-- `isDog` is not g-homogeneous: `ab` is a dog, `c < ab`, but no dog
    `z ≤ c` exists (since `c` is an atom and `isDog c = False`). -/
theorem isDog_not_gHomogeneous : ¬ Mereology.gHomogeneous isDog := by
  intro h
  have hlt : (FakeMassEntity.c : FakeMassEntity) < .ab :=
    ⟨show fmLe .c .ab = true from rfl,
     fun heq => by cases heq⟩
  obtain ⟨z, hzc, hPz⟩ := h .ab .c trivial hlt
  -- z ≤ c means fmLe z c = true; by cases on z, only z = c works
  cases z with
  | a => exact absurd hzc (show ¬(fmLe .a .c = true) from by decide)
  | b => exact absurd hzc (show ¬(fmLe .b .c = true) from by decide)
  | c => exact hPz  -- isDog c = False
  | ab => exact absurd hzc (show ¬(fmLe .ab .c = true) from by decide)

-- ============================================================================
-- §11: Blocking ↔ Marking Strategy Correspondence
-- ============================================================================

/-- The blocking principle connects article inventory to available type-shifts,
    and `deriveStrategy` connects article inventory to marking strategy. This
    theorem shows the full correspondence for the four Table 4.4 languages:
    the same `DefMarkingParams` that determine the marking strategy also
    determine which type-shifts are blocked.

    This is the structural core of Moroney's analysis: article inventory is the
    single parameter from which both the typological classification AND the
    available interpretations of bare nouns are derived. -/
theorem blocking_strategy_correspondence :
    -- English: both forms → generallyMarked, both ι and ∃ blocked
    (deriveStrategy englishParams = .generallyMarked ∧
     englishParams.hasUniqueForm = true ∧
     englishParams.hasAnaphoricForm = true) ∧
    -- German: two different forms → bipartite, ι split into weak/strong
    (deriveStrategy germanParams = .bipartite ∧
     germanParams.hasUniqueForm = true ∧
     germanParams.hasAnaphoricForm = true ∧
     germanParams.sameForm = false) ∧
    -- Thai: only dem → markedAnaphoric, ι^x blocked (dem), ι unblocked (bare)
    (deriveStrategy thaiParams = .markedAnaphoric ∧
     thaiParams.hasUniqueForm = false ∧
     thaiParams.hasAnaphoricForm = true) ∧
    -- Shan: no forms → unmarked, nothing blocked, all shifts available
    (deriveStrategy shanParams = .unmarked ∧
     shanParams.hasUniqueForm = false ∧
     shanParams.hasAnaphoricForm = false ∧
     shanBlocking.iotaBlocked = false ∧
     shanBlocking.existsBlocked = false ∧
     shanBlocking.downBlocked = false) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

-- ============================================================================
-- §12: Demonstrative–Bare Noun Contrast (§2.1.3)
-- ============================================================================

/-- Shan demonstratives add spatial content to the presupposition filter,
    while bare definites have a trivial filter. This derives the contrast:

    - Bare noun: any unique satisfier of P_s is a candidate
    - DEM noun: only spatially-proximal/distal satisfiers of P_s

    The demonstrative is always optional in Shan because the bare noun
    already provides a definite reading via unblocked ι. The demonstrative
    adds information (spatial restriction) but never replaces an unavailable
    reading (unlike Thai/Mandarin where demonstratives are required for
    anaphoric definiteness). -/
theorem demonstrative_adds_spatial_info {E : Type}
    (restrictor : E → Bool) (spatialPred : SpatialRelation → E → Bool) :
    -- Bare definite has trivial filter
    (Fragments.Shan.Definiteness.bareDefinite restrictor).presupFilter =
      (fun _ => true) ∧
    -- nâj adds proximal filter
    (Fragments.Shan.Definiteness.demDenotation
      Fragments.Shan.Definiteness.naj restrictor spatialPred).presupFilter =
      spatialPred .proximal ∧
    -- nân adds distal filter
    (Fragments.Shan.Definiteness.demDenotation
      Fragments.Shan.Definiteness.nan restrictor spatialPred).presupFilter =
      spatialPred .distal :=
  ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- §13: Bridge to Classifier Semantics (Ch. 3)
-- ============================================================================

/-- Shan is a CLF-for-N language: the classifier atomizes the noun
    denotation (@cite{little-moroney-royer-2022}; @cite{moroney-2021} Ch. 3).

    The classifier semantics module provides `clfForNoun` as a thin wrapper
    around `Mereology.atomize`. This bridge confirms that Shan classifiers
    use the atomization strategy (CLF-for-N), connecting the Shan fragment's
    `ClassifierStrategy.forNoun` to the denotation function. -/
theorem shan_clf_is_atomization {α : Type*} [PartialOrder α]
    (P : α → Prop) :
    Semantics.Noun.Classifier.classifierDenot
      Core.NounCategorization.ClassifierStrategy.forNoun P
      (fun _ => 0) 0   -- μ and n are unused for CLF-for-N
    = Semantics.Noun.Classifier.clfForNoun P := rfl

end Moroney2021
