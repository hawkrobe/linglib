import Linglib.Features.Definiteness
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Semantics.Definiteness.Description
import Linglib.Semantics.Definiteness.Interpret
import Linglib.Fragments.German.Definiteness
import Linglib.Fragments.English.Definiteness
import Linglib.Fragments.Thai.Definiteness
import Linglib.Fragments.Mandarin.Definiteness
import Linglib.Fragments.Shan.Definiteness

/-!
# Schwarz (2009): Two Types of Definites in Natural Language
[schwarz-2009] [schwarz-2013] [hawkins-1978]
[coppock-beaver-2015] [patel-grosz-grosz-2017]

The central thesis of [schwarz-2009] is that the surface category
"definite article" decomposes into **two structurally distinct articles**
with different presupposition profiles:

- **weak article** — uniqueness presupposition (Russell/Frege/Strawson; the
  Coppock–Beaver `Uniqueness` projector)
- **strong article** — familiarity presupposition (Heim/Kamp; an antecedent
  in prior discourse)

Crucially, this is not a stipulation about meaning: it is read off the
morphology in languages whose article paradigm overtly distinguishes the
two — most prominently German (weak *im*, *vom*, *zum* vs strong *in dem*,
*von dem*, *zu dem*), but also Fering, Lakhota, Akan, Hausa, and others
([schwarz-2013]). English collapses both into syncretic *the*, masking
the distinction at the surface.

## What this file tests

The split is operationalized in the Core layer by:

- **`Semantics.Definiteness.Description`** — distinct `.unique` (weak) and
  `.anaphoric` (strong) constructors, with different argument shapes
  (`.unique` carries a *situation* index for resource-situation binding;
  `.anaphoric` carries a *discourse* index for antecedent lookup).
- **`Semantics.Definiteness.Description.expectedPresupType`** — projects each kind
  to the [schwarz-2009] presupposition type it expresses.
- **`Semantics.Definiteness.Determiner`** — the declared determiner set records the
  morphological inventory; `Determiner.IsSyncretic` is the predicate that
  distinguishes English-style syncretism from German-style bipartition.

We verify:

1. **Two distinct presupposition types** — `.uniqueness` and `.familiarity`
   are not collapsible in `DefPresupType`.
2. **Constructor split** — `.unique` and `.anaphoric` project to different
   presupposition types (uniqueness vs familiarity).
3. **Different argument shapes** — `.unique` consults the situation
   assignment via `interpSitPronoun`; `.anaphoric` consults the entity
   assignment via the discourse index. The interpreter realizes this
   difference structurally.
4. **Morphological correlate** — German (`bipartite`) marks the two types
   with distinct articles; English (`generallyMarked`) syncretizes them.
   The inventory bool `uniqueAnaphoricSyncretism` is the discriminator.
5. **Donkey anaphora patterns with strong** — `.donkey` use type maps to
   `.familiarity`, predicting that languages with the contrast use the
   strong article for donkey pronouns (German *von dem*, not *vom*).
6. **Bridging split** — part-whole bridging maps to uniqueness (weak
   article), relational/producer bridging to familiarity (strong article).
   This is [schwarz-2013] §3.2 generalized via `bridgingPresupType`.
-/

namespace Schwarz2009

open Features.Definiteness
open Intensional
open Intensional.Variables
open Semantics.Definiteness

-- ════════════════════════════════════════════════════════════════
-- §1: The two presupposition types are genuinely distinct
-- ════════════════════════════════════════════════════════════════

/-- The two Schwarz presupposition types are distinct constructors of
    `DefPresupType`. The whole architectural claim of [schwarz-2009]
    rests on this: if the types were the same, there would be no contrast
    to expose morphologically. -/
theorem two_presup_types_distinct :
    DefPresupType.uniqueness ≠ DefPresupType.familiarity := by decide

/-- `DefPresupType` has *exactly* the two Schwarz types — no third
    article-presupposition type. (The donkey/bridging cells in
    `DefiniteUseType` collapse into these two via `useTypeToPresupType` /
    `bridgingPresupType`.) -/
theorem presup_types_exhaustive :
    ∀ p : DefPresupType, p = .uniqueness ∨ p = .familiarity := by
  intro p; cases p <;> simp

-- ════════════════════════════════════════════════════════════════
-- §2: Constructor-level split — `.unique` ≠ `.anaphoric` semantically
-- ════════════════════════════════════════════════════════════════

variable {E W : Type}

/-- The weak article (`.unique` in the Core sum type) projects to the
    uniqueness presupposition. -/
theorem unique_is_uniqueness (R : DenotGS E W .et) (sIdx : Nat) :
    (Description.unique R sIdx).expectedPresupType = some .uniqueness := rfl

/-- The strong article (`.anaphoric` in the Core sum type) projects to the
    familiarity presupposition. -/
theorem anaphoric_is_familiarity (R : DenotGS E W .et) (d : Nat) :
    (Description.anaphoric R d).expectedPresupType = some .familiarity := rfl

/-- The two articles project to distinct presupposition types — the
    central [schwarz-2009] contrast at the type level. -/
theorem unique_anaphoric_presup_distinct
    (R : DenotGS E W .et) (sIdx d : Nat) :
    (Description.unique R sIdx).expectedPresupType ≠
      (Description.anaphoric R d).expectedPresupType := by
  rw [unique_is_uniqueness, anaphoric_is_familiarity]
  intro h
  exact two_presup_types_distinct (Option.some_inj.mp h)

-- ════════════════════════════════════════════════════════════════
-- §3: Different argument shapes — situation vs discourse binding
-- ════════════════════════════════════════════════════════════════

/-! The two articles do not just project different presupposition types —
they consult different *parts* of the bi-assignment. The weak article
binds a structural **situation pronoun** (its restrictor is evaluated at
`interpSitPronoun sIdx gs`); the strong article looks up a **discourse
referent** in the entity assignment (`g d`). -/

/-- The weak article's restrictor sees the entire situation assignment
    `gs` (the `unique` constructor passes `gs` to `R`). The situation
    index `sIdx` is structurally recorded but does not affect the
    interpretation directly — the restrictor itself is what calls
    `interpSitPronoun sIdx` to fetch the resource situation. -/
theorem weak_article_consults_situation_assignment
    (R : DenotGS E W .et) (sIdx : Nat)
    (g : Core.Assignment E) (gs : SitAssignment W) :
    interpret (.unique R sIdx) g gs =
      russellIota (fun x => R g gs x) := rfl

/-- The strong article's referent is the entity at the discourse index
    `g d`, accepted iff the restrictor holds of it. The situation
    assignment is consulted only through the restrictor `R` — the
    constructor itself reads the entity slot. -/
theorem strong_article_consults_entity_assignment
    (R : DenotGS E W .et) (d : Nat)
    (g : Core.Assignment E) (gs : SitAssignment W) :
    interpret (.anaphoric R d) g gs =
      (letI := Classical.dec (R g gs (g d))
       if R g gs (g d) then some (g d) else none) := rfl

/-- The classifier `usesSituationPronoun` correctly flags the weak article
    as a structural binder of the resource situation; the strong article
    is not. This is the structural correlate of the [schwarz-2009]
    claim that uniqueness is *situational* and familiarity is *anaphoric*. -/
theorem situation_binding_classifies_articles
    (R : DenotGS E W .et) (sIdx d : Nat) :
    (Description.unique R sIdx).usesSituationPronoun = true ∧
    (Description.anaphoric R d).usesSituationPronoun = false := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §4: Morphological correlate — German bipartite vs English syncretic
-- ════════════════════════════════════════════════════════════════

/-! [schwarz-2009] reads the two-article distinction off German
morphology. English collapses both into *the*; the contrast is masked at
the surface but recoverable via `Determiner.IsSyncretic`. -/

/-- German has both articles overtly, with no syncretism — the structural
    [schwarz-2009] contrast is morphologically visible. -/
theorem german_two_articles :
    Determiner.MarksPresup German.Definiteness.determiners .uniqueness ∧
    Determiner.MarksPresup German.Definiteness.determiners .familiarity ∧
    ¬ Determiner.IsSyncretic German.Definiteness.determiners := by decide

/-- English has both articles, but they are syncretic — *the* covers both.
    The [schwarz-2009] contrast is real but morphologically invisible. -/
theorem english_syncretic_articles :
    Determiner.MarksPresup English.Definiteness.determiners .uniqueness ∧
    Determiner.MarksPresup English.Definiteness.determiners .familiarity ∧
    Determiner.IsSyncretic English.Definiteness.determiners := by decide

/-- The morphological discriminator: German is `.bipartite` (two distinct
    forms), English is `.generallyMarked` (one syncretic form). Both
    distinguish the same semantic types — the surface morphology differs. -/
theorem strategy_split :
    Determiner.markingStrategy German.Definiteness.determiners = .bipartite ∧
    Determiner.markingStrategy English.Definiteness.determiners = .generallyMarked :=
  ⟨German.Definiteness.marking, English.Definiteness.marking⟩

/-- The number of morphologically distinguished presupposition types
    differs across the two languages, even though the underlying
    inventory of semantic distinctions is the same.

    German marks 2 (bipartite); English marks 1 (the single *the* form).
    This is the [patel-grosz-grosz-2017] D-layer count read off
    the article system. -/
theorem morphological_distinction_count :
    (articleTypeToDistinguishedPresup
      (Determiner.articleType German.Definiteness.determiners)).length = 2 ∧
    (articleTypeToDistinguishedPresup
      (Determiner.articleType English.Definiteness.determiners)).length = 1
  := by decide

-- ════════════════════════════════════════════════════════════════
-- §5: Hawkins use types map onto the Schwarz split (§3.1)
-- ════════════════════════════════════════════════════════════════

/-- [schwarz-2013] §3.1: anaphoric uses pattern with the strong
    article — i.e., they project the familiarity presupposition. -/
theorem anaphoric_use_is_familiarity :
    useTypeToPresupType .anaphoric = .familiarity := rfl

/-- Immediate-situation and larger-situation uses pattern with the weak
    article — uniqueness presupposition. -/
theorem situational_uses_are_uniqueness :
    useTypeToPresupType .immediateSituation = .uniqueness ∧
    useTypeToPresupType .largerSituation = .uniqueness := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §6: Donkey anaphora patterns with the strong article (§3)
-- ════════════════════════════════════════════════════════════════

/-- [schwarz-2009] §3: donkey pronouns require the strong article
    in German (*von dem*, not *vom*). At the use-type level, this
    follows from `useTypeToPresupType .donkey = .familiarity` — the
    same presupposition type the strong article carries.

    This is a non-trivial empirical prediction: a quantifier-bound
    pronoun in a syntactically inaccessible position is treated by
    the morphology as a *familiarity* phenomenon rather than a
    *uniqueness* phenomenon. -/
theorem donkey_use_is_familiarity :
    useTypeToPresupType .donkey = .familiarity := rfl

/-- Donkey anaphora and discourse anaphora project the same
    presupposition type — they pattern together morphologically. -/
theorem donkey_patterns_with_anaphoric :
    useTypeToPresupType .donkey = useTypeToPresupType .anaphoric := rfl

/-! ### Cross-linguistic realization of donkey anaphora

The cross-linguistic pattern ([schwarz-2009] §3; cf. [moroney-2021]
Table 4.4 for the parallel pattern with anaphoric definites):

- **German**: strong article (*von dem*) — the two-article system
  distinguishes the donkey use overtly
- **Thai/Mandarin**: demonstrative — demonstratives fill the
  strong-article role
- **Shan**: bare noun — no articles, so no morphological signal -/

/-- Cross-linguistic datum on how donkey anaphora is expressed
    morphologically, connecting `DefiniteUseType.donkey` to concrete
    article forms.

    The article system (`articleSystem`) is *derived* from the language's
    fragment-level `determiners`, not stipulated independently — the
    declared `Determiner.Entry` list is the single source of truth. -/
structure DonkeyArticleDatum where
  language : String
  isoCode : String
  /-- Morphological form used for donkey pronouns -/
  form : String
  /-- Declared determiner set (single source of truth from which
      `articleSystem` is derived). -/
  determiners : List Determiner.Entry

/-- Schwarz `ArticleType` classification, derived from `determiners`. -/
def DonkeyArticleDatum.articleSystem (d : DonkeyArticleDatum) : ArticleType :=
  Determiner.articleType d.determiners

def germanDonkey : DonkeyArticleDatum :=
  { language := "German", isoCode := "deu"
    form := "strong article (von dem)"
    determiners := German.Definiteness.determiners }

def thaiDonkey : DonkeyArticleDatum :=
  { language := "Thai", isoCode := "tha"
    form := "demonstrative"
    determiners := Thai.Definiteness.determiners }

def mandarinDonkey : DonkeyArticleDatum :=
  { language := "Mandarin", isoCode := "cmn"
    form := "demonstrative"
    determiners := Mandarin.Definiteness.determiners }

def shanDonkey : DonkeyArticleDatum :=
  { language := "Shan", isoCode := "shn"
    form := "bare noun"
    determiners := Shan.Definiteness.determiners }

/-- All cross-linguistic donkey article data. -/
def donkeyArticleData : List DonkeyArticleDatum :=
  [germanDonkey, thaiDonkey, mandarinDonkey, shanDonkey]

/-- In languages with a weak/strong article distinction, donkey anaphora
    uses the strong form — never the weak form. This is predicted by
    `donkey_use_is_familiarity`: strong articles encode familiarity,
    and donkey anaphora requires familiarity. -/
theorem weakAndStrong_uses_strong :
    (donkeyArticleData.filter (·.articleSystem == .weakAndStrong)).all
      (·.form == "strong article (von dem)") = true := by decide

-- ════════════════════════════════════════════════════════════════
-- §7: Bridging split ([schwarz-2013] §3.2)
-- ════════════════════════════════════════════════════════════════

/-- [schwarz-2013] §3.2: bridging splits across the two articles.
    Part-whole bridging (*the village ... the church*) takes the weak
    article — situational uniqueness. Relational/producer bridging
    (*the play ... the author*) takes the strong article — anaphoric
    familiarity. -/
theorem bridging_split_at_presup_layer :
    bridgingPresupType .partWhole = .uniqueness ∧
    bridgingPresupType .relational = .familiarity := ⟨rfl, rfl⟩

/-- The two bridging subtypes are exactly the two Schwarz presupposition
    types — bridging is a microcosm of the [schwarz-2009] contrast.
    This is the empirical core of why the bridging split argument
    motivates a structural rather than purely lexical theory of
    definiteness. -/
theorem bridging_subtypes_realize_both_presup_types :
    bridgingPresupType .partWhole ≠ bridgingPresupType .relational := by
  rw [bridging_split_at_presup_layer.1, bridging_split_at_presup_layer.2]
  exact two_presup_types_distinct

-- ════════════════════════════════════════════════════════════════
-- §8: The two articles refer to different antecedents (the payoff)
-- ════════════════════════════════════════════════════════════════

/-! The semantic distinction is not just a presupposition-type label —
the two articles can pick *different referents* in the same context. We
build a tiny scenario where the unique satisfier of a restrictor is one
entity, and the discourse-indexed entity is a different one (which also
satisfies the restrictor). The weak article picks the indexed-by-
uniqueness referent (none, because there are two satisfiers); the strong
article picks the discourse-indexed antecedent. -/

/-- Two students. -/
inductive Student where
  | alice
  | bob
  deriving DecidableEq, Repr

/-- Both students count as students. The restrictor has *two* satisfiers,
    so the weak (uniqueness) article fails — there is no unique satisfier. -/
def studentRestr : DenotGS Student Unit .et := fun _g _gs _x => True

/-- Discourse referent at index 0 is Alice. The strong article
    (`.anaphoric`) reads off this slot. -/
def gAlice : Core.Assignment Student := fun _ => Student.alice

def gs0 : SitAssignment Unit := fun _ => ()

/-- The weak article fails on a multi-satisfier restrictor — uniqueness
    presupposition violation. -/
theorem weak_article_fails_on_multi :
    interpret (E := Student) (W := Unit) (.unique studentRestr 0) gAlice gs0 = none := by
  classical
  rw [interpret_unique]
  have hExU : ¬ ∃! x : Student, studentRestr gAlice gs0 x := by
    rw [existsUnique_iff_existence_and_uniqueness]
    rintro ⟨_, h⟩
    have : Student.alice = Student.bob := h .alice .bob trivial trivial
    cases this
  by_contra h
  exact hExU ((russellIota_isSome_iff_exists_unique _).mp
    (Option.ne_none_iff_isSome.mp h))

/-- The strong article succeeds — it returns the discourse-indexed
    referent (Alice) regardless of how many entities satisfy the
    restrictor. The familiarity presupposition does its work via the
    discourse index, not via uniqueness. -/
theorem strong_article_picks_indexed_antecedent :
    interpret (E := Student) (W := Unit) (.anaphoric studentRestr 0) gAlice gs0 =
      some Student.alice := by
  classical
  rw [interpret_anaphoric]
  simp [studentRestr, gAlice]

/-- The empirical payoff at the Core API: the two articles, given the
    same restrictor and bi-assignment, can disagree on what they return.
    This is the semantic counterpart of the German morphological split. -/
theorem two_articles_can_disagree :
    interpret (E := Student) (W := Unit) (.unique studentRestr 0) gAlice gs0 ≠
    interpret (E := Student) (W := Unit) (.anaphoric studentRestr 0) gAlice gs0 := by
  rw [weak_article_fails_on_multi, strong_article_picks_indexed_antecedent]
  intro h
  cases h

end Schwarz2009
