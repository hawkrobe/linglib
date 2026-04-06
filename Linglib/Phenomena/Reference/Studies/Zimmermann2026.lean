import Linglib.Fragments.Hausa.Determiners
import Linglib.Fragments.Akan.Determiners
import Linglib.Theories.Semantics.Lexical.Determiner.UnifiedUniversal
import Linglib.Theories.Semantics.Lexical.Determiner.ONEModifiers
import Linglib.Theories.Semantics.Lexical.Determiner.ChoiceFunction
import Linglib.Phenomena.Plurals.Studies.HaslingerHienEtAl2025

/-!
# @cite{zimmermann-2026}: African Lambdas I — Formal Semantics of African
Languages: The Nominal Domain
@cite{zimmermann-2026}

Review article surveying formal-semantic research on the nominal domain
in (mostly West) African languages, covering definiteness, indefiniteness,
universal quantification, and number marking.

## Key Theoretical Contributions Formalized Here

1. **The Hausa UQ system is 2-form** (§4.1): *koo-wane* (distributive) vs
   *duk(a)* (non-distributive). This instantiates the Q_∀ + ONE
   decomposition from @cite{haslinger-etal-2025-nllt}.

2. **The INDEF scope contrast** (§3.3): Hausa *wani/wata* (∃-quantifier,
   flexible scope) vs Akan *bí* (choice function, wide scope only under
   negation). African languages provide clearer evidence than English
   for the choice function vs ∃-quantifier distinction.

3. **The DEF-marker debate** (§3.1): Akan *nó* is variously analysed as
   strong DEF, weak DEF, or demonstrative. The distribution does not
   match any single European-based DEF analysis cleanly.

## What This Study Does NOT Formalize

- Cross-categorial DEF-markers (§3.2): Ga *lε* on VPs/TPs
- Logophoric pronouns (§3.5): Ewe *yè* (infrastructure exists in
  `Core/Discourse/Logophoricity.lean`)
- Inverse number marking (§4.2): Dagaare *-ri*
- DEF-INDEF co-occurrence (§3.4): compositional interaction of *bí* + *nó*

These are left for future work in dedicated study files.

## Relation to @cite{haslinger-etal-2025-nllt}

The Haslinger et al. typological sample (11 languages) is extended here
with Hausa (Chadic, 2-form) and Akan (Kwa, 1-form). The study file
`HaslingerHienEtAl2025.lean` formalizes the Q_∀ + ONE decomposition
that Zimmermann's §4.1 builds on. This file adds the African language
data and the indefiniteness contrast (§3.3) which Haslinger et al.
do not cover.
-/

namespace Phenomena.Reference.Studies.Zimmermann2026

open Fragments.Hausa.Determiners
open Fragments.Akan.Determiners
open Semantics.Lexical.Determiner.UnifiedUniversal
open Semantics.Lexical.Determiner.ONEModifiers
open Semantics.Lexical.Determiner.ChoiceFunction
open Phenomena.Plurals.Studies.HaslingerHienEtAl2025

-- ════════════════════════════════════════════════════
-- § 1. Hausa UQ Decomposition
-- ════════════════════════════════════════════════════

/-! The Hausa *koo*/*duk* split is an instance of the 2-form UQ
    system from @cite{haslinger-etal-2025-nllt}. *koo-wane* maps
    to Q_∀[ONE_∅] and *duk(a)* to bare Q_∀. -/

/-- The *koo*/*duk* split parallels the English every/all and German
    jeder/alle splits — same Q_∀, different complement selection.
    @cite{zimmermann-2026} §4.1, @cite{haslinger-etal-2025-nllt}. -/
theorem hausa_parallels_english :
    HausaUQ.koo.isDistributive = true ∧
    HausaUQ.duk.isDistributive = false := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 2. *koo* = Q_∀[ONE_∅]: Distributive Universal
-- ════════════════════════════════════════════════════

/-- *koo-wane* takes SG count NPs (atoms), ensuring ONE_∅ is
    satisfied. On an atomic restrictor, `kooSem P Q` distributes
    to every atom — equivalent to `∀x, P x → Q x`.

    @cite{zimmermann-2008}: only *koo*-quantifiers can bind SG pronouns
    (ex. 23a), because only they iterate over individual atoms. -/
theorem koo_distributes {α : Type*} [PartialOrder α]
    {P Q : α → Prop}
    (hONE : ONE_empty P) :
    kooSem P Q ↔ ONE_empty P ∧ (∀ x, P x → Q x) := by
  simp only [kooSem, everyPresup]
  constructor
  · intro ⟨_, hQ⟩
    exact ⟨hONE, (every_distributes hONE).mp hQ⟩
  · intro ⟨_, hAll⟩
    exact ⟨hONE, (every_distributes hONE).mpr hAll⟩

/-- *duk(a)* takes DEF PL/mass NPs (CUM denotation). On a CUM
    restrictor with maximal element m, `dukSem P Q` reduces to Q(m).

    @cite{zimmermann-2008}: *duk*-NPs freely co-occur with collective
    predicates (ex. 22b), because they apply the predicate to the
    maximal sum rather than distributing over atoms. -/
theorem duk_collective {α : Type*} [SemilatticeSup α]
    {P Q : α → Prop} (hCum : Mereology.CUM P)
    {m : α} (hMax : Mereology.isMaximal P m) :
    dukSem P Q ↔ Q m :=
  dng_cum' hCum hMax

-- ════════════════════════════════════════════════════
-- § 3. INDEF Scope Contrast: ∃ vs Choice Function
-- ════════════════════════════════════════════════════

/-! The most theoretically significant contribution of the African
    language data: the INDEF scope contrast between Hausa *wani/wata*
    and Akan *bí* provides cross-linguistic evidence for the choice
    function / ∃-quantifier distinction.

    In English, indefinites are ambiguous between CF and ∃ analyses
    (both predict flexible scope). In Hausa and Akan, the two analyses
    make different predictions under negation:

    Hausa *wani*: ¬ > ∃ is available (narrow scope)
    Akan *bí*: ∃ > ¬ only (wide scope, from CF binding)

    @cite{zimmermann-2026} §3.3 exx. (13), (15). -/

/-- Hausa *wani* and Akan *bí* differ in scope under negation:
    *bí* (CF) forces wide scope; *wani* (∃) allows narrow scope.
    This contrast is derived from `IndefType`, not stipulated per-language.
    @cite{zimmermann-2026} §3.3 exx. (13), (15). -/
theorem indef_scope_contrast :
    -- Akan bí: CF → obligatory wide scope under negation
    biIndefType.forcesWideScopeUnderNeg = true ∧
    -- Hausa wani: ∃ → narrow scope available under negation
    HausaIndef.wani.indefType.allowsNarrowScopeUnderNeg = true ∧
    -- Bare NPs in both languages: ∃ → narrow scope
    bareNPIndefType.allowsNarrowScopeUnderNeg = true ∧
    HausaIndef.bare.indefType.allowsNarrowScopeUnderNeg = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The CF analysis of *bí* predicts wide scope under negation:
    the CF is applied before negation takes effect.

    Under negation: ¬VP(f(N))
    = "it's not the case that this particular N is VP'd"
    NOT: "there's no N that is VP'd"

    @cite{owusu-2022}, @cite{zimmermann-2026} §3.3 ex. (15). -/
theorem bi_cf_wide_scope {E : Type*}
    (f : CF E) (hf : f.isCorrect)
    (N : E → Prop) (VP : E → Prop)
    (hN : ∃ x, N x) (hAll : ∀ x, N x → VP x) :
    VP (f N) :=
  cf_wide_scope_under_negation f hf N VP hN hAll

/-- The ∃ analysis of *wani* allows narrow scope under negation:
    ¬∃x[N(x) ∧ VP(x)] is satisfiable.

    @cite{zimmermann-2014}, @cite{zimmermann-2026} §3.3 ex. (13). -/
theorem wani_exists_narrow_scope {E : Type*}
    (N : E → Prop) (VP : E → Prop)
    (hNone : ∀ x, N x → ¬VP x) :
    ¬∃ x, N x ∧ VP x :=
  exists_narrow_scope_under_negation N VP hNone

-- ════════════════════════════════════════════════════
-- § 4. Akan *nó*: The DEF-Marker Debate
-- ════════════════════════════════════════════════════

/-! Zimmermann §3.1 surveys three analyses of Akan *nó*. The analysis
    matters for the typology of definiteness systems: if *nó* is a
    weak (uniqueness) marker, Akan has the reverse of the Marka-Dafing
    system; if it's a demonstrative, Akan lacks a true definite article.

    @cite{bombi-2018}'s uniqueness analysis captures the most data,
    including:
    - Infelicity with globally unique NPs (ex. 1: *ewia* 'sun')
    - Obligatoriness in larger-situation contexts (ex. 4a)
    - Non-occurrence on superlative NPs
    - Different distribution from demonstrative *saa...nó*

    But it leaves open: why is *nó* absent on superlative NPs? -/

/-- The three analyses all agree that *nó* contributes some form of
    discourse-linking. The key empirical test: *nó* is bad with
    globally unique NPs but required with anaphoric ones.
    @cite{owusu-2022} ex. (1)–(2), @cite{zimmermann-2026} §3.1. -/
theorem no_discourse_linking :
    preferredAnalysis = .weak ∧
    preferredAnalysis.toPresupType = .uniqueness :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Interpretive Flexibility of *bi-ara*
-- ════════════════════════════════════════════════════

/-! Akan *bi-ara* gets universal, NPI, and FC readings depending on
    syntactic context. @cite{philipp-2022} proposes this falls out from
    structural ambiguity: the INDEF marker *bí* combined with the
    alternative-sensitive scalar operator *ara* at different attachment
    sites.

    This connects to the exhaustification-based analysis of FC items
    in the Chierchia/Fox/Spector tradition, but with the added twist
    that the base indefinite is a choice function, not an ∃-quantifier.
    @cite{zimmermann-2026} §4.1.2 ex. (27). -/

/-- *bi-ara* is structurally complex: INDEF (*bí*) + scalar operator
    (*ara*). The base indefinite *bí* is a choice function — derived
    from `IndefType`, not stipulated.
    @cite{owusu-2022}, @cite{zimmermann-2026} §3.3. -/
theorem biara_base_is_cf :
    biIndefType = .choiceFunction := rfl

-- ════════════════════════════════════════════════════
-- § 6. Extended Typological Sample
-- ════════════════════════════════════════════════════

/-! Zimmermann's survey adds Hausa to the @cite{haslinger-etal-2025-nllt}
    sample as a 2-form Chadic language. The extended sample now covers
    Niger-Congo (Kwa, Mande, Atlantic), Chadic, Afro-Asiatic, and
    Austronesian in addition to Indo-European and Japonic. -/

/-- Hausa entry for the typological sample: 2-form system with
    *koo-wane* (distributive) and *duk(a)* (non-distributive).
    @cite{zimmermann-2008}, @cite{zimmermann-2026} §4.1. -/
def hausaUQEntry : UQLanguageEntry where
  language := "Hausa"
  systemType := .twoForm
  distForm := "koo-wane(m.)/koo-wace(f.)"
  nonDistForm := "duk(a)"
  family := "Chadic"

/-- Verify Hausa is classified as 2-form. -/
theorem hausa_is_two_form :
    hausaUQEntry.systemType = .twoForm := rfl

/-- Akan *bi-ara* entry for the typological sample.
    Akan is harder to classify: *bi-ara* is the only overt universal
    quantifier, but its three-way ambiguity (∀/NPI/FC) makes it
    unlike a simple 1-form system. We classify it as 1-form since
    there is only one overt form, noting the caveat.
    @cite{philipp-2022}, @cite{zimmermann-2026} §4.1.2. -/
def akanUQEntry : UQLanguageEntry where
  language := "Akan"
  systemType := .oneForm
  distForm := "bi-ara"
  family := "Kwa"

/-- Extended sample: Haslinger et al.'s original 11 + Hausa + Akan = 13. -/
def extendedSample : List UQLanguageEntry :=
  typologicalSample ++ [hausaUQEntry, akanUQEntry]

theorem extended_sample_size :
    extendedSample.length = 13 := by native_decide

end Phenomena.Reference.Studies.Zimmermann2026
