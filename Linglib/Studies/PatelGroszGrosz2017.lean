import Linglib.Typology.Pronoun.Basic
import Linglib.Core.Nominal.Determiner
import Linglib.Fragments.German.Definiteness

/-!
# Patel-Grosz & Grosz (2017): Revisiting Pronominal Typology
@cite{patel-grosz-grosz-2017} @cite{schwarz-2009} @cite{schwarz-2013}
@cite{elbourne-2005} @cite{cardinaletti-starke-1999}

@cite{patel-grosz-grosz-2017} (LI 48(2)) argue, for German, that personal
pronouns (PER: *er/sie/es*) and demonstrative pronouns (DEM: *der/die/das*) have
the **same core makeup** — both a null NP plus a definite-determiner head (Ddet),
i.e. both are definite descriptions — and that DEM merely **adds a D_deix
layer**. The PER/DEM distribution then follows from **structural economy**
(*Minimize DP!*): PER, being less structured, is the default; DEM is licensed
only by an added pragmatic effect (emotivity §5.1, disambiguation §5.2,
register §5.3).

The paper's three contributions are made *true by construction* on substrate
they motivated, rather than stipulated here:

* **DEM = PER + deixis** is the type `DemonstrativePronoun extends
  PersonalPronoun` (`Typology/Pronoun/Basic.lean`) — a demonstrative pronoun
  structurally *contains* a personal pronoun, mirroring `Determiner.Demonstrative
  extends Determiner`. So "DEM contains PER" is the `extends`, not a typological
  universal asserted over invented data.
* **Pronouns are definite descriptions** is
  `PersonalPronoun.denote_selector_eq_toNominalKind`
  (`Semantics/Reference/PronounDenotation.lean`): a pronoun's referent is the
  `NominalKind.anaphoric` strong-article definite over its φ-feature restrictor.
* The **two-article ↔ two-D-layer** correlation (§4) is read off the determiner
  inventory (`Determiner.articleType`), not stipulated.

## Implementation notes

The paper is German-focused (with Bavarian in §5.3 and passing mention of
Portuguese/French/Hebrew). The earlier ~11-language `dLayers`/licensing table, a
five-context licensing inventory, and a Finnish "counterexample" had no basis in
the text and have been removed. *Minimize DP!* as a genuine node-count order
(over `Pareto.lean`/`FeaturePreorder`) is left as a `Todo`; here the economy is
recorded structurally (DEM carries the extra D_deix layer) and in prose.
-/

namespace PatelGroszGrosz2017

open Features.Definiteness (ArticleType)

/-- The **three** pragmatic contexts that license a demonstrative pronoun in
    German (@cite{patel-grosz-grosz-2017} §5): a positive pragmatic effect must
    override the *Minimize DP!* preference for the less-structured PER. -/
inductive DEMLicensingContext where
  /-- §5.1 Emotivity — the speaker expresses emotional engagement with the referent. -/
  | emotivity
  /-- §5.2 Disambiguation — DEM avoids the most prominent antecedent (anti-topicality). -/
  | disambiguation
  /-- §5.3 Register — colloquial/informal register. -/
  | register
  deriving DecidableEq, Repr

/-! ### German pronoun inventory -/

-- Personal pronouns (PER): the Ddet + null-NP core, no deixis layer.
def er  : PersonalPronoun := { form := "er",  person := some .third, number := some .Sing, gender := some .masculine }
def sie : PersonalPronoun := { form := "sie", person := some .third, number := some .Sing, gender := some .feminine }
def es  : PersonalPronoun := { form := "es",  person := some .third, number := some .Sing, gender := some .neuter }

-- Demonstrative pronouns (DEM): the PER core plus a D_deix layer.
def der : DemonstrativePronoun := { form := "der", person := some .third, number := some .Sing, gender := some .masculine, deictic := .distal }
def die : DemonstrativePronoun := { form := "die", person := some .third, number := some .Sing, gender := some .feminine,  deictic := .distal }
def das : DemonstrativePronoun := { form := "das", person := some .third, number := some .Sing, gender := some .neuter,    deictic := .distal }

/-- A language's 3rd-person pronoun system: its PER and DEM inventories, its
    article inventory (the single source of truth for `articleType`), and the
    pragmatic contexts licensing DEM. -/
structure PronounSystem where
  language : String
  personal : List PersonalPronoun
  demonstrative : List DemonstrativePronoun
  determiners : List Determiner.Entry
  licensing : List DEMLicensingContext

namespace PronounSystem

/-- Number of D-layers, **derived**: a language with demonstrative pronouns
    projects the D_deix layer (2); a PER-only language has one (Ddet only). -/
def dLayers (s : PronounSystem) : Nat := if s.demonstrative.isEmpty then 1 else 2

/-- The Schwarz `ArticleType`, **derived** from the determiner inventory. -/
def articleType (s : PronounSystem) : ArticleType := Determiner.articleType s.determiners

end PronounSystem

/-- German: PER *er/sie/es*, DEM *der/die/das*, weak/strong articles, all three
    DEM-licensing contexts attested (@cite{patel-grosz-grosz-2017} §5). -/
def german : PronounSystem :=
  { language := "German"
    personal := [er, sie, es]
    demonstrative := [der, die, das]
    determiners := German.Definiteness.determiners
    licensing := [.emotivity, .disambiguation, .register] }

/-! ### The three contributions, derived -/

/-- **DEM = PER + deixis** (the core-makeup claim): every demonstrative pronoun
    structurally contains a personal pronoun — true by the `extends`, not a
    stipulated universal over a language sample. The φ-features (person/number/
    gender) live on the shared PER core; the deixis is the only addition. -/
theorem dem_contains_per (d : DemonstrativePronoun) :
    d.toPersonalPronoun.person = d.person ∧ d.toPersonalPronoun.number = d.number :=
  ⟨rfl, rfl⟩

/-- **Gender concord is uniform across PER and DEM** because gender is a feature
    of the shared PER core, not of the deixis layer. This is the structural basis
    for @cite{patel-grosz-grosz-2017} §3's corpus finding that gender mismatches
    (a grammatically neuter noun like *Ehepaar* 'married couple' referred to by a
    non-neuter pronoun) are *equally* available for PER and DEM — falsifying the
    claim that demonstratives must match grammatical gender. -/
theorem dem_gender_is_per_gender (d : DemonstrativePronoun) :
    d.gender = d.toPersonalPronoun.gender := rfl

/-- German projects two D-layers — **derived** from the presence of DEM forms,
    not stipulated as a `Nat`. -/
theorem german_two_layers : german.dLayers = 2 := by decide

/-- German's article system is `.weakAndStrong` (two distinct article forms) —
    derived from the determiner inventory, matching its two D-layers
    (@cite{patel-grosz-grosz-2017} §4). -/
theorem german_weakAndStrong : german.articleType = .weakAndStrong := by decide

/-- The @cite{schwarz-2009}/@cite{schwarz-2013} weak/strong article typology meets
    @cite{patel-grosz-grosz-2017}'s D-layer count: German's two distinct article
    forms (which derive `.bipartite`) correspond to its two D-layers and the
    `.weakAndStrong` article type. All three facts are derived from the German
    determiner inventory + the DEM forms, not stipulated. -/
theorem schwarz_pgg_german_consistent :
    Determiner.markingStrategy German.Definiteness.determiners = .bipartite ∧
    german.dLayers = 2 ∧
    german.articleType = .weakAndStrong :=
  ⟨German.Definiteness.marking, by decide⟩

end PatelGroszGrosz2017
