import Linglib.Typology.Pronoun.Basic
import Linglib.Core.Nominal.Determiner
import Linglib.Fragments.German.Definiteness
import Linglib.Studies.Schwarz2009

/-!
# Patel-Grosz & Grosz (2017): Revisiting Pronominal Typology
@cite{patel-grosz-grosz-2017} @cite{schwarz-2009} @cite{schwarz-2013}
@cite{elbourne-2005} @cite{cardinaletti-starke-1999}

@cite{patel-grosz-grosz-2017} (LI 48(2)) argue, for German, that personal pronouns
(PER: *er/sie/es*) and demonstrative pronouns (DEM: *der/die/das*) have the **same
core makeup** — both a null NP plus a definite determiner — and differ only in that
DEM adds an **anaphoric index**: DEM is the @cite{schwarz-2009} *strong* article,
PER the *weak* article ("the latter are anaphoric in a way that the former are
not"). The extra layer is that index, **not** spatial deixis — their footnote 1
stresses "it is far from clear that there is anything truly 'demonstrative' about"
German DEMs. So here *der/die/das* are **strong-article `PersonalPronoun`s**, not a
separate demonstrative type; the genuinely deictic `NominalKind.demonstrative` is a
different object. The PER/DEM distribution then follows from **structural economy**
(*Minimize DP!*): PER, being less structured, is the default; DEM is licensed only
by an added pragmatic effect (emotivity §5.1, disambiguation §5.2, register §5.3).

The contributions are made *true by construction* on shared substrate:

* **DEM = PER + anaphoric index** is the @cite{schwarz-2009} weak/strong refinement
  `Core.Nominal.interpret_anaphoric_eq_unique_of_existsUnique`: the strong description
  (DEM, `.anaphoric`) and the weak description (PER, `.unique`) over one restrictor
  pick the same referent exactly when the indexed entity is the unique satisfier —
  off that, DEM is anaphoric in a way PER is not. Both denote via
  `NominalKind.ofPresupType`, with the strength round-tripping through
  `expectedPresupType` (`NominalKind.expectedPresupType_ofPresupType`); the
  off-uniqueness **divergence** — DEM and PER picking *different* referents — is
  `der_er_can_diverge`, reusing @cite{schwarz-2009} §8's two-satisfier scenario.
* The **two-series ↔ two-article** correlation (§4) is read off the determiner
  inventory (`Determiner.articleType`) and the lexicalized strong series, not
  stipulated.

## Implementation notes

The paper is German-focused (Bavarian in §5.3, passing Portuguese/French/Hebrew).
The earlier ~11-language table, a five-context licensing inventory, and a Finnish
"counterexample" had no basis in the text and were removed. *Minimize DP!* as a
genuine node-count order (over `Pareto.lean`/`FeaturePreorder`) is left as a `Todo`.
The §3 corpus finding — that gender mismatches (e.g. neuter *Mädchen*/*Ehepaar* with
a non-neuter pronoun) are *equally* available for PER and DEM, PG&G's argument
against a [±NP] split — is recorded in prose, as formalizing it needs antecedent
modeling absent here.
-/

namespace PatelGroszGrosz2017

open Features.Definiteness (ArticleType)

/-- The **three** pragmatic contexts that license the strong-article ("DEM") series
    in German (@cite{patel-grosz-grosz-2017} §5): a positive pragmatic effect must
    override the *Minimize DP!* preference for the less-structured PER. -/
inductive DEMLicensingContext where
  /-- §5.1 Emotivity — the speaker expresses emotional engagement with the referent. -/
  | emotivity
  /-- §5.2 Disambiguation — DEM avoids the most prominent antecedent (anti-topicality). -/
  | disambiguation
  /-- §5.3 Register — colloquial/dialectal register. -/
  | register
  deriving DecidableEq, Repr

/-! ### German 3rd-person pronoun inventory

@cite{patel-grosz-grosz-2017} footnote 1: German *der/die/das* are not truly
demonstrative — they are the **strong-article** counterpart of the personal-pronoun
series. So both series are `PersonalPronoun`, differing only in @cite{schwarz-2009}
article strength; which series a form belongs to is recorded here (the `weak`/`strong`
split of `PronounSystem`), not in the theory-neutral `PersonalPronoun` schema. -/

-- Weak series (PER): the uniqueness/weak article.
def er  : PersonalPronoun := { form := "er",  person := some .third, number := some .Sing, gender := some .masculine }
def sie : PersonalPronoun := { form := "sie", person := some .third, number := some .Sing, gender := some .feminine }
def es  : PersonalPronoun := { form := "es",  person := some .third, number := some .Sing, gender := some .neuter }

-- Strong series ("DEM"): the same core plus the strong-article anaphoric index.
def der : PersonalPronoun := { form := "der", person := some .third, number := some .Sing, gender := some .masculine }
def die : PersonalPronoun := { form := "die", person := some .third, number := some .Sing, gender := some .feminine }
def das : PersonalPronoun := { form := "das", person := some .third, number := some .Sing, gender := some .neuter }

/-- A language's 3rd-person pronoun system as PG&G analyze it: the weak (PER) and
    strong ("DEM") article series, the article inventory (source of `articleType`),
    and the pragmatic contexts licensing the strong series. -/
structure PronounSystem where
  language : String
  weak : List PersonalPronoun
  strong : List PersonalPronoun
  determiners : List Determiner.Entry
  licensing : List DEMLicensingContext

namespace PronounSystem

/-- The language lexicalizes a distinct strong-article series (PG&G's added D-layer):
    at least one strong form is present. Derived, not stipulated. -/
def LexicalizesStrong (s : PronounSystem) : Prop := 0 < s.strong.length

instance : DecidablePred LexicalizesStrong :=
  fun s => inferInstanceAs (Decidable (0 < s.strong.length))

end PronounSystem

/-- German: weak PER *er/sie/es*, strong "DEM" *der/die/das*, weak/strong articles,
    all three licensing contexts attested (@cite{patel-grosz-grosz-2017} §5). -/
def german : PronounSystem :=
  { language := "German"
    weak := [er, sie, es]
    strong := [der, die, das]
    determiners := German.Definiteness.determiners
    licensing := [.emotivity, .disambiguation, .register] }

/-! ### The contributions, derived -/

/-- German lexicalizes a distinct strong-article pronoun series — **derived** from
    the presence of *der/die/das*, not stipulated. -/
theorem german_lexicalizes_strong : german.LexicalizesStrong := by decide

/-- German's article system is `.weakAndStrong` (two distinct article forms) —
    derived from the determiner inventory, matching its weak/strong pronoun series
    (@cite{patel-grosz-grosz-2017} §4). -/
theorem german_weakAndStrong :
    Determiner.articleType german.determiners = .weakAndStrong := by decide

/-- The @cite{schwarz-2009}/@cite{schwarz-2013} weak/strong typology meets PG&G's
    two-series claim: German's two distinct article forms (deriving `.bipartite`)
    correspond to its lexicalized strong series and the `.weakAndStrong` article
    type — all derived from the determiner inventory + the strong forms. -/
theorem schwarz_pgg_german_consistent :
    Determiner.markingStrategy German.Definiteness.determiners = .bipartite ∧
    german.LexicalizesStrong ∧
    Determiner.articleType german.determiners = .weakAndStrong :=
  ⟨German.Definiteness.marking, german_lexicalizes_strong, german_weakAndStrong⟩

/-! ### The empirical payoff: the two series can diverge -/

/-- @cite{patel-grosz-grosz-2017}'s actual claim — DEM "is anaphoric in a way" PER
    "is not" — made concrete: the strong-article "DEM" reading (*der*,
    `ofPresupType .familiarity`) and the weak-article PER reading (*er*,
    `ofPresupType .uniqueness`), over **one** restrictor and bi-assignment, pick
    *different* referents. Reusing @cite{schwarz-2009} §8's two-satisfier scenario:
    the weak PER fails uniqueness (two satisfiers → `none`) while the strong DEM
    reads off the discourse index. This is the divergence direction the convergence
    theorem (`Core.Nominal.interpret_anaphoric_eq_unique_of_existsUnique`) rules out
    only under uniqueness. -/
theorem der_er_can_diverge :
    Core.Nominal.interpret
        (Core.Nominal.NominalKind.ofPresupType .uniqueness Schwarz2009.studentRestr 0)
        Schwarz2009.gAlice Schwarz2009.gs0
      ≠ Core.Nominal.interpret
        (Core.Nominal.NominalKind.ofPresupType .familiarity Schwarz2009.studentRestr 0)
        Schwarz2009.gAlice Schwarz2009.gs0 :=
  Schwarz2009.two_articles_can_disagree

end PatelGroszGrosz2017
