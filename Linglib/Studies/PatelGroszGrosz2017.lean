import Linglib.Syntax.Category.Pronoun.Basic
import Linglib.Syntax.Category.Determiner.Basic
import Linglib.Fragments.German.Definiteness
import Linglib.Studies.Schwarz2009
import Linglib.Semantics.Presupposition.PhiFeatures

/-!
# Patel-Grosz & Grosz (2017): Revisiting Pronominal Typology
[patel-grosz-grosz-2017] [schwarz-2009] [schwarz-2013]
[elbourne-2005] [cardinaletti-starke-1999]

[patel-grosz-grosz-2017] (LI 48(2)) argue, for German, that personal pronouns
(PER: *er/sie/es*) and demonstrative pronouns (DEM: *der/die/das*) have the **same
core makeup** — both a null NP plus a definite determiner — and differ only in that
DEM adds an **anaphoric index**: DEM is the [schwarz-2009] *strong* article,
PER the *weak* article ("the latter are anaphoric in a way that the former are
not"). The extra layer is that index, **not** spatial deixis — their footnote 1
stresses "it is far from clear that there is anything truly 'demonstrative' about"
German DEMs. So here *der/die/das* are **strong-article `PersonalPronoun`s**, not a
separate demonstrative type. The genuinely deictic objects are a different matter: the
`Description.demonstrative` denotation, and the deictic demonstrative *pronoun*
`DemonstrativePronoun` (German *dieser*, English *this*), which carries a `Features.Deixis.Feature`
— *der* does **not**, so it is no `Demonstrative` (`Syntax/Category/Pronoun/Demonstrative.lean`). PER/DEM
(article strength) is thus orthogonal to demonstrativehood (deixis). The PER/DEM distribution then
follows from **structural economy**
(*Minimize DP!*): PER, being less structured, is the default; DEM is licensed only
by an added pragmatic effect (emotivity §5.1, disambiguation §5.2, register §5.3).

The contributions are made *true by construction* on shared substrate:

* **DEM = PER + anaphoric index** is the [schwarz-2009] weak/strong refinement
  `Semantics.Definiteness.interpret_anaphoric_eq_unique_of_existsUnique`: the strong description
  (DEM, `.anaphoric`) and the weak description (PER, `.unique`) over one restrictor
  pick the same referent exactly when the indexed entity is the unique satisfier —
  off that, DEM is anaphoric in a way PER is not. Both denote via
  `Description.ofPresupType`, with the strength round-tripping through
  `expectedPresupType` (`Description.expectedPresupType_ofPresupType`); the
  off-uniqueness **divergence** — DEM and PER picking *different* referents — is
  `der_er_can_diverge`, reusing [schwarz-2009] §8's two-satisfier scenario.
* The **two-series ↔ two-article** correlation (§4) is read off the determiner
  inventory (`Determiner.articleType`) and the lexicalized strong series, not
  stipulated.

## Implementation notes

The paper is German-focused (Bavarian in §5.3, passing Portuguese/French/Hebrew).
The earlier ~11-language table, a five-context licensing inventory, and a Finnish
"counterexample" had no basis in the text and were removed. *Minimize DP!* as a
genuine node-count order (over `Pareto.lean`/`PullbackPreorder`) is left as a `Todo`.
The §3 corpus finding — that gender mismatches (e.g. neuter *Mädchen*/*Ehepaar* with
a non-neuter pronoun) are *equally* available for PER and DEM, PG&G's argument
against a [±NP] split — is recorded in prose, as formalizing it needs antecedent
modeling absent here.
-/

namespace PatelGroszGrosz2017

open Features.Definiteness (ArticleType)

/-- The **three** pragmatic contexts that license the strong-article ("DEM") series
    in German ([patel-grosz-grosz-2017] §5): a positive pragmatic effect must
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

[patel-grosz-grosz-2017] footnote 1: German *der/die/das* are not truly
demonstrative — they are the **strong-article** counterpart of the personal-pronoun
series. So both series are `PersonalPronoun`, differing only in [schwarz-2009]
article strength; which series a form belongs to is recorded here (the `weak`/`strong`
split of `PronounSystem`), not in the theory-neutral `PersonalPronoun` schema. -/

-- Weak series (PER): the uniqueness/weak article.
def er  : PersonalPronoun := { form := "er",  person := some .third, number := some .singular, gender := some .masculine }
def sie : PersonalPronoun := { form := "sie", person := some .third, number := some .singular, gender := some .feminine }
def es  : PersonalPronoun := { form := "es",  person := some .third, number := some .singular, gender := some .neuter }

-- Strong series ("DEM"): the same core plus the strong-article anaphoric index.
def der : PersonalPronoun := { form := "der", person := some .third, number := some .singular, gender := some .masculine }
def die : PersonalPronoun := { form := "die", person := some .third, number := some .singular, gender := some .feminine }
def das : PersonalPronoun := { form := "das", person := some .third, number := some .singular, gender := some .neuter }

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
    all three licensing contexts attested ([patel-grosz-grosz-2017] §5). -/
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
    ([patel-grosz-grosz-2017] §4). -/
theorem german_weakAndStrong :
    Determiner.articleType german.determiners = .weakAndStrong := by decide

/-- The [schwarz-2009]/[schwarz-2013] weak/strong typology meets PG&G's
    two-series claim: German's two distinct article forms (deriving `.bipartite`)
    correspond to its lexicalized strong series and the `.weakAndStrong` article
    type — all derived from the determiner inventory + the strong forms. -/
theorem schwarz_pgg_german_consistent :
    Determiner.markingStrategy German.Definiteness.determiners = .bipartite ∧
    german.LexicalizesStrong ∧
    Determiner.articleType german.determiners = .weakAndStrong :=
  ⟨German.Definiteness.marking, german_lexicalizes_strong, german_weakAndStrong⟩

/-! ### The empirical payoff: the two series can diverge -/

/-- [patel-grosz-grosz-2017]'s actual claim — DEM "is anaphoric in a way" PER
    "is not" — made concrete: the strong-article "DEM" reading (*der*,
    `ofPresupType .familiarity`) and the weak-article PER reading (*er*,
    `ofPresupType .uniqueness`), over **one** restrictor and bi-assignment, pick
    *different* referents. Reusing [schwarz-2009] §8's two-satisfier scenario:
    the weak PER fails uniqueness (two satisfiers → `none`) while the strong DEM
    reads off the discourse index. This is the divergence direction the convergence
    theorem (`Semantics.Definiteness.interpret_anaphoric_eq_unique_of_existsUnique`) rules out
    only under uniqueness. -/
theorem der_er_can_diverge :
    Semantics.Definiteness.interpret
        (Semantics.Definiteness.Description.ofPresupType .uniqueness Schwarz2009.studentRestr 0)
        Schwarz2009.gAlice Schwarz2009.gs0
      ≠ Semantics.Definiteness.interpret
        (Semantics.Definiteness.Description.ofPresupType .familiarity Schwarz2009.studentRestr 0)
        Schwarz2009.gAlice Schwarz2009.gs0 :=
  Schwarz2009.two_articles_can_disagree

/-! ### Grounding the Pronoun API: `PersonalPronoun` denotes via a φ-restricted definite description

A personal pronoun is a definite description over a null NP whose φ-features are presuppositions
([elbourne-2005] pronouns-as-definites; gender = null-NP concord à la Sauerland; the
partial-identity view of φ in `Semantics/Presupposition/PhiFeatures`, after Cooper/Heim & Kratzer).
The PER series is the **weak** article (uniqueness); the marked DEM series the **strong**
(familiarity, `der_er_can_diverge` above) — article-strength is *per-series*, not a per-element slot
(like deficiency, unlike the demonstrative's deixis). The load-bearing parallel to the demonstrative
grounding (`Studies/Hanink2021`): there `deixis` filled `Description.demonstrative`'s slot; here the
`Proform.phi` **gender** supplies the restrictor's presupposition. -/

open Semantics.Presupposition.PhiFeatures (femSem)

/-- `⟦sie⟧` made concrete: the feminine PER's weak-article restrictor **is** the `femSem`
    presupposition — true by construction (`(femSem isFemale).presup = isFemale`), so the gender
    feature *drives* the definite description's restrictor rather than re-stipulating it. -/
theorem feminine_per_restrictor_is_femSem {E W : Type}
    (isFemale : E → Prop) (sIdx : Nat) :
    Semantics.Definiteness.Description.ofPresupType .uniqueness
        ((fun _ _ x => (femSem isFemale).presup x) :
          Intensional.Variables.DenotGS E W .et) sIdx
      = Semantics.Definiteness.Description.unique
          ((fun _ _ x => isFemale x) :
            Intensional.Variables.DenotGS E W .et) sIdx := rfl

/-- Consequently a feminine PER picks the *unique female* — the gender presupposition is the
    restrictor of the weak-article definite (`ιx[isFemale x]`). -/
theorem feminine_per_picks_unique_female {E W : Type}
    (isFemale : E → Prop) (sIdx : Nat)
    (g : Core.Assignment E) (gs : Intensional.Variables.SitAssignment W) :
    Semantics.Definiteness.interpret
        (Semantics.Definiteness.Description.ofPresupType .uniqueness
          ((fun _ _ x => (femSem isFemale).presup x) :
            Intensional.Variables.DenotGS E W .et) sIdx) g gs
      = Semantics.Definiteness.russellIota (E := E) (fun x => isFemale x) :=
  Semantics.Definiteness.interpret_unique
    ((fun _ _ x => isFemale x) : Intensional.Variables.DenotGS E W .et) sIdx g gs

end PatelGroszGrosz2017
