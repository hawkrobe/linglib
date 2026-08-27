import Linglib.Syntax.Minimalist.Features
import Linglib.Fragments.Basque.Pronouns
import Linglib.Fragments.Magahi.Pronouns
import Linglib.Fragments.Tamil.Pronouns
import Linglib.Fragments.Romance.Galician.Pronouns
import Linglib.Data.Examples.AlokBhalla2026

/-!
# Alok and Bhalla (2026): allocutivity and the syntax of honorifics

A review of allocutive marking — verbal encoding of the addressee's features —
and of honorifics as syntactic features. Allocutive markers come in three
morphosyntactic kinds (agreement morphemes, addressee-hosting heads, clitic
pronouns), distribute over clause types in three ways (root only, embedded-root
contexts, freely in finite clauses), and are sourced from three loci where the
discourse participants are represented (the speech-act phrase, the finiteness
phrase, an applicative-like addressee phrase). Honorific features are
relational: [iHON] on a nominal phrase orders the speaker against the referent,
so every phrase in a clause sets its own level.

The marker kinds, distributions and loci are recorded per language as the
review reports them, and the example rows check the distributional claims
through each language's assignment. The Magahi rows check the fused
subject/addressee suffixes against the Fragment's paradigm, the matching of
second-person pronouns with the marker, and the independence of third-person
levels; the Hindi rows check the plural-agreement route to subject
honorification. The old survey table this file used to carry was not the
paper's Table 1, which is Tamil number marking.

## References

* [alok-bhalla-2026]
* [alok-2020]
* [portner-pak-zanuttini-2019]
* [speas-tenny-2003]
* [dayal-2025]
* [wang-r-2023]
-/

namespace AlokBhalla2026

open Minimalist Data.Examples

/-! ### Languages -/

/-- The allocutive languages the review discusses at the level of marker type
    and distribution. -/
inductive Language where
  | souletinBasque
  | innovativeSouthernBasque
  | magahi
  | tamil
  | korean
  | japanese
  | galician
  deriving DecidableEq, Repr

def Language.glottocode : Language → String
  | .souletinBasque => "soul1243"
  | .innovativeSouthernBasque => "basq1248"
  | .magahi => "maga1260"
  | .tamil => "tami1289"
  | .korean => "kore1280"
  | .japanese => "nucl1643"
  | .galician => "gali1258"

/-- The language of a row, for the languages with a profile. -/
def languageOf : String → Option Language
  | "soul1243" => some .souletinBasque
  | "maga1260" => some .magahi
  | "tami1289" => some .tamil
  | "kore1280" => some .korean
  | "nucl1643" => some .japanese
  | "gali1258" => some .galician
  | _ => none

/-! ### The morphosyntax of the marker -/

/-- The three kinds of allocutive marker: an agreement reflex on a functional
    head, a head that itself hosts the addressee, a clitic spelling out the
    addressee. -/
inductive MarkerType where
  | agreement
  | head
  | clitic
  deriving DecidableEq, Repr

/-- The analyses the review reports for each language; Basque and Japanese are
    contested. -/
def analyses : Language → List MarkerType
  | .souletinBasque | .innovativeSouthernBasque => [.agreement, .clitic]
  | .magahi | .tamil => [.agreement]
  | .korean => [.head]
  | .japanese => [.agreement, .head]
  | .galician => [.clitic]

/-- Register level named by a row's honorific feature. -/
def levelOf : String → Option Features.Register.Level
  | "nh" => some .informal
  | "h" => some .neutral
  | "hh" => some .formal
  | _ => none

/-- Magahi's suffixes are composites of the subject's and the addressee's
    honorific features (exx 2–6, 42–43): every row's marker is the Fragment's
    fused form for its two levels. -/
theorem magahi_fusion_rows :
    ∀ row ∈ Examples.all, row.language = "maga1260" → ∀ m ∈ row.feature? "marker",
      ∀ s ∈ (row.feature? "subject").bind levelOf, ∀ a ∈ (row.feature? "addressee").bind levelOf,
        Magahi.Pronouns.allocutive s a = some m := by
  decide +kernel

/-- The Souletin markers of ex 1 and the Galician clitics are the Fragments'. -/
theorem marker_rows :
    ∀ row ∈ Examples.all, ∀ m ∈ row.feature? "marker",
      (row.language = "soul1243" → m ∈ Basque.Pronouns.allocutiveMarkers.map (·.form)) ∧
      (row.language = "gali1258" → m ∈ Galician.Pronouns.allocutiveClitics.map (·.form)) ∧
      (row.language = "tami1289" → m = Tamil.Pronouns.pluralSuffix) := by
  decide +kernel

/-! ### Distribution and loci -/

/-- The three distributional types: root clauses only; also embedded-root
    contexts (complements of saying, reason clauses); freely in finite embedded
    clauses. -/
inductive Distribution where
  | rootOnly
  | embeddedRoot
  | free
  deriving DecidableEq, Repr

def distribution : Language → Distribution
  | .souletinBasque | .korean => .rootOnly
  | .japanese | .tamil => .embeddedRoot
  | .magahi | .innovativeSouthernBasque | .galician => .free

/-- Where the discourse participants are represented: the speech-act phrase,
    the finiteness phrase, or an applicative-like addressee phrase whose
    licensing is language-specific. -/
inductive Locus where
  | sa
  | fin
  | addr
  deriving DecidableEq, Repr

/-- The loci the review's sources assign; Tamil's two marker positions support
    two loci, Japanese's complementizer-sensitive embedding an addressee
    phrase. -/
def loci : Language → List Locus
  | .souletinBasque | .korean => [.sa]
  | .magahi => [.fin]
  | .tamil => [.sa, .fin]
  | .japanese => [.sa, .addr]
  | .innovativeSouthernBasque | .galician => [.addr]

/-- A clause context. -/
inductive Context where
  | root
  | embeddedRoot
  | finiteNonRoot
  | nonfinite
  deriving DecidableEq, Repr

/-- The contexts each distributional type admits. -/
def Distribution.Admits : Distribution → Context → Prop
  | .rootOnly, c => c = .root
  | .embeddedRoot, c => c = .root ∨ c = .embeddedRoot
  | .free, c => c ≠ .nonfinite

instance : DecidableRel Distribution.Admits := λ d c ↦ by
  cases d <;> simp [Distribution.Admits] <;> infer_instance

/-- The speech-act phrase is available only in root and embedded-root contexts;
    languages sourced from it alone are at most of the embedded-root type. -/
theorem sa_only_restricted (l : Language) (h : loci l = [.sa]) :
    distribution l ≠ .free := by
  cases l <;> simp_all [loci, distribution]

/-- The context an embedding feature names. -/
def contextOf : String → Option Context
  | "saying" | "reason" => some .embeddedRoot
  | "complement" | "believe" | "perceptual" | "relative" | "nounComplement" | "factive"
  | "wh" => some .finiteNonRoot
  | "nonfinite" => some .nonfinite
  | _ => none

/-- Embedded rows: a marker in the embedded clause is grammatical exactly where
    the language's distributional type admits the context (exx 12–18, 21,
    30–31); rows whose alternatives add the marker are read through those
    alternatives. -/
theorem distribution_rows :
    ∀ row ∈ Examples.all, ∀ l ∈ languageOf row.language,
      ∀ ctx ∈ (row.feature? "embedding").bind contextOf, ctx ≠ .nonfinite →
        (row.judgment = .acceptable ↔ (distribution l).Admits ctx) := by
  decide +kernel

/-- Nonfinite complements carry the marker exactly in languages with an
    addressee phrase below the finiteness phrase: Galician's infinitives (ex 32)
    against Magahi's nonfinite clauses (ex 30), where the finiteness locus
    demands a finite clause. -/
theorem nonfinite_rows :
    ∀ row ∈ Examples.all, ∀ l ∈ languageOf row.language,
      row.feature? "embedding" = some "nonfinite" →
        (row.judgment = .acceptable ∧ row.alternatives = [] ↔ .addr ∈ loci l) ∧
        (∀ alt ∈ row.alternatives, alt.2 = .acceptable ↔ .addr ∈ loci l) := by
  decide +kernel

/-- Japanese *-mas-* in nonroot complements is sensitive to the complementizer:
    licensed under *koto* and *yooni*, not under *to* (ex 33). -/
theorem japanese_complementizer_rows :
    ∀ row ∈ Examples.all, row.language = "nucl1643" →
      ∀ c ∈ row.feature? "embedding", c ∈ ["koto", "yooni", "to"] →
        (row.judgment = .acceptable ↔ c ≠ "to") := by
  decide +kernel

/-! ### Honorific features -/

/-- The social ordering [iHON] establishes between the speaker and a referent:
    ⟦iHON⟧ = λx. S ≺ x with ≺ one of ≥, <, <<. -/
inductive SocialOrder where
  | ge
  | lt
  | ll
  deriving DecidableEq, Repr

/-- The honorific level a social ordering determines. -/
def levelOfOrder : SocialOrder → HonLevel
  | .ge => .nh
  | .lt => .h
  | .ll => .hh

/-- The ordering a level encodes. -/
def orderOfLevel : HonLevel → SocialOrder
  | .nh => .ge
  | .h => .lt
  | .hh => .ll

@[simp] theorem levelOfOrder_orderOfLevel (l : HonLevel) : levelOfOrder (orderOfLevel l) = l := by
  cases l <;> rfl

@[simp] theorem orderOfLevel_levelOfOrder (o : SocialOrder) :
    orderOfLevel (levelOfOrder o) = o := by
  cases o <;> rfl

/-- [portner-pak-zanuttini-2019]'s Korean speech-style particles as bundles of
    the speaker–addressee status and discourse formality (ex 34). -/
def portnerParticle : SocialOrder → Bool → Option String
  | .lt, true => some "supnita"
  | .lt, false => some "eyo"
  | .ge, false => some "e"
  | _, _ => none

/-- The status a row's feature names. -/
def orderOf : String → Option SocialOrder
  | "ge" => some .ge
  | "lt" => some .lt
  | "ll" => some .ll
  | _ => none

/-- The Korean rows with status and formality features carry the particle the
    bundle realizes (exx 8a, 8b, 8d). -/
theorem korean_particle_rows :
    ∀ row ∈ Examples.all, ∀ o ∈ (row.feature? "status").bind orderOf,
      ∀ f ∈ row.feature? "formal",
        portnerParticle o (f = "+") = row.feature? "particle" := by
  decide +kernel

/-- Second-person pronouns in a Magahi clause share one level, and match the
    allocutive marker's addressee level (exx 41–43). -/
theorem magahi_second_person_rows :
    ∀ row ∈ Examples.all, row.language = "maga1260" → row.judgment = .acceptable →
      ∀ p ∈ row.feature? "pronoun2",
        (∀ q ∈ row.feature? "pronoun2Other", q = p) ∧
        ∀ a ∈ row.feature? "addressee", a = p := by
  decide +kernel

/-- A mismatch between two second-person pronouns is out (ex 41). -/
theorem magahi_mismatch_row :
    ∀ row ∈ Examples.all, ∀ p ∈ row.feature? "pronoun2", ∀ q ∈ row.feature? "pronoun2Other",
      q ≠ p → row.judgment = .unacceptable := by
  decide +kernel

/-- Third-person levels are set independently: the same nonhonorific-subject
    verb hosts a nonhonorific and an honorific object pronoun (ex 44), and one
    clause carries three distinct levels (ex 45) — the case for [iHON] on every
    nominal phrase rather than one status feature per clause. -/
theorem third_person_independent :
    (∃ r ∈ Examples.all, ∃ s ∈ Examples.all,
      r.feature? "pronoun3" = some "nh" ∧ s.feature? "pronoun3" = some "h" ∧
      r.feature? "subject" = s.feature? "subject" ∧
      r.judgment = .acceptable ∧ s.judgment = .acceptable) ∧
    ∃ r ∈ Examples.all, r.feature? "pronoun2" = some "hh" ∧
      r.feature? "pronoun3" = some "nh" ∧ r.feature? "pronoun3Other" = some "h" ∧
      r.judgment = .acceptable := by
  decide +kernel

/-- Hindi has no allocutive marking; an honorific subject co-opts plural
    agreement (ex 48). -/
theorem hindi_plural_rows :
    ∀ row ∈ Examples.all, row.language = "hind1269" →
      (row.feature? "agreement" = some "pl" ↔
        row.feature? "subjectNumber" = some "pl" ∨ row.feature? "subjectHon" = some "h") := by
  decide +kernel

end AlokBhalla2026
