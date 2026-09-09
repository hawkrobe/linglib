import Linglib.Data.Examples.ElkinsTorrenceBrown2026
import Linglib.Syntax.Minimalist.ExtendedProjection.ClauseSpine
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Morphology.DistributedMorphology.VocabularyInsertion.FeatureBundle

/-!
# Elkins, Torrence and Brown (2026): Wh-movement paths and oblique extraction in Mam

This file formalizes [elkins-torrence-brown-2026]'s analysis of the movement enclitic =(y)a' of
San Juan Ostuncalco Mam (Mayan), which optionally appears on the predicate, and on any directional
auxiliary, when an instrument, benefactive, dative, locative, reason, purpose or manner adjunct is
extracted, but not with absolutive or ergative arguments ([aissen-2017]'s Ergative Extraction
Constraint sends the agent through an antipassive) or with temporals. The enclitic may occur once
per Voice⁰ and Dir⁰ of a clause and, in long-distance extraction, once per clause along the
dependency: in the embedded clause exactly when that clause is at least VoiceP-sized, so on both
predicates over a full CP or an aspectless VoiceP complement, on the matrix predicate only over a
nonfinite VP complement, and on the embedded predicate only in an embedded question. The authors
analyse the enclitic as the spellout of Ā-agreement between the extracted adjunct and the
[Ā]-bearing heads Voice⁰ and Dir⁰ it passes through under Relativized-Minimality successive
cyclicity ([rizzi-1990], [abels-2003]): Attract Closest forces the mover through the specifier of
each intervening [Ā]-bearer, each Voice⁰ or Dir⁰ copies the [obl] Case feature the mover receives
from its relational noun, and the bundle [Ā, obl] is realized as =(y)a' or as ∅. The rival Chain
Reduction via Substitution of [mendes-ranero-2021] for the K'ichean fronting particle *wi*, which
spells out lower copies at the base position and at each Spec,CP stopover and so derives the
Fronting Particle Generalization, predicts a single reflex within a clause, none in the matrix
clause over an aspectless complement, and one inside a nonfinite complement, all contrary to the
Mam data; DP-intervention leapfrogging ([keine-zeijlstra-2025]) predicts at most one reflex per
intervening argument, contrary to a clause with three; and an Agent-Focus-like analysis fails
because the enclitic co-occurs with the passive and appears in every clause of the path while the
antipassive is confined to the clause of origin. The two systems also differ in which adjuncts
trigger the reflex: reasons, purposes and manners do in Mam but are high adjuncts without [appl]
in K'ichean, and temporals trigger neither.

## Implementation notes

* Clause sizes are the substrate's `ClauseSpine`s, full CP, VoiceP and bare VP, with the
  directional head `Head.dir`, a Mayan-specific category above VoiceP, spliced in by `spine`. A
  dependency is the list of clauses the mover crosses, bottom-up; its `path` is the [Ā]-bearers of
  those clauses and its `sites` the Voice and Dir heads among them, so the reflex in a clause is
  decided by whether the clause projects Voice (`licensed_iff_projects_voice`). The rival
  mechanisms are predicates on the same dependencies, and the rows discriminate them.
* The Agree-and-insertion step is the substrate's `applyAgree` and `spellout` on a Voice head with
  an unvalued [oblique] probe and the vocabulary item (46a); the null exponent (46b) is the
  independent optionality of each site, `patterns`.
* [obl] on the movers is the article's featural hypothesis (§1.3, §4.2, §5.3): relational nouns
  assign it, the locative and manner wh-words are assumed to acquire it, temporals lack it.
* The examples are `Data.Examples.ElkinsTorrenceBrown2026`; the K'iche' rows are
  [mendes-ranero-2021]'s as reported there. The variety is SJO Mam; [scott-2023]'s San Juan
  Atitán Mam is a distinct variety.

## References

* [elkins-torrence-brown-2026]
* [mendes-ranero-2021]
* [rizzi-1990]
* [abels-2003]
* [keine-zeijlstra-2025]
* [van-urk-2018]
* [scott-2023]
* [england-1989]
* [aissen-2017]
-/

namespace ElkinsTorrenceBrown2026

open Minimalist DistributedMorphology Data.Examples ElkinsTorrenceBrown2026.Examples
open scoped DistributedMorphology.VocabularyItem

/-! ### The extended verbal domain (§1.3) -/

/-- A head of the SJO Mam clausal spine: a head of the substrate spine, or a directional auxiliary
Dir⁰, the Mayan-specific head whose projection dominates VoiceP (8). -/
inductive Head
  | cat (c : Cat)
  | dir
  deriving DecidableEq, Repr

/-- A clause as its projected heads, bottom-up. -/
abbrev Spine := List Head

/-- A clause of the given size with `n` directionals above Voice (8). Nonfinite clauses, which lack
Voice, lack directionals (§3.4). -/
def spine (s : ClauseSpine) (n : ℕ) : Spine :=
  s.projectedHeads.flatMap λ c =>
    if c = .Voice then .cat .Voice :: List.replicate n .dir else [.cat c]

/-- The reduced K'ichean complement of [mendes-ranero-2021], an AspP without a CP layer (§5.1). -/
def aspP : ClauseSpine := ⟨[.V, .Appl, .v, .Voice, .Asp], by decide⟩

/-- The feature bearers of [Ā], (41) and (44): C⁰, Voice⁰ and Dir⁰. -/
def BearsA (h : Head) : Prop := h = .cat .C ∨ h = .cat .Voice ∨ h = .dir

instance : DecidablePred BearsA := λ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- The heads that copy the mover's [obl] and host the reflex, (45)–(46): Voice⁰ and Dir⁰. C⁰
attracts by [Ā] alone, so there is no C-domain reflex. -/
def HostsReflex (h : Head) : Prop := h = .cat .Voice ∨ h = .dir

instance : DecidablePred HostsReflex := λ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem HostsReflex.bearsA {h : Head} (hh : HostsReflex h) : BearsA h := Or.inr hh

/-! ### The movement path (§4.1–4.3) -/

/-- A dependency: the clauses the extracted adjunct crosses, bottom-up, the clause of origin
first. -/
abbrev Dependency := List Spine

/-- The movement path, (43): the [Ā]-bearing heads of the clauses crossed, bottom-up and tagged by
clause. By Attract Closest (39) the mover stops in the specifier of each. -/
def path (d : Dependency) : List (ℕ × Head) :=
  (List.range d.length).flatMap λ i =>
    ((d.getD i []).filter λ h => decide (BearsA h)).map (i, ·)

/-- The sites of the reflex: the Agree relations with Voice⁰ or Dir⁰ along the path (§4.2). -/
def sites (d : Dependency) : List (ℕ × Head) :=
  (path d).filter λ p => decide (HostsReflex p.2)

/-- =(y)a' is licensed in clause `i` of the dependency when the path has a site there. -/
def Licensed (d : Dependency) (i : ℕ) : Prop := i ∈ (sites d).map Prod.fst

instance (d : Dependency) (i : ℕ) : Decidable (Licensed d i) :=
  inferInstanceAs (Decidable (_ ∈ _))

theorem mem_path {d : Dependency} {i : ℕ} {h : Head} :
    (i, h) ∈ path d ↔ i < d.length ∧ h ∈ d.getD i [] ∧ BearsA h := by
  simp only [path, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨j, hj, h', ⟨hmem, hb⟩, rfl, rfl⟩
    exact ⟨hj, hmem, hb⟩
  · rintro ⟨hi, hmem, hb⟩
    exact ⟨i, hi, h, ⟨hmem, hb⟩, rfl, rfl⟩

/-- The reflex is licensed in a clause exactly when the clause contains a reflex host: every
Voice⁰ or Dir⁰ crossed is an [Ā]-bearer and so a stopover. -/
theorem licensed_iff {d : Dependency} {i : ℕ} :
    Licensed d i ↔ ∃ h ∈ d.getD i [], HostsReflex h := by
  simp only [Licensed, sites, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨j, h⟩, ⟨hp, hh⟩, rfl⟩
    exact ⟨h, (mem_path.mp hp).2.1, hh⟩
  · rintro ⟨h, hmem, hh⟩
    refine ⟨(i, h), ⟨mem_path.mpr ⟨?_, hmem, hh.bearsA⟩, hh⟩, rfl⟩
    by_contra hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hmem
    exact List.not_mem_nil hmem

/-- A clause of a given size contains a reflex host exactly when the size projects Voice, since
directionals come only with Voice. -/
theorem exists_hostsReflex_spine_iff (s : ClauseSpine) (n : ℕ) :
    (∃ h ∈ spine s n, HostsReflex h) ↔ .Voice ∈ s.projectedHeads := by
  simp only [spine, List.mem_flatMap]
  constructor
  · rintro ⟨h, ⟨c, hc, hmem⟩, hh⟩
    split at hmem
    · next hcv => exact hcv ▸ hc
    · next hcv =>
      rw [List.mem_singleton] at hmem
      rcases hh with rfl | rfl
      · exact absurd (Head.cat.inj hmem).symm hcv
      · exact Head.noConfusion hmem
  · intro hv
    exact ⟨.cat .Voice, ⟨.Voice, hv, by simp⟩, Or.inl rfl⟩

theorem projects_voice_iff (s : ClauseSpine) :
    s.projects .Voice = true ↔ .Voice ∈ s.projectedHeads := by
  simp [ClauseSpine.projects]

/-- Table 3: =(y)a' is licensed in a clause of the dependency exactly when that clause's size
projects Voice, so in full CP and aspectless complements but not in nonfinite ones (§3.3–3.4,
§4.3). -/
theorem licensed_iff_projects_voice {d : Dependency} {i : ℕ} {s : ClauseSpine} {n : ℕ}
    (hd : d.getD i [] = spine s n) : Licensed d i ↔ s.projects .Voice = true := by
  rw [licensed_iff, hd, exists_hostsReflex_spine_iff, projects_voice_iff]

/-! ### Multiple exponence (§3.1, §5.2) -/

/-- Within a clause the sites are Voice⁰ and each directional, (45): `n + 1` of them. -/
theorem sites_monoclausal (n : ℕ) :
    sites [spine .cP n] = (0, .cat .Voice) :: List.replicate n (0, .dir) := by
  simp [sites, path, spine, ClauseSpine.cP, BearsA, HostsReflex, List.map_replicate]

theorem sites_monoclausal_length (n : ℕ) : (sites [spine .cP n]).length = n + 1 := by
  rw [sites_monoclausal]
  simp

/-- (46b): each site is independently realized as =(y)a' or as ∅, so the surface patterns of a
dependency are the sublists of its sites. -/
def patterns (d : Dependency) : List (List (ℕ × Head)) := (sites d).sublists

/-- (22): with one directional the enclitic may appear on both hosts, on neither, or on either
alone, four combinations. -/
theorem patterns_length_22 : (patterns [spine .cP 1]).length = 4 := by decide

/-- (63): with two directionals there are three sites although the intransitive clause has a
single argument DP, so leapfrogging over intervening DPs ([keine-zeijlstra-2025]) yields too few
stopovers (§5.2). -/
theorem sites_exceed_interveners : 1 < (sites [spine .cP 2]).length := by
  rw [sites_monoclausal_length]
  decide

/-! ### The rival mechanisms (§3.6, §5.1) -/

/-- Chain Reduction via Substitution, (55)–(57): the reflex spells out the lower copies of the
mover, the base copy in the clause of origin and the intermediate copy in each Spec,CP crossed,
which linearizes onto the predicate of the next clause up. -/
def CopyLicensed (d : Dependency) (i : ℕ) : Prop :=
  i = 0 ∨ (0 < i ∧ i < d.length ∧ .cat .C ∈ d.getD (i - 1) [])

instance (d : Dependency) (i : ℕ) : Decidable (CopyLicensed d i) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _ ∧ _))

/-- The Fronting Particle Generalization (54): over a single embedded clause, the matrix reflex is
contingent on the embedded clause projecting C. -/
theorem fpg (e m : Spine) : CopyLicensed [e, m] 1 ↔ .cat .C ∈ e := by
  simp [CopyLicensed]

/-- Applied to Mam, copy spellout allows a single reflex in a monoclausal dependency, whereas
Ā-agreement gives one per Voice⁰ and Dir⁰ (§3.1, §5.1). -/
theorem copy_single_site (n : ℕ) : (∀ i, CopyLicensed [spine .cP n] i → i = 0) ∧
    (sites [spine .cP n]).length = n + 1 :=
  ⟨λ i h => h.elim id λ h' => by
    have h1 := h'.1
    have h2 := h'.2.1
    simp only [List.length_singleton] at h2
    omega, sites_monoclausal_length n⟩

/-- Over an aspectless complement, (31): copy spellout predicts no matrix reflex, since the
complement has no Spec,CP, whereas Ā-agreement predicts one at the matrix Voice⁰. -/
theorem copy_fails_aspectless :
    ¬ CopyLicensed [spine .voiceP 0, spine .cP 0] 1 ∧
      Licensed [spine .voiceP 0, spine .cP 0] 1 := by
  decide

/-- Over a nonfinite complement, (34): copy spellout predicts a reflex in the complement, where
the base copy sits, whereas Ā-agreement finds no Voice⁰ there. -/
theorem copy_fails_nonfinite :
    CopyLicensed [spine .bareVP 0, spine .cP 0] 0 ∧
      ¬ Licensed [spine .bareVP 0, spine .cP 0] 0 := by
  decide

/-- Conversely, Ā-agreement through the verbal domain would put a matrix reflex over a K'ichean
AspP complement, (53), against the Fronting Particle Generalization; copy spellout does not. -/
theorem agree_fails_fpg :
    Licensed [spine aspP 0, spine .cP 0] 1 ∧ ¬ CopyLicensed [spine aspP 0, spine .cP 0] 1 := by
  decide

/-- An Agent-Focus-like reflex is confined to the clause of origin, as the antipassive is in
(38); =(y)a' is licensed in every clause of the path, (24). -/
theorem origin_only_fails : Licensed [spine .cP 0, spine .cP 0] 1 ∧ (1 : ℕ) ≠ 0 := by
  decide

/-! ### Which movers trigger the reflex (§2, §5.3) -/

/-- The adjunct classes of §2.2. -/
inductive Adjunct
  | instrument
  | benefactive
  | dative
  | locative
  | reason
  | purpose
  | manner
  | temporal
  deriving DecidableEq, Fintype

/-- The article's featural hypothesis (9), footnotes 3 and 12, §5.3: every adjunct class but the
temporals bears the [obl] Case feature that Voice⁰ and Dir⁰ copy. -/
def Adjunct.BearsObl (a : Adjunct) : Prop := a ≠ .temporal

instance : DecidablePred Adjunct.BearsObl := λ _ => inferInstanceAs (Decidable (_ ≠ _))

/-- [mendes-ranero-2021]'s low adjuncts, merged in Spec,ApplP with [appl], which alone trigger
*wi* (§5.3). -/
def Adjunct.IsLow (a : Adjunct) : Prop :=
  a = .instrument ∨ a = .benefactive ∨ a = .dative ∨ a = .locative

instance : DecidablePred Adjunct.IsLow := λ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- Table 4: the Mam and K'ichean triggers differ exactly at reasons, purposes and manners. -/
theorem table4 (a : Adjunct) :
    ¬ (a.BearsObl ↔ a.IsLow) ↔ a = .reason ∨ a = .purpose ∨ a = .manner := by
  revert a
  decide

/-- What is extracted, if anything: an absolutive argument, an ergative argument, or an adjunct. -/
inductive Mover
  | none
  | absolutive
  | ergative
  | adjunct (a : Adjunct)
  deriving DecidableEq

/-- Only an adjunct with [obl] feeds the reflex: absolutives and ergatives lack it (§4.2). -/
def Mover.BearsObl : Mover → Prop
  | .adjunct a => a.BearsObl
  | _ => False

instance : ∀ m : Mover, Decidable m.BearsObl
  | .adjunct a => inferInstanceAs (Decidable a.BearsObl)
  | .none => inferInstanceAs (Decidable False)
  | .absolutive => inferInstanceAs (Decidable False)
  | .ergative => inferInstanceAs (Decidable False)

/-- The reflex is realizable in clause `i` when the mover bears [obl] and the path has a site
there. -/
def Realizable (m : Mover) (d : Dependency) (i : ℕ) : Prop := m.BearsObl ∧ Licensed d i

instance (m : Mover) (d : Dependency) (i : ℕ) : Decidable (Realizable m d i) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Agree and insertion (§4.2) -/

/-- Voice⁰ of the analysis: an [Ā]-bearing head with an unvalued [oblique] probe that Agree with
the mover values, (45a). -/
def voice : Voice.Head :=
  { flavor := .agentive, hasD := true, features := .ofGramFeatures [.unvalued (.oblique false)] }

/-- (46a): the vocabulary item realizing the valued [obl] on Voice⁰ or Dir⁰. -/
def eqYa : VocabularyItem GramFeature String := [.valued (.oblique true)] ⟷ "=(y)a'"

/-- Agree with an [obl] mover followed by insertion yields the enclitic. -/
theorem agree_spellout :
    (applyAgree voice.features (.ofGramFeatures [.valued (.oblique true)]) .oblique).bind
      (spellout [eqYa]) = some "=(y)a'" := by
  decide

/-- A mover without [obl], an absolutive argument or a temporal, transmits nothing to Voice⁰. -/
theorem no_obl_no_agree : applyAgree voice.features ⊥ .oblique = none := by
  decide

/-! ### The rows (§2, §3, §5) -/

/-- The movers as named in the rows. -/
def moverTable : List (String × Mover) :=
  [("none", .none), ("absolutive", .absolutive), ("ergative", .ergative),
    ("instrument", .adjunct .instrument), ("benefactive", .adjunct .benefactive),
    ("dative", .adjunct .dative), ("locative", .adjunct .locative), ("reason", .adjunct .reason),
    ("purpose", .adjunct .purpose), ("manner", .adjunct .manner), ("temporal", .adjunct .temporal)]

/-- Whether the reflex may appear, as recorded in the rows. -/
def reflexTable : List (String × Bool) := [("licensed", true), ("blocked", false)]

/-- The monoclausal Mam rows of §2 and §3.5–3.6: the enclitic is licensed exactly for the movers
bearing [obl]. -/
theorem mamRows_realizable :
    ∀ e ∈ [ex_10b, ex_11b, ex_12b, ex_13a, ex_13b, ex_14b, ex_15b, ex_16b, ex_17b, ex_18b, ex_19b,
        ex_20b, ex_21b, ex_35c, ex_37, ex_65],
      ∀ m, e.parse? "mover" moverTable = some m → ∀ b, e.parse? "reflex" reflexTable = some b →
        (b = true ↔ Realizable m [spine .cP 0] 0) := by
  decide

/-- The K'iche' rows (51) and (64): *wi* is licensed exactly for the low adjuncts. -/
theorem kicheRows_low :
    ∀ e ∈ [ex_51, ex_64], ∀ a, e.parse? "mover" moverTable = some (.adjunct a) →
      ∀ b, e.parse? "reflex" reflexTable = some b → (b = true ↔ a.IsLow) := by
  decide

/-- The rows with directionals, (22) and (63): one host per Voice⁰ and directional. -/
theorem directionalRows_sites :
    ∀ e ∈ [ex_22, ex_63], ∀ n, e.nat? "directionals" = some n →
      ∀ k, e.nat? "hosts" = some k → (sites [spine .cP n]).length = k := by
  decide

/-- The clause sizes as named in the rows. -/
def sizeTable : List (String × ClauseSpine) :=
  [("cP", .cP), ("voiceP", .voiceP), ("bareVP", .bareVP), ("aspP", aspP)]

/-- The dependency of a long-distance row: the embedded clause and, when the wh-expression lands
in the matrix clause, the full-CP matrix clause above it. -/
def dependencyOf (e : LinguisticExample) : Option Dependency :=
  (e.parse? "embeddedSize" sizeTable).bind λ s =>
    e.parse? "landing" [("embedded", [spine s 0]), ("matrix", [spine s 0, spine .cP 0])]

/-- The long-distance Mam rows (24), (26), (31) and (34), Table 3: the reflex in each clause
follows from Ā-agreement along the path. -/
theorem mamLD_licensed :
    ∀ e ∈ [ex_24, ex_26, ex_31, ex_34], ∀ d, dependencyOf e = some d →
      (∀ b, e.parse? "embeddedReflex" reflexTable = some b → (b = true ↔ Licensed d 0)) ∧
        ∀ b, e.parse? "matrixReflex" reflexTable = some b → (b = true ↔ Licensed d 1) := by
  decide

/-- The long-distance K'iche' rows (52) and (53) follow from copy spellout. -/
theorem kicheLD_copy :
    ∀ e ∈ [ex_52, ex_53], ∀ d, dependencyOf e = some d →
      (∀ b, e.parse? "embeddedReflex" reflexTable = some b → (b = true ↔ CopyLicensed d 0)) ∧
        ∀ b, e.parse? "matrixReflex" reflexTable = some b → (b = true ↔ CopyLicensed d 1) := by
  decide

end ElkinsTorrenceBrown2026
