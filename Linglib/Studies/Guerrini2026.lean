import Linglib.Semantics.Kinds.NominalMappingParameter
import Linglib.Semantics.Plurality.Distributivity
import Linglib.Semantics.Plurality.Cumulativity
import Linglib.Studies.TesslerGoodman2019
import Linglib.Studies.Longobardi2001
import Linglib.Studies.Cohen1999
import Linglib.Studies.Nickel2009
import Linglib.Data.Examples.Guerrini2026

/-!
# [guerrini-2026]: Distributive kind predication

Janek Guerrini, "Distributive kind predication", *Natural Language Semantics*
34:85–136 (2026).

## Thesis

Generalizations with kind-denoting plurals (English bare plurals, Italian
definite plurals) are structurally **ambiguous** — not because `Gen` has a
complex semantics, but because the kind-denoting plural licenses parses with no
`Gen` at all: Bona Fide Generic (BFG: kind restricts `Gen`, law-like), and the
`Gen`-free Distributive Kind Predication (DKP: `DIST` over the kind at `s₀`,
accidental), Cumulative Kind Predication (CKP: `**`, §4), and Derived Property
Predication (DPP: property → low-scoped `∃`, §5.3). Singular indefinites cannot
denote kinds (`∩` undefined for singular count nouns), so DKP/CKP never apply
and they are limited to BFG, explaining their narrower distribution (Table 1).

This file derives the LF typology from the shared Chierchia kind-denotation
primitive ([chierchia-1998]), states the prevalence bridge to
[tessler-goodman-2019], and contrasts the non-quantificational DKP/CKP analyses
with the quantificational rivals [cohen-1999a] and [nickel-2009]. Empirical
stimuli are typed rows in `Data/Examples/Guerrini2026.json` (`Examples.all`).
-/

namespace Guerrini2026

open Semantics.Kinds.NMP (NominalMapping NominalDenotation CanDenoteKind downDefinedFor)
open Semantics.Plurality (distMaximal allSatisfy noneSatisfy)
open Data.Examples (LinguisticExample)

/-! ### The four LF parses -/

/-- The four LF parses of a sentence with a kind-denoting plural (diagram (145)).
    The first three require kind denotation; the fourth requires property
    denotation. Singular indefinites access only `bonaFideGeneric`. -/
inductive GeneralizationLF
  | bonaFideGeneric      -- kind restricts `Gen`; structure (29)/(19)
  | distributiveKindPred -- `DIST` over the kind at `s₀`; structure (30)
  | cumulativeKindPred   -- `**` over the kind at `s₀`; §4
  | existentialDPP       -- property → low-scoped `∃`; structure (105b)
  deriving DecidableEq, Repr

/-- BFG is law-like (modal `Gen`); the three `Gen`-free parses are accidental
    (DPP, an existential episodic reading, is not a generalization but groups
    with the non-generic parses here). -/
def lfFlavor : GeneralizationLF → Bool  -- `true` = law-like, `false` = accidental
  | .bonaFideGeneric => true
  | _                => false

/-- Whether a parse involves the silent quantificational adverb `Gen`. Only BFG
    does, so only BFG supports Quantificational Variability Effects and is
    subject to [tessler-goodman-2019]'s prevalence inference. -/
def involvesGen : GeneralizationLF → Bool
  | .bonaFideGeneric => true
  | _                => false

/-- Only the Bona Fide Generic parse involves `Gen`, hence QVEs and threshold
    inference (examples (8), (90), (92)). -/
theorem only_bfg_involves_gen (lf : GeneralizationLF) :
    involvesGen lf = true ↔ lf = .bonaFideGeneric := by cases lf <;> simp [involvesGen]

/-! ### The named operators (foundational by construction)

DKP is `DIST` over the kind extension; CKP is the cumulative operator `**`. Both
are the theory-layer operators under the paper's names, so theorems about them
are theorems about `distMaximal` / `Cumulative`. -/

/-- Distributive Kind Predication: distribute `P` over the kind's extension at
    `s₀` (structure (30): `∀y(y ≤ ∩lions_{s₀}) → ⟦hunt⟧_{s₀}(y)`). -/
abbrev distributiveKindPred {Atom W : Type} (kindExt : W → Finset Atom)
    (P : Atom → W → Prop) [∀ a w, Decidable (P a w)] (s₀ : W) : Prop :=
  distMaximal P (kindExt s₀) s₀

/-- Cumulative Kind Predication: the cumulative operator `**` relates the kind
    extension to a set of locations (§4, structure (62)). -/
abbrev cumulativeKindPred {Atom Loc : Type} (R : Atom → Loc → Prop)
    (kindExt : Finset Atom) (locations : Finset Loc) : Prop :=
  Semantics.Plurality.Cumulativity.Cumulative R kindExt locations

/-! ### Nominal Mapping and denotation (diagram (145), §5.3) -/

/-- Cross-linguistic nominal forms. -/
inductive NominalExpression
  | englishBarePlural | italianDefinitePlural | italianBarePlural
  deriving DecidableEq, Repr

/-- The Nominal Mapping Parameter ([chierchia-1998]) per nominal form. -/
def nominalMapping : NominalExpression → NominalMapping
  | .englishBarePlural     => .argAndPred
  | .italianDefinitePlural => .predOnly
  | .italianBarePlural     => .predOnly

/-- Whether an overt determiner D is present (Italian definite plural alone). -/
def HasD : NominalExpression → Prop
  | .italianDefinitePlural => True
  | _                      => False

instance : DecidablePred HasD := fun ne => by cases ne <;> unfold HasD <;> infer_instance

/-- Available denotations per nominal form. Kind denotation from `CanDenoteKind`;
    property denotation from the parameter + D-status (`predOnly` + D maps to a
    kind, blocking the property reading). -/
def CanDenote (ne : NominalExpression) : NominalDenotation → Prop
  | .kind     => CanDenoteKind (nominalMapping ne) (HasD ne)
  | .property => match nominalMapping ne with
    | .argOnly    => False
    | .argAndPred => True
    | .predOnly   => ¬ HasD ne

instance : ∀ ne nd, Decidable (CanDenote ne nd) := fun ne nd => by
  cases nd <;> unfold CanDenote
  · infer_instance
  · cases ne <;> unfold nominalMapping <;> infer_instance

/-- Kind denotation enables DKP and CKP; property denotation enables DPP; BFG is
    always available (kind or property can restrict `Gen`). Diagram (145). -/
def LFAvailable (ne : NominalExpression) : GeneralizationLF → Prop
  | .bonaFideGeneric      => True
  | .distributiveKindPred => CanDenote ne .kind
  | .cumulativeKindPred   => CanDenote ne .kind
  | .existentialDPP       => CanDenote ne .property

instance : ∀ ne lf, Decidable (LFAvailable ne lf) := fun ne lf => by
  cases lf <;> unfold LFAvailable <;> infer_instance

/-- English BPs are ambiguous (kind and property); Italian definite plurals
    denote kinds only; Italian bare plurals denote properties only. -/
theorem nominal_denotations :
    (CanDenote .englishBarePlural .kind ∧ CanDenote .englishBarePlural .property) ∧
    (CanDenote .italianDefinitePlural .kind ∧ ¬ CanDenote .italianDefinitePlural .property) ∧
    (¬ CanDenote .italianBarePlural .kind ∧ CanDenote .italianBarePlural .property) :=
  ⟨⟨trivial, trivial⟩, ⟨trivial, fun h => h trivial⟩, ⟨id, id⟩⟩

/-- The four LF paths of diagram (145): English BPs access all four; Italian
    definite plurals the kind paths (no DPP); Italian bare plurals the property
    paths (no DKP/CKP). -/
theorem diagram_145_four_paths :
    (LFAvailable .englishBarePlural .bonaFideGeneric ∧
      LFAvailable .englishBarePlural .distributiveKindPred ∧
      LFAvailable .englishBarePlural .cumulativeKindPred ∧
      LFAvailable .englishBarePlural .existentialDPP) ∧
    (LFAvailable .italianDefinitePlural .distributiveKindPred ∧
      ¬ LFAvailable .italianDefinitePlural .existentialDPP) ∧
    (¬ LFAvailable .italianBarePlural .distributiveKindPred ∧
      LFAvailable .italianBarePlural .existentialDPP) :=
  ⟨⟨trivial, trivial, trivial, trivial⟩, ⟨trivial, fun h => h trivial⟩, ⟨id, id⟩⟩

/-! ### Table 1: distribution of generalizations -/

/-- Nominal form in a generalization. -/
inductive NominalForm
  | kindDenotingPlural | singularIndefinite
  deriving DecidableEq, Repr

/-- Table 1: kind-denoting plurals appear in both flavors; singular indefinites
    only in law-like ones. (`true` = felicitous; the kind/law-like cell uses
    `lfFlavor`-style booleans.) -/
def table1 : NominalForm → Bool → Bool  -- second arg: `true` = law-like flavor
  | .kindDenotingPlural, _    => true
  | .singularIndefinite, b    => b

/-- Singular indefinites lack the accidental flavor — the end of a four-step
    chain: `∩` undefined for singular count nouns ⇒ no kind denotation ⇒ no
    DKP/CKP ⇒ only BFG ⇒ only law-like. -/
theorem singular_no_accidental :
    downDefinedFor .count false = false ∧
    (∀ lf : GeneralizationLF, lfFlavor lf = false →
      lf = .distributiveKindPred ∨ lf = .cumulativeKindPred ∨ lf = .existentialDPP) ∧
    table1 .singularIndefinite false = false :=
  ⟨rfl, fun lf h => by cases lf <;> simp_all [lfFlavor], rfl⟩

/-- Table 1 is derivable from LF availability + LF→flavor: English BPs have LFs
    of both flavors; property-only nominals have only BFG (law-like). -/
theorem table1_from_lf_structure :
    (∃ lf, LFAvailable .englishBarePlural lf ∧ lfFlavor lf = true) ∧
    (∃ lf, LFAvailable .englishBarePlural lf ∧ lfFlavor lf = false) ∧
    lfFlavor .bonaFideGeneric = true ∧
    ¬ LFAvailable .italianBarePlural .distributiveKindPred :=
  ⟨⟨.bonaFideGeneric, trivial, rfl⟩, ⟨.distributiveKindPred, trivial, rfl⟩, rfl, id⟩

/-! ### Homogeneity removal (Table 3, §3.3)

`DIST` and `Gen` each contribute homogeneity. `all` removes DIST-homogeneity;
`always` (a Q-adverb, = overt `Gen`) removes Gen-homogeneity. -/

/-- The adverb/quantifier that removes a homogeneity source. -/
inductive HomogeneityRemover | all | always deriving DecidableEq, Repr

/-- `all` targets `DIST`-homogeneity, `always` targets `Gen`-homogeneity. The
    boolean argument is `true` for DIST, `false` for Gen. -/
def removesHomogeneity : HomogeneityRemover → Bool → Bool
  | .all,    isDist => isDist
  | .always, isDist => !isDist

/-- Referential definite plurals (DIST only) accept `all` not `always`; singular
    indefinite generics (`Gen` only) accept `always` not `all`; kind-denoting
    plural generics (both, by ambiguity) accept both. -/
theorem table3 :
    (removesHomogeneity .all true = true ∧ removesHomogeneity .always true = false) ∧
    (removesHomogeneity .all false = false ∧ removesHomogeneity .always false = true) := by
  decide

/-! ### Subjunctive and aspect diagnostics (§3.5, §3.4) -/

/-- Italian mood on the relative clause modifying the subject DP. -/
inductive ItalianMood | indicative | subjunctive deriving DecidableEq, Repr

/-- The subjunctive is licensed only inside `Gen`'s restrictor, so it forces the
    BFG parse (example (44)); the indicative keeps all parses. -/
def lfAvailableWithMood : ItalianMood → GeneralizationLF → Bool
  | .indicative,  _                 => true
  | .subjunctive, .bonaFideGeneric  => true
  | .subjunctive, _                 => false

/-- The subjunctive disambiguates to BFG; the indicative preserves ambiguity. -/
theorem subjunctive_disambiguates (lf : GeneralizationLF) :
    lfAvailableWithMood .subjunctive lf = true ↔ lf = .bonaFideGeneric := by
  cases lf <;> simp [lfAvailableWithMood]

/-- VP aspect. Episodic VPs have no `Hab`/`Gen`, so BFG is unavailable and only
    the `Gen`-free parses survive — why episodic bare plurals get near-universal
    readings without generic quantification (§5). -/
inductive VPAspect | habitual | episodic deriving DecidableEq, Repr

/-- In episodic sentences BFG is unavailable; DKP/CKP/DPP remain. -/
def lfCompatibleWithAspect : VPAspect → GeneralizationLF → Bool
  | .habitual, _                 => true
  | .episodic, .bonaFideGeneric  => false
  | .episodic, _                 => true

/-- The episodic kind-plural advantage: DKP is available in episodics, BFG is
    not, and singular indefinites (`∩` undefined for singular count) lack DKP. -/
theorem episodic_kind_plural_advantage :
    lfCompatibleWithAspect .episodic .distributiveKindPred = true ∧
    CanDenote .englishBarePlural .kind ∧
    downDefinedFor .count false = false ∧
    lfCompatibleWithAspect .episodic .bonaFideGeneric = false :=
  ⟨rfl, trivial, rfl, rfl⟩

/-! ### Epistemic adjectives and singular kinds (§5.2.2, §6.2) -/

/-- Adjective reading: a nonlocal (propositional) reading blocks kind denotation,
    hence DKP (examples (99)–(104)). -/
inductive AdjReading | localReading | nonlocal deriving DecidableEq, Repr

/-- Only local adjective readings support kind predication. -/
def adjSupportsKind : AdjReading → Bool
  | .localReading => true
  | .nonlocal     => false

/-- Singular kind terms are atomic (following [barker-1992], [schwarzschild-1996],
    [dayal-2004]): `DIST` and `**` need pluralities, so only BFG is available —
    no accidental or cumulative readings (§6.2, examples (133)–(136)). -/
def singularKindLFAvailable : GeneralizationLF → Bool
  | .bonaFideGeneric => true
  | _                => false

/-- Singular kind terms support only law-like readings. -/
theorem singular_kind_law_like_only (lf : GeneralizationLF) :
    singularKindLFAvailable lf = true ↔ lf = .bonaFideGeneric := by
  cases lf <;> simp [singularKindLFAvailable]

/-! ### Prevalence bridge to [tessler-goodman-2019] (§3.6)

Threshold semantics applies to the BFG parse. The DKP parse has no `Gen`: its
truth conditions are extensional (`DIST` over the actual kind extension), hence
*stronger* than any threshold generic. Prevalence is the bridge quantity. -/

open TesslerGoodman2019 (genericMeaning GenThreshold)
open Semantics.Degree (deg thr)

/-- Prevalence of `P` among the atoms of an extension at `w`:
    `|{a ∈ ext | P a w}| / |ext|`. (Generalizes to
    `Quantification.prevalenceOn ext (fun _ => True) (P · w)`.) -/
def prevalenceAtWorld {Atom W : Type} (P : Atom → W → Prop) [∀ a w, Decidable (P a w)]
    (ext : Finset Atom) (w : W) : ℚ :=
  if ext.card = 0 then 0 else (ext.filter (fun a => P a w)).card / ext.card

/-- DKP is true (all actual kind members satisfy `P`) iff prevalence is 1: the
    extensional, non-generic truth condition of the DKP parse. -/
theorem dkp_true_iff_prevalence_one {Atom W : Type} (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (ext : Finset Atom) (w : W) (hne : ext.Nonempty) :
    distMaximal P ext w ↔ prevalenceAtWorld P ext w = 1 := by
  have hcard : ext.card ≠ 0 := Finset.card_ne_zero.mpr hne
  have hcardQ : (ext.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  simp only [distMaximal, prevalenceAtWorld, hcard, ↓reduceIte]
  constructor
  · intro hall
    have hfilt : ext.filter (fun a => P a w) = ext := by
      ext a; simp only [Finset.mem_filter, and_iff_left_iff_imp]; exact hall a
    rw [hfilt, div_self hcardQ]
  · intro hdiv
    have heq : ((ext.filter (fun a => P a w)).card : ℚ) = ext.card := by
      rwa [div_eq_iff hcardQ, one_mul] at hdiv
    have hceq : (ext.filter (fun a => P a w)).card = ext.card := by exact_mod_cast heq
    have hfilt : ext.filter (fun a => P a w) = ext :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ ext) (le_of_eq hceq.symm)
    intro a ha
    have hmem : a ∈ ext.filter (fun a => P a w) := by rw [hfilt]; exact ha
    exact (Finset.mem_filter.mp hmem).2

/-- DKP is determinately false iff prevalence is 0 (no kind member satisfies `P`). -/
theorem dkp_false_iff_prevalence_zero {Atom W : Type} (P : Atom → W → Prop)
    [∀ a w, Decidable (P a w)] (ext : Finset Atom) (w : W) :
    noneSatisfy P ext w ↔ prevalenceAtWorld P ext w = 0 := by
  by_cases hne : ext.Nonempty
  · have hcard : ext.card ≠ 0 := Finset.card_ne_zero.mpr hne
    have hcardQ : (ext.card : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
    simp only [noneSatisfy, prevalenceAtWorld, hcard, ↓reduceIte]
    constructor
    · intro hall
      have hfilt : ext.filter (fun a => P a w) = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro a ha
        rw [Finset.mem_filter] at ha
        exact hall a ha.1 ha.2
      rw [hfilt, Finset.card_empty, Nat.cast_zero, zero_div]
    · intro hdiv
      have heq : ((ext.filter (fun a => P a w)).card : ℚ) = 0 := by
        rw [div_eq_zero_iff] at hdiv; exact hdiv.resolve_right hcardQ
      have hceq : (ext.filter (fun a => P a w)).card = 0 := by exact_mod_cast heq
      have hfilt : ext.filter (fun a => P a w) = ∅ := Finset.card_eq_zero.mp hceq
      intro a ha hPa
      have hmem : a ∈ ext.filter (fun a => P a w) := Finset.mem_filter.mpr ⟨ha, hPa⟩
      rw [hfilt] at hmem
      exact absurd hmem (Finset.notMem_empty _)
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp [noneSatisfy, prevalenceAtWorld]

/-- DKP-true entails the BFG (threshold) reading at *every* threshold: prevalence
    100% exceeds them all. -/
theorem dkp_true_implies_generic_true_all_thresholds :
    ∀ θ : GenThreshold, genericMeaning θ (prevPct 100) = true := by decide

/-- The threshold-sensitive region is where the two parses do real work: at 70%
    prevalence the generic is true against a 60% threshold, false against 80%. -/
theorem dkp_gap_is_threshold_sensitive :
    genericMeaning (thrPct 60) (prevPct 70) = true ∧
    genericMeaning (thrPct 80) (prevPct 70) = false := by decide

/-- The parses can disagree: at 7-of-10 the DKP parse is a trivalent gap (not all,
    not none) while the BFG parse is true at a 60% threshold. -/
theorem parses_can_disagree :
    (¬ allSatisfy (fun (a : Fin 10) (_ : Fin 1) => a.val < 7) Finset.univ (0 : Fin 1)) ∧
    (¬ noneSatisfy (fun (a : Fin 10) (_ : Fin 1) => a.val < 7) Finset.univ (0 : Fin 1)) ∧
    genericMeaning (thrPct 60) (prevPct 70) = true := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Empirical predictions over the (21)–(136) stimuli

Stimuli are typed `LinguisticExample` rows in `Data/Examples/Guerrini2026.json`.
`featOf`/`readOf` project the paper-specific tags and reading-level judgments. -/

/-- A paper-feature value of an example row. -/
def featOf (r : LinguisticExample) (k : String) : Option String :=
  (r.paperFeatures.find? (·.1 == k)).map (·.2)

/-- A reading-level judgment of an example row. -/
def readOf (r : LinguisticExample) (n : String) : Option Features.Judgment :=
  (r.readings.find? (·.1 == n)).map (·.2)

/-- Table 1 over the (21)/(22) stimuli: kind-denoting plurals are felicitous in
    both flavors; singular indefinites are infelicitous in accidental ones. -/
theorem genericity_table1_data :
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "genericity" &&
        featOf r "nominalForm" == some "kindDenotingPlural")).all
        (·.judgment == .acceptable) = true ∧
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "genericity" &&
        featOf r "nominalForm" == some "singularIndefinite" &&
        featOf r "flavor" == some "accidental")).all
        (·.judgment == .unacceptable) = true := by decide

/-- Near-universal asymmetry across episodics (§5) and epistemic adjectives
    (§5.2.2): kind-denoting plurals and local adjectives get the near-universal
    (DKP) reading; singular indefinites and nonlocal adjectives do not. -/
theorem near_universal_tracks_kind :
    (Examples.all.filter (fun r => (featOf r "diagnostic" == some "episodic" ||
        featOf r "diagnostic" == some "epistemic-adj") &&
        (featOf r "nominalForm" == some "kindDenotingPlural" ||
         featOf r "adjReading" == some "local"))).all
        (readOf · "near-universal" == some .acceptable) = true ∧
    (Examples.all.filter (fun r => (featOf r "diagnostic" == some "episodic" ||
        featOf r "diagnostic" == some "epistemic-adj") &&
        (featOf r "nominalForm" == some "singularIndefinite" ||
         featOf r "adjReading" == some "nonlocal"))).all
        (readOf · "near-universal" == some .unacceptable) = true := by decide

/-- Accidental-reading asymmetry, including the [greenberg-2004]/[greenberg-2007]
    data reported in §3.7: kind-denoting plurals license accidental readings,
    singular indefinites do not. -/
theorem accidental_tracks_kind :
    (Examples.all.filter (fun r => (featOf r "diagnostic" == some "greenberg" ||
        featOf r "diagnostic" == some "italian-gen") &&
        (featOf r "nominalForm" == some "kindDenotingPlural" ||
         featOf r "nominalExpression" == some "italianDefinitePlural"))).all
        (readOf · "accidental" == some .acceptable) = true ∧
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "greenberg" &&
        featOf r "nominalForm" == some "singularIndefinite")).all
        (readOf · "accidental" == some .unacceptable) = true := by decide

/-- Singular vs plural kind terms (§6.2): singular kind terms lack accidental and
    cumulative readings; plural kind terms have the accidental reading. -/
theorem singular_kind_divergence_data :
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "singular-kind" &&
        featOf r "kindTermNumber" == some "singular")).all
        (fun r => readOf r "accidental" == some .unacceptable &&
                  readOf r "cumulative" == some .unacceptable) = true ∧
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "singular-kind" &&
        featOf r "kindTermNumber" == some "plural")).all
        (readOf · "accidental" == some .acceptable) = true := by decide

/-- Q-adverb and cumulativity diagnostics: `always`/Q-adverbs (overt `Gen`) strip
    the DKP/CKP readings while `all` (the DIST counterpart) does not — no `Gen`. -/
theorem qadv_and_cumulativity_data :
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "homogeneity-removal" &&
        featOf r "remover" == some "all")).all (·.judgment == .acceptable) = true ∧
    (Examples.all.filter (fun r => featOf r "diagnostic" == some "homogeneity-removal" &&
        featOf r "remover" == some "always")).all (·.judgment == .unacceptable) = true ∧
    readOf Examples.ex68a "cumulative" == some .acceptable ∧
    readOf Examples.ex69 "cumulative" == some .unacceptable := by decide

/-! ### Bridge to [longobardi-2001] -/

open Longobardi2001 (bnCanBeReferential toNominalMapping romance english)

/-- [longobardi-2001]'s referential bare nominal = Guerrini's kind denotation;
    both bottom out in Chierchia's `CanDenoteKind`. English BPs can be
    referential/denote kinds; Italian (Romance) bare nominals cannot. -/
theorem referential_iff_longobardi_kind :
    (bnCanBeReferential english = true ↔ CanDenote .englishBarePlural .kind) ∧
    (bnCanBeReferential romance = false ↔ ¬ CanDenote .italianBarePlural .kind) :=
  ⟨⟨fun _ => trivial, fun _ => rfl⟩, ⟨fun _ => id, fun _ => rfl⟩⟩

/-- End-to-end chain from [longobardi-2001]'s `strongD` to Table 1: Romance
    `strongD` ⇒ `predOnly` ⇒ no kind ⇒ no DKP ⇒ no accidental flavor. -/
theorem strongd_to_table1 :
    romance.strongD = true ∧
    toNominalMapping romance = .predOnly ∧
    ¬ CanDenoteKind .predOnly False ∧
    ¬ CanDenote .italianBarePlural .kind ∧
    ¬ LFAvailable .italianBarePlural .distributiveKindPred ∧
    table1 .singularIndefinite false = false := ⟨rfl, rfl, id, id, id, rfl⟩

/-! ### Cross-framework divergences: DKP/CKP are non-quantificational

Guerrini's "not a complex semantics for Gen" makes the accidental and cumulative
readings *non-quantificational*, against the rivals [cohen-1999a]
(majority/proportional `Gen`) and [nickel-2009] (ways-of-normality `Gen`), which
treat the same data as a quantifier. These theorems put the analyses on shared
models and show they disagree on truth value and ontology. -/

/-- **DKP vs [cohen-1999a], one shared 7-of-10 model.** Cohen's majority `Gen`
    judges it true (7/10 > 1/2) as a *proportional quantifier* (`cohen_proportional`);
    the DKP parse is a trivalent gap with no `Gen`. Same datum, opposite ontology. -/
theorem dkp_vs_cohen_disagree :
    (¬ distributiveKindPred (fun _ => (Finset.univ : Finset (Fin 10)))
        (fun a (_ : Fin 1) => a.val < 7) (0 : Fin 1)) ∧
    (¬ noneSatisfy (fun (a : Fin 10) (_ : Fin 1) => a.val < 7) Finset.univ (0 : Fin 1)) ∧
    Cohen1999.cohenGEN (Finset.univ : Finset (Fin 10)) (fun _ => True) (fun a => a.val < 7) ∧
    involvesGen .distributiveKindPred = false := by
  refine ⟨by decide, by decide, ?_, rfl⟩
  rw [Cohen1999.cohen_iff_thresholdGt _ _ _ (by decide)]; decide

/-- Habitat of an elephant in [nickel-2009]'s shared model (6 African, 4 Asian). -/
inductive Habitat | africa | asia deriving DecidableEq, Repr

/-- Which habitat each elephant lives in. -/
def elephantLives : Nickel2009.Entity → Habitat → Prop
  | e, .africa => e.id < 6
  | e, .asia   => e.id ≥ 6

instance : ∀ e h, Decidable (elephantLives e h) := fun e h => by
  cases h <;> unfold elephantLives <;> infer_instance

/-- **CKP vs [nickel-2009]/[cohen-1999a] on "Elephants live in Africa and Asia".**
    Cumulative kind predication succeeds with no `Gen`; Nickel's conjunctive `Gen`
    succeeds *as a quantifier*; Cohen's majority `Gen` *fails* on the Asia conjunct
    (4/10 < 1/2). One datum, three analyses; only Guerrini's is non-quantificational. -/
theorem ckp_vs_gen_on_elephants :
    cumulativeKindPred elephantLives Nickel2009.elephants {Habitat.africa, Habitat.asia} ∧
    involvesGen .cumulativeKindPred = false ∧
    Nickel2009.nickelConjunctiveGEN Nickel2009.elephants Nickel2009.elephantNormalIn
      Nickel2009.ways Nickel2009.isElephant Nickel2009.livesInAfrica Nickel2009.livesInAsia ∧
    ¬ Cohen1999.cohenGEN Nickel2009.elephants Nickel2009.isElephant Nickel2009.livesInAsia := by
  refine ⟨by decide, rfl, by decide, ?_⟩
  rw [Cohen1999.cohen_iff_thresholdGt _ _ _ (by decide)]; decide

end Guerrini2026
