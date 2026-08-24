import Linglib.Syntax.Case.Dependent

/-!
# Case assignment in Sakha

[baker-vinokurova-2010] argue that Sakha needs both of the case-assignment
mechanisms on offer: configurational dependent case ([marantz-1991]) for
accusative and dative, and Agree with a functional head ([chomsky-2000]) for
nominative and genitive. The two coexist in one grammar rather than competing,
which `CaseSystemConfig` records by giving each structural case its own
mechanism slot; `sakhaConfig` is the resulting parameterization.

Differential object marking falls out of phase visibility. A specific object
shifts to the edge of VP and is visible on the CP cycle, where it and the
subject form the competitor pair the accusative rule needs; a nonspecific
object stays inside VP, is invisible to T, and surfaces unmarked. The
causative cascade is the sharper test: adding a lower theme changes the case
on the causee from accusative to dative, which no head-driven Agree relation
can mediate.

## Main results

* `two_modalities_required`: neither a purely configurational nor a purely
  Agree-based grammar derives the Sakha pattern.
* `dom_alternation_in_object`: object case tracks phase visibility alone.
* `causee_case_depends_on_base_transitivity`: the causative cascade.
* `argumental_status_drives_case`: bare-NP adverbs are not case competitors.
* `all_four_modalities_in_one_clause`: T-Agree, D-Agree and both dependent
  rules valuing four NPs in a single derivation.

## Implementation notes

ECM is not modelled: `PhasedNP` does not distinguish embedded from matrix
domains.

## References

* [baker-vinokurova-2010]
-/
namespace BakerVinokurova2010

open Syntax.Case

/-! ### The Sakha configuration -/

/-- Sakha's case system: accusative alignment with the
    [baker-vinokurova-2010] two-modality split. ACC and DAT are
    dependent (Marantz); NOM and GEN are Agree-based (Chomsky). -/
def sakhaConfig : CaseSystemConfig where
  langType := .accusative
  nomMode  := .agreeT
  datMode  := .dependent
  accMode  := .dependent
  genMode  := .agreeD

/-! ### NP positions -/

/-- A subject NP merged at the vP edge / SpecTP — visible on the CP cycle. -/
def subj (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .cp, shifted := false }

/-- A VP-internal NP that has shifted (specific object, raised theme). -/
def shiftedVP (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .vp, shifted := true }

/-- A VP-internal NP that has not shifted (nonspecific object). -/
def lowVP (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .vp, shifted := false }

/-! ### Monotransitive with a shifted object -/

/-- "Masha cake-ACC ate" with a specific object: the object shifts,
    competes with the subject on the CP cycle, and is valued ACC. -/
def transSpecific : List PhasedNP := [subj "subj", shiftedVP "obj"]

def transSpecificResult : List CasedNP := assignCasesPhased sakhaConfig transSpecific

/-- The shifted object competes with the subject on the CP cycle and is
    valued accusative by the dependent rule, not by Agree. -/
theorem trans_specific_obj_acc :
    getCaseOf "obj" transSpecificResult = some .acc ∧
    getSourceOf "obj" transSpecificResult = some .dependent := by decide

/-- The subject is valued nominative by T-Agree, not by the unmarked
    default. -/
theorem trans_specific_subj_nom :
    getCaseOf "subj" transSpecificResult = some .nom ∧
    getSourceOf "subj" transSpecificResult = some .agree := by decide

/-! ### Monotransitive with an unshifted object -/

/-- "Masha cake ate" with a nonspecific object: the object stays in
    VP and is invisible to T on the CP cycle, so the ACC rule never
    fires (no competitor pair). The object surfaces unmarked. -/
def transNonspecific : List PhasedNP := [subj "subj", lowVP "obj"]

def transNonspecificResult : List CasedNP :=
  assignCasesPhased sakhaConfig transNonspecific

/-- Nonspecific object: no ACC, surfaces unmarked. PIC-driven DOM. -/
theorem trans_nonspecific_obj_unmarked :
    getSourceOf "obj" transNonspecificResult = some .unmarked := by decide

/-- T-Agree finds the highest CP-visible unvalued NP, the subject, in both
    DOM variants. -/
theorem trans_nonspecific_subj_nom :
    getCaseOf "subj" transNonspecificResult = some .nom ∧
    getSourceOf "subj" transNonspecificResult = some .agree := by decide

/-! ### Differential object marking -/

/-- The DOM alternation: object case differs purely by whether the
    object has shifted out of VP, with no change to the subject. The
    grammar does not stipulate "specificity → ACC"; it is derived
    from phase visibility and the accusative rule. -/
theorem dom_alternation_in_object :
    getCaseOf "obj" transSpecificResult ≠ getCaseOf "obj" transNonspecificResult := by
  decide

theorem dom_subject_invariant :
    getCaseOf "subj" transSpecificResult = getCaseOf "subj" transNonspecificResult := by
  decide

/-! ### Ditransitives -/

/-- Ditransitive with a specific theme: the DAT rule values the goal on the
    VP cycle, and the shifted theme competes with the subject on the CP
    cycle. -/
def ditransitive : List PhasedNP :=
  [subj "subj", lowVP "goal", shiftedVP "theme"]

def ditransitiveResult : List CasedNP := assignCasesPhased sakhaConfig ditransitive

/-- The goal is valued dative by the dative rule on the VP cycle. -/
theorem ditrans_goal_dat :
    getCaseOf "goal" ditransitiveResult = some .dat ∧
    getSourceOf "goal" ditransitiveResult = some .dependent := by decide

/-- Specific theme receives ACC on the CP cycle (after the goal has
    been valued DAT and removed from competition). -/
theorem ditrans_theme_acc :
    getCaseOf "theme" ditransitiveResult = some .acc ∧
    getSourceOf "theme" ditransitiveResult = some .dependent := by decide

theorem ditrans_subj_nom :
    getCaseOf "subj" ditransitiveResult = some .nom ∧
    getSourceOf "subj" ditransitiveResult = some .agree := by decide

/-- The NOM/DAT/ACC ditransitive pattern: dative on the goal is what
    bleeds the accusative rule on the VP cycle, so only the theme surfaces
    accusative despite two VP-internal NPs. The general reason is
    `dat_persists_through_assignCasesPhased`. -/
theorem ditrans_full_pattern :
    getCaseOf "subj" ditransitiveResult = some .nom ∧
    getCaseOf "goal" ditransitiveResult = some .dat ∧
    getCaseOf "theme" ditransitiveResult = some .acc := by decide

/-! ### Unaccusatives -/

/-- Unaccusative: the theme raises to SpecTP, leaving no ACC competitor. -/
def unaccusative : List PhasedNP := [subj "theme"]

def unaccResult : List CasedNP := assignCasesPhased sakhaConfig unaccusative

theorem unacc_theme_nom :
    getCaseOf "theme" unaccResult = some .nom ∧
    getSourceOf "theme" unaccResult = some .agree := by decide

/-- No NP receives ACC: the dependent rule needs two competitors. -/
theorem unacc_no_acc :
    ∀ cn ∈ unaccResult, cn.case ≠ .acc := by decide

/-! ### Agree-nominative is not the unmarked default -/

/-! The same surface NOM can have either source, and the source is what
downstream probes see. Sakha NOM is always `.agree`; a default-NOM grammar
would have it `.unmarked`. -/

/-- No NOM in a Sakha derivation comes from the unmarked default. -/
theorem all_nom_is_agree_in_sakha :
    ∀ cn ∈ transSpecificResult ++ ditransitiveResult ++ unaccResult,
      cn.case = .nom → cn.source = .agree := by decide

/-! ### The causative cascade -/

/-! Morphological causatives in Sakha cascade: the causee surfaces
accusative when the base verb is intransitive, since max VP holds one
argumental NP and offers no dative competitor, but dative when the base verb
is transitive, since max VP then holds two and the dative rule fires.

This is the cleanest test of the dependent-case modality. Adding an NP — the
lower theme — changes the case on a different NP, the causee, which no
head-driven Agree relation can do. The dative rule bleeding the accusative
rule on the VP cycle predicts the cascade with no further stipulation. -/

/-- "Sardaana made Aisen cry", on an intransitive base. Max VP holds only
    the causee, so neither dependent rule fires on the VP cycle; the causee
    shifts to the CP phase, competes with the causer, and is valued
    accusative there. -/
def causativeOfIntransitive : List PhasedNP :=
  [subj "causer", shiftedVP "causee"]

def causIntransResult : List CasedNP :=
  assignCasesPhased sakhaConfig causativeOfIntransitive

theorem caus_intrans_causee_acc :
    getCaseOf "causee" causIntransResult = some .acc ∧
    getSourceOf "causee" causIntransResult = some .dependent := by decide

theorem caus_intrans_causer_nom :
    getCaseOf "causer" causIntransResult = some .nom ∧
    getSourceOf "causer" causIntransResult = some .agree := by decide

/-- "Misha made Masha eat soup", on a transitive base. Max VP holds the
    causee and the theme, both argumental, so the dative rule values the
    higher of them dative and bleeds the accusative rule; the theme then
    shifts to the CP phase, competes with the causer, and is valued
    accusative. -/
def causativeOfTransitive : List PhasedNP :=
  [subj "causer", lowVP "causee", shiftedVP "theme"]

def causTransResult : List CasedNP :=
  assignCasesPhased sakhaConfig causativeOfTransitive

theorem caus_trans_causee_dat :
    getCaseOf "causee" causTransResult = some .dat ∧
    getSourceOf "causee" causTransResult = some .dependent := by decide

theorem caus_trans_theme_acc :
    getCaseOf "theme" causTransResult = some .acc ∧
    getSourceOf "theme" causTransResult = some .dependent := by decide

theorem caus_trans_causer_nom :
    getCaseOf "causer" causTransResult = some .nom ∧
    getSourceOf "causer" causTransResult = some .agree := by decide

/-- The causative cascade: the *same* causative morpheme produces ACC
    on the causee over an intransitive base and DAT over a transitive one.
    The only difference is the number of argumental NPs in max VP, which is
    the structural signature of dependent case. -/
theorem causee_case_depends_on_base_transitivity :
    getCaseOf "causee" causIntransResult = some .acc ∧
    getCaseOf "causee" causTransResult = some .dat := by decide

/-! ### Bare-NP adverbs -/

/-! [baker-vinokurova-2010] restrict the dependent rules to argumental
NPs, those bearing a θ-role with respect to some case assigner. Bare-NP
adverbs like *sajyn* 'summer' are not case competitors even when c-commanded
by a caseless NP, which `PhasedNP.isArgumental` records: an NP set
non-argumental is filtered out of `unmarkedVisible` and can neither trigger
nor receive dependent case. The same noun surfaces accusative as the object
of a transitive verb and unmarked as a temporal adverb. -/

/-- Adverbial NP — bears no θ-role w.r.t. a case-assigning head. -/
def adverb (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .cp,
    shifted := false, isArgumental := false }

/-- "Bihigi beqehee ystan-nybyt" 'we yesterday jumped': an argumental
    subject and a non-argumental adverb, leaving one NP in case
    competition. -/
def intransitiveWithAdverb : List PhasedNP :=
  [subj "subj", adverb "yesterday"]

def intrAdvResult : List CasedNP :=
  assignCasesPhased sakhaConfig intransitiveWithAdverb

/-- The adverb is not marked accusative, the accusative rule not seeing it
    as a competitor; it falls through to the default sweep. -/
theorem adverb_does_not_get_acc :
    getCaseOf "yesterday" intrAdvResult = some .nom ∧
    getSourceOf "yesterday" intrAdvResult = some .unmarked := by decide

theorem subj_with_adverb_nom_agree :
    getCaseOf "subj" intrAdvResult = some .nom ∧
    getSourceOf "subj" intrAdvResult = some .agree := by decide

/-- "Masha sajyn-y axt-ar" 'Masha summer-ACC misses': the same noun as
    the object of a transitive verb, where it bears a θ-role, counts as
    argumental, and is marked accusative. -/
def transitiveSummerObject : List PhasedNP :=
  [subj "masha", shiftedVP "summer"]

def transSummerResult : List CasedNP :=
  assignCasesPhased sakhaConfig transitiveSummerObject

theorem summer_as_object_gets_acc :
    getCaseOf "summer" transSummerResult = some .acc ∧
    getSourceOf "summer" transSummerResult = some .dependent := by decide

/-- The same noun receives ACC when argumental and unmarked NOM when
    adverbial, with no lexical ambiguity stipulated. -/
theorem argumental_status_drives_case :
    getCaseOf "summer" transSummerResult ≠ getCaseOf "yesterday" intrAdvResult ∧
    getSourceOf "summer" transSummerResult ≠ getSourceOf "yesterday" intrAdvResult := by
  decide

/-! ### Neither modality suffices alone -/

/-- Pure Marantz (Sakha pattern with NOM as unmarked default and no
    Agree-based case): all structural cases are configurational. -/
def pureMarantz : CaseSystemConfig where
  langType := .accusative
  nomMode  := .unmarkedDefault
  datMode  := .dependent
  accMode  := .dependent
  genMode  := .nonstructural

/-- Pure Chomsky: every structural case assigned by Agree with a functional
    head, DAT purely inherent ([chomsky-2000], [chomsky-2001]). -/
def pureChomsky : CaseSystemConfig where
  langType := .accusative
  nomMode  := .agreeT
  datMode  := .nonstructural
  accMode  := .agreeV
  genMode  := .agreeD

/-- Pure Marantz gives the subject the same surface NOM as Sakha but a
    different source, so the modalities differ where the morphology does
    not. -/
theorem pure_marantz_subj_unmarked :
    getSourceOf "subj" (assignCasesPhased pureMarantz ditransitive) = some .unmarked := by
  decide

/-- Pure Chomsky derives no DAT at all, contradicting the productive DAT on
    Sakha structural goals. -/
theorem pure_chomsky_no_algorithmic_dat :
    ∀ cn ∈ assignCasesPhased pureChomsky ditransitive, cn.case ≠ .dat := by decide

/-- Pure Chomsky reaches the same ACC on the theme by Agree where Sakha
    reaches it by the dependent rule. -/
theorem pure_chomsky_acc_via_agree :
    getCaseOf "theme" (assignCasesPhased pureChomsky ditransitive) = some .acc ∧
    getSourceOf "theme" (assignCasesPhased pureChomsky ditransitive) = some .agree := by
  decide

/-- The cascade is the wedge against any pure-Agree account: pure Chomsky
    leaves the causee of a transitive base without DAT, its v-Agree probe
    targeting the theme instead. -/
theorem pure_chomsky_misses_causative_cascade :
    getCaseOf "causee" (assignCasesPhased pureChomsky causativeOfTransitive) ≠
      some .dat ∧
    getCaseOf "causee" causTransResult = some .dat := by
  refine ⟨?_, ?_⟩ <;> decide

/-- Neither pure modality derives the Sakha pattern: pure Marantz misses the
    NOM-as-Agree source, pure Chomsky misses DAT on both the ditransitive and
    the causative cascade. -/
theorem two_modalities_required :
    -- Pure Marantz fails on the NOM source fingerprint
    (getSourceOf "subj" (assignCasesPhased pureMarantz ditransitive) ≠ some .agree) ∧
    -- Pure Chomsky fails on DAT in the ditransitive
    (¬ ∃ cn ∈ assignCasesPhased pureChomsky ditransitive, cn.case = .dat) ∧
    -- Pure Chomsky additionally fails on the causative cascade
    (getCaseOf "causee" (assignCasesPhased pureChomsky causativeOfTransitive) ≠
       some .dat) ∧
    -- Sakha succeeds on all three
    (getSourceOf "subj" ditransitiveResult = some .agree) ∧
    (∃ cn ∈ ditransitiveResult, cn.case = .dat) ∧
    (getCaseOf "causee" causTransResult = some .dat) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### DP-internal possessors -/

/-! [baker-vinokurova-2010] have D Agree with the possessor inside DP and
value it GEN. The clausal cycles see the DP as opaque, its possessor filtered
out of `unmarkedVisible` by the `inDP` flag, and `applyGenAgree` runs as the
DP-internal counterpart to T-Agree. -/

/-- A DP-internal possessor: opaque to clause-level case competition
    but valued GEN by D-Agree. -/
def possessor (label : String) : PhasedNP :=
  { label := label, lexicalCase := none, basePhase := .cp,
    shifted := false, isArgumental := true, inDP := true }

/-- "Aisen's house [is in town]" — the matrix subject is a DP whose
    possessor `aisen` is valued GEN by D-Agree. The possessor is
    invisible to clausal probes; the head noun (`house`) is the
    subject of T-Agree and surfaces NOM. -/
def possessedSubject : List PhasedNP := [subj "house", possessor "aisen"]

def possessedResult : List CasedNP :=
  assignCasesPhased sakhaConfig possessedSubject

theorem possessor_gets_gen_via_agree :
    getCaseOf "aisen" possessedResult = some .gen ∧
    getSourceOf "aisen" possessedResult = some .agree := by decide

theorem possessed_head_gets_nom :
    getCaseOf "house" possessedResult = some .nom ∧
    getSourceOf "house" possessedResult = some .agree := by decide

/-- The genitive possessor is invisible to the accusative rule: in a
    transitive with a possessed object the head noun receives accusative,
    not the possessor. -/
def transWithPossessedObj : List PhasedNP :=
  [subj "subj", shiftedVP "book", possessor "aisen"]

def transPossResult : List CasedNP :=
  assignCasesPhased sakhaConfig transWithPossessedObj

theorem possessor_is_opaque_to_clausal_acc :
    getCaseOf "aisen" transPossResult = some .gen ∧
    getCaseOf "book"  transPossResult = some .acc := by decide

/-- Both Agree probes and both dependent rules value four NPs in one
    derivation. -/
theorem all_four_modalities_in_one_clause :
    let cl : List PhasedNP :=
      [subj "subj", lowVP "goal", shiftedVP "theme", possessor "aisen"]
    let r := assignCasesPhased sakhaConfig cl
    getSourceOf "subj"  r = some .agree     ∧  -- T-Agree
    getSourceOf "aisen" r = some .agree     ∧  -- D-Agree
    getSourceOf "goal"  r = some .dependent ∧  -- dative rule
    getSourceOf "theme" r = some .dependent := by decide

end BakerVinokurova2010
