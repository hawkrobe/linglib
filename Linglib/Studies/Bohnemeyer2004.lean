import Linglib.Fragments.Mayan.Yukatek.VerbClasses
import Linglib.Semantics.Causation.Chain
import Linglib.Semantics.ArgumentStructure.EventStructure
import Linglib.Studies.Lucy1994
import Linglib.Syntax.Voice.Alternation

/-!
# Bohnemeyer 2004: split intransitivity, linking, and lexical representation

This file formalizes the account of Yukatek Maya split intransitivity in [bohnemeyer-2004].
[kraemer-wunderlich-1999] derive the language's argument linking from lexical aspect alone;
Bohnemeyer argues that what the linking rules see is event structure, specifically whether the
intransitive base entails internal causation. Transitivizing an internally-caused base gives
applicative linking, the added applied object realized as U with the original S left as A;
transitivizing an externally-caused base gives causative linking, the added instigator realized as
A with the original S demoted to U (rules (26)–(27)). Which overt suffix appears, *-t* or *-s*, is
lexically idiosyncratic and can dissociate from the linking, as *balak'* 'roll' and *péek* 'move'
show in opposite directions.

The aspect-conditioned split itself follows from the same causal chain: the participant of a
causing subevent outranks that of the caused subevent (31), and an imperfective viewpoint aligns
with the initial subevent while a perfective one aligns with the final subevent or the chain as a
whole (32) — accusative and ergative defaults respectively.

Verb-class data is the Yukatek Fragment's; the transitivizing suffixes are paper-specific and
recorded here.

## Main definitions

* `CausalChainPosition`, `Outranks`, `linkingDefault`, `sMarkerFromViewpoint` — the thematic
  hierarchy of (31) and the linking-by-viewpoint rule of (32)
* `applicativeLinking`, `causativeLinking`, `verbLinking`, `addedTermRole` — the two
  transitivizations as `ValencyAlternation`s, and the role their added participant takes
* `TransitivizerSuffix`, `transitivizerSuffix` — the overt suffix, kept apart from the linking
* `DetransitivizationType` — the antipassive, anticausative and passive of (28)–(30)

## Main results

* `linking_derives_completive`, `linking_derives_incompletive` — the split follows from (31)+(32)
* `causation_determines_linking` against `eventType_underdetermines_linking`,
  `stemClass_underdetermines_linking`, `suffix_underdetermines_linking` — what fixes the linking
  and what does not
* `linking_patterns_swap_roles`, `linking_markers` — the two alternations are mirror images, read
  off their records rather than stipulated
* `degree_achievements_causativize`, `haanEat_applicative_despite_inactive` — the counterexamples
  to aspect- and class-based linking
* `passive_anticausative_distinct_by_A_fate` — the fate of the initial A separates the two
* `salience_agrees_on_shared_roots`, `haanEat_defies_transitiviser_diagnostic` — where this
  classification meets [lucy-1994]'s

## References

* [bohnemeyer-2004]
* [kraemer-wunderlich-1999]
* [levin-hovav-1995]
* [lucy-1994]
-/

namespace Bohnemeyer2004

open ArgumentStructure.EventStructure Semantics.Aspect Causation Mayan Voice Yukatek

/-! ### Causal chain and thematic hierarchy -/

/-- Thematic hierarchy from causal-chain position (31): the participant of a causing subevent
outranks the participant of the caused subevent for linking. -/
def Outranks : CausalChainPosition → CausalChainPosition → Prop
  | .onset, .terminus => True
  | _, _ => False

/-- The core term role (31)'s hierarchy projects a causal-chain position onto: the outranking
participant is the A of a transitive clause, the outranked one its P. -/
def termRole : CausalChainPosition → TermRole
  | .onset => .A
  | .terminus => .P

/-- The marker set a core term role takes in Yukatek: A takes set A and P set B. The sole argument
of an intransitive takes whichever the viewpoint selects — that is the split
(`sMarkerFromViewpoint`). -/
def markerOf : TermRole → Option MarkerSet
  | .A => some .setA
  | .P => some .setB
  | .S | .X => none

/-- The thematic hierarchy is asymmetric: no position both outranks and is outranked by the
same position. -/
theorem outranks_asymm {a b : CausalChainPosition} (h : Outranks a b) :
    ¬ Outranks b a := by
  cases a <;> cases b <;> simp_all [Outranks]

/-- The marker assignment respects the hierarchy: an outranking position is realized as A and so
takes the subject marker, the position it outranks as P and so the object marker. The split thus
follows from (31) via the term roles rather than being stipulated per position. -/
theorem marker_respects_outranks {a b : CausalChainPosition} (h : Outranks a b) :
    markerOf (termRole a) = some .setA ∧ markerOf (termRole b) = some .setB := by
  cases a <;> cases b <;> simp_all [Outranks, termRole, markerOf]

/-! ### Linking by viewpoint -/

/-- §7 rule (32): viewpoint aspect selects which end of the causal chain
    provides the linking default.

    - Imperfective viewpoints align with the initial (causing) subevent, so the highest-ranking
      role is the default — the accusative pattern.
    - Perfective viewpoints align with the final (caused) subevent or the chain as a whole, so the
      lowest-ranking role is the default — the ergative pattern. -/
def linkingDefault : Perfectivity → CausalChainPosition
  | .imperfective => .onset
  | .perfective => .terminus

/-- The marker the sole argument (S) of an intransitive receives, derived by
    composing rule (32) (viewpoint → default position) with rule (31)'s
    hierarchy projection (position → term role → marker).
    The split *falls out* of the causal chain rather than being stipulated
    per viewpoint.

    - Onset default (imperfective): S patterns with A, taking set A.
    - Terminus default (perfective): S patterns with U, taking set B. -/
def sMarkerFromViewpoint (v : Perfectivity) : Option MarkerSet :=
  markerOf (termRole (linkingDefault v))

/-! ### Linking by viewpoint derives the split

The composed mechanism reproduces the Yukatek split recorded in the Fragment's
`sArgumentMarker`: perfective status → ergative (set-B), imperfective →
accusative (set-A). -/

theorem linking_derives_completive :
    sMarkerFromViewpoint .perfective = sArgumentMarker .completive := rfl

theorem linking_derives_subjunctive :
    sMarkerFromViewpoint .perfective = sArgumentMarker .subjunctive := rfl

theorem linking_derives_incompletive :
    sMarkerFromViewpoint .imperfective = sArgumentMarker .incompletive := rfl

/-! ### Linking pattern under transitivization -/

/-- Rule (26): transitivizing an internally-caused base nucleativizes an applied object as P while
the base's S is maintained, surfacing as the A of the derived transitive clause. Creissels'
P-applicativization, over an intransitive base. -/
def applicativeLinking : ValencyAlternation :=
  { pApplicativization with
      name := "Yukatek applicative"
      fateOfA := .na
      fateOfS := .maintained
      initialTransitive := some false }

/-- Rule (27): transitivizing an externally-caused base nucleativizes an instigator as A, the
base's S surfacing as P — Creissels' causativization unchanged. -/
def causativeLinking : ValencyAlternation := causativization

/-- The causation type of the intransitive base selects the alternation (rules 26–27). -/
def predictLinking : InternalExternalCause → ValencyAlternation
  | .internal => applicativeLinking
  | .external => causativeLinking

/-- The alternation a Yukatek verb undergoes under transitivization. -/
def verbLinking (v : YukatekVerb) : ValencyAlternation :=
  predictLinking v.causationType

/-- The other core term role of a transitive clause. -/
def otherRole : TermRole → TermRole
  | .A => .P
  | .P => .A
  | r => r

/-- The role the added participant receives, read off the alternation. -/
def addedRole (va : ValencyAlternation) : Option TermRole := va.newParticipant

/-- The role the base's S receives: a transitive clause has two core terms, so it is whichever the
added participant did not take. -/
def originalRole (va : ValencyAlternation) : Option TermRole :=
  va.newParticipant.map otherRole

/-- Applicative and causative linking are mirror images, and not by stipulation: each alternation
adds a participant in the role the other leaves to the base's S, so the marker one assigns to the
added argument is the marker the other assigns to the original S. -/
theorem linking_patterns_swap_roles :
    addedRole applicativeLinking = originalRole causativeLinking ∧
    originalRole applicativeLinking = addedRole causativeLinking := ⟨rfl, rfl⟩

/-- The marker each participant receives follows from its role by `markerOf`: the applicative adds
a set-B argument and keeps the base's S as set A, the causative the reverse. -/
theorem linking_markers :
    (addedRole applicativeLinking).bind markerOf = some .setB ∧
    (originalRole applicativeLinking).bind markerOf = some .setA ∧
    (addedRole causativeLinking).bind markerOf = some .setA ∧
    (originalRole causativeLinking).bind markerOf = some .setB := ⟨rfl, rfl, rfl, rfl⟩

/-- Both transitivizations are valency-increasing, which the detransitivizations of (28)–(30) are
not — the two halves of the system are one mechanism read in two directions. -/
theorem transitivizations_increase_valency :
    applicativeLinking.isValencyIncreasing = true ∧
    causativeLinking.isValencyIncreasing = true := ⟨rfl, rfl⟩

/-- The role a verb's added participant takes: P under applicative linking, A under causative. -/
def addedTermRole (v : YukatekVerb) : Option TermRole := addedRole (verbLinking v)

/-! ### Transitivizing suffix vs linking

The overt transitivizing suffix is lexically specified and *usually* tracks the linking pattern,
but the two can dissociate — the paper's central argument against aspect-based linking. The suffix
is paper-specific lexical data, so it is recorded here against the Fragment's entries rather than
in the Fragment. -/

/-- The overt transitivizing suffix ([bohnemeyer-2004]): applicative *-t* or causative *-s*. -/
inductive TransitivizerSuffix where
  | applicativeT
  | causativeS
  deriving DecidableEq, Repr

/-- The suffix each verb the paper documents takes under transitivization (4), (5), (6), (7), (8),
(9), (10), (11). Lexically idiosyncratic: *balak'* and *péek* are both active and externally
caused, yet take *-t* and *-s* respectively. -/
def suffixTable : List (YukatekVerb × TransitivizerSuffix) :=
  [(meyah, .applicativeT), (baaxal, .applicativeT), (haanEat, .applicativeT),
   (balak, .applicativeT), (tsiirin, .applicativeT),
   (kim, .causativeS), (luub, .causativeS), (peek, .causativeS)]

/-- The suffix of a documented verb; `none` for verbs the paper does not exemplify. -/
def transitivizerSuffix (v : YukatekVerb) : Option TransitivizerSuffix :=
  suffixTable.lookup v

/-- The verbs whose transitivization the paper exemplifies. -/
def documented : List YukatekVerb := suffixTable.map (·.1)

/-! ### What determines the linking

Causation type determines the alternation by rules (26)–(27). The paper's argument is that the
properties competing accounts appeal to do not: each of lexical aspect (which is what
[kraemer-wunderlich-1999]'s rule (14) reads), stem class, and the overt suffix leaves the linking
open, witnessed by a minimal pair of documented verbs. -/

/-- Causation type settles the alternation. -/
theorem causation_determines_linking (v w : YukatekVerb)
    (h : v.causationType = w.causationType) : verbLinking v = verbLinking w := by
  simp [verbLinking, h]

/-- Event type does not: *meyah* 'work' and *balak'* 'roll' are both processes, and they link
differently — the counterexample to rule (14), which reads only lexical aspect ((4) vs (10)). -/
theorem eventType_underdetermines_linking :
    meyah.stemClass.eventType = balak.stemClass.eventType ∧
    addedTermRole meyah ≠ addedTermRole balak := ⟨rfl, by decide⟩

/-- Stem class does not: *hàan* 'eat' and *kim* 'die' are both inactive, and they link differently
((9) vs (6)). -/
theorem stemClass_underdetermines_linking :
    haanEat.stemClass = kim.stemClass ∧
    addedTermRole haanEat ≠ addedTermRole kim := ⟨rfl, by decide⟩

/-- The overt suffix does not: *meyah* and *balak'* both take *-t*, and they link differently —
"balak' takes the applicative suffix –t when transitivized. However, the linking properties of the
transitivized stem balak'-t are those of a causativized stem" (§6). -/
theorem suffix_underdetermines_linking :
    transitivizerSuffix meyah = transitivizerSuffix balak ∧
    addedTermRole meyah ≠ addedTermRole balak := ⟨rfl, by decide⟩

/-- Nor does the suffix follow from causation type and stem class: *balak'* and *péek* agree on
both and still differ in suffix ((8), (10)) — the dissociation runs in both directions. -/
theorem suffix_not_predictable :
    balak.stemClass = peek.stemClass ∧ balak.causationType = peek.causationType ∧
    transitivizerSuffix balak ≠ transitivizerSuffix peek := ⟨rfl, rfl, by decide⟩

/-- Every documented verb links by its causation type: those with internally-caused bases add a P,
the rest an A. -/
theorem documented_linking :
    documented.all (fun v =>
      addedTermRole v == some (if v.causationType == .internal then .P else .A)) = true := by
  decide

/-! ### Degree achievements: event type vs aspect -/

/-- Degree achievements are event-structurally state changes, not processes,
    even though they behave atelically.

    §5: the class takes the resultative *-a'n* ((19), *ka'n-a'n-en* 'I'm very
    tired') and incorporates the universal quantifier *láah* ((20),
    *lúub-láah* 'they fell completely'), which active intransitives do not,
    despite behaving atelically under (15). -/
theorem kaan_is_state_change :
    kaan.stemClass.eventType = .stateChange := rfl

theorem naak_is_state_change :
    naak.stemClass.eventType = .stateChange := rfl

/-- Degree achievements transitivize like state-change verbs, adding an instigator as A rather
than an applied object as P.

    This is the first direct counterevidence against [kraemer-wunderlich-1999]'s aspect-based
    linking: rule (14) treats them with the process verbs and so predicts applicativization, but
    they causativize like every other state-change verb — (17) lists the class, (21) derives
    *lúub* 'fall'. -/
theorem degree_achievements_causativize :
    addedTermRole kaan = some .A ∧ addedTermRole naak = some .A := ⟨rfl, rfl⟩

/-- *hàan* 'eat' is inactive by stem class yet internally caused, and it applicativizes ((9)): if
stem class determined transitivization it would causativize like *kim* 'die'. -/
theorem haanEat_applicative_despite_inactive :
    haanEat.stemClass = .inactive ∧ addedTermRole haanEat = some .P := ⟨rfl, rfl⟩

/-! ### Bridge to detransitivization

The three Yukatek detransitivizations are instances of the cross-linguistic
valency-alternation typology (`Syntax/Voice/Alternation.lean`).
That substrate keeps passive and anticausative distinct by the fate of the
initial A — passive *denucleativizes* it (retained in participant structure as
a possible oblique agent), anticausative *suppresses* it (removed entirely). -/

/-- Detransitivization type in Yukatek, from rules (28)–(30).

    - Antipassive (rule 28): removes the caused event, retaining the causing
      process. Active intransitives inflect like antipassive stems.
    - Anticausative (rule 29): removes the causing event, retaining the caused
      state/change. Inactive intransitives inflect like anticausative stems.
    - Passive (rule 30): like anticausative but adds PROC_C and instigator to
      the caused event. -/
inductive DetransitivizationType where
  | antipassive   -- retain causing process, remove caused event
  | anticausative -- retain caused event, remove causing process
  | passive       -- retain caused event, add instigator
  deriving DecidableEq, Repr

/-- Map each Yukatek detransitivization to its cross-linguistic valency
    alternation: antipassive → antipassivization (P denucleativized, A → S),
    anticausative → decausativization (A suppressed, P → S), passive →
    passivization (A denucleativized but retained, P → S). -/
def DetransitivizationType.toAlternation : DetransitivizationType → ValencyAlternation
  | .antipassive => antipassivization
  | .anticausative => decausativization
  | .passive => passivization

/-- All three detransitivizations are valency-decreasing.
    ex. (12): p'eh "chip" → antipassive p'èeh, passive p'e'h-el,
    anticausative p'éeh-el. -/
theorem detransitivizations_decrease_valency :
    (DetransitivizationType.toAlternation .antipassive).isValencyDecreasing = true ∧
    (DetransitivizationType.toAlternation .anticausative).isValencyDecreasing = true ∧
    (DetransitivizationType.toAlternation .passive).isValencyDecreasing = true :=
  ⟨rfl, rfl, rfl⟩

/-- The fate of the initial A separates passive from anticausative — the
    distinction the coarser intransitivization typology collapses: passive
    denucleativizes A (kept in participant structure), anticausative suppresses
    it (removed). -/
theorem passive_anticausative_distinct_by_A_fate :
    (DetransitivizationType.toAlternation .passive).fateOfA = .denucleativized ∧
    (DetransitivizationType.toAlternation .anticausative).fateOfA = .suppressed :=
  ⟨rfl, rfl⟩

/-! ### Template-level detransitivization -/

/-- Detransitivization as a template-level operation. rules (28)–(30)
    decompose detransitivization in terms of which subevent is retained:

    - Antipassive: retain the causing process → accomplishment → activity
    - Anticausative: retain the caused change → accomplishment → achievement
    - Passive: like anticausative but adds PROC_C + instigator (same template
      output as anticausative, with additional participant structure) -/
def DetransitivizationType.templateResult : DetransitivizationType → Template
  | .antipassive => .activity       -- retain PROC, remove CAUSE+CHANGE
  | .anticausative => .achievement  -- remove PROC+CAUSE, retain CHANGE
  | .passive => .achievement        -- retain CHANGE, add instigator

/-- Antipassive yields a process (activity); anticausative/passive yield a
    state change (achievement). This connects to the event type distinction
    that governs verb class membership. -/
theorem antipassive_yields_process :
    (DetransitivizationType.templateResult .antipassive).eventType = .process := rfl

theorem anticausative_yields_stateChange :
    (DetransitivizationType.templateResult .anticausative).eventType = .stateChange := rfl

/-- Anticausative template result matches `Template.intransitiveVariant` from
    `EventStructure.lean`: both yield achievement from accomplishment. -/
theorem anticausative_matches_intransitiveVariant :
    some (DetransitivizationType.templateResult .anticausative)
    = Template.intransitiveVariant .accomplishment := rfl

/-! ### The rest of the inventory -/

/-- The Fragment's externally-caused verbs, across three stem classes: manner-of-motion and
sound-emission actives, positionals ((25)), and inactive degree achievements ((17)). -/
def externallyCaused : List YukatekVerb :=
  [chiik, haarax, huuy, mosoon, pirik, walak, chilTal, xolTal, lab, tiil, tsuuk, kaan, naak]

/-- Each of them is externally caused whatever its stem class, and so adds an instigator as A:
stem class varies across the list while the linking does not. -/
theorem externally_caused_causativize :
    externallyCaused.all (fun v =>
      v.causationType == .external && addedTermRole v == some .A) = true := by decide

/-! ### Bridge to split ergativity -/

/-- The linking-by-viewpoint mechanism derives the same alignment as the
    `SplitErgativity` system parameterized by status category. -/
theorem linking_consistent_with_split :
    (yukatekSplit.alignment .completive = .ergative) ∧
    (yukatekSplit.alignment .incompletive = .accusative) := ⟨rfl, rfl⟩

/-- Yukatek's split is aspect-conditioned, like Hindi and Georgian. All three
    use perfective → ergative, imperfective → accusative (modulo
    language-specific factor types). -/
theorem aspect_conditioned_split_family :
    yukatekSplit.alignment .completive =
      Alignment.hindiSplit.alignment .perfective := rfl

/-! ### Stem classes vs Lucy's root classes

[lucy-1994] classifies underived Yukatek roots by required transitiviser;
this paper's five stem classes cut the same lexicon by status inflection.
The comparison lives here because the paper engages Lucy's analysis
directly — §5 argues degree achievements defeat its Vendlerian construal
of these classes. -/

/-- Stem class → [lucy-1994] salience class. Partial: `inchoative` stems
    derive from adjectival roots (completive *-chah*), which Lucy holds
    outside the predicate-root cut, and `positional` roots form Lucy's
    separate cross-cutting class (completive *-lah*) — the two stem
    classes share only the anomalous incompletive *-tal*. -/
def salienceClassOf : VerbStemClass → Option ArgumentStructure.SalienceClass
  | .active => some .agent
  | .inactive => some .patient
  | .transitiveActive => some .agentPatient
  | .inchoative => none
  | .positional => none

/-- Where the two samples share a lexeme, stem class and Lucy's derived
    root class agree: kim ~ kíim 'die', luub ~ lúub' 'fall',
    naak ~ ná'ak 'ascend'. -/
theorem salience_agrees_on_shared_roots :
    salienceClassOf kim.stemClass = Lucy1994.predictedClass Lucy1994.kiim ∧
    salienceClassOf luub.stemClass = Lucy1994.predictedClass Lucy1994.luub ∧
    salienceClassOf naak.stemClass = Lucy1994.predictedClass Lucy1994.naak :=
  ⟨rfl, rfl, rfl⟩

/-- hàan 'eat' defeats a purely transitiviser-based classification: its
    stem class maps to patient salient, yet it transitivizes with
    applicative *-t* — the exponent Lucy's diagnostic reads as agent
    salient. The suffix tracks internal causation, not class (ex. (9)). -/
theorem haanEat_defies_transitiviser_diagnostic :
    transitivizerSuffix haanEat = some .applicativeT ∧
    salienceClassOf haanEat.stemClass = some .patient := ⟨rfl, rfl⟩

/-- péek: active in this paper's classification (manner-of-motion
    process, with idiosyncratic causative *-s*), but a `#`-marked
    state-change root in [lucy-1994] ex. (4) — the two sources classify
    the same root differently. -/
theorem peek_stem_vs_root_class_divergence :
    salienceClassOf peek.stemClass = some .agent ∧
    Lucy1994.predictedClass Lucy1994.peek = some .patient := ⟨rfl, rfl⟩

end Bohnemeyer2004
