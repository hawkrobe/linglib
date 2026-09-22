import Linglib.Syntax.Minimalist.Ellipsis
import Linglib.Semantics.Root.Defs
import Linglib.Syntax.Minimalist.Verbal.LittleV
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Fragments.Dargwa.ComplexPredicates

/-!
# Kalyakin (2026): VP ellipsis and argument structure alternations in Muira Dargwa

This file formalizes Kalyakin's argument that Muira Dargwa complex predicates show v-stranding
VP-ellipsis: the light verb survives while its complement, the VP containing the non-verbal root,
is elided. With [E] on v the deletion domain is smaller than that of English VP-ellipsis, so the
causative alternation, a difference in Voice over one root, is tolerated (§5) while the root must
still match, and both readings of *again* survive (§4.1), unlike English, where only the
repetitive one does. Roots that impose a manner on an activity attach to v rather than to the
direct object and so lie outside the deletion domain, and antipassives coerce a root into that
position, which is why they resist ellipsis (§5). The NV-drop test shows that the root and the
argument go together, so the elided constituent is the VP (§3.6). The paper's survey (§6) puts
Persian and British *do* beside Muira Dargwa with [E] on v, and Bangla with [E] on Voice, and
finds that Persian, unlike Muira Dargwa, respects Goldberg's Verbal Identity Requirement.

## References

* [kalyakin-2026]
* [merchant-2013]
* [toosarvandani-2009]
* [goldberg-2005]
* [kratzer-1996]
* [cuervo-2003]
* [anand-hardt-mccloskey-2021]
-/

namespace Kalyakin2026

open ArgumentStructure
open Minimalist Minimalist.Voice
open Minimalist.Ellipsis

/-! ### Mismatch predictions -/

/-- The spine position of a root by its position in the event structure (§2.2): a change-of-state
root merges with the direct object, at V in v's complement, and a manner root attaches to v, at
the VP-adjunction site outside it. -/
def rootSite : Semantics.Root.Position → SpinePosition
  | .complement => .V
  | .adjoined => .vpAdjunct


/-- The core prediction is that vVPE tolerates both voice and transitivity mismatches while
    blocking lexical verb mismatches. -/
theorem vVPE_mismatch_pattern :
    vStrandingVPE.Tolerates .voice ∧
    vStrandingVPE.Tolerates .transitivity ∧
    ¬ vStrandingVPE.Tolerates .lexical := by decide

/-- English VPE has a strictly more restrictive profile than vVPE:
    it additionally blocks transitivity mismatches. -/
theorem vpEllipsis_more_restrictive :
    ¬ vpEllipsis.Tolerates .transitivity ∧
    vStrandingVPE.Tolerates .transitivity := by decide

/-! ### The causative alternation under vVPE (§5)

The two alternants of a change-of-state root differ in the light verb alone, `[vDO, vBE]`
against `[vGO, vBE]` in [cuervo-2003]'s calculus, and share the VP below it. vVPE strands the
light verb and elides its complement, so the shared VP satisfies identity and the alternation is
tolerated; English VP-ellipsis deletes the vP, where v_trans ≠ v_unacc fails identity
([merchant-2013]). -/

/-- The causative alternant of a change-of-state root: a state under `vDO`. -/
def causative : List LittleV := [.vDO, .vBE]

/-- The inchoative alternant: the same state under `vGO`. -/
def inchoative : List LittleV := [.vGO, .vBE]

/-- The alternants differ in the light verb and share its complement, the VP. -/
theorem alternants_share_vp :
    LittleV.Causative causative ∧ LittleV.Inchoative inchoative ∧
      causative.tail = inchoative.tail ∧ causative ≠ inchoative := by
  decide

/-- The causative alternation is tolerated under vVPE because transitivity mismatches are
    allowed. -/
theorem causative_alternation_ok_under_vVPE :
    vStrandingVPE.Tolerates .transitivity := by decide

/-- The causative alternation is blocked under English VPE because transitivity mismatches are
    blocked. -/
theorem causative_alternation_blocked_english :
    ¬ vpEllipsis.Tolerates .transitivity := by decide

/-! ### Antipassive Blocking -/

/-- Antipassive roots in Muira Dargwa are coerced to v-adjunction, outside vVPE's deletion domain,
    so they cannot be elided (§5). -/
theorem antipassive_blocks_vVPE : vStrandingVPE.Spares (rootSite .adjoined) := by decide

/-- Change-of-state roots, merged with the direct object, lie inside vVPE's deletion domain and
    can be elided. -/
theorem change_of_state_allows_vVPE : vStrandingVPE.Deletes (rootSite .complement) := by decide

/-! ### Cross-Linguistic Predictions -/

/-- The hierarchy of mismatch tolerance across ellipsis types:
    sluicing < English VPE < vVPE.
    Each step down tolerates strictly more mismatches. -/
theorem mismatch_hierarchy :
    -- Sluicing: blocks both voice and transitivity
    ¬ sluicing.Tolerates .voice ∧
    ¬ sluicing.Tolerates .transitivity ∧
    -- English VPE: allows voice, blocks transitivity
    vpEllipsis.Tolerates .voice ∧
    ¬ vpEllipsis.Tolerates .transitivity ∧
    -- vVPE: allows both voice and transitivity
    vStrandingVPE.Tolerates .voice ∧
    vStrandingVPE.Tolerates .transitivity := by
  decide

/-- vVPE's [E] position, v, is strictly below English VPE's, Voice, so by Sailor's generalization
    any mismatch tolerated by English VPE is tolerated by vVPE. -/
theorem vVPE_below_vpEllipsis :
    vStrandingVPE.ePosition < vpEllipsis.ePosition := by decide

/-! ### End-to-End Argumentation Chain -/

/-- End-to-end chain: the alternants share their VP under distinct light verbs ([cuervo-2003]),
    vVPE with [E] on v elides the VP alone ([merchant-2013]), so the alternation is tolerated
    under vVPE ([kalyakin-2026]). -/
theorem end_to_end_causative_chain :
    causative.tail = inchoative.tail ∧ causative ≠ inchoative ∧
      vStrandingVPE.Deletes (rootSite .complement) ∧ vStrandingVPE.Tolerates .transitivity := by
  decide

/-- Merchant's theory also predicts that sluicing, with [E] on C, blocks voice mismatches, since
    Voice is inside TP, the deletion domain of sluicing. The Santa Cruz sluicing data set
    ([anand-hardt-mccloskey-2021], §5.5) independently confirms this: across
    4,700 annotated sluices, zero
    antecedent–ellipsis site pairings exhibit active/passive voice mismatches.
    The same theoretical apparatus that Kalyakin extends to vVPE
    already works for sluicing. -/
theorem sluicing_voice_blocked_convergent :
    ¬ sluicing.Tolerates .voice := by decide

/-! ### Again Diagnostic -/

/-- Under vVPE, BOTH repetitive and restitutive *again* survive.
    This contrasts with English VPE (only repetitive survives) and
    confirms the deletion domain is VP (complement of v), not vP.

    [kalyakin-2026] §4.1 (exx. 52a–b): both repetitive and
    restitutive ʔibrra 'again' are available under vVPE in Muira Dargwa.
    [toosarvandani-2009] (ex. 90) independently shows both readings
    available for Persian vVPE. -/
theorem vVPE_both_again :
    vStrandingVPE.Spares AgainReading.repetitive.site ∧
      vStrandingVPE.Spares AgainReading.restitutive.site := by decide

/-- English VPE deletes restitutive *again*, so only the repetitive reading survives.
    ([merchant-2013], building on Johnson 2004, von Stechow 1996). -/
theorem vpEllipsis_only_repetitive :
    vpEllipsis.Spares AgainReading.repetitive.site ∧
      ¬ vpEllipsis.Spares AgainReading.restitutive.site := by decide

/-- The *again* contrast directly distinguishes vVPE from English VPE:
    same test, different result — proving different deletion domains. -/
theorem again_distinguishes_vVPE_from_vpEllipsis :
    vStrandingVPE.Spares AgainReading.restitutive.site ∧
      ¬ vpEllipsis.Spares AgainReading.restitutive.site := by decide

/-! ### Fragment Integration: NV Root Position → vVPE -/

open Dargwa.ComplexPredicates in

/-- Whether a CPr's non-verbal root lies in vVPE's deletion domain, at the position the fragment
annotates. -/
def cprInVVPEDomain (cpr : Dargwa.ComplexPredicates.AnnotatedCPr) : Prop :=
  vStrandingVPE.Deletes (rootSite cpr.rootPosition)

instance (cpr : Dargwa.ComplexPredicates.AnnotatedCPr) : Decidable (cprInVVPEDomain cpr) := by
  unfold cprInVVPEDomain; infer_instance

open Dargwa.ComplexPredicates in

/-- Change-of-state NVs (complement position) are inside vVPE's
    deletion domain: they can be elided. -/
theorem cos_in_domain :
    cprInVVPEDomain warmUp ∧ cprInVVPEDomain openCPr ∧
    cprInVVPEDomain calmCPr ∧ cprInVVPEDomain praiseCPr ∧
    cprInVVPEDomain repairCPr := by decide +kernel

open Dargwa.ComplexPredicates in

/-- Manner/activity NVs (adjoined position) are outside vVPE's
    deletion domain: they survive ellipsis. This is why antipassive
    roots (coerced to adjunction) block vVPE. -/
theorem manner_outside_domain :
    ¬ cprInVVPEDomain runCPr ∧ ¬ cprInVVPEDomain jumpCPr := by decide +kernel

/-! ### NV-Drop Test (vVPE vs Argument Ellipsis) -/

/-- Datum for the NV-drop constituency test.
    [kalyakin-2026] §3.6 distinguishes vVPE from argument ellipsis (AE):
    - vVPE: NV+argument deleted together (constituent = VP)
    - AE: argument alone deleted, NV survives
    - *NV alone deleted, argument survives → ungrammatical
    The ungrammaticality of NV-only deletion proves the elided
    constituent is VP (containing both NV and argument), not just NV. -/
structure NVDropDatum where
  description : String
  nvDropped : Bool
  argDropped : Bool
  grammatical : Bool
  deriving Repr

/-- Dropping the NV and the argument together, which is vVPE, is grammatical. -/
def nvArgDrop : NVDropDatum :=
  { description := "vVPE: NV+arg elided together"
  , nvDropped := true, argDropped := true, grammatical := true }

/-- Dropping the argument alone, which is argument ellipsis, is grammatical. -/
def argOnlyDrop : NVDropDatum :=
  { description := "AE: argument elided, NV survives"
  , nvDropped := false, argDropped := true, grammatical := true }

/-- Dropping the NV alone while the argument survives is ungrammatical, which rules out NV-drop
    as a process distinct from vVPE: the NV cannot be deleted without its complement. -/
def nvOnlyDrop : NVDropDatum :=
  { description := "NV-only drop: ungrammatical"
  , nvDropped := true, argDropped := false, grammatical := false }

/-- The NV-drop test confirms constituent deletion: NV+arg is a
    constituent (VP), NV alone is not. -/
theorem nv_drop_constituency :
    nvArgDrop.grammatical = true ∧
    argOnlyDrop.grammatical = true ∧
    nvOnlyDrop.grammatical = false := ⟨rfl, rfl, rfl⟩

/-! ### The survey of verb-stranding ellipsis (§6) -/

/-- The languages with verb-stranding ellipsis the paper compares. -/
inductive Language
  | muiraDargwa
  | persian
  | bangla
  | britishEnglish
  deriving DecidableEq, Repr

/-- The ellipsis of each language: [E] on v in Muira Dargwa, in Persian, where both readings of
*again* survive ((90), after Toosarvandani), and in British *do*, which tolerates voice and
argument-structure mismatches alike ((97)–(98), after Silk); [E] on Voice in Bangla, where the
restitutive reading is lost (94) and adjuncts are recovered (95), the light verb evacuating by
head movement (after Haldar). -/
def Language.ellipsis : Language → Ellipsis
  | .bangla => vpEllipsis
  | _ => vStrandingVPE

/-- Whether the language respects Goldberg's Verbal Identity Requirement, identity of the light
verbs of antecedent and target ((92)), where the paper reports it: Persian prohibits every
light-verb mismatch (91), Muira Dargwa tolerates them (§5). -/
def Language.respectsVIR? : Language → Option Bool
  | .persian => some true
  | .muiraDargwa => some false
  | _ => none

/-- Every language but Bangla elides the complement of v. -/
theorem ellipsis_eq_vStrandingVPE_iff (l : Language) :
    l.ellipsis = vStrandingVPE ↔ l ≠ .bangla := by
  cases l <;> decide

/-- Persian and Muira Dargwa share the [E] position but differ on the Verbal Identity Requirement,
so languages with [E] on v may respect or disregard it. -/
theorem persian_stricter_than_dargwa :
    Language.persian.ellipsis = Language.muiraDargwa.ellipsis ∧
      Language.persian.respectsVIR? = some true ∧
      Language.muiraDargwa.respectsVIR? = some false :=
  ⟨rfl, rfl, rfl⟩

/-- Bangla's ellipsis is the larger one, and the *again* test shows it: restitutive *again* is
deleted in Bangla but survives in Muira Dargwa. -/
theorem bangla_larger_domain :
    Language.muiraDargwa.ellipsis.ePosition < Language.bangla.ellipsis.ePosition ∧
      ¬ Language.bangla.ellipsis.Spares AgainReading.restitutive.site ∧
      Language.muiraDargwa.ellipsis.Spares AgainReading.restitutive.site := by
  decide

end Kalyakin2026
