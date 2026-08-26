import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Probe.Profile
import Linglib.Data.Examples.AissenPolian2025

/-!
# Possessor extraction and categorical subject in Tseltalan

Aissen and Polian argue that a Tseltalan possessor never Ā-subextracts: nominal opacity, a
Keine horizon at N⁰ for the wh-probe on C⁰, forces an extracted possessor to A-move first to
Spec,TP or Spec,ApplP, where Attract Closest over DPs decides whether it can — a specific
possessive's D layer, an agent, a specific subject or theme, or an occupied Spec,ApplP stops
it. Hence only non-specific possessums strand, and the possessor that reaches Spec,TP is the
ψ-subject of a categorical judgment.

Nominal opacity is the profile `nominalOpacity` read through `Invisible`, Attract Closest is
`isClosestGoalIn` over D-bearing leaves on the paper's structures, `judgment` reads the
judgment type off the same search, and the paper's examples are the rows, over which
`stranding_iff`, `piedPiping_specific` and `psi_no_piedPiping` hold.

## References

* [aissen-polian-2025]
* [keine-2019]
* [kuroda-1972]
* [little-2020b]
* [polian-2013]
* [gavruseva-2000]
* [aissen-1996]
* [coon-baier-levin-2021]
* [heycock-doron-2003]
-/

namespace AissenPolian2025

open Minimalist SyntacticObject
open RoseTree RoseTree.Nonplanar

/-! ### Probes -/

/-- Nominal opacity: the wh-probe on C⁰ has every node in the extended projection of N⁰ as its
horizon, `[wh]C⁰ ⊣‖ N`. -/
def nominalOpacity : Probe.Profile := ⟨.C, some .N⟩

/-- The [EPP:D] probe on T⁰, without horizon. -/
def dProbeT : Probe.Profile := ⟨.T, none⟩

/-- The [EPP:D] probe on Appl⁰, without horizon. -/
def dProbeAppl : Probe.Profile := ⟨.Appl, none⟩

/-- The [EPP:WH] probe on D⁰ that drives pied-piping with inversion, without horizon. -/
def secondaryWh : Probe.Profile := ⟨.D, none⟩

/-- `target` is invisible to a probe with profile `p` sitting at `probe` when it lies behind the
profile's horizon. -/
def Invisible (p : Probe.Profile) (root probe target : SyntacticObject) : Prop :=
  ∃ h, p.horizon = some h ∧ behindHorizonIn root probe target h

theorem invisible_iff_behindHorizon (h : Cat) (root probe target : SyntacticObject)
    {p : Probe.Profile} (hp : p.horizon = some h) :
    Invisible p root probe target ↔ behindHorizonIn root probe target h :=
  ⟨fun ⟨_, hh, hb⟩ => by rw [hp] at hh; exact Option.some_inj.1 hh ▸ hb, fun hb => ⟨h, hp, hb⟩⟩

/-- A probe without horizon sees everything in its domain. -/
theorem not_invisible_of_horizon_none (root probe target : SyntacticObject) {p : Probe.Profile}
    (hp : p.horizon = none) : ¬ Invisible p root probe target :=
  fun ⟨_, hh, _⟩ => by simp [hp] at hh

theorem dProbe_sees_through (root probe target : SyntacticObject) :
    ¬ Invisible dProbeT root probe target ∧ ¬ Invisible dProbeAppl root probe target ∧
      ¬ Invisible secondaryWh root probe target :=
  ⟨not_invisible_of_horizon_none _ _ _ rfl, not_invisible_of_horizon_none _ _ _ rfl,
   not_invisible_of_horizon_none _ _ _ rfl⟩

/-! ### The structures -/

/-- A leaf is D-bearing when its token's outer category is D: the goals of an [EPP:D] probe. -/
def hasD (s : SyntacticObject) : Bool :=
  match s.getLIToken with
  | some tok => tok.item.outerCat == .D
  | none => false

private def tC : LIToken := ⟨.simple .C [], 1⟩
private def tT : LIToken := ⟨.simple .T [], 2⟩
private def tV : LIToken := ⟨.simple .V [], 3⟩
private def tv : LIToken := ⟨.simple .v [], 4⟩
private def tAppl : LIToken := ⟨.simple .Appl [], 5⟩
private def tP : LIToken := ⟨.simple .P [], 6⟩
private def tPsr : LIToken := ⟨.simple .D [], 7⟩
private def tPsm : LIToken := ⟨.simple .N [], 8⟩
private def tD : LIToken := ⟨.simple .D [], 9⟩
private def tAgt : LIToken := ⟨.simple .D [], 10⟩
private def tSubjD : LIToken := ⟨.simple .D [], 11⟩
private def tSubjN : LIToken := ⟨.simple .N [], 12⟩
private def tThemeD : LIToken := ⟨.simple .D [], 13⟩
private def tThemeN : LIToken := ⟨.simple .N [], 14⟩
private def tPivot : LIToken := ⟨.simple .N [], 15⟩

private def C₀ : SyntacticObject := lexLeaf tC
private def T₀ : SyntacticObject := lexLeaf tT
private def Appl₀ : SyntacticObject := lexLeaf tAppl
private def Psr : SyntacticObject := lexLeaf tPsr
private def D₀ : SyntacticObject := lexLeaf tD
private def Agt : SyntacticObject := lexLeaf tAgt
private def SubjD : SyntacticObject := lexLeaf tSubjD
private def ThemeD : SyntacticObject := lexLeaf tThemeD

/-- A non-specific possessive, `[PossP Psr Psm]`. -/
private def possP : RoseTree SOLabel := nodeP (leafP tPsr) (leafP tPsm)

/-- A specific possessive, `[DP D⁰ [PossP Psr Psm]]`. -/
private def dp : RoseTree SOLabel := nodeP (leafP tD) possP

/-- A locative PP over a non-specific possessive, `[PP P [PossP Psr Psm]]`. -/
private def pp : RoseTree SOLabel := nodeP (leafP tP) possP

/-- (9c) with a non-specific possessive S_O: `[TP T⁰ [VP V⁰ PossP]]`. -/
private def unaccPossP : RoseTree SOLabel := nodeP (leafP tT) (nodeP (leafP tV) possP)

/-- (9c) with a specific possessive S_O: `[TP T⁰ [VP V⁰ DP]]`. -/
private def unaccDP : RoseTree SOLabel := nodeP (leafP tT) (nodeP (leafP tV) dp)

/-- (9a) with a non-specific possessive O: `[TP T⁰ [vP Agt [v' v⁰ [VP V⁰ PossP]]]]`. -/
private def transPossP : RoseTree SOLabel :=
  nodeP (leafP tT) (nodeP (leafP tAgt) (nodeP (leafP tv) (nodeP (leafP tV) possP)))

/-- (29) the raising applicative: `[vP Agt [v' v⁰ [ApplP Appl⁰ [VP V⁰ PossP]]]]` under T⁰. -/
private def raisingAppl : RoseTree SOLabel :=
  nodeP (leafP tT)
    (nodeP (leafP tAgt) (nodeP (leafP tv) (nodeP (leafP tAppl) (nodeP (leafP tV) possP))))

/-- (9b) with a locative PP, `[TP T⁰ [vP S_A [v' v⁰ [VP V⁰ PP]]]]`, for a specific or a
non-specific S_A. -/
private def unerg (subj : LIToken) : RoseTree SOLabel :=
  nodeP (leafP tT) (nodeP (leafP subj) (nodeP (leafP tv) (nodeP (leafP tV) pp)))

/-- (71) theme over locative, `[TP T⁰ [VP V⁰ [Theme PP]]]`, for a specific or a non-specific
theme: path verbs, locative existentials and locative copulas. -/
private def themeLoc (theme : LIToken) : RoseTree SOLabel :=
  nodeP (leafP tT) (nodeP (leafP tV) (nodeP (leafP theme) pp))

/-- (83) the experiencer PP merged above the theme, `[TP T⁰ [VP PP [V' V⁰ Theme]]]`. -/
private def experiencer : RoseTree SOLabel :=
  nodeP (leafP tT) (nodeP pp (nodeP (leafP tV) (leafP tThemeD)))

/-- (40a) an existential with a bare pivot, `[TP T⁰ [VP V⁰ NP]]`. -/
private def existential : RoseTree SOLabel :=
  nodeP (leafP tT) (nodeP (leafP tV) (leafP tPivot))

/-! ### Nominal opacity -/

/-- The possessor of a specific S_O is invisible to C⁰'s wh-probe. -/
theorem psr_invisible_dp :
    Invisible nominalOpacity (ofPlanar (nodeP (leafP tC) unaccDP)) C₀ Psr :=
  ⟨.N, rfl, by decide⟩

/-- So is the possessor of a non-specific S_O: opacity does not depend on size. -/
theorem psr_invisible_possP :
    Invisible nominalOpacity (ofPlanar (nodeP (leafP tC) unaccPossP)) C₀ Psr :=
  ⟨.N, rfl, by decide⟩

/-- And the possessor inside a locative PP: PP islands follow from nominal opacity. -/
theorem psr_invisible_pp :
    Invisible nominalOpacity (ofPlanar (nodeP (leafP tC) (themeLoc tThemeN))) C₀ Psr :=
  ⟨.N, rfl, by decide⟩

/-- The D head of a specific possessive is visible, so the whole DP can be pied-piped. -/
theorem dHead_visible :
    ¬ Invisible nominalOpacity (ofPlanar (nodeP (leafP tC) unaccDP)) C₀ D₀ :=
  fun ⟨_, hh, hb⟩ => by
    simp only [nominalOpacity, Option.some.injEq] at hh
    exact absurd (hh ▸ hb) (by decide)

/-! ### Attract Closest -/

/-- The possessor of a non-specific S_O is T⁰'s closest D-goal: it raises to Spec,TP and can
strand the possessum. -/
theorem unacc_possP_psr_closest : isClosestGoalIn (ofPlanar unaccPossP) T₀ Psr hasD := by
  decide

/-- In a specific S_O the D layer is the closer goal: the whole DP raises and the possessor is
shielded. -/
theorem unacc_dp_dHead_closest :
    isClosestGoalIn (ofPlanar unaccDP) T₀ D₀ hasD ∧
      ¬ isClosestGoalIn (ofPlanar unaccDP) T₀ Psr hasD :=
  ⟨by decide, by decide⟩

/-- The agent of a transitive is the closer goal, so the possessor of O cannot reach Spec,TP. -/
theorem trans_agt_closest :
    isClosestGoalIn (ofPlanar transPossP) T₀ Agt hasD ∧
      ¬ isClosestGoalIn (ofPlanar transPossP) T₀ Psr hasD :=
  ⟨by decide, by decide⟩

/-- In the raising applicative the possessor of O is Appl⁰'s closest D-goal: it externalizes to
Spec,ApplP. -/
theorem appl_psr_closest : isClosestGoalIn (ofPlanar raisingAppl) Appl₀ Psr hasD := by decide

/-- A specific unergative subject stops T⁰ before the possessor inside the locative PP. -/
theorem unerg_specific_blocks :
    isClosestGoalIn (ofPlanar (unerg tSubjD)) T₀ SubjD hasD ∧
      ¬ isClosestGoalIn (ofPlanar (unerg tSubjD)) T₀ Psr hasD :=
  ⟨by decide, by decide⟩

/-- A non-specific unergative subject is no DP, so the possessor is the closest goal. -/
theorem unerg_nonspecific_psr_closest : isClosestGoalIn (ofPlanar (unerg tSubjN)) T₀ Psr hasD := by
  decide

/-- A specific theme c-commanding the locative PP raises instead of the possessor. -/
theorem theme_specific_blocks :
    isClosestGoalIn (ofPlanar (themeLoc tThemeD)) T₀ ThemeD hasD ∧
      ¬ isClosestGoalIn (ofPlanar (themeLoc tThemeD)) T₀ Psr hasD :=
  ⟨by decide, by decide⟩

/-- A non-specific theme lets T⁰ reach the possessor inside the PP. -/
theorem theme_nonspecific_psr_closest :
    isClosestGoalIn (ofPlanar (themeLoc tThemeN)) T₀ Psr hasD := by decide

/-- With the experiencer PP merged above the theme, neither c-commands the other and both are
closest goals; the experiential reading requires the experiencer to raise. -/
theorem experiencer_both_closest :
    isClosestGoalIn (ofPlanar experiencer) T₀ Psr hasD ∧
      isClosestGoalIn (ofPlanar experiencer) T₀ ThemeD hasD :=
  ⟨by decide, by decide⟩

/-! ### Judgment type -/

/-- Categorical judgments have a subject of predication, thetic ones present a situation. -/
inductive JudgmentType
  | categorical
  | thetic
  deriving DecidableEq, Repr

instance (root probe : SyntacticObject) :
    Decidable (∃ g ∈ root.subtrees, isClosestGoalIn root probe g hasD) :=
  Multiset.decidableExistsMultiset

/-- A clause is categorical when T⁰'s [EPP:D] probe finds a goal to raise to Spec,TP — the
ψ-subject — and thetic when it finds none. -/
def judgment (root probe : SyntacticObject) : JudgmentType :=
  if ∃ g ∈ root.subtrees, isClosestGoalIn root probe g hasD then .categorical else .thetic

/-- An existential with a bare pivot contains no DP: the clause is thetic. -/
theorem existential_thetic : judgment (ofPlanar existential) T₀ = .thetic := by decide

/-- Predicative possession is categorical, with the possessor as ψ-subject. -/
theorem possession_categorical : judgment (ofPlanar unaccPossP) T₀ = .categorical := by decide

/-! ### The paper's examples -/

/-- Stranding succeeds exactly when the possessum is non-specific and no DP or occupied
external position stands between the possessor and its probe (Table 4). -/
theorem stranding_iff :
    ∀ row ∈ Examples.all, row.feature? "strategy" = some "stranding" →
      (row.judgment = .acceptable ↔
        row.feature? "possessum" = some "nonSpecific" ∧
          row.feature? "intervener" = some "none") := by
  decide

/-- Pied-piping succeeds only with a specific possessum, since only a DP can be wh-moved. -/
theorem piedPiping_specific :
    ∀ row ∈ Examples.all, row.feature? "strategy" = some "piedPiping" →
      row.judgment = .acceptable → row.feature? "possessum" = some "specific" := by decide

/-- In predicative possession and experiential collocations possessor and possessum form no
constituent, so pied-piping is out. -/
theorem psi_no_piedPiping :
    ∀ row ∈ Examples.all, row.feature? "strategy" = some "piedPiping" →
      (row.feature? "construction" = some "predicativePossession" ∨
        row.feature? "construction" = some "experientialCollocation") →
      row.judgment ≠ .acceptable := by decide

end AissenPolian2025
