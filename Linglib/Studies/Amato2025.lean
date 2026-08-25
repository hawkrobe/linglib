import Mathlib.Tactic.DeriveFintype
import Linglib.Syntax.Minimalist.Agree.Basic
import Linglib.Syntax.Minimalist.Verbal.Voice
import Linglib.Semantics.ArgumentStructure.AuxiliarySelection

/-!
# Nested Agree and apparent minimality violations: [amato-2025]

[amato-2025] derives apparent minimality violations from *Nested Agree*
(Definition (1)): the probes on a head are extrinsically ordered, and a later
probe must exploit the dependency an earlier one established, so its search
starts from the earlier probe's goal — everything the head c-commands above
that goal lies outside its domain, and a structurally closer matching goal is
skipped with minimality respected at every step. `run` is that engine on the
substrate's `FeatureBundle` slots and `Probe.search`: a probe's domain is the
c-command-ordered list of accessible heads (the paper's own notation in (6),
(8), (32), (34)), read off a projection spine by `domain`, which stops at a
phase head's complement (PIC); a valued probe (a case assigner, `[∗Infl:perf∗]`)
matches only an unvalued slot and values its goal, an unvalued probe matches
any specified slot and is valued by an active goal (fn. 23, defective
intervention).

The paper's derivations then run as stated: Standard Italian auxiliary
selection ((9)–(20), over the substrate's `TransitivityClass` and impersonal/passive
`Voice.Flavor`) under the Vocabulary Items (14), the Ariellese and Tufillese orderings and entries
(22)–(24), the ditransitive case/agreement alignments (25)–(28) with
[barany-2024]'s typological gap, Icelandic DAT-NOM (29a/b), Lak perfective
agreement (32), Spanish VOS (34), Bulgarian multiple wh-fronting (36), and
Hindi-Urdu (38)–(40). Out of scope: Merge and binding inside v's cycle (the SCC
ordering of (16)–(17) enters as v's input), participle agreement (§4.3.2), and
the Appendix's comparison with MME, Multitasking and ECoMPS.
-/

namespace Amato2025

open Minimalist Features
open Minimalist.FeatureBundle (ofGramFeatures)
open ArgumentStructure.AuxiliarySelection

variable {H : Type*} [DecidableEq H]

/-! ### The engine -/

/-- The feature state of a derivation: every head's bundle. -/
abbrev State (H : Type*) := H → FeatureBundle

/-- A projection: its specifiers, highest first, over its head. -/
structure Layer (H : Type*) where
  specs : List H
  head : H

/-- The heads a probe above these projections can reach, in c-command order — each
projection's specifiers then its head, down to and including the first phase head,
whose complement the PIC freezes. -/
def domain (phase : H → Bool) : List (Layer H) → List H
  | [] => []
  | l :: ls => l.specs ++ l.head :: (if phase l.head then [] else domain phase ls)

/-- Goal `g` matches the probe at dimension `t` on `α` (fn. 23): an unvalued probe
matches any specified slot — an unvalued one too, defective intervention — while a
valued probe (a case assigner, `[∗Infl:perf∗]`) matches only an unvalued slot, so a
DP whose case is already valued is invisible to case assignment. -/
def goalMatches (s : State H) (α : H) (t : FeatureType) (g : H) : Bool :=
  match s α t with
  | .unvalued => (s g t).isSpecified
  | .valued _ => (s g t).isUnvalued
  | .absent => false

/-- Agree between `α` and its goal `g` at `t`: an unvalued probe copies the goal's value
when the goal has one and is active for `t` (an inactive goal is matched but values
nothing); a valued probe values the goal. -/
def agree (act : H → FeatureType → Bool) (s : State H) (α : H) (t : FeatureType) (g : H) :
    State H :=
  match s α t, s g t with
  | .unvalued, .valued v =>
    if act g t then Function.update s α (Function.update (s α) t (.valued v)) else s
  | .valued v, .unvalued => Function.update s g (Function.update (s g) t (.valued v))
  | _, _ => s

/-- Discharge the probes on `α` in their extrinsic order over `dom` (Definition (1)):
each probe searches for its closest matching goal from the previous probe's goal on —
reusing that "Agree-channel", so what `α` c-commands above it is outside the search —
and from the top of `dom` when the previous probe found no goal (§4.1.2). Returns each
probe's goal and the resulting state. -/
def run (act : H → FeatureType → Bool) (α : H) (dom : List H) (ts : List FeatureType)
    (s : State H) : List (Option H) × State H :=
  go none ts s
where
  go : Option H → List FeatureType → State H → List (Option H) × State H
  | _, [], s => ([], s)
  | prev, t :: ts, s =>
    let g := (Probe.ofVis (goalMatches s α t)).search
      (prev.elim dom (λ β => dom.dropWhile (λ x => decide (x ≠ β))))
    let r := go g ts (g.elim s (agree act s α t))
    (g :: r.1, r.2)

/-- The domain of a probe nested under the goal `β`: the suffix of the c-command order
from `β`. -/
theorem nestedDomain {pre post : List H} {β : H} (hβ : β ∉ pre) :
    (pre ++ β :: post).dropWhile (λ x => decide (x ≠ β)) = β :: post := by
  induction pre with
  | nil => simp
  | cons a pre ih =>
    have ha : a ≠ β := λ h => hβ (h ▸ List.mem_cons.2 (Or.inl rfl))
    simpa [ha] using ih λ h => hβ (List.mem_cons_of_mem _ h)

/-- Trees (2)–(3): the alleged intervener `δ`, c-commanded above the goal `β` of the
first probe, lies outside the domain of every probe nested under `β`. -/
theorem notMem_nestedDomain {pre post : List H} {β δ : H}
    (hnd : (pre ++ β :: post).Nodup) (hδ : δ ∈ pre) :
    δ ∉ (pre ++ β :: post).dropWhile (λ x => decide (x ≠ β)) := by
  obtain ⟨-, -, hdisj⟩ := List.nodup_append.1 hnd
  rw [nestedDomain λ h => hdisj β h β (List.mem_cons.2 (Or.inl rfl)) rfl]
  exact λ h => hdisj δ hδ δ h rfl

/-- Multiple Agree: `[∗wh∗]` reaches every matching goal in c-command order (§4.2.3). -/
def multipleAgree (s : State H) (α : H) (t : FeatureType) (dom : List H) : List H :=
  dom.filter (goalMatches s α t)

/-- (36): the Merge feature `[·wh·]`, nested under the last goal of `[∗wh∗]`, raises it
first; each later application, its landing site being above the probe, searches the
remaining domain afresh. The movers, in order of movement. -/
def whFronting (s : State H) (α : H) (dom : List H) : List H :=
  let p := Probe.ofVis (goalMatches s α .wh)
  match (multipleAgree s α .wh dom).getLast? with
  | none => []
  | some β =>
    (p.search (dom.dropWhile (λ x => decide (x ≠ β)))).toList ++ rest p dom.length (dom.erase β)
where
  rest (p : Probe H) : Nat → List H → List H
  | 0, _ => []
  | n + 1, d =>
    match p.search d with
    | none => []
    | some g => g :: rest p n (d.erase g)

/-! ### The paper's heads -/

/-- The heads of the paper's trees. -/
inductive Head
  | t | perf | asp | c | v | voice | appl | verb
  | dpSbj | dpObj | dpR | dpT | dpDat | dpNom | si | whSbj | whObj
  deriving DecidableEq, Repr, Fintype

/-- v and Voice are phase heads (§3.4.2, fn. 18). -/
def isPhase : Head → Bool
  | .v | .voice => true
  | _ => false

/-- Every goal values its probe. -/
def allActive : Head → FeatureType → Bool := λ _ _ => true

/-- `[ϕ:p]`. -/
def person (p : Person) : GramFeature := .valued (.phi (.person p))

/-! ### Standard Italian auxiliary selection (§3)

Perf bears `[∗Infl:perf∗]` and `[∗π:_∗]`, ordered as in (7) or (22). v first runs its own
cycle over the object ((9), (16)); Perf then probes the vP, T the PerfP (11). -/

/-- A clause of §3.4: v's class (`TransitivityClass`; an unergative verb is transitive
with a covert cognate object bearing default features, fn. 10) under no Voice head, or
under Voice_imp (§3.4.4) or Voice_pass (fn. 18). -/
structure Clause where
  verb : TransitivityClass
  voice : Option Voice.Flavor := none
  deriving DecidableEq, Repr

/-- The heads before Agree, with subject person `p`: Perf `[∗Infl:perf∗], [∗π:_∗]`; T
`[∗case:nom∗], [∗ϕ:_∗]`; a transitive v `[Infl:_], [∗case:acc∗], [∗π:_∗]` or, in (15), a
defective v `[Infl:_]`; Voice_imp `[Infl:_], [π:_]` (20), Voice_pass `[Infl:_]`; the
subject `[ϕ:p], [case:_]`; a full object `[ϕ:3], [case:_]` (the unaccusative theme,
`[ϕ:p]`), a reflexive object `[ϕ:_], [case:_]` (16); *si* `[π:_], [case:_]`. -/
def initial (cl : Clause) (p : Person) : Head → FeatureBundle
  | .perf => ofGramFeatures [.valued (.infl .perf), FeatureType.person.unvalued]
  | .t => ofGramFeatures [.valued (.case .nom), FeatureType.person.unvalued]
  | .v =>
    match cl.verb with
    | .unaccusative => ofGramFeatures [FeatureType.infl.unvalued]
    | _ => ofGramFeatures [FeatureType.infl.unvalued, .valued (.case .acc),
        FeatureType.person.unvalued]
  | .voice =>
    match cl.voice with
    | some .impersonal =>
      ofGramFeatures [FeatureType.infl.unvalued, FeatureType.person.unvalued]
    | some .passive => ofGramFeatures [FeatureType.infl.unvalued]
    | _ => ⊥
  | .si => ofGramFeatures [FeatureType.person.unvalued, FeatureType.case.unvalued]
  | .dpSbj => ofGramFeatures [person p, FeatureType.case.unvalued]
  | .dpObj =>
    match cl.verb with
    | .reflexive => ofGramFeatures [FeatureType.person.unvalued, FeatureType.case.unvalued]
    | .unaccusative => ofGramFeatures [person p, FeatureType.case.unvalued]
    | _ => ofGramFeatures [person .third, FeatureType.case.unvalued]
  | _ => ⊥

/-- The projections below Perf: (10)/(18) for a transitive v, (15) for a defective one,
under the Voice layer of (20) when there is one. -/
def perfSpine (cl : Clause) : List (Layer Head) :=
  (match cl.voice with
    | some .impersonal => [⟨[.si], .voice⟩]
    | some _ => [⟨[], .voice⟩]
    | none => []) ++
  match cl.verb with
  | .unaccusative => [⟨[.dpObj], .v⟩, ⟨[], .verb⟩]
  | _ => [⟨[.dpSbj], .v⟩, ⟨[], .verb⟩, ⟨[], .dpObj⟩]

/-- v's cycle ((9), (16)): accusative, then π-Agree with the object — nothing for a
defective v. -/
def afterV (cl : Clause) (p : Person) : State Head :=
  (run allActive .v [.verb, .dpObj] (if cl.verb = .unaccusative then [] else [.case, .person])
    (initial cl p)).2

/-- Perf's cycle under the feature ordering `ord`. -/
def perfCycle (ord : List FeatureType) (cl : Clause) (p : Person) :
    List (Option Head) × State Head :=
  run allActive .perf (domain isPhase (perfSpine cl)) ord (afterV cl p)

/-- T's cycle (11): nominative, then ϕ. -/
def tCycle (ord : List FeatureType) (cl : Clause) (p : Person) :
    List (Option Head) × State Head :=
  run allActive .t (domain isPhase (⟨[], .perf⟩ :: perfSpine cl)) [.case, .person]
    (perfCycle ord cl p).2

/-- The state after v, Perf and T have probed. -/
def derive (ord : List FeatureType) (cl : Clause) (p : Person) : State Head :=
  (tCycle ord cl p).2

/-- (7): the argument-structure-driven ordering. -/
def standardItalian : List FeatureType := [.infl, .person]

/-- (22): the subject-driven ordering. -/
def ariellese : List FeatureType := [.person, .infl]

/-- Perf's domain in (10): the subject is c-commanded first, then v. -/
example : domain isPhase (perfSpine ⟨.transitive, none⟩) = [.dpSbj, .v] := rfl

/-- (10), (18): `[∗Infl:perf∗]` finds v, and `[∗π:_∗]`, nested under it, agrees with v
across the subject — for transitive, unergative and reflexive v alike. -/
theorem perf_targets_v (c : TransitivityClass) (hc : c ≠ .unaccusative) (p : Person) :
    (perfCycle standardItalian ⟨c, none⟩ p).1 = [some .v, some .v] := by
  revert c p; decide

/-- (15): π-Agree on Perf fails — the defective v bears no person feature and the raised
theme in Spec,v is above the Nested-Agree goal. -/
theorem perf_unaccusative (p : Person) :
    (perfCycle standardItalian ⟨.unaccusative, none⟩ p).1 = [some .v, none] := by
  revert p; decide

/-- (20): both probes on Perf target Voice_imp, whose person feature is unvalued. -/
theorem perf_impersonal (c : TransitivityClass) (p : Person) :
    (perfCycle standardItalian ⟨c, some .impersonal⟩ p).1 = [some .voice, some .voice] := by
  revert c p; decide

/-- (11): T assigns nominative to the subject and, nested under that dependency,
ϕ-agrees with it rather than with the higher Perf. -/
theorem t_targets_subject (p : Person) :
    (tCycle standardItalian ⟨.transitive, none⟩ p).1 = [some .dpSbj, some .dpSbj] := by
  revert p; decide

/-- Vocabulary Items (14): `/AVERE/ ↔ Perf[π:α]`, `/ESSERE/` elsewhere. -/
def standardItalianAux (s : State Head) : PerfectAux :=
  if (s .perf .person).isValued then .have else .be

/-- (4)–(5): the derivation yields exactly the canonical Romance distribution — HAVE with
transitive and unergative verbs, BE with unaccusative and reflexive ones — for every
subject person. -/
theorem standardItalian_aux (c : TransitivityClass) (p : Person) :
    standardItalianAux (derive standardItalian ⟨c, none⟩ p) = canonicalSelection c := by
  revert c p; decide

/-- (5d), fn. 18: under Voice_imp or Voice_pass the auxiliary is BE whatever the verb —
Perf's π-probe, nested under Infl-Agree with Voice, meets an unvalued or absent person
feature. -/
theorem standardItalian_voice (c : TransitivityClass) (f : Voice.Flavor)
    (hf : f = .impersonal ∨ f = .passive) (p : Person) :
    standardItalianAux (derive standardItalian ⟨c, some f⟩ p) = .be := by
  rcases hf with rfl | rfl <;> (revert c p; decide)

/-- (23), Ariellese: `/AVERE/ ↔ Perf[π:-participant]`. -/
def arielleseAux (s : State Head) : PerfectAux :=
  if s .perf .person = .valued .third then .have else .be

/-- (21): under the ordering (22) the auxiliary follows the subject's person alone — BBH
whatever the argument structure (§3.5). -/
theorem ariellese_aux (c : TransitivityClass) (p : Person) :
    arielleseAux (derive ariellese ⟨c, none⟩ p) = if p = .third then .have else .be := by
  revert c p; decide

/-- (24), Tufillese: `/AVERE/ ↔ Perf[π:α] / T[ϕ:3sg]`. -/
def tufilleseAux (s : State Head) : PerfectAux :=
  if (s .perf .person).isValued ∧ s .t .person = .valued .third then .have else .be

/-- The mixed system: BBH where Standard Italian has HAVE, BE where it has BE (§3.5). -/
theorem tufillese_aux (c : TransitivityClass) (p : Person) :
    tufilleseAux (derive standardItalian ⟨c, none⟩ p) =
      if canonicalSelection c = .have ∧ p = .third then .have else .be := by
  revert c p; decide

/-! ### Case and agreement in ditransitive clauses (§4.1.1) -/

/-- The two orderings of `[∗case∗]` and `[∗ϕ:_∗]` on a head. -/
inductive ProbeOrder
  | caseFirst | phiFirst
  deriving DecidableEq, Repr, Fintype

/-- The probes on v, in order. -/
def ProbeOrder.probes : ProbeOrder → List FeatureType
  | .caseFirst => [.case, .person]
  | .phiFirst => [.person, .case]

/-- (25)–(28): v `[∗case:acc∗], [∗ϕ:_∗]` over `DP_R … Appl … V … DP_T`, the recipient
already dative from Appl or not. -/
def ditransitiveInitial (applDat : Bool) : Head → FeatureBundle
  | .v => ofGramFeatures [.valued (.case .acc), FeatureType.person.unvalued]
  | .dpR => ofGramFeatures
      [person .third, if applDat then .valued (.case .dat) else FeatureType.case.unvalued]
  | .dpT => ofGramFeatures [person .third, FeatureType.case.unvalued]
  | _ => ⊥

/-- Which argument v assigns accusative to and which it ϕ-agrees with. -/
structure Alignment where
  caseTarget : Option Head
  agrTarget : Option Head
  deriving DecidableEq, Repr

/-- The alignment v derives under ordering `o` with or without dative from Appl. -/
def ditransitive (o : ProbeOrder) (applDat : Bool) : Alignment :=
  match o, (run allActive .v [.dpR, .appl, .verb, .dpT] o.probes (ditransitiveInitial applDat)).1
    with
  | .caseFirst, [c, a] => ⟨c, a⟩
  | .phiFirst, [a, c] => ⟨c, a⟩
  | _, _ => ⟨none, none⟩

/-- (25): indirective case and agreement — ϕ-Agree with the theme across the recipient. -/
theorem ditransitive_caseFirst_dat : ditransitive .caseFirst true = ⟨some .dpT, some .dpT⟩ := by
  decide

/-- (26): secundative case and agreement. -/
theorem ditransitive_caseFirst_noDat :
    ditransitive .caseFirst false = ⟨some .dpR, some .dpR⟩ := by decide

/-- (27): indirective case, secundative agreement. -/
theorem ditransitive_phiFirst_dat : ditransitive .phiFirst true = ⟨some .dpT, some .dpR⟩ := by
  decide

/-- (28): secundative case and agreement again. -/
theorem ditransitive_phiFirst_noDat :
    ditransitive .phiFirst false = ⟨some .dpR, some .dpR⟩ := by decide

/-- Table 1's gap ([barany-2024]): no ordering and no Appl setting gives accusative on
the recipient with agreement on the theme. -/
theorem no_secundativeCase_indirectiveAgreement (o : ProbeOrder) (d : Bool) :
    ditransitive o d ≠ ⟨some .dpR, some .dpT⟩ := by
  revert o d; decide

/-! ### Icelandic DAT-NOM constructions (§4.1.2) -/

/-- (29a) versus (29b). -/
inductive Clausal
  | monoclausal | biclausal
  deriving DecidableEq, Repr, Fintype

/-- T `[∗case:nom∗], [∗ϕ:_∗]` over `DP_dat … DP_nom`; in (29b) the lower T has already
assigned nominative. -/
def icelandicInitial : Clausal → Head → FeatureBundle
  | _, .t => ofGramFeatures [.valued (.case .nom), FeatureType.number.unvalued]
  | _, .dpDat => ofGramFeatures [.valued (.phi (.number .plural)), .valued (.case .dat)]
  | .monoclausal, .dpNom =>
    ofGramFeatures [.valued (.phi (.number .plural)), FeatureType.case.unvalued]
  | .biclausal, .dpNom => ofGramFeatures [.valued (.phi (.number .plural)), .valued (.case .nom)]
  | _, _ => ⊥

/-- Datives are defective goals for ϕ-Agree: matched, never valuing. -/
def icelandicActive : Head → FeatureType → Bool
  | .dpDat, .number => false
  | _, _ => true

/-- The two orderings that coexist on Icelandic T. -/
def icelandicOrder : ProbeOrder → List FeatureType
  | .caseFirst => [.case, .number]
  | .phiFirst => [.number, .case]

/-- T's number slot after probing. -/
def icelandic (k : Clausal) (o : ProbeOrder) : FeatureSlot FeatureType.number.ValueOf :=
  (run icelandicActive .t [.dpDat, .dpNom] (icelandicOrder o) (icelandicInitial k)).2 .t .number

/-- (29a), case first: nominative to the object, then ϕ-Agree with it across the dative
(*líka*). -/
theorem icelandic_monoclausal_caseFirst :
    icelandic .monoclausal .caseFirst = .valued .plural := by decide

/-- (29a), ϕ first: the dative intervenes defectively — default agreement (*líkar*). -/
theorem icelandic_monoclausal_phiFirst : icelandic .monoclausal .phiFirst = .unvalued := by
  decide

/-- (29b): with nominative assigned below, matrix T's case probe finds no goal, so ϕ is
unrestricted and meets the dative under either ordering — default agreement only. -/
theorem icelandic_biclausal (o : ProbeOrder) : icelandic .biclausal o = .unvalued := by
  revert o; decide

/-! ### Person agreement in the Lak perfective (§4.2.1) -/

/-- (32): Asp `[∗Infl:perf∗], [∗π:_∗]`, v `[Infl:_], [∗π:_∗]`, subject person `ps`, object
person `po`. -/
def lakInitial (ps po : Person) : Head → FeatureBundle
  | .asp => ofGramFeatures [.valued (.infl .perf), FeatureType.person.unvalued]
  | .v => ofGramFeatures [FeatureType.infl.unvalued, FeatureType.person.unvalued]
  | .dpSbj => ofGramFeatures [person ps]
  | .dpObj => ofGramFeatures [person po]
  | _ => ⊥

/-- Asp's person slot after v has agreed with the object and Asp with v. -/
def lak (ps po : Person) : FeatureSlot FeatureType.person.ValueOf :=
  let s := (run allActive .v [.dpObj] [.person] (lakInitial ps po)).2
  (run allActive .asp (domain isPhase [⟨[.dpSbj], .v⟩, ⟨[], .dpObj⟩]) [.infl, .person] s).2
    .asp .person

/-- (31c)–(31d): the perfective auxiliary carries the internal argument's person, whatever
the external argument's. -/
theorem lak_agrees_with_object (ps po : Person) : lak ps po = .valued po := by
  revert ps po; decide

/-! ### Subject agreement in Spanish VOS (§4.2.2) -/

/-- (34): T `[∗case:nom∗], [∗ϕ:_∗]` over the shifted object `[case:acc], [ϕ:α]` and the
subject `[case:_], [ϕ:β]`. -/
def vosInitial : Head → FeatureBundle
  | .t => ofGramFeatures [.valued (.case .nom), FeatureType.person.unvalued]
  | .dpObj => ofGramFeatures [.valued (.case .acc), person .third]
  | .dpSbj => ofGramFeatures [FeatureType.case.unvalued, person .third]
  | _ => ⊥

/-- (33): the case-marked object is no goal for nominative, and ϕ-Agree, nested under
case assignment, targets the subject. -/
theorem vos_subject_agreement :
    (run allActive .t [.dpObj, .dpSbj] [.case, .person] vosInitial).1 =
      [some .dpSbj, some .dpSbj] := by decide

/-! ### Bulgarian multiple wh-fronting (§4.2.3) -/

/-- (36): C `[∗wh∗] ≻ [·wh·]` over wh-sbj in Spec,T, T, and wh-obj at the edge of vP. -/
def bulgarianInitial : Head → FeatureBundle
  | .c => ofGramFeatures [FeatureType.wh.unvalued]
  | .whSbj | .whObj => ofGramFeatures [.valued (.wh true)]
  | _ => ⊥

/-- C's domain in (36). -/
def bulgarianDomain : List Head :=
  domain isPhase [⟨[.whSbj], .t⟩, ⟨[.whObj], .v⟩, ⟨[], .verb⟩]

/-- (35): the object fronts first, the subject lands in the outer specifier, and the base
order is preserved. -/
theorem bulgarian_order : whFronting bulgarianInitial .c bulgarianDomain = [.whObj, .whSbj] := by
  decide

/-- Without Multiple Agree the wh-probe's first goal is the subject, the order minimality
alone predicts. -/
example : (Probe.ofVis (goalMatches bulgarianInitial .c .wh)).search bulgarianDomain =
    some .whSbj := by decide

/-! ### Agreement with unmarked DPs in Hindi-Urdu (§4.3.1) -/

/-- (37)/(39): ergative subject in Spec,Asp; (38a)/(40): both arguments case-marked in
Spec,Asp; (38b): unmarked subject in Spec,v under imperfective Asp. -/
inductive HindiClause
  | ergSubject | bothMarked | unmarkedSubject
  deriving DecidableEq, Repr, Fintype

/-- T `[∗Infl:_∗], [∗ϕ:_∗]`; Asp `[Infl:perf]` or `[Infl:impf]`; v `[∗ϕ:_∗]`; the DPs
with the case Asp assigned them. -/
def hindiInitial (k : HindiClause) (ps po : Person) : Head → FeatureBundle
  | .t => ofGramFeatures [FeatureType.infl.unvalued, FeatureType.person.unvalued]
  | .asp => ofGramFeatures [.valued (.infl (if k = .unmarkedSubject then .impf else .perf))]
  | .v => ofGramFeatures [FeatureType.person.unvalued]
  | .dpSbj => ofGramFeatures
      [person ps, if k = .unmarkedSubject then FeatureType.case.unvalued else .valued (.case .erg)]
  | .dpObj => ofGramFeatures
      [person po, if k = .bothMarked then .valued (.case .acc) else FeatureType.case.unvalued]
  | _ => ⊥

/-- The projections below T in (39), (40) and (38b). -/
def hindiSpine : HindiClause → List (Layer Head)
  | .ergSubject => [⟨[.dpSbj], .asp⟩, ⟨[], .v⟩, ⟨[], .verb⟩, ⟨[], .dpObj⟩]
  | .bothMarked => [⟨[.dpSbj, .dpObj], .asp⟩, ⟨[], .v⟩, ⟨[], .verb⟩]
  | .unmarkedSubject => [⟨[], .asp⟩, ⟨[.dpSbj], .v⟩, ⟨[], .verb⟩, ⟨[], .dpObj⟩]

/-- T's person slot after v has probed its complement (empty in (40), the object having
moved, fn. 33) and T has Infl-agreed with Asp and, nested under it, probed for ϕ. -/
def hindi (k : HindiClause) (ps po : Person) : FeatureSlot FeatureType.person.ValueOf :=
  let s := (run allActive .v (if k = .bothMarked then [] else [.verb, .dpObj]) [.person]
    (hindiInitial k ps po)).2
  (run allActive .t (domain isPhase (hindiSpine k)) [.infl, .person] s).2 .t .person

/-- (37): starting from Asp, ϕ-Agree skips the ergative subject and reaches v's copy of
the object's features. -/
theorem hindi_object_agreement (ps po : Person) : hindi .ergSubject ps po = .valued po := by
  revert ps po; decide

/-- (38a): with both DPs case-marked above Asp, only v's unvalued slot remains — default
agreement. -/
theorem hindi_default_agreement (ps po : Person) : hindi .bothMarked ps po = .unvalued := by
  revert ps po; decide

/-- (38b): an unmarked subject in Spec,v is the first ϕ-goal below Asp. -/
theorem hindi_subject_agreement (ps po : Person) :
    hindi .unmarkedSubject ps po = .valued ps := by
  revert ps po; decide

end Amato2025
