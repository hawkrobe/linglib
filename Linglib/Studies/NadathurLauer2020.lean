import Linglib.Semantics.Causation.Necessity
import Linglib.Semantics.Causation.Sufficiency
import Linglib.Studies.Karttunen1971

/-!
# Nadathur and Lauer (2020): Causal Necessity, Causal Sufficiency, and Causative Verbs

This file formalizes the three scenarios of [nadathur-lauer-2020] and its constraint on
volitional action. Periphrastic *cause* asserts causal necessity and periphrastic *make*
causal sufficiency, two notions that come apart over a structural-equation dynamics after
[pearl-2000]: in the fire scenario the drought is necessary but not sufficient for the
fire, so *cause* is felicitous and *make* is not until the missing precondition is fixed
(`Fire.make_infelicitous_for_fire`, `Fire.make_felicitous_for_fire_with_known_line`); in the
bus scenario the visit is sufficient but not necessary (`Bus.make_felicitous_for_bus`,
`Bus.cause_infelicitous_for_bus`); and in the lighthouse scenario the temporal location
constraint blocks *make* for the earlier of two necessary causes while *cause* survives for
both (`Lighthouse.make_felicitous_for_storms`, `Lighthouse.make_infelicitous_for_earthquake`).
The constraint on volitional action separates *make* from *let*: a permission scenario
satisfies bare sufficiency yet fails it (`Volitional.volitionalActionConstraint`), while
command and persuasion satisfy it. The paper's observation against an entailment-based
taxonomy, that necessity implications are cancellable and reinforceable while sufficiency
implications are not, closes the file.

## Implementation notes

The substrate's necessity semantics implements the actual-cause formulation of
[nadathur-2023-implicatives] rather than the paper's own definition, a move the paper
itself anticipates in suggesting that necessity causatives may be better explicated through
a definition of actual cause; the sufficiency semantics is the sufficiency clause of the
paper's definition, and its non-inevitability precondition is not represented. Preemption
is not formalized, following the paper's decision to set it aside.

## TODO

One necessity proof runs under a raised recursion limit; a structural proof through the
parent equations would remove it.

## References

* [nadathur-lauer-2020]
* [pearl-2000]
* [nadathur-2023-implicatives]
* [karttunen-1971]
-/

namespace NadathurLauer2020

open Causation Causation.Mechanism Causation.SEM
open Causation.Sufficiency (makeSem)
open Causation.Necessity (causeSem)

namespace Fire

/-- Vertices for the fire dynamics (Fig 2): P=power restored, D=drought,
    G=grass inflammable, L=line down, F=fire. -/
inductive V | P | D | G | L | F deriving DecidableEq, Fintype, Repr

/-- Causal graph: G←{D}; F←{G,P,L}; P,D,L exogenous. -/
def graph : CausalGraph V := ⟨λ
  | .P => ∅ | .D => ∅ | .L => ∅
  | .G => {.D}
  | .F => {.G, .P, .L}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := λ | .P => 0 | .D => 0 | .L => 0 | .G => 1 | .F => 2

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- Fire dynamics: G := D (inflammability tracks drought); F := G ∧ P ∧ L
    (fire ignites only when grass inflammable, power on, line touching). -/
noncomputable def fireSEM : BoolSEM V :=
  { graph := graph
    mech := λ
      | .P => const (G := graph) false
      | .D => const (G := graph) false
      | .L => const (G := graph) false
      | .G => deterministic (λ ρ => ρ ⟨.D, by simp [graph]⟩)
      | .F => deterministic (λ ρ =>
          ρ ⟨.G, by simp [graph]⟩ &&
          ρ ⟨.P, by simp [graph]⟩ &&
          ρ ⟨.L, by simp [graph]⟩) }

instance : CausalGraph.IsDAG fireSEM.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic fireSEM where
  mech_det v := match v with
    | .P | .D | .L => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .G | .F => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background s_b: drought conditions and inflammable grass observed,
    line condition unknown. (Per N&L p. 19, footnote 21: realistic
    epistemic ignorance about whether the line was already down.) -/
noncomputable def s_b : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .D true |>.extend .G true

/-- Extended background s_b1: the line is also known to be down. -/
noncomputable def s_b1 : Valuation (λ _ : V => Bool) := s_b.extend .L true

private lemma entails_iff {s : Valuation (λ _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails fireSEM s v x ↔
      SEM.developDetVtxFuel fireSEM s 3 v = some x :=
  SEM.causallyEntails_iff_fuel fireSEM ranking (by cases v <;> decide) s x

/-- (31a) `#Restoring power made the field catch fire.` Make-side: P=true
    is NOT sufficient for F=true relative to s_b. With L undetermined,
    the fire mechanism `G ∧ P ∧ L` stays unsettled (Def 23's clause (b)
    fails). -/
theorem make_infelicitous_for_fire :
    ¬ makeSem fireSEM s_b .P true .F true := by
  rintro ⟨-, hb⟩
  exact absurd (entails_iff.mp hb) (by decide)

/-- (31b, with extended background s_b1 where L is also known) `Restoring
    power caused the field to catch fire.` Both *make* and *cause* hold.
    With s_b1 fixing D=G=L=1, P=true is both sufficient and necessary
    for F=true. -/
theorem make_felicitous_for_fire_with_known_line :
    makeSem fireSEM s_b1 .P true .F true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

end Fire

namespace Bus

/-- Vertices for the bus dynamics (Fig 3): Vis=Ava visiting, Tr=training,
    Rn=rain forecast, Bk=bike gone, Bs=Lia takes the bus. -/
inductive V | Vis | Tr | Rn | Bk | Bs deriving DecidableEq, Fintype, Repr

/-- Causal graph: Bk←{Vis,Tr}; Bs←{Rn,Bk}; Vis,Tr,Rn exogenous. -/
def graph : CausalGraph V := ⟨λ
  | .Vis => ∅ | .Tr => ∅ | .Rn => ∅
  | .Bk => {.Vis, .Tr}
  | .Bs => {.Rn, .Bk}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := λ | .Vis => 0 | .Tr => 0 | .Rn => 0 | .Bk => 1 | .Bs => 2

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- Bus dynamics: Bk := Vis ∧ Tr (bike taken when Ava visits AND trains);
    Bs := Rn ∨ Bk (bus taken when rain OR bike gone). The OR for Bs
    matches Fig 3's `f_B` table on p. 20: B=1 iff R=1 or G=1. This
    creates the "sufficient but unnecessary" structure for T: T=1 forces
    Bs=1 (sufficient via Bk), but Rn=1 alone also forces Bs=1 (so T not
    necessary). -/
noncomputable def busSEM : BoolSEM V :=
  { graph := graph
    mech := λ
      | .Vis => const (G := graph) false
      | .Tr => const (G := graph) false
      | .Rn => const (G := graph) false
      | .Bk => deterministic (λ ρ =>
          ρ ⟨.Vis, by simp [graph]⟩ &&
          ρ ⟨.Tr, by simp [graph]⟩)
      | .Bs => deterministic (λ ρ =>
          ρ ⟨.Rn, by simp [graph]⟩ ||
          ρ ⟨.Bk, by simp [graph]⟩) }

instance : CausalGraph.IsDAG busSEM.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic busSEM where
  mech_det v := match v with
    | .Vis | .Tr | .Rn => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .Bk | .Bs => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background s_b: Ava visiting, rain forecast. Training status Tr is the
    purported cause of bus-taking (via bike taken). -/
noncomputable def s_b : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .Vis true |>.extend .Rn true

private lemma entails_iff {s : Valuation (λ _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails busSEM s v x ↔
      SEM.developDetVtxFuel busSEM s 3 v = some x :=
  SEM.causallyEntails_iff_fuel busSEM ranking (by cases v <;> decide) s x

private lemma necessary_iff {s : Valuation (λ _ : V => Bool)} {c e : V} :
    BoolSEM.causallyNecessary busSEM s c e ↔
      SEM.causallyNecessaryFuel busSEM 3 s c true e true :=
  SEM.causallyNecessary_iff_fuel busSEM ranking
    (by intro v; cases v <;> decide) s c true e true

/-- (33a) `Ava's training made Lia take the bus to work.` Make-side:
    T=true is sufficient for B=true relative to s_b: under the strict
    dynamics Bs stays unsettled in the background (Bk waits on Tr), so
    Def 23's non-inevitability clause (a) holds, and Tr:=1 forces
    Bk:=1 forces Bs:=1 for clause (b). -/
theorem make_felicitous_for_bus :
    makeSem busSEM s_b .Tr true .Bs true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

set_option maxRecDepth 4096 in
/-- (33b) `#Ava's training caused Lia to take the bus.` Cause-side: fails
    Def 10b necessity via the **no-alternative** clause, exactly N&L's
    route: the exogenous settlement `s_b[Tr ↦ 0]` still entails Bs = 1
    (rain alone suffices via the OR mechanism) without entailing Tr = 1. -/
theorem cause_infelicitous_for_bus :
    ¬ causeSem busSEM s_b .Tr true .Bs true := by
  rintro ⟨-, hnec⟩
  exact absurd (necessary_iff.mp hnec) (by decide)

end Bus

/-! Per-vertex temporal index and the temporal-location constraint
    ([nadathur-lauer-2020] Def 28). Local to this study file —
    promote to substrate (`Core/Causal/SEM/Temporal.lean`) if a second
    consumer emerges. -/

namespace Lighthouse

/-- Vertices: Q=earthquake (time 1), S=storms (time 2), L=tower collapse
    (time 3). -/
inductive V | Q | S | L deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨λ
  | .Q => ∅ | .S => ∅
  | .L => {.Q, .S}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := λ | .Q => 0 | .S => 0 | .L => 1

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- Lighthouse dynamics: L := Q ∧ S (collapse requires both
    earthquake-induced foundation damage AND extreme storms). -/
noncomputable def lighthouseSEM : BoolSEM V :=
  { graph := graph
    mech := λ
      | .Q => const (G := graph) false
      | .S => const (G := graph) false
      | .L => deterministic (λ ρ =>
          ρ ⟨.Q, by simp [graph]⟩ &&
          ρ ⟨.S, by simp [graph]⟩) }

instance : CausalGraph.IsDAG lighthouseSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic lighthouseSEM where
  mech_det v := match v with
    | .Q | .S => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .L => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Temporal index: per-vertex timestamp. Q happens at time 1, S at 2,
    L at 3. -/
def lighthouseTimes : V → Nat
  | .Q => 1 | .S => 2 | .L => 3

/-- **Temporal location constraint** ([nadathur-lauer-2020] Def 28):
    a background situation `s` is valid for a causative claim with
    evaluation time `t` iff every vertex `s` fixes has time ≤ t.

    Default evaluation time is the cause's time. -/
def validBackgroundFor (idx : V → Nat) (t : Nat)
    (s : Valuation (λ _ : V => Bool)) : Prop :=
  ∀ v, (s.get v).isSome → idx v ≤ t

private lemma entails_iff {s : Valuation (λ _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails lighthouseSEM s v x ↔
      developDetVtxFuel lighthouseSEM s 2 v = some x :=
  SEM.causallyEntails_iff_fuel lighthouseSEM ranking (by cases v <;> decide) s x

/-- (35d) `The storms made the tower collapse.` Felicitous: with
    background fixing Q=true (the earlier necessary cause), S=true
    suffices for L=true. -/
theorem make_felicitous_for_storms :
    makeSem lighthouseSEM (Valuation.empty.extend .Q true) .S true .L true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

/-- (35c) `#The earthquake made the tower collapse.` Infelicitous via
    Def 28 temporal-location constraint: the only background under which
    Q=true would be sufficient for L=true is one fixing S=true, but S
    happens at time 2 > 1 = time of Q. So no temporally-valid background
    supports the make-claim.

    Concretely: for the make-claim to hold per Def 23(b), the strict
    development of `s + (Q := true)` must fix L = 1, which requires S to
    be fixed in s. But `lighthouseTimes .S = 2 > 1`, so any such `s`
    violates `validBackgroundFor lighthouseTimes 1` — S stays u-valued
    and L = Q ∧ S stays unsettled. -/
theorem make_infelicitous_for_earthquake :
    ∀ s, validBackgroundFor lighthouseTimes 1 s →
      ¬ makeSem lighthouseSEM s .Q true .L true := by
  intro s hValid
  rintro ⟨-, hb⟩
  -- S is fixed by neither s (time 2 > 1) nor the Q-extension, so the
  -- strict dynamics leaves L = Q ∧ S unsettled.
  have hSnone : (s.extend V.Q true).get V.S = none := by
    rw [Valuation.extend_get_ne (by decide : V.S ≠ V.Q)]
    by_contra hSome
    have hIsSome : (s.get V.S).isSome := by
      cases h' : s.get V.S
      · exact absurd h' hSome
      · rfl
    have := hValid V.S hIsSome
    simp [lighthouseTimes] at this
  have hSdev : developDetVtx? lighthouseSEM (s.extend V.Q true) V.S = none :=
    developDetVtx?_exogenous _ hSnone (by decide)
  have hLnone : (s.extend V.Q true).get V.L = none := by
    rw [Valuation.extend_get_ne (by decide : V.L ≠ V.Q)]
    by_contra hSome
    have hIsSome : (s.get V.L).isSome := by
      cases h' : s.get V.L
      · exact absurd h' hSome
      · rfl
    have := hValid V.L hIsSome
    simp [lighthouseTimes] at this
  have hLdev : developDetVtx? lighthouseSEM (s.extend V.Q true) V.L = none :=
    developDetVtx?_inner_none _ hLnone ⟨V.S, by decide⟩ hSdev
  rw [SEM.causallyEntails, hLdev] at hb
  simp at hb

end Lighthouse

/-! N&L's Def 43 distinguishes *make* from sister periphrastics like *let*:
    when the effect is a volitional action with intention vertex W_E,
    the background must not fix W_E in a way that makes the cause
    determinative regardless of the agent's will. -/

namespace Volitional

/-- Pairs an effect vertex with its associated intention vertex (W_E).
    `none` means the effect is not volitional. -/
def IntentionMap (V : Type*) := V → Option V

/-- **Constraint on volitional action** ([nadathur-lauer-2020] Def 43):
    in the evaluation of a make-causative with cause `C` and effect `E`,
    no intention vertex `W_E` paired with `E` may be such that BOTH
    (i) `W_E := false` is sufficient for `E := false` relative to
    `bg + (C := true)` AND (ii) `W_E` is determined by `bg \ (C := true)`.

    For deterministic SEMs `makeSem ... wE false eff false` is the
    sufficiency check; `(bg.remove cause).get wE ≠ none` is the
    determined-ness check. -/
def volitionalActionConstraint {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (intentions : IntentionMap V) (bg : Valuation (λ _ : V => Bool))
    (cause effect : V) : Prop :=
  ∀ wE, intentions effect = some wE →
    ¬ (makeSem M (bg.extend cause true) wE false effect false ∧
       (bg.remove cause).get wE ≠ none)

end Volitional

-- § Permission scenario (Fig 5): make INFELICITOUS

namespace Permission

open Volitional (volitionalActionConstraint IntentionMap)

/-- Vertices: WD = children's desire to dance, G = Gurung's permission,
    D = children dance. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨λ
  | .WD => ∅ | .G => ∅
  | .D => {.WD, .G}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := λ | .WD => 0 | .G => 0 | .D => 1

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- Permission dynamics (Fig 5): D := W_D ∧ G. Both desire AND
    permission needed for dancing. -/
noncomputable def permissionSEM : BoolSEM V :=
  { graph := graph
    mech := λ
      | .WD => const (G := graph) false
      | .G => const (G := graph) false
      | .D => deterministic (λ ρ =>
          ρ ⟨.WD, by simp [graph]⟩ &&
          ρ ⟨.G, by simp [graph]⟩) }

instance : CausalGraph.IsDAG permissionSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic permissionSEM where
  mech_det v := match v with
    | .WD | .G => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .D => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background: children eager to dance (W_D := true). Cause is G
    (Gurung's permission); effect is D (dancing). -/
noncomputable def bg : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .WD true

/-- Intention map: dancing's intention vertex is W_D. -/
def intentions : IntentionMap V := λ
  | .D => some .WD
  | _ => none

private lemma entails_iff {s : Valuation (λ _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails permissionSEM s v x ↔
      developDetVtxFuel permissionSEM s 2 v = some x :=
  SEM.causallyEntails_iff_fuel permissionSEM ranking (by cases v <;> decide) s x

/-- Bare sufficiency holds: G:=true is sufficient for D=true given W_D=true. -/
theorem permission_makeSem :
    makeSem permissionSEM bg .G true .D true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

/-- (40a) `??Gurung made the children dance.` Volitional-action
    constraint VIOLATED: with W_D fixed in bg, W_D := false is sufficient
    for D := false (W_D ∧ G with W_D=false gives false), and W_D is
    determined by bg \ {G} (W_D was in bg, removing G doesn't unfix it).
    Per Def 43, this rules out felicitous use of *make*. -/
theorem permission_violates_volitional_constraint :
    ¬ volitionalActionConstraint permissionSEM intentions bg .G .D := by
  intro h
  -- Specialize to W_D
  apply h .WD rfl
  refine ⟨?_, ?_⟩
  · -- makeSem permissionSEM (bg + G:=true) WD false D false: with G granted,
    -- D = W_D ∧ G is settled true (so D = false is not inevitable), and
    -- revoking the desire settles D = false.
    exact ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩
  · -- (bg.remove .G).get .WD ≠ none. bg fixes .WD=true; removing .G doesn't change that.
    intro hNone
    -- (bg.remove .G).get .WD: .WD ≠ .G so remove doesn't touch it; equals bg.get .WD = some true.
    have : (bg.remove .G).get .WD = some true := by
      simp [Valuation.remove, Valuation.get, bg, Valuation.extend]
    rw [this] at hNone
    exact Option.some_ne_none _ hNone

/-- (40a) Combined predicate: bare make-sufficiency AND volitional constraint
    must BOTH hold for *make* to be felicitous. Permission scenario gives
    the former but fails the latter — N&L's headline §4.1 prediction. -/
theorem permission_make_infelicitous :
    ¬ (makeSem permissionSEM bg .G true .D true ∧
       volitionalActionConstraint permissionSEM intentions bg .G .D) := by
  intro ⟨_, hConstraint⟩
  exact permission_violates_volitional_constraint hConstraint

end Permission

-- § Command scenario (Fig 6): make FELICITOUS

namespace Command

open Volitional (volitionalActionConstraint IntentionMap)

/-- Command scenario: same vertices as Permission, different mechanism.
    Bg may or may not fix W_D — N&L's (41)/(42) show *make* felicitous
    in either case, so command-style mechanism makes W_D irrelevant
    once G fires. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨λ
  | .WD => ∅ | .G => ∅
  | .D => {.WD, .G}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := λ | .WD => 0 | .G => 0 | .D => 1

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- Command dynamics (Fig 6): D := W_D ∨ G. Either authority alone OR
    independent desire suffices for dancing. -/
noncomputable def commandSEM : BoolSEM V :=
  { graph := graph
    mech := λ
      | .WD => const (G := graph) false
      | .G => const (G := graph) false
      | .D => deterministic (λ ρ =>
          ρ ⟨.WD, by simp [graph]⟩ ||
          ρ ⟨.G, by simp [graph]⟩) }

instance : CausalGraph.IsDAG commandSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic commandSEM where
  mech_det v := match v with
    | .WD | .G => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .D => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def intentions : IntentionMap V := λ
  | .D => some .WD
  | _ => none

private lemma entails_iff {s : Valuation (λ _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails commandSEM s v x ↔
      developDetVtxFuel commandSEM s 2 v = some x :=
  SEM.causallyEntails_iff_fuel commandSEM ranking (by cases v <;> decide) s x

/-- (41) context: the children are independently eager (W_D = 1). -/
noncomputable def bgEager : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .WD true

/-- (42) context: the children are reluctant (W_D = 0). -/
noncomputable def bgReluctant : Valuation (λ _ : V => Bool) :=
  Valuation.empty.extend .WD false

/-- (41) Bare sufficiency in the eager context: with W_D = 1 fixed,
    D = W_D ∨ G stays unsettled while G is (Def 23a holds under the
    strict dynamics), and G := 1 settles it. N&L's (41)/(42) contexts
    differ only in the background setting of W_D; *make* is felicitous
    in both. -/
theorem command_makeSem_eager :
    makeSem commandSEM bgEager .G true .D true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

/-- (42) Bare sufficiency in the reluctant context (W_D = 0). -/
theorem command_makeSem_reluctant :
    makeSem commandSEM bgReluctant .G true .D true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

/-- (42a) `Gurung made the children dance` (reluctant context).
    Volitional-action constraint SATISFIED: W_D := false is NOT
    sufficient for D := false (D = W_D ∨ G with G = 1 settles true
    regardless), so Def 43's bad condition fails on its first conjunct. -/
theorem command_satisfies_volitional_constraint :
    volitionalActionConstraint commandSEM intentions bgReluctant .G .D := by
  intro wE hWE
  -- intentions .D = some .WD; so wE = .WD.
  cases hWE
  rintro ⟨⟨-, hb⟩, -⟩
  -- hb : the strict development of bgReluctant + G:=1 + WD:=0 entails D = 0;
  -- but D = W_D ∨ G = 0 ∨ 1 = 1.
  exact absurd (entails_iff.mp hb) (by decide)

/-- (42a) Combined: the reluctant command scenario gives BOTH bare
    sufficiency AND volitional-constraint satisfaction → make-felicitous. -/
theorem command_make_felicitous :
    makeSem commandSEM bgReluctant .G true .D true ∧
    volitionalActionConstraint commandSEM intentions bgReluctant .G .D :=
  ⟨command_makeSem_reluctant, command_satisfies_volitional_constraint⟩

end Command

-- § Persuasion scenario (Fig 7): make FELICITOUS

namespace Persuasion

open Volitional (volitionalActionConstraint IntentionMap)

/-- Persuasion scenario: G manipulates W_D, then W_D drives D.
    Distinct mechanism: G acts via the agent's desire, not in parallel. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨λ
  | .G => ∅
  | .WD => {.G}
  | .D => {.WD}⟩

/-- Depth certificate (also the rank for the fuel bridge). -/
def depth : V → ℕ := λ | .G => 0 | .WD => 1 | .D => 2

private lemma depth_lt : ∀ {u v : V}, u ∈ graph.parents v → depth u < depth v := by
  intro u v h; revert h; cases u <;> cases v <;> decide

private def ranking : CausalGraph.Ranking graph := ⟨depth, depth_lt⟩

instance : CausalGraph.IsDAG graph := ranking.isDAG

/-- Persuasion dynamics (Fig 7): W_D := G (Gurung's action shapes
    desires); D := W_D (children dance iff they want to). -/
noncomputable def persuasionSEM : BoolSEM V :=
  { graph := graph
    mech := λ
      | .G => const (G := graph) false
      | .WD => deterministic (λ ρ => ρ ⟨.G, by simp [graph]⟩)
      | .D => deterministic (λ ρ => ρ ⟨.WD, by simp [graph]⟩) }

instance : CausalGraph.IsDAG persuasionSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic persuasionSEM where
  mech_det v := match v with
    | .G => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .WD | .D => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def intentions : IntentionMap V := λ
  | .D => some .WD
  | _ => none

private lemma entails_iff {s : Valuation (λ _ : V => Bool)} {v : V} {x : Bool} :
    SEM.causallyEntails persuasionSEM s v x ↔
      developDetVtxFuel persuasionSEM s 3 v = some x :=
  SEM.causallyEntails_iff_fuel persuasionSEM ranking (by cases v <;> decide) s x

/-- Bare sufficiency: G:=true forces W_D=true forces D=true. -/
theorem persuasion_makeSem :
    makeSem persuasionSEM Valuation.empty .G true .D true :=
  ⟨λ h => absurd (entails_iff.mp h) (by decide), entails_iff.mpr (by decide)⟩

/-- (44a) `Gurung made the children dance (by playing their favourite song).`
    Volitional-action constraint SATISFIED: although W_D := false is
    sufficient for D := false (D = W_D), W_D is NOT determined by the
    background (empty bg leaves W_D undetermined). Second conjunct of
    Def 43's bad condition fails. -/
theorem persuasion_satisfies_volitional_constraint :
    volitionalActionConstraint persuasionSEM intentions Valuation.empty .G .D := by
  intro wE hWE
  cases hWE
  intro ⟨_, hDet⟩
  -- hDet : (Valuation.empty.remove .G).get .WD ≠ none
  -- But Valuation.empty.get .WD = none, and remove only sets vertices to none.
  apply hDet
  show ((Valuation.empty : Valuation (λ _ : V => Bool)).remove V.G).get V.WD = none
  simp [Valuation.remove, Valuation.get, Valuation.empty]

theorem persuasion_make_felicitous :
    makeSem persuasionSEM Valuation.empty .G true .D true ∧
    volitionalActionConstraint persuasionSEM intentions Valuation.empty .G .D :=
  ⟨persuasion_makeSem, persuasion_satisfies_volitional_constraint⟩

end Persuasion

/-! N&L §4.2 argues that the necessity inference of *make* is a
    pragmatic enrichment, not entailed content. Their argument runs
    through implicature tests:
    - **Cancellability** (49): "Gurung made the children dance, but they
      might have danced anyway" — felicitous, cancels the necessity
      reading without contradiction.
    - **Reinforceability** (50): "The data made me do it. I would never
      have done it otherwise." — felicitous, reinforces the necessity
      reading without redundancy.
    - **Soccer camp (16)**: a fully felicitous use of *make* in an
      explicitly necessity-denying context.

    Structurally, these all follow from N&L's headline result that
    *make* asserts sufficiency only — necessity is a separable layer.
    The Bus and Fire scenarios already witness this:
    - Bus: `make` holds while necessity (`cause`) fails (sufficient ≠ necessary)
    - Fire (with known line): `make` and `cause` hold without redundancy
      (the two assertions are independently informative)

    These scenarios are the structural counterpart of the implicature
    tests; the prose tests follow from them. -/

/-- **Cancellability witness** (cf. (49)): the bus scenario shows that
    *make* can hold while *cause* (necessity) fails. So if *make* did
    entail necessity, this scenario would be contradictory; since it's
    not, the necessity inference must be cancellable. -/
theorem necessity_cancellable :
    makeSem Bus.busSEM Bus.s_b .Tr true .Bs true ∧
    ¬ causeSem Bus.busSEM Bus.s_b .Tr true .Bs true :=
  ⟨Bus.make_felicitous_for_bus, Bus.cause_infelicitous_for_bus⟩

/-- **Reinforceability witness** (cf. (50)): the fire scenario with
    known-line background gives both *make* and (predictably) *cause*
    felicity. Asserting "the data made me do it; I'd never have done it
    otherwise" reinforces necessity onto a sufficiency-asserting
    *make*-claim — felicitous because the two assertions are independent. -/
theorem necessity_reinforceable :
    makeSem Fire.fireSEM Fire.s_b1 .P true .F true :=
  Fire.make_felicitous_for_fire_with_known_line

/-! N&L's central observation against entailment-based taxonomy:
periphrastic causatives share [karttunen-1971]'s sufficient-only
entailment cell while differing in causal mechanism (sufficiency for
*make* vs necessity for *cause*). The comparison is N&L's, so it lives
here; `necessity_cancellable` above is its kernel-checked witness. -/

namespace KarttunenCells

open Karttunen1971 (Schema)

/-- Derive the Karttunen `Schema` cell from an `Implicative` polarity
    (two-way cell: complement entailment under both polarities). -/
def karttunenOfImplicative (b : Implicative) : Schema := ⟨.necessaryAndSufficient, b⟩

/-- Map modern `Causative` to the Karttunen cell that matches the
    builder's **entailment pattern** (Karttunen's original criterion).

    All positive causative builders (make, force, enable, cause) share the
    same Karttunen cell: sufficient-only. This is because:
    - Affirmative "V-ed X to VP" → VP (all require the effect occurred)
    - Negation "didn't V X to VP" ↛ ¬VP (effect might occur from other causes)

    [nadathur-lauer-2020]'s insight: these verbs differ in causal
    MECHANISM (sufficiency vs necessity) despite sharing the same
    ENTAILMENT PATTERN. See `cause_make_same_cell_different_mechanism`. -/
def karttunenOfCausative : Causative → Schema
  | .make | .force | .enable | .cause => ⟨.sufficient, .positive⟩
  | .prevent => ⟨.sufficient, .negative⟩

theorem manage_karttunen_class :
    karttunenOfImplicative .positive = Schema.manage := rfl

theorem fail_karttunen_class :
    karttunenOfImplicative .negative = Schema.fail := rfl

theorem force_karttunen_class :
    karttunenOfCausative .force = Schema.force := rfl

theorem prevent_karttunen_class :
    karttunenOfCausative .prevent = Schema.prevent := rfl

/-- All positive causative builders map to `Schema.force`
    (Karttunen's sufficient-only cell). -/
theorem cause_karttunen_class :
    karttunenOfCausative .cause = Schema.force := rfl

/-- `cause` and `make` have the same Karttunen entailment cell
    (sufficient-only) despite having different causal mechanisms.
    This is the central insight of [nadathur-lauer-2020]: same
    entailment pattern ≠ same truth conditions. The difference is
    kernel-checked at `NadathurLauer2020.necessity_cancellable` (the Bus
    scenario: `makeSem` holds while `causeSem` fails). -/
theorem cause_make_same_cell_different_mechanism :
    karttunenOfCausative .cause = karttunenOfCausative .make ∧
    Causative.cause ≠ .make := ⟨rfl, by decide⟩

end KarttunenCells

end NadathurLauer2020
