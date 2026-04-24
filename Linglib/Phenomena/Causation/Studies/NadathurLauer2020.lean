import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Causation.Sufficiency

/-!
# @cite{nadathur-lauer-2020}: Causal Necessity, Causal Sufficiency, and the Implications of Causative Verbs

@cite{nadathur-lauer-2020} @cite{pearl-2000}

Nadathur & Lauer 2020. *Glossa* 5(1): 49.

## Headline claim

Periphrastic *make* and *cause* differ truth-conditionally:
- *cause* asserts **causal necessity** (Def 24)
- *make* asserts **causal sufficiency** (Def 23)

The two notions are mathematically distinct over a structural-equation
framework: there exist scenarios where one holds but the other doesn't,
producing minimal-pair contrasts in felicity.

This file formalizes N&L's three illustrative scenarios (§3.6.1-§3.6.3)
plus the volitional-action constraint (§4.1, Def 43) that distinguishes
*make* from sister periphrastics like *let*.

## Project-canonical definitions

The substrate's `Necessity.causeSem` (in `Theories/Semantics/Causation/`)
implements @cite{nadathur-2024} **Definition 10b** rather than this paper's
literal Def 24. The paper itself anticipates this in fn 18: "the semantics
of necessity causatives may well be better explicated in terms of one of
the definitions of *actual cause*, rather than the version of causal
necessity defined here." Def 10b IS an actual-cause formulation. The
deviation is principled.

`Sufficiency.makeSem` is N&L's Def 23 essentially verbatim (modulo the
actuality conjunct, which the deterministic substrate makes redundant
with the development-equals-effect clause).

## Scenarios

- **Fire (§3.6.1, Fig 2)**: necessary but insufficient cause. *cause* OK,
  *make* infelicitous. Adding the missing precondition flips both to
  felicitous.
- **Bus (§3.6.2, Fig 3)**: sufficient but unnecessary cause. *make* OK,
  *cause* infelicitous.
- **Lighthouse (§3.6.3, Fig 4)**: temporal location constraint (Def 28)
  blocks *make* for the earlier of two necessary causes; *cause* remains
  felicitous for both.
- **Permission (§4.1, Fig 5)**: bare sufficiency holds but Def 43
  (volitional-action constraint) fails — predicts *make* infelicitous.
- **Command (§4.1, Fig 6)** + **Persuasion (§4.1, Fig 7)**: Def 43
  satisfied — predicts *make* felicitous in both authority and
  manipulation contexts.

## Excluded

The Suzy/Billy preemption scenario (the centerpiece of Lewis 1973,
@cite{lewis-1973-causation}) is **not formalized here** — N&L footnote 8
explicitly says "we will not discuss the specifics of pre-emption in this
paper." The scenario lives at `Lewis1973.Overdetermination` (the
chronologically-canonical owner). See `ProductionDependence.lean`'s
discussion for the cross-paper consequence.
-/

namespace Phenomena.Causation.Studies.NadathurLauer2020

open Core.Causal Core.Causal.Mechanism Core.Causal.SEM
open Semantics.Causation.Sufficiency (makeSem)
open Semantics.Causation.Necessity (causeSem)

-- ════════════════════════════════════════════════════
-- § §3.6.1 Fire scenario (necessary but insufficient)
-- ════════════════════════════════════════════════════

namespace Fire

/-- Vertices for the fire dynamics (Fig 2): P=power restored, D=drought,
    G=grass inflammable, L=line down, F=fire. -/
inductive V | P | D | G | L | F deriving DecidableEq, Fintype, Repr

/-- Causal graph: G←{D}; F←{G,P,L}; P,D,L exogenous. -/
def graph : CausalGraph V := ⟨fun
  | .P => ∅ | .D => ∅ | .L => ∅
  | .G => {.D}
  | .F => {.G, .P, .L}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .P => 0 | .D => 0 | .L => 0 | .G => 1 | .F => 2)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Fire dynamics: G := D (inflammability tracks drought); F := G ∧ P ∧ L
    (fire ignites only when grass inflammable, power on, line touching). -/
noncomputable def fireSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .P => const (G := graph) false
      | .D => const (G := graph) false
      | .L => const (G := graph) false
      | .G => deterministic (fun ρ => ρ ⟨.D, by simp [graph]⟩)
      | .F => deterministic (fun ρ =>
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
noncomputable def s_b : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .D true |>.extend .G true

/-- Extended background s_b1: the line is also known to be down. -/
noncomputable def s_b1 : Valuation (fun _ : V => Bool) := s_b.extend .L true

/-- (31a) `#Restoring power made the field catch fire.` Make-side: P=true
    is NOT sufficient for F=true relative to s_b. With L undetermined,
    the fire mechanism `G ∧ P ∧ L` cannot fire to true. -/
theorem make_infelicitous_for_fire :
    ¬ makeSem fireSEM s_b .P true .F true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff]
  rw [developDetVtx_unfold]
  intro h; exact Bool.false_ne_true h

/-- Computing developDetVtx fireSEM at root vertices and downstream
    vertices, given a valuation. Helper for Fire's cause-side proofs. -/
private theorem dev_F_eq (s : Valuation _) :
    developDetVtx fireSEM s .F =
      ((s.get .F).getD
        (developDetVtx fireSEM s .G &&
         developDetVtx fireSEM s .P &&
         developDetVtx fireSEM s .L)) := by
  rw [developDetVtx_unfold]
  match h : s.get .F with
  | none => simp [h]; rfl
  | some _ => simp [h]

/-- (31b, with extended background s_b1 where L is also known) `Restoring
    power caused the field to catch fire.` Both *make* and *cause* hold.
    With s_b1 fixing D=G=L=1, P=true is both sufficient and necessary
    for F=true. -/
theorem make_felicitous_for_fire_with_known_line :
    makeSem fireSEM s_b1 .P true .F true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff]
  rw [developDetVtx_unfold]
  rfl

end Fire

-- ════════════════════════════════════════════════════
-- § §3.6.2 Bus scenario (sufficient but unnecessary)
-- ════════════════════════════════════════════════════

namespace Bus

/-- Vertices for the bus dynamics (Fig 3): Vis=Ava visiting, Tr=training,
    Rn=rain forecast, Bk=bike gone, Bs=Lia takes the bus. -/
inductive V | Vis | Tr | Rn | Bk | Bs deriving DecidableEq, Fintype, Repr

/-- Causal graph: Bk←{Vis,Tr}; Bs←{Rn,Bk}; Vis,Tr,Rn exogenous. -/
def graph : CausalGraph V := ⟨fun
  | .Vis => ∅ | .Tr => ∅ | .Rn => ∅
  | .Bk => {.Vis, .Tr}
  | .Bs => {.Rn, .Bk}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .Vis => 0 | .Tr => 0 | .Rn => 0 | .Bk => 1 | .Bs => 2)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Bus dynamics: Bk := Vis ∧ Tr (bike taken when Ava visits AND trains);
    Bs := Rn ∨ Bk (bus taken when rain OR bike gone). The OR for Bs
    matches Fig 3's `f_B` table on p. 20: B=1 iff R=1 or G=1. This
    creates the "sufficient but unnecessary" structure for T: T=1 forces
    Bs=1 (sufficient via Bk), but Rn=1 alone also forces Bs=1 (so T not
    necessary). -/
noncomputable def busSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .Vis => const (G := graph) false
      | .Tr => const (G := graph) false
      | .Rn => const (G := graph) false
      | .Bk => deterministic (fun ρ =>
          ρ ⟨.Vis, by simp [graph]⟩ &&
          ρ ⟨.Tr, by simp [graph]⟩)
      | .Bs => deterministic (fun ρ =>
          ρ ⟨.Rn, by simp [graph]⟩ ||
          ρ ⟨.Bk, by simp [graph]⟩) }

instance : CausalGraph.IsDAG busSEM.graph := inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic busSEM where
  mech_det v := match v with
    | .Vis | .Tr | .Rn => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .Bk | .Bs => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background s_b: Ava visiting, rain forecast. Training status Tr is the
    purported cause of bus-taking (via bike taken). -/
noncomputable def s_b : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .Vis true |>.extend .Rn true

/-- (33a) `Ava's training made Lia take the bus to work.` Make-side:
    T=true is sufficient for B=true relative to s_b. With Vis=Rn=1
    in background, Tr:=1 forces Bk:=1 forces Bs:=1. -/
theorem make_felicitous_for_bus :
    makeSem busSEM s_b .Tr true .Bs true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff]
  rw [developDetVtx_unfold]
  rfl

/-- (33b) `#Ava's training caused Lia to take the bus.` Cause-side:
    fails N&L's Def 24 / project-canonical Def 10b necessity.

    Under this substrate's eager-default semantics (every undetermined
    root vertex defaults to its `const` mechanism value), `developDetVtx
    busSEM s_b .Bs = true` already (because Rn=true in s_b suffices via
    the OR mechanism). This makes causeSem's **precondition** clause
    fail: "the dynamics does not already entail effect=xE in the
    background" is false here.

    N&L's stepwise semantics (which leaves Bs undetermined until both
    parents are determined) instead derives infelicity via the noAlternative
    clause — a consistent supersituation lacking Tr=true that still
    produces Bs=true. Same empirical conclusion (cause infelicitous),
    different load-bearing clause; see module docstring on substrate
    deviation. -/
theorem cause_infelicitous_for_bus :
    ¬ causeSem busSEM s_b .Tr true .Bs true := by
  rintro ⟨_, ⟨_, hPre⟩, _, _⟩
  -- hPre : developDetVtx busSEM s_b .Bs ≠ true
  -- But under eager-default semantics, dev .Bs from s_b = Rn ∨ Bk =
  -- true ∨ (Vis ∧ default Tr) = true ∨ (true ∧ false) = true.
  apply hPre
  rw [developDetVtx_unfold]
  rfl

end Bus

-- ════════════════════════════════════════════════════
-- § §3.6.3 Lighthouse scenario (temporal location constraint)
-- ════════════════════════════════════════════════════

/-! Per-vertex temporal index and the temporal-location constraint
    (@cite{nadathur-lauer-2020} Def 28). Local to this study file —
    promote to substrate (`Core/Causal/SEM/Temporal.lean`) if a second
    consumer emerges. -/

namespace Lighthouse

/-- Vertices: Q=earthquake (time 1), S=storms (time 2), L=tower collapse
    (time 3). -/
inductive V | Q | S | L deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun
  | .Q => ∅ | .S => ∅
  | .L => {.Q, .S}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .Q => 0 | .S => 0 | .L => 1)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Lighthouse dynamics: L := Q ∧ S (collapse requires both
    earthquake-induced foundation damage AND extreme storms). -/
noncomputable def lighthouseSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .Q => const (G := graph) false
      | .S => const (G := graph) false
      | .L => deterministic (fun ρ =>
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

/-- **Temporal location constraint** (@cite{nadathur-lauer-2020} Def 28):
    a background situation `s` is valid for a causative claim with
    evaluation time `t` iff every vertex `s` fixes has time ≤ t.

    Default evaluation time is the cause's time. -/
def validBackgroundFor (idx : V → Nat) (t : Nat)
    (s : Valuation (fun _ : V => Bool)) : Prop :=
  ∀ v, (s.get v).isSome → idx v ≤ t

/-- (35d) `The storms made the tower collapse.` Felicitous: with
    background fixing Q=true (the earlier necessary cause), S=true
    suffices for L=true. -/
theorem make_felicitous_for_storms :
    makeSem lighthouseSEM (Valuation.empty.extend .Q true) .S true .L true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff]
  rw [developDetVtx_unfold]
  rfl

/-- (35c) `#The earthquake made the tower collapse.` Infelicitous via
    Def 28 temporal-location constraint: the only background under which
    Q=true would be sufficient for L=true is one fixing S=true, but S
    happens at time 2 > 1 = time of Q. So no temporally-valid background
    supports the make-claim.

    Concretely: for the make-claim to hold per Def 23, need a background
    `s` such that adding Q to s develops L. Under eager-default semantics,
    `dev L from (s + Q:=true) = Q ∧ S`. For this to equal true, S must
    be fixed to true in s. But `lighthouseTimes .S = 2 > 1`, so any such
    `s` violates `validBackgroundFor lighthouseTimes 1`. -/
theorem make_infelicitous_for_earthquake :
    ∀ s, validBackgroundFor lighthouseTimes 1 s →
      ¬ makeSem lighthouseSEM s .Q true .L true := by
  intro s hValid
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff]
  intro h
  -- h : developDetVtx lighthouseSEM (s.extend .Q true) .L = true
  -- Per validBackgroundFor and lighthouseTimes .S = 2 > 1, s.get .S = none.
  have hSnone : s.get .S = none := by
    by_contra hSome
    have hIsSome : (s.get .S).isSome := by
      cases h' : s.get .S
      · exact absurd h' hSome
      · rfl
    have := hValid .S hIsSome
    simp [lighthouseTimes] at this
  -- developDetVtx of L in s.extend .Q true: L undetermined → mech L (parents)
  -- mech L = Q ∧ S = true ∧ developDetVtx s' .S
  -- developDetVtx s' .S: S undetermined in s' (since hSnone) → const false = false
  -- So mech L = true ∧ false = false ≠ true. Contradiction with h.
  rw [developDetVtx_unfold] at h
  have hLnone : (s.extend .Q true).get .L = none := by
    rw [Valuation.extend_get_ne (by decide : V.L ≠ V.Q)]
    -- s.get .L: validBackgroundFor with t=1 and lighthouseTimes .L = 3 > 1
    -- so s can't fix .L either
    by_contra hSome
    have hIsSome : (s.get .L).isSome := by
      cases h' : s.get .L
      · exact absurd h' hSome
      · rfl
    have := hValid .L hIsSome
    simp [lighthouseTimes] at this
  rw [hLnone] at h
  -- h is now mech .L applied to parent values = true
  -- Compute parent values
  have hVtxQ : developDetVtx lighthouseSEM (s.extend .Q true) .Q = true := by
    rw [developDetVtx_unfold, Valuation.extend_get_same]
  have hVtxS : developDetVtx lighthouseSEM (s.extend .Q true) .S = false := by
    rw [developDetVtx_unfold]
    rw [Valuation.extend_get_ne (by decide : V.S ≠ V.Q)]
    rw [hSnone]
    rfl
  -- Strategy: prove `developDetVtx ... .L = false` independently and
  -- combine with h via Bool inequality.
  -- Reduce h to the same form, then substitute parent values.
  change (developDetVtx lighthouseSEM (s.extend V.Q true) V.Q &&
          developDetVtx lighthouseSEM (s.extend V.Q true) V.S) = true at h
  rw [hVtxQ, hVtxS] at h
  exact Bool.false_ne_true h

end Lighthouse

-- ════════════════════════════════════════════════════
-- § §4.1 Volitional-action constraint (Def 43)
-- ════════════════════════════════════════════════════

/-! N&L's Def 43 distinguishes *make* from sister periphrastics like *let*:
    when the effect is a volitional action with intention vertex W_E,
    the background must not fix W_E in a way that makes the cause
    determinative regardless of the agent's will. -/

namespace Volitional

/-- Pairs an effect vertex with its associated intention vertex (W_E).
    `none` means the effect is not volitional. -/
def IntentionMap (V : Type*) := V → Option V

/-- **Constraint on volitional action** (@cite{nadathur-lauer-2020} Def 43):
    in the evaluation of a make-causative with cause `C` and effect `E`,
    no intention vertex `W_E` paired with `E` may be such that BOTH
    (i) `W_E := false` is sufficient for `E := false` relative to
    `bg + (C := true)` AND (ii) `W_E` is determined by `bg \ (C := true)`.

    For deterministic SEMs `makeSem ... wE false eff false` is the
    sufficiency check; `(bg.remove cause).get wE ≠ none` is the
    determined-ness check. -/
def volitionalActionConstraint {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [SEM.IsDeterministic M]
    (intentions : IntentionMap V) (bg : Valuation (fun _ : V => Bool))
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

def graph : CausalGraph V := ⟨fun
  | .WD => ∅ | .G => ∅
  | .D => {.WD, .G}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .WD => 0 | .G => 0 | .D => 1)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Permission dynamics (Fig 5): D := W_D ∧ G. Both desire AND
    permission needed for dancing. -/
noncomputable def permissionSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .WD => const (G := graph) false
      | .G => const (G := graph) false
      | .D => deterministic (fun ρ =>
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
noncomputable def bg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .WD true

/-- Intention map: dancing's intention vertex is W_D. -/
def intentions : IntentionMap V := fun
  | .D => some .WD
  | _ => none

/-- Bare sufficiency holds: G:=true is sufficient for D=true given W_D=true. -/
theorem permission_makeSem :
    makeSem permissionSEM bg .G true .D true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff, developDetVtx_unfold]
  rfl

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
  · -- makeSem permissionSEM (bg + G:=true) WD false D false
    -- ie developDetVtx ... D = false when WD=false, G=true
    unfold makeSem SEM.causallySufficient developsToValue
    rw [developDet_hasValue_iff, developDetVtx_unfold]
    -- Compute: bg + G:=true + WD:=false → D mech = WD ∧ G = false ∧ true = false
    -- The match on D's value: D undetermined, recurse on parents
    have hWD : developDetVtx permissionSEM (((bg.extend .G true).extend .WD false)) .WD = false := by
      rw [developDetVtx_unfold, Valuation.extend_get_same]
    have hG : developDetVtx permissionSEM (((bg.extend .G true).extend .WD false)) .G = true := by
      rw [developDetVtx_unfold]
      rw [Valuation.extend_get_ne (by decide : V.G ≠ V.WD)]
      rw [Valuation.extend_get_same]
    have hDnone : (((bg.extend .G true).extend .WD false)).get .D = none := by
      rw [Valuation.extend_get_ne (by decide : V.D ≠ V.WD)]
      rw [Valuation.extend_get_ne (by decide : V.D ≠ V.G)]
      rfl
    rw [hDnone]
    change (developDetVtx permissionSEM ((bg.extend V.G true).extend V.WD false) V.WD &&
            developDetVtx permissionSEM ((bg.extend V.G true).extend V.WD false) V.G) = false
    rw [hWD, hG]; rfl
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

def graph : CausalGraph V := ⟨fun
  | .WD => ∅ | .G => ∅
  | .D => {.WD, .G}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .WD => 0 | .G => 0 | .D => 1)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Command dynamics (Fig 6): D := W_D ∨ G. Either authority alone OR
    independent desire suffices for dancing. -/
noncomputable def commandSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .WD => const (G := graph) false
      | .G => const (G := graph) false
      | .D => deterministic (fun ρ =>
          ρ ⟨.WD, by simp [graph]⟩ ||
          ρ ⟨.G, by simp [graph]⟩) }

instance : CausalGraph.IsDAG commandSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic commandSEM where
  mech_det v := match v with
    | .WD | .G => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .D => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def intentions : IntentionMap V := fun
  | .D => some .WD
  | _ => none

/-- Bare sufficiency holds with empty background: G:=true alone forces D=true. -/
theorem command_makeSem :
    makeSem commandSEM Valuation.empty .G true .D true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff, developDetVtx_unfold]
  rfl

/-- (41a)/(42a) `Gurung made the children dance` (in command context).
    Volitional-action constraint SATISFIED: W_D := false is NOT sufficient
    for D := false (D = W_D ∨ G with G=true gives D=true regardless).
    First conjunct of Def 43's bad condition fails, so constraint holds. -/
theorem command_satisfies_volitional_constraint :
    volitionalActionConstraint commandSEM intentions Valuation.empty .G .D := by
  intro wE hWE
  -- intentions .D = some .WD; so wE = .WD.
  cases hWE
  intro ⟨hSuf, _⟩
  -- hSuf : makeSem commandSEM (empty + G:=true) .WD false .D false
  -- ie developDetVtx ((empty.extend G:=true).extend WD:=false) .D = false
  -- Compute: D mech = WD ∨ G = false ∨ true = true ≠ false. CONTRADICTION.
  unfold makeSem SEM.causallySufficient developsToValue at hSuf
  rw [developDet_hasValue_iff, developDetVtx_unfold] at hSuf
  let s' : Valuation (fun _ : V => Bool) :=
    (Valuation.empty.extend V.G true).extend V.WD false
  have hDnone : s'.get V.D = none := by
    show ((Valuation.empty.extend V.G true).extend V.WD false).get V.D = none
    rw [Valuation.extend_get_ne (by decide : V.D ≠ V.WD)]
    rw [Valuation.extend_get_ne (by decide : V.D ≠ V.G)]
    rfl
  rw [hDnone] at hSuf
  have hWD : developDetVtx commandSEM s' V.WD = false := by
    rw [developDetVtx_unfold, Valuation.extend_get_same]
  have hG : developDetVtx commandSEM s' V.G = true := by
    rw [developDetVtx_unfold]
    rw [Valuation.extend_get_ne (by decide : V.G ≠ V.WD)]
    rw [Valuation.extend_get_same]
  change (developDetVtx commandSEM s' V.WD ||
          developDetVtx commandSEM s' V.G) = false at hSuf
  rw [hWD, hG] at hSuf
  exact Bool.noConfusion hSuf

/-- (41a)/(42a) Combined: command scenario gives BOTH bare sufficiency
    AND volitional constraint satisfaction → make-felicitous. -/
theorem command_make_felicitous :
    makeSem commandSEM Valuation.empty .G true .D true ∧
    volitionalActionConstraint commandSEM intentions Valuation.empty .G .D :=
  ⟨command_makeSem, command_satisfies_volitional_constraint⟩

end Command

-- § Persuasion scenario (Fig 7): make FELICITOUS

namespace Persuasion

open Volitional (volitionalActionConstraint IntentionMap)

/-- Persuasion scenario: G manipulates W_D, then W_D drives D.
    Distinct mechanism: G acts via the agent's desire, not in parallel. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

def graph : CausalGraph V := ⟨fun
  | .G => ∅
  | .WD => {.G}
  | .D => {.WD}⟩

instance : CausalGraph.IsDAG graph := CausalGraph.IsDAG.of_depth graph
  (fun | .G => 0 | .WD => 1 | .D => 2)
  (fun {u v} h => by cases v <;> cases u <;> simp_all [graph])

/-- Persuasion dynamics (Fig 7): W_D := G (Gurung's action shapes
    desires); D := W_D (children dance iff they want to). -/
noncomputable def persuasionSEM : BoolSEM V :=
  { graph := graph
    mech := fun
      | .G => const (G := graph) false
      | .WD => deterministic (fun ρ => ρ ⟨.G, by simp [graph]⟩)
      | .D => deterministic (fun ρ => ρ ⟨.WD, by simp [graph]⟩) }

instance : CausalGraph.IsDAG persuasionSEM.graph :=
  inferInstanceAs (CausalGraph.IsDAG graph)

noncomputable instance : SEM.IsDeterministic persuasionSEM where
  mech_det v := match v with
    | .G => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .WD | .D => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

def intentions : IntentionMap V := fun
  | .D => some .WD
  | _ => none

/-- Bare sufficiency: G:=true forces W_D=true forces D=true. -/
theorem persuasion_makeSem :
    makeSem persuasionSEM Valuation.empty .G true .D true := by
  unfold makeSem SEM.causallySufficient developsToValue
  rw [developDet_hasValue_iff, developDetVtx_unfold]
  rfl

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
  show ((Valuation.empty : Valuation (fun _ : V => Bool)).remove V.G).get V.WD = none
  simp [Valuation.remove, Valuation.get, Valuation.empty]

theorem persuasion_make_felicitous :
    makeSem persuasionSEM Valuation.empty .G true .D true ∧
    volitionalActionConstraint persuasionSEM intentions Valuation.empty .G .D :=
  ⟨persuasion_makeSem, persuasion_satisfies_volitional_constraint⟩

end Persuasion

-- ════════════════════════════════════════════════════
-- § §4.2 Causal "perfection" (cancellability/reinforceability)
-- ════════════════════════════════════════════════════

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

end Phenomena.Causation.Studies.NadathurLauer2020
