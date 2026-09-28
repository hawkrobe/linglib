module

public import Mathlib.Data.Fintype.Prod
public import Linglib.Semantics.Causation.CausalModel.Dependence
public import Linglib.Semantics.Causation.VerbClass
public import Linglib.Semantics.Polarity.Basic
public import Linglib.Core.Relation.ReflTransGen
public import Linglib.Studies.Karttunen1971a
public import Linglib.Fragments.English.Verbs.Inventory

/-!
# Nadathur and Lauer (2020): Causal Necessity, Causal Sufficiency, and Causative Verbs

This file formalizes the lexical entries, the three scenarios, and the constraint on volitional
action of Nadathur and Lauer. Periphrastic *cause* asserts causal necessity and periphrastic *make*
causal sufficiency (`denotation`), two notions that come apart over a structural-equation dynamics
after Pearl: in the fire scenario the drought is necessary but not sufficient for the fire, so
*cause* is felicitous and *make* is not until the missing precondition is fixed
(`Fire.make_infelicitous_for_fire`, `Fire.make_felicitous_for_fire_with_known_line`); in the bus
scenario the visit is sufficient but not necessary (`Bus.make_felicitous_for_bus`,
`Bus.cause_infelicitous_for_bus`); and in the lighthouse scenario the temporal location constraint
blocks *make* for the earlier of two necessary causes while *cause* survives for both
(`Lighthouse.make_felicitous_for_storms`, `Lighthouse.make_infelicitous_for_earthquake`). *Let* and
*force* are sufficiency causatives as well (`denotation_eq_causallySufficient`), and the constraint
on volitional action separates *make* from *let*: a permission scenario satisfies bare sufficiency
yet fails it (`Volitional.volitionalActionConstraint`), while command and persuasion satisfy it. The
paper's observation against an entailment-based taxonomy, that necessity implications are
cancellable and reinforceable while sufficiency implications are not, closes the file.

## Implementation notes

The scenarios are causal models whose exogenous variables read the context, and backgrounds are
observations. The necessity semantics is Nadathur's 2023 actual-cause formulation
(`CausalModel.CausallyNecessary`) rather than the paper's own definition, a move the paper itself
anticipates in suggesting that necessity causatives may be better explicated through a definition
of actual cause; the sufficiency semantics is the paper's Definition (23), both clauses, over the
strict development (`CausalModel.CausallySufficient`).
`denotation` takes the background situation as given: the entries in (25) also remove the cause
from the background and require that the cause occurred, and neither step is represented.
Preemption is not formalized, following the paper's decision to set it aside. The paper gives no
entry for *prevent*; `denotation` fills that class with the blocking semantics of Sloman, Barbey
and Hotaling, read like the other entries by strict entailment: the preventer's value does not
settle the effect, and some other value of it does.

## TODO

The necessity verdict is decided in the kernel over every exogenous settlement; a structural proof
through the parent equations would be more informative. The concluding section suggests that lexical
causatives assert both necessity and sufficiency; the English fragment classes *kill* and *melt*
with *make*, and `denotation` has no class for the conjunction.

## References

* [nadathur-lauer-2020]
* [pearl-2000]
* [nadathur-2023-implicatives]
* [karttunen-1971]
* [sloman-barbey-hotaling-2009]
-/

@[expose] public section

namespace NadathurLauer2020

open CausalModel

/-! ### Lexical entries -/

section Denotation

variable {U V : Type*} {α : V → Type*} [DecidableEq V] (M : CausalModel U V α) [M.IsAcyclic]

/-- A sufficiency causative asserts causal sufficiency. Besides *make* the class holds *let*,
which differs from *make* only in its constraint on background situations (Section 4.1), and
*force* (footnote 25). -/
def IsSufficiencyCausative (b : Causative) : Prop :=
  b = .make ∨ b = .force ∨ b = .enable

instance : DecidablePred IsSufficiencyCausative := fun _ ↦
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

/-- `denotation M b` is the truth condition of the causative class `b` over the dynamics `M`,
relative to a background observation. *Cause* asserts that the cause settles the effect and is
causally necessary for it, and the sufficiency causatives assert causal sufficiency
(Section 3.4); *prevent*, which the paper leaves aside, takes the blocking semantics of
[sloman-barbey-hotaling-2009]. -/
def denotation (b : Causative) (s : ∀ v, Flat (α v)) (c : V) (x : α c) (e : V) (y : α e) :
    Prop :=
  match b with
  | .cause => M.CausallyEntails (Function.update s c ↑x) e y ∧ M.CausallyNecessary s c x e y
  | .make | .force | .enable => M.CausallySufficient s c x e y
  | .prevent => ¬ M.CausallyEntails (Function.update s c ↑x) e y ∧
      ∃ x', x' ≠ x ∧ M.CausallyEntails (Function.update s c ↑x') e y

variable {M}

theorem denotation_eq_causallySufficient {b : Causative} (h : IsSufficiencyCausative b) :
    denotation M b = M.CausallySufficient := by
  rcases h with rfl | rfl | rfl <;> rfl

/-- A sufficiency causative entails that imposing the background and the cause settles the
effect in every context. -/
theorem solve_update_eq_of_denotation {b : Causative} (hb : IsSufficiencyCausative b)
    {s : ∀ v, Flat (α v)} {c : V} {x : α c} {e : V} {y : α e} (h : denotation M b s c x e y)
    [∀ v, Nonempty (α v)] (u : U) : M.solve (Function.update s c ↑x) u e = y := by
  rw [denotation_eq_causallySufficient hb] at h
  exact h.2.solve_eq_of_intervene u

end Denotation

namespace Fire

/-- Vertices for the fire dynamics (Fig 2): P=power restored, D=drought,
    G=grass inflammable, L=line down, F=fire. -/
inductive V | P | D | G | L | F deriving DecidableEq, Fintype, Repr

/-- Fire dynamics: G := D (inflammability tracks drought); F := G ∧ P ∧ L
    (fire ignites only when grass inflammable, power on, line touching). The context settles the
    exogenous P, D and L. -/
def fireModel : CausalModel (Bool × Bool × Bool) V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ w = .D ∧ v = .G ∨ (w = .G ∨ w = .P ∨ w = .L) ∧ v = .F⟩
  eqn
    | .P => fun u _ ↦ u.1
    | .D => fun u _ ↦ u.2.1
    | .L => fun u _ ↦ u.2.2
    | .G => fun _ x ↦ x .D
    | .F => fun _ x ↦ x .G && x .P && x .L

instance : DecidableRel fireModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable (w = .D ∧ v = .G ∨ (w = .G ∨ w = .P ∨ w = .L) ∧ v = .F))

instance : fireModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- Background s_b: drought conditions and inflammable grass observed,
    line condition unknown. (Per N&L p. 19, footnote 21: realistic
    epistemic ignorance about whether the line was already down.) -/
def s_b : V → Flat Bool := Function.update (Function.update ⊥ .D ↑true) .G ↑true

/-- Extended background s_b1: the line is also known to be down. -/
def s_b1 : V → Flat Bool := Function.update s_b .L ↑true

/-- (31a) `#Restoring power made the field catch fire.` Make-side: P=true
    is NOT sufficient for F=true relative to s_b. With L undetermined,
    the fire mechanism `G ∧ P ∧ L` stays unsettled (Def 23's clause (b)
    fails). -/
theorem make_infelicitous_for_fire :
    ¬ fireModel.CausallySufficient s_b .P true .F true := by
  decide

/-- (31b, with extended background s_b1 where L is also known) `Restoring
    power caused the field to catch fire.` Both *make* and *cause* hold.
    With s_b1 fixing D=G=L=1, P=true is both sufficient and necessary
    for F=true. -/
theorem make_felicitous_for_fire_with_known_line :
    fireModel.CausallySufficient s_b1 .P true .F true := by
  decide

end Fire

namespace Bus

/-- Vertices for the bus dynamics (Fig 3): Vis=Ava visiting, Tr=training,
    Rn=rain forecast, Bk=bike gone, Bs=Lia takes the bus. -/
inductive V | Vis | Tr | Rn | Bk | Bs deriving DecidableEq, Fintype, Repr

/-- Bus dynamics: Bk := Vis ∧ Tr (bike taken when Ava visits AND trains);
    Bs := Rn ∨ Bk (bus taken when rain OR bike gone). The OR for Bs
    matches Fig 3's `f_B` table on p. 20: B=1 iff R=1 or G=1. This
    creates the "sufficient but unnecessary" structure for T: T=1 forces
    Bs=1 (sufficient via Bk), but Rn=1 alone also forces Bs=1 (so T not
    necessary). The context settles the exogenous Vis, Tr and Rn. -/
def busModel : CausalModel (Bool × Bool × Bool) V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w = .Vis ∨ w = .Tr) ∧ v = .Bk ∨ (w = .Rn ∨ w = .Bk) ∧ v = .Bs⟩
  eqn
    | .Vis => fun u _ ↦ u.1
    | .Tr => fun u _ ↦ u.2.1
    | .Rn => fun u _ ↦ u.2.2
    | .Bk => fun _ x ↦ x .Vis && x .Tr
    | .Bs => fun _ x ↦ x .Rn || x .Bk

instance : DecidableRel busModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w = .Vis ∨ w = .Tr) ∧ v = .Bk ∨ (w = .Rn ∨ w = .Bk) ∧ v = .Bs))

instance : busModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- Background s_b: Ava visiting, rain forecast. Training status Tr is the
    purported cause of bus-taking (via bike taken). -/
def s_b : V → Flat Bool := Function.update (Function.update ⊥ .Vis ↑true) .Rn ↑true

/-- (33a) `Ava's training made Lia take the bus to work.` Make-side:
    T=true is sufficient for B=true relative to s_b: under the strict
    dynamics Bs stays unsettled in the background (Bk waits on Tr), so
    Def 23's non-inevitability clause (a) holds, and Tr:=1 forces
    Bk:=1 forces Bs:=1 for clause (b). -/
theorem make_felicitous_for_bus : busModel.CausallySufficient s_b .Tr true .Bs true := by
  decide

/-- (33b) `#Ava's training caused Lia to take the bus.` Cause-side: fails
    Def 10b necessity via the **no-alternative** clause, exactly N&L's
    route: the exogenous settlement `s_b[Tr ↦ 0]` still entails Bs = 1
    (rain alone suffices via the OR mechanism) without entailing Tr = 1. -/
theorem cause_infelicitous_for_bus : ¬ denotation busModel .cause s_b .Tr true .Bs true :=
  fun h ↦ absurd h.2 (by decide +kernel)

end Bus

/-! Per-vertex temporal index and the temporal-location constraint
    ([nadathur-lauer-2020] Def 28). -/

namespace Lighthouse

/-- Vertices: Q=earthquake (time 1), S=storms (time 2), L=tower collapse
    (time 3). -/
inductive V | Q | S | L deriving DecidableEq, Fintype, Repr

/-- In the lighthouse dynamics L := Q ∧ S: collapse requires both earthquake-induced foundation
damage and extreme storms. The context settles the exogenous Q and S. -/
def lighthouseModel : CausalModel (Bool × Bool) V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w = .Q ∨ w = .S) ∧ v = .L⟩
  eqn
    | .Q => fun u _ ↦ u.1
    | .S => fun u _ ↦ u.2
    | .L => fun _ x ↦ x .Q && x .S

instance : DecidableRel lighthouseModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w = .Q ∨ w = .S) ∧ v = .L))

instance : lighthouseModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- Temporal index: per-vertex timestamp. Q happens at time 1, S at 2,
    L at 3. -/
def lighthouseTimes : V → Nat
  | .Q => 1 | .S => 2 | .L => 3

/-- **Temporal location constraint** ([nadathur-lauer-2020] Def 28):
    a background situation `s` is valid for a causative claim with
    evaluation time `t` iff every vertex `s` fixes has time ≤ t.

    Default evaluation time is the cause's time. -/
def validBackgroundFor (idx : V → Nat) (t : Nat) (s : V → Flat Bool) : Prop :=
  ∀ v, s v ≠ ⊥ → idx v ≤ t

/-- (35d) `The storms made the tower collapse.` Felicitous: with
    background fixing Q=true (the earlier necessary cause), S=true
    suffices for L=true. -/
theorem make_felicitous_for_storms :
    lighthouseModel.CausallySufficient (Function.update ⊥ .Q ↑true) .S true .L true := by
  decide

/-- (35c) `#The earthquake made the tower collapse.` Infelicitous via
    Def 28 temporal-location constraint: the only background under which
    Q=true would be sufficient for L=true is one fixing S=true, but S
    happens at time 2 > 1 = time of Q. So no temporally-valid background
    supports the make-claim: S, exogenous and unobserved, is settled in no development, and
    L = Q ∧ S waits on it. -/
theorem make_infelicitous_for_earthquake :
    ∀ s, validBackgroundFor lighthouseTimes 1 s →
      ¬ lighthouseModel.CausallySufficient s .Q true .L true := by
  rintro s hValid ⟨-, hb⟩
  have hunset : ∀ v, lighthouseTimes v > 1 → Function.update s .Q ↑true v = ⊥ := fun v hv ↦ by
    have hvQ : v ≠ .Q := by rintro rfl; simp [lighthouseTimes] at hv
    rw [Function.update_of_ne hvQ]
    by_contra h
    exact absurd (hValid v h) (by omega)
  have hS : ∀ z, ¬ lighthouseModel.CausallyEntails (Function.update s .Q ↑true) .S z := by
    intro z h
    rcases causallyEntails_iff.1 h with h | ⟨-, h⟩
    · rw [hunset .S (by decide)] at h; exact Flat.bot_ne_coe h
    · have hno : ∀ w, ¬ lighthouseModel.graph.Adj w .S := by decide
      have h₁ := h.2 (false, true) (fun _ ↦ false) fun w hw ↦ absurd hw (hno w)
      have h₀ := h.2 (false, false) (fun _ ↦ false) fun w hw ↦ absurd hw (hno w)
      exact absurd (h₁.trans h₀.symm) (by decide)
  rcases causallyEntails_iff.1 hb with h | ⟨-, hpar, -⟩
  · rw [hunset .L (by decide)] at h; exact Flat.bot_ne_coe h
  · obtain ⟨z, hz⟩ := hpar .S (by decide)
    exact hS z hz

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
    `bg + (C := true)` AND (ii) `W_E` is determined by `bg \ (C := true)`. -/
def volitionalActionConstraint {U V : Type*} [DecidableEq V]
    (M : CausalModel U V fun _ ↦ Bool) [M.IsAcyclic]
    (intentions : IntentionMap V) (bg : V → Flat Bool) (cause effect : V) : Prop :=
  ∀ wE, intentions effect = some wE →
    ¬ (M.CausallySufficient (Function.update bg cause ↑true) wE false effect false ∧
       Function.update bg cause ⊥ wE ≠ ⊥)

end Volitional

-- § Permission scenario (Fig 5): make INFELICITOUS

namespace Permission

open Volitional (volitionalActionConstraint IntentionMap)

/-- Vertices: WD = children's desire to dance, G = Gurung's permission,
    D = children dance. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

/-- In the permission dynamics (Fig 5) D := W_D ∧ G, both desire and permission being needed for
dancing. The context settles W_D and G. -/
def permissionModel : CausalModel (Bool × Bool) V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w = .WD ∨ w = .G) ∧ v = .D⟩
  eqn | .WD => fun u _ ↦ u.1 | .G => fun u _ ↦ u.2 | .D => fun _ x ↦ x .WD && x .G

instance : DecidableRel permissionModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w = .WD ∨ w = .G) ∧ v = .D))

instance : permissionModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

/-- Background: children eager to dance (W_D := true). Cause is G
    (Gurung's permission); effect is D (dancing). -/
def bg : V → Flat Bool := Function.update ⊥ .WD ↑true

/-- Intention map: dancing's intention vertex is W_D. -/
def intentions : IntentionMap V := fun
  | .D => some .WD
  | _ => none

/-- Bare sufficiency holds: G:=true is sufficient for D=true given W_D=true. -/
theorem permission_makeSem : permissionModel.CausallySufficient bg .G true .D true := by
  decide

/-- (40a) `??Gurung made the children dance.` Volitional-action constraint VIOLATED: with W_D
    fixed in bg, W_D := false is sufficient for D := false (W_D ∧ G with W_D=false gives false),
    and W_D is determined by bg \ {G}. Per Def 43, this rules out felicitous use of *make*. -/
theorem permission_violates_volitional_constraint :
    ¬ volitionalActionConstraint permissionModel intentions bg .G .D :=
  fun h ↦ h .WD rfl ⟨by decide, by decide⟩

/-- (40a) Combined predicate: bare make-sufficiency AND volitional constraint
    must BOTH hold for *make* to be felicitous. Permission scenario gives
    the former but fails the latter — N&L's headline §4.1 prediction. -/
theorem permission_make_infelicitous :
    ¬ (permissionModel.CausallySufficient bg .G true .D true ∧
       volitionalActionConstraint permissionModel intentions bg .G .D) :=
  fun ⟨_, hConstraint⟩ ↦ permission_violates_volitional_constraint hConstraint

end Permission

-- § Command scenario (Fig 6): make FELICITOUS

namespace Command

open Volitional (volitionalActionConstraint IntentionMap)

/-- Command scenario: same vertices as Permission, different mechanism.
    Bg may or may not fix W_D — N&L's (41)/(42) show *make* felicitous
    in either case, so command-style mechanism makes W_D irrelevant
    once G fires. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

/-- In the command dynamics (Fig 6) D := W_D ∨ G, either authority alone or independent desire
sufficing for dancing. The context settles W_D and G. -/
def commandModel : CausalModel (Bool × Bool) V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ (w = .WD ∨ w = .G) ∧ v = .D⟩
  eqn | .WD => fun u _ ↦ u.1 | .G => fun u _ ↦ u.2 | .D => fun _ x ↦ x .WD || x .G

instance : DecidableRel commandModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable ((w = .WD ∨ w = .G) ∧ v = .D))

instance : commandModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

def intentions : IntentionMap V := fun
  | .D => some .WD
  | _ => none

/-- (41) context: the children are independently eager (W_D = 1). -/
def bgEager : V → Flat Bool := Function.update ⊥ .WD ↑true

/-- (42) context: the children are reluctant (W_D = 0). -/
def bgReluctant : V → Flat Bool := Function.update ⊥ .WD ↑false

/-- (41) Bare sufficiency holds in the eager context. With W_D = 1 observed, D = W_D ∨ G is
settled by the strict dynamics only once G is, and G := 1 settles it. N&L's (41)/(42) contexts
differ only in the background setting of W_D; *make* is felicitous in both. -/
theorem command_makeSem_eager : commandModel.CausallySufficient bgEager .G true .D true := by
  decide

/-- (42) Bare sufficiency in the reluctant context (W_D = 0). -/
theorem command_makeSem_reluctant :
    commandModel.CausallySufficient bgReluctant .G true .D true := by
  decide

/-- (42a) `Gurung made the children dance` (reluctant context).
    Volitional-action constraint SATISFIED: W_D := false is NOT
    sufficient for D := false (D = W_D ∨ G with G = 1 settles true
    regardless), so Def 43's bad condition fails on its first conjunct. -/
theorem command_satisfies_volitional_constraint :
    volitionalActionConstraint commandModel intentions bgReluctant .G .D := by
  rintro wE ⟨⟩
  decide

/-- (42a) Combined: the reluctant command scenario gives BOTH bare
    sufficiency AND volitional-constraint satisfaction → make-felicitous. -/
theorem command_make_felicitous :
    commandModel.CausallySufficient bgReluctant .G true .D true ∧
    volitionalActionConstraint commandModel intentions bgReluctant .G .D :=
  ⟨command_makeSem_reluctant, command_satisfies_volitional_constraint⟩

end Command

-- § Persuasion scenario (Fig 7): make FELICITOUS

namespace Persuasion

open Volitional (volitionalActionConstraint IntentionMap)

/-- Persuasion scenario: G manipulates W_D, then W_D drives D.
    Distinct mechanism: G acts via the agent's desire, not in parallel. -/
inductive V | WD | G | D deriving DecidableEq, Fintype, Repr

/-- In the persuasion dynamics (Fig 7) W_D := G, Gurung's action shaping desires, and D := W_D,
the children dancing iff they want to. The context settles G. -/
def persuasionModel : CausalModel Bool V fun _ ↦ Bool where
  graph := ⟨fun w v ↦ w = .G ∧ v = .WD ∨ w = .WD ∧ v = .D⟩
  eqn | .G => fun u _ ↦ u | .WD => fun _ x ↦ x .G | .D => fun _ x ↦ x .WD

instance : DecidableRel persuasionModel.graph.Adj := fun w v ↦
  inferInstanceAs (Decidable (w = .G ∧ v = .WD ∨ w = .WD ∧ v = .D))

instance : persuasionModel.IsAcyclic := Finite.wellFounded_of_irrefl_transGen (by decide)

def intentions : IntentionMap V := fun
  | .D => some .WD
  | _ => none

/-- Bare sufficiency: G:=true forces W_D=true forces D=true. -/
theorem persuasion_makeSem : persuasionModel.CausallySufficient ⊥ .G true .D true := by
  decide

/-- (44a) `Gurung made the children dance (by playing their favourite song).`
    Volitional-action constraint SATISFIED: although W_D := false is
    sufficient for D := false (D = W_D), W_D is NOT determined by the
    background (empty bg leaves W_D undetermined). Second conjunct of
    Def 43's bad condition fails. -/
theorem persuasion_satisfies_volitional_constraint :
    volitionalActionConstraint persuasionModel intentions ⊥ .G .D := by
  rintro wE ⟨⟩
  decide

theorem persuasion_make_felicitous :
    persuasionModel.CausallySufficient ⊥ .G true .D true ∧
    volitionalActionConstraint persuasionModel intentions ⊥ .G .D :=
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
    denotation Bus.busModel .make Bus.s_b .Tr true .Bs true ∧
    ¬ denotation Bus.busModel .cause Bus.s_b .Tr true .Bs true :=
  ⟨Bus.make_felicitous_for_bus, Bus.cause_infelicitous_for_bus⟩

/-- **Reinforceability witness** (cf. (50)): the fire scenario with
    known-line background gives both *make* and (predictably) *cause*
    felicity. Asserting "the data made me do it; I'd never have done it
    otherwise" reinforces necessity onto a sufficiency-asserting
    *make*-claim — felicitous because the two assertions are independent. -/
theorem necessity_reinforceable :
    Fire.fireModel.CausallySufficient Fire.s_b1 .P true .F true :=
  Fire.make_felicitous_for_fire_with_known_line

/-! N&L's central observation against entailment-based taxonomy:
periphrastic causatives share [karttunen-1971]'s sufficient-only
entailment cell while differing in causal mechanism (sufficiency for
*make* vs necessity for *cause*). The comparison is N&L's, so it lives
here; `necessity_cancellable` above is its kernel-checked witness. -/

namespace KarttunenCells

open Karttunen1971a (Schema)

/-- Derive the Karttunen `Schema` cell from an implicative verb's polarity
    (two-way cell: complement entailment under both polarities). -/
def karttunenOfImplicative (b : Polarity) : Schema := ⟨.necessaryAndSufficient, b⟩

/-- Map modern `Causative` to the Karttunen cell that matches the
    builder's **entailment pattern** (Karttunen's original criterion).

    All positive causative builders (make, force, enable, cause) share the
    same Karttunen cell: sufficient-only. This is because:
    - Affirmative "V-ed X to VP" → VP (all require the effect occurred)
    - Negation "didn't V X to VP" ↛ ¬VP (effect might occur from other causes)

    [nadathur-lauer-2020]'s insight: these verbs differ in causal
    MECHANISM (sufficiency vs necessity) despite sharing the same
    ENTAILMENT PATTERN. See `cause_make_same_cell_different_denotation`. -/
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

/-- *cause* and *make* share [karttunen-1971]'s sufficient-only entailment cell yet denote
different relations: in the bus scenario *make* holds and *cause* fails
(`necessity_cancellable`). -/
theorem cause_make_same_cell_different_denotation :
    karttunenOfCausative .cause = karttunenOfCausative .make ∧
    denotation Bus.busModel .cause ≠ denotation Bus.busModel .make :=
  ⟨rfl, fun h ↦ necessity_cancellable.2 <|
    (congrArg (· Bus.s_b .Tr true .Bs true) h).mpr necessity_cancellable.1⟩

end KarttunenCells

/-! ### The English causatives

The English fragment records each causative's class; composing it with `denotation` gives the
paper's predictions. -/

section English

variable {U V : Type*} {α : V → Type*} [DecidableEq V] (M : CausalModel U V α) [M.IsAcyclic]

/-- *Let* asserts the causal sufficiency *make* does (Section 4.1); the volitional action
constraint, not the dependence relation, separates them
(`Permission.permission_make_infelicitous`). -/
theorem let_denotation_eq_make :
    English.Verbs.let_.causative.map (denotation M) =
      English.Verbs.make.causative.map (denotation M) := rfl

example : English.Verbs.force.causative.map (denotation M) = some M.CausallySufficient := rfl

end English

end NadathurLauer2020
