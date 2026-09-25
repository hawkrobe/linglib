module

public import Linglib.Semantics.Conditionals.Restrictor
public import Linglib.Data.Examples.VonFintelIatridou2005
public import Mathlib.Tactic.DeriveFintype

/-!
# von Fintel & Iatridou (2005): What to Do If You Want to Go to Harlem

This file formalizes [von-fintel-iatridou-2005]'s analysis of anankastic conditionals, the
Harlem sentence *if you want to go to Harlem, you have to take the A train* (1). Three analyses
in [kratzer-1991]'s framework fail. The obvious one, the *if*-clause restricting the modal base
of a teleological *have to* ordered by the actual goals (11), founders on the Hoboken problem:
when you actually want to go to Hoboken the best *want-Harlem* worlds take the PATH train, so the
sentence is predicted false. [saebo-2001]'s analysis adds the hypothetical goal to the ordering
source instead (14), and founders on conflicting goals: with Hoboken and Harlem inconsistent,
the best worlds achieve either, so the sentence is again false (13). The nested analysis, a
covert closeness modal restricted by the *if*-clause over the teleological one (15), (16),
fails where the closest *want-Harlem* worlds keep the Hoboken goal (§5). The paper's proposal
follows [sloman-1970]: a teleological modal takes a designated goal, which every world
quantified over achieves, while the remaining goals are ancillary considerations that rank
those worlds; *have to* quantifies over all goal-achieving accessible worlds and *ought to*
over the best of them (24), so *have to* entails *ought to* and not conversely (`haveTo`,
`oughtTo`). The designated goal overrides the actual goals, which dissolves the Hoboken and
mayor problems (25), (26) and predicts the *have to* and *ought to* verdicts of Huitink's van
Nistelrooy scenario (27). Necessary conditions come out trivially true under *have to* (34),
and [nissenbaum-2005]'s *to go to Harlem, you ought to kiss Pedro Martinez* (36) comes out true,
against which the paper conjectures that the prejacent must be an essential part of a way of
achieving the goal (42), `IsEssentialPart`.

## Implementation notes

The obvious analysis is `Conditional.Restrictor.conditionalNecessity`, and the designated-goal
modals are Kratzer necessity over the base restricted to the goal, with the ancillary ordering
source for *ought to* and the empty one for *have to*. The scenarios are finite world types
with the relevant propositions as predicates and the refutations decided. The condition (42)
quantifies over arbitrary propositions, and so holds of any prejacent as soon as some accessible
world lacks both the prejacent and the goal (`isEssentialPart_of_exists`); the paper leaves the
status of the condition open. The paper's examples are the rows of
`Data.Examples.VonFintelIatridou2005`.

## References

* [von-fintel-iatridou-2005]
* [kratzer-1991]
* [saebo-2001]
* [sloman-1970]
* [nissenbaum-2005]
-/

@[expose] public section

namespace VonFintelIatridou2005

open Modality Conditional.Restrictor

variable {W : Type*} {f : ModalBase W} {g : OrderingSource W} {p q : W → Prop} {w : W}

/-! ### The obvious analysis and the Hoboken problem (§3) -/

/-- In the Hoboken scenario you take the A train or the PATH train, and hypothetically want to go
to Harlem or not; the A train reaches Harlem, the PATH train Hoboken. -/
inductive Hoboken
  /-- Wants Harlem, takes the A train. -/
  | wantA
  /-- Wants Harlem, takes the PATH train. -/
  | wantPath
  /-- Does not want Harlem, takes the A train. -/
  | otherA
  /-- Does not want Harlem, takes the PATH train. -/
  | otherPath
  deriving DecidableEq, Fintype

namespace Hoboken

abbrev wantHarlem : Hoboken → Prop := λ w => w = wantA ∨ w = wantPath
abbrev takeA : Hoboken → Prop := λ w => w = wantA ∨ w = otherA
abbrev goHoboken : Hoboken → Prop := λ w => w = wantPath ∨ w = otherPath
abbrev goHarlem : Hoboken → Prop := takeA

/-- The actual goal in every world is to go to Hoboken. -/
abbrev goals : OrderingSource Hoboken := λ _ => [goHoboken]

/-- On (11), the obvious analysis, the *if*-clause restricting the circumstantial base of a modal
ordered by the actual goals, makes the Harlem sentence false, since the best *want-Harlem*
world takes the PATH train. -/
theorem not_obvious : ¬ conditionalNecessity (λ _ => []) goals wantHarlem takeA wantA := by
  simp only [conditionalNecessity, necessity_iff_all, bestWorlds, mem_bestAmong,
    ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection, atLeastAsGoodAs_iff,
    List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
    Set.mem_ofPred_eq]
  decide

end Hoboken

/-! ### Sæbø's analysis and conflicting goals (§4) -/

/-- The conflicting-goals scenario (13): this afternoon you take the A train to Harlem or the
PATH train to Hoboken, not both. -/
inductive Conflict
  | aTrain
  | pathTrain
  deriving DecidableEq, Fintype

namespace Conflict

abbrev takeA : Conflict → Prop := (· = aTrain)
abbrev goHarlem : Conflict → Prop := takeA
abbrev goHoboken : Conflict → Prop := (· = pathTrain)

/-- Sæbø's ordering source (14) is the actual goal of going to Hoboken with the hypothetical
goal of going to Harlem added. -/
abbrev saebo : OrderingSource Conflict := λ _ => [goHoboken, goHarlem]

/-- Sæbø's analysis makes the Harlem sentence false, since with the two goals inconsistent the
best worlds achieve either, and not all take the A train. -/
theorem not_saebo : ¬ necessity (λ _ => []) saebo takeA aTrain := by
  simp only [necessity_iff_all, bestWorlds, mem_bestAmong, ModalBase.accessibleWorlds,
    propIntersection, atLeastAsGoodAs_iff, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff,
    implies_true, and_true, Set.mem_ofPred_eq]
  decide

end Conflict

/-! ### Nested modality (§5) -/

/-- In the scenario of §5 the closest world in which you want to go to Harlem is one in which
you still want to go to Hoboken as well. -/
inductive Nested
  /-- The actual world: wants Hoboken, takes the PATH train. -/
  | actual
  /-- Wants both, takes the PATH train. -/
  | bothPath
  /-- Wants both, takes the A train. -/
  | bothA
  deriving DecidableEq, Fintype

namespace Nested

abbrev wantHarlem : Nested → Prop := λ w => w = bothPath ∨ w = bothA
abbrev takeA : Nested → Prop := (· = bothA)
abbrev goHoboken : Nested → Prop := λ w => w = actual ∨ w = bothPath
abbrev goHarlem : Nested → Prop := takeA

/-- The goals of each world are Hoboken in the actual world and both in the others. -/
def goals : OrderingSource Nested
  | actual => [goHoboken]
  | _ => [goHoboken, goHarlem]

/-- The closeness ordering of the higher modal is agreement with the actual world on wanting
Hoboken. -/
abbrev closeness : OrderingSource Nested := λ _ => [goHoboken]

/-- On (16), the nested analysis, a closeness modal restricted by the *if*-clause over the
teleological modal, makes the Harlem sentence false, since in the closest *want-Harlem* world
the Hoboken goal survives and the PATH train is among the best worlds. -/
theorem not_nested :
    ¬ conditionalNecessity (λ _ => []) closeness wantHarlem
      (λ w' => necessity (λ _ => []) goals takeA w') actual := by
  simp only [conditionalNecessity, necessity_iff_all, bestWorlds, mem_bestAmong,
    ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection, atLeastAsGoodAs_iff,
    List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
    Set.mem_ofPred_eq]
  intro h
  have := h bothPath (by decide) bothPath
  simp only [goals, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true,
    and_true] at this
  exact absurd (this (by decide)) (by decide)

end Nested

/-! ### Designated goals (§6) -/

/-- *To p, have to q* (24b) holds when every accessible world achieving the designated goal `p`
is a `q`-world. -/
def haveTo (f : ModalBase W) (p q : W → Prop) (w : W) : Prop :=
  conditionalNecessity f emptyBackground p q w

/-- *To p, ought to q* (24a) holds when every accessible world achieving the designated goal `p`
that is best by the ancillary considerations `g` is a `q`-world. -/
def oughtTo (f : ModalBase W) (g : OrderingSource W) (p q : W → Prop) (w : W) : Prop :=
  conditionalNecessity f g p q w

theorem haveTo_iff : haveTo f p q w ↔ ∀ v ∈ f.accessibleWorlds w, p v → q v :=
  (restrictor_eq_strict f p q w).trans Conditional.mem_strictImp_forall

/-- Sloman's insight is that *have to* entails *ought to* whatever the ancillary
considerations. -/
theorem oughtTo_of_haveTo (h : haveTo f p q w) : oughtTo f g p q w := by
  rw [oughtTo, conditionalNecessity, necessity_iff_all]
  intro v hv
  have hv' := mem_propIntersection.1 (bestAmong_subset _ _ hv)
  exact haveTo_iff.1 h v (mem_propIntersection.2 λ r hr => hv' r (List.mem_cons_of_mem _ hr))
    (hv' p (List.mem_cons_self ..))

/-- A necessary condition of the goal is trivially something you have to do (34). -/
theorem haveTo_of_imp (h : ∀ v, p v → q v) : haveTo f p q w :=
  haveTo_iff.2 λ v _ hp => h v hp

/-- In Sloman's London example (23) the train is the best means without being the only one, so
*you ought to take the train, but you don't have to*. World `true` goes by train, `false` by
bus; both arrive by noon, and only the train is comfortable. -/
theorem exists_oughtTo_not_haveTo :
    oughtTo (λ _ : Bool => []) (λ _ => [(· = true)]) (λ _ => True) (· = true) true ∧
      ¬ haveTo (λ _ : Bool => []) (λ _ => True) (· = true) true := by
  simp only [oughtTo, conditionalNecessity, haveTo_iff, necessity_iff_all, bestWorlds,
    mem_bestAmong, ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection,
    atLeastAsGoodAs_iff, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true,
    and_true, Set.mem_ofPred_eq]
  decide

/-- By (25), with going to Harlem the designated goal the Hoboken problem does not arise; you have
to take the A train whatever your actual goals. -/
theorem Hoboken.haveTo_takeA : haveTo (λ _ => []) Hoboken.goHarlem Hoboken.takeA Hoboken.wantA :=
  haveTo_of_imp λ _ h => h

/-- In Huitink's van Nistelrooy scenario (27) both the A and the C train reach Harlem, and Ruud
rides the A train. -/
inductive Ruud
  | aTrain
  | cTrain
  deriving DecidableEq, Fintype

namespace Ruud

abbrev takeA : Ruud → Prop := (· = aTrain)
abbrev meetRuud : Ruud → Prop := takeA

/-- You do not have to take the A train, but given that you want to meet Ruud you ought to. -/
theorem not_haveTo_and_oughtTo :
    ¬ haveTo (λ _ => []) (λ _ => True) takeA aTrain ∧
      oughtTo (λ _ => []) (λ _ => [meetRuud]) (λ _ => True) takeA aTrain := by
  simp only [oughtTo, conditionalNecessity, haveTo_iff, necessity_iff_all, bestWorlds,
    mem_bestAmong, ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection,
    atLeastAsGoodAs_iff, List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true,
    and_true, Set.mem_ofPred_eq]
  decide

end Ruud

/-! ### Kissing Pedro Martinez (§7.2) -/

/-- In Nissenbaum's scenario (36) the A and the C train reach Harlem, Pedro Martinez rides the C
train, and you want to kiss him. -/
inductive Pedro
  | aTrain
  | cTrainKiss
  | home
  deriving DecidableEq, Fintype

namespace Pedro

abbrev goHarlem : Pedro → Prop := λ w => w = aTrain ∨ w = cTrainKiss
abbrev kissPedro : Pedro → Prop := (· = cTrainKiss)

/-- The designated-goal semantics predicts *to go to Harlem, you ought to kiss Pedro Martinez*
true, contrary to fact. -/
theorem oughtTo_kissPedro : oughtTo (λ _ => []) (λ _ => [kissPedro]) goHarlem kissPedro aTrain := by
  simp only [oughtTo, conditionalNecessity, necessity_iff_all, bestWorlds, mem_bestAmong,
    ModalBase.accessibleWorlds, ModalBase.restrict, propIntersection, atLeastAsGoodAs_iff,
    List.forall_mem_cons, List.mem_nil_iff, false_imp_iff, implies_true, and_true,
    Set.mem_ofPred_eq]
  decide

end Pedro

/-- By (42), `q` is an essential part of a way of achieving `p` when some premises together with
`q` entail `p` over the modal base while without `q` they do not. -/
def IsEssentialPart (f : ModalBase W) (p q : W → Prop) (w : W) : Prop :=
  ∃ P : List (W → Prop), (∀ v ∈ propIntersection (f w ++ P ++ [q]), p v) ∧
    ¬ ∀ v ∈ propIntersection (f w ++ P), p v

/-- Over arbitrary premises the condition (42) is undiscriminating, since any prejacent is an
essential part as soon as some accessible world lacks both the prejacent and the goal, the
premise that either the goal holds or the prejacent fails doing the work. -/
theorem isEssentialPart_of_exists (h : ∃ v ∈ f.accessibleWorlds w, ¬ q v ∧ ¬ p v) :
    IsEssentialPart f p q w := by
  obtain ⟨v, hv, hq, hp⟩ := h
  refine ⟨[λ u => p u ∨ ¬ q u], λ u hu => ?_, λ hall => hp (hall v ?_)⟩
  · simp only [propIntersection, Set.mem_ofPred_eq, List.append_assoc, List.mem_append,
      List.mem_singleton, or_imp, forall_and, forall_eq] at hu
    exact hu.2.1.resolve_right (not_not.2 hu.2.2)
  · simp only [propIntersection, Set.mem_ofPred_eq, List.mem_append, List.mem_singleton, or_imp,
      forall_and, forall_eq]
    exact ⟨hv, Or.inr hq⟩

/-- In Nissenbaum's scenario, staying home neither kisses Pedro nor reaches Harlem, so kissing
Pedro counts as essential by (42). -/
theorem Pedro.isEssentialPart_kissPedro :
    IsEssentialPart (λ _ => []) Pedro.goHarlem Pedro.kissPedro Pedro.aTrain :=
  isEssentialPart_of_exists ⟨Pedro.home, λ _ h => (List.mem_nil_iff _).1 h |>.elim, by decide⟩

end VonFintelIatridou2005
