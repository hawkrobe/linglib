module

public import Mathlib.Data.List.Permutation
public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Fragments.Taos.Agreement

/-!
# Middleton (2026): the ordering of impoverishment rules in Taos and Basque

[arregi-nevins-2012] organise the postsyntax into modules: Feature Markedness, where
impoverishment applies, precedes Linearization and the Linear Operations module, where
metathesis applies; and within Feature Markedness the paradigmatic rules, conditioned by the
features of the node they change, apply as a block before the syntagmatic rules, conditioned by
the features of more than one node (their (72), §4.8). [middleton-2026] tests both orderings
against the verbal agreement prefixes of Taos (Kiowa-Tanoan) and finds them unequal: the
Basque and Taos data both need impoverishment before metathesis (§3), but four Taos
interactions need a syntagmatic rule to feed a paradigmatic one (§4.2.1–§4.2.4) while a fifth
needs the reverse (§4.2.5), so the two kinds of impoverishment interleave.

The prefix is the `Prefix` of the paper's (1), an agent, a goal and an object, each a list of
[harbour-2016]'s person and [harbour-2014]'s number features. A Taos rule is a `Rule`: the slot
it changes and an `ImpoverishmentRule` at that slot's `Neighborhood`, so that the paper's
paradigmatic/syntagmatic labels are the library's `Paradigmatic` and `Syntagmatic` and each is
proved. The block architecture is the order `ParaThenSyn` on rule sequences; a paradigmatic and
a syntagmatic rule have one block-conforming order (`run_eq_of_paraThenSyn`), so wherever the
paper shows the two orders differ (`case1_orders_differ` through `case4_orders_differ`) the
block architecture is committed to the wrong prefix. The Basque half runs the domain-level
rules of `Spellout.lean` over the auxiliary: Participant Dissimilation obliterates a clitic, the
T-Noninitiality repairs move an ergative clitic or insert L, and the Ondarru and Zamudio
auxiliaries come out right only with markedness before the linear module.

## Implementation notes

* The dummy object *no* is an object with no features; an absent argument is `none`. Inverse
  agreement is the paper's (8), both values of one number feature (`Inverse`), so the inverse
  witnesses are quantified over any such bundle rather than fixed to one.
* The paper's (27) and (44) mention positions ("the leftmost number bundle", a goal after a
  dual agent); `leftmostMinimal` takes the slot it targets and checks that no earlier slot has
  number features, and the Taos metathesis section works on the linearized feature string,
  where (27) is the deletion of a feature terminal.
* The Basque terminals are clitics with a case feature and T with `[+tense]`, standing in for
  Arregi and Nevins's `[+past]`, which the library's feature inventory lacks; every auxiliary
  here is past tense, so the value never discriminates. Ergative Metathesis fronts the first
  ergative clitic after a word-initial T, Arregi and Nevins's (105), rather than swapping
  adjacent terminals as the paper's (13) has it: the Zamudio auxiliary of (19) has a dative
  clitic between T and the ergative. L-Support and Ergative Metathesis are the two repairs of
  T-Noninitiality and form one module, as in Arregi and Nevins §6.2.4, which is why the
  markedness-after-linear order strands a T-initial auxiliary in `ondarru_linear_then_markedness`
  and `zamudio_linear_then_markedness` rather than producing the paper's starred forms (17b) and
  (19b) verbatim.
* Vocabulary Insertion is not modelled: each theorem ends at the feature bundle the paper reads
  off the exponents, and the docstring names the exponence rule and the table cell.

## TODO

* The complete derivation of Table 1 is in the paper's online appendix, not on file; the
  exponence rules (20)–(22), (31), (33), (34), (38) and (42) and the paradigm itself await it.

## References

* [J. Middleton, *A remark on the ordering of impoverishment rules: differences between Taos
  and Basque*][middleton-2026]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [D. Harbour, *Paucity, abundance, and the theory of number*][harbour-2014]
* [D. Harbour, *Impossible persons*][harbour-2016]
* [C. Kontak and J. Kunkel, *Grammar sketch of Northern Tiwa, Taos dialect*][kontak-kunkel-1987]
* [L. J. Watkins, *A grammar of Kiowa*][watkins-1984]
-/

@[expose] public section

namespace Middleton2026

open Minimalist DistributedMorphology

/-- A terminal: its features, in the decomposition of [harbour-2014] and [harbour-2016]. -/
abbrev Arg := List FeatureVal

/-! ### Person and number

The paper's (2) and (3): Taos distinguishes three persons and three numbers. -/

/-- First person, `[+participant +author]`. -/
def first : Arg := [.participant true, .author true]

/-- Second person, `[+participant −author]`. -/
def second : Arg := [.participant true, .author false]

/-- Third person, `[−participant −author]`. -/
def third : Arg := [.participant false, .author false]

/-- Singular, `[+atomic +minimal]`. -/
def singular : Arg := [.atomic true, .minimal true]

/-- Dual, `[−atomic +minimal]`. -/
def dual : Arg := [.atomic false, .minimal true]

/-- Plural, `[−atomic −minimal]`. -/
def plural : Arg := [.atomic false, .minimal false]

/-- `a` bears every feature of `fs`. -/
def Arg.bears (fs a : Arg) : Bool := fs.all a.contains

/-- `a` has a number feature. -/
def Arg.hasNumber (a : Arg) : Bool :=
  a.any fun | .atomic _ | .minimal _ => true | _ => false

/-- Inverse agreement, the paper's (8): D hosts both values of one number feature. -/
def Inverse (a : Arg) : Prop :=
  (FeatureVal.atomic true ∈ a ∧ FeatureVal.atomic false ∈ a) ∨
    (FeatureVal.minimal true ∈ a ∧ FeatureVal.minimal false ∈ a)

instance : DecidablePred Inverse := fun a ↦
  inferInstanceAs (Decidable ((_ ∈ a ∧ _ ∈ a) ∨ (_ ∈ a ∧ _ ∈ a)))

/-! ### The agreement prefix

The prefix of the paper's (1) agrees with the agent, the goal and the object, linearized in
that order ([watkins-1984]). -/

/-- The three daughters of AgrP in (1), in linear order. -/
inductive Slot where
  | agent
  | goal
  | object
  deriving DecidableEq

/-- The slots before a slot in the linear order of (1). -/
def Slot.before : Slot → List Slot
  | .agent => []
  | .goal => [.agent]
  | .object => [.agent, .goal]

/-- The argument in slot `t`, as a rule at slot `s` sees it: the focus, or the context at the
offset between the two positions of (1). -/
def Slot.view : Slot → Slot → Neighborhood (Option Arg) → Option Arg
  | .agent, .agent, n | .goal, .goal, n | .object, .object, n => n.focus
  | .agent, .goal, n | .goal, .object, n => n.rightCtx.getD 0 none
  | .agent, .object, n => n.rightCtx.getD 1 none
  | .goal, .agent, n | .object, .goal, n => n.leftCtx.getD 0 none
  | .object, .agent, n => n.leftCtx.getD 1 none

/-- The position of a feature within its argument after Linearization, the paper's (4) and
(5): `[±participant] [±author] [±atomic] [±minimal]`. -/
def rank : FeatureVal → ℕ
  | .participant _ => 0
  | .author _ => 1
  | .atomic _ => 2
  | .minimal _ => 3
  | _ => 4

/-- The agreement prefix of (1): the agent, goal and object, each possibly absent. The dummy
object *no* is an object with no features. -/
structure Prefix where
  /-- The agent. -/
  agent : Option Arg
  /-- The goal. -/
  goal : Option Arg
  /-- The object. -/
  object : Option Arg
  deriving DecidableEq

namespace Prefix

/-- The argument in a slot. -/
def get (p : Prefix) : Slot → Option Arg
  | .agent => p.agent
  | .goal => p.goal
  | .object => p.object

/-- Replace the argument in a slot. -/
def set (p : Prefix) : Slot → Option Arg → Prefix
  | .agent, a => { p with agent := a }
  | .goal, a => { p with goal := a }
  | .object, a => { p with object := a }

/-- The neighborhood of a slot: its argument in focus, the other two as context in the order
of (1). -/
def around (p : Prefix) : Slot → Neighborhood (Option Arg)
  | .agent => ⟨p.agent, [], [p.goal, p.object]⟩
  | .goal => ⟨p.goal, [p.agent], [p.object]⟩
  | .object => ⟨p.object, [p.goal, p.agent], []⟩

/-- Seen from any slot's neighborhood, slot `t` holds the prefix's argument for `t`. -/
@[simp] theorem view_around (p : Prefix) (s t : Slot) : s.view t (p.around s) = p.get t := by
  cases s <;> cases t <;> rfl

/-- The features of the prefix after Linearization: each argument's features in the order of
(1), and within an argument `[±participant] [±author] [±atomic] [±minimal]`, the paper's (4)
and (5). -/
def linearize (p : Prefix) : SpelloutDomain FeatureVal :=
  ([p.agent, p.goal, p.object].filterMap id).flatMap fun a ↦
    (List.range 5).flatMap fun k ↦ a.filter (rank · == k)

end Prefix

/-! ### Rules of impoverishment

A rule is the paper's `X → ↯ / context`: the slot whose argument changes, and an
`ImpoverishmentRule` at that slot's neighborhood whose target is the structural change. -/

/-- The structural change of a rule: delete features, or the whole argument. -/
inductive Change where
  | delete (fs : Arg)
  | obliterate

/-- Apply a change to an argument. -/
def Change.apply : Change → Option Arg → Option Arg
  | .delete fs, some a => some (a.filter fun f ↦ !fs.contains f)
  | .delete _, none => none
  | .obliterate, _ => none

/-- A rule of impoverishment over the prefix. -/
structure Rule where
  /-- The slot whose argument the rule changes. -/
  slot : Slot
  /-- The rule at that slot's neighborhood. -/
  rule : ImpoverishmentRule (Option Arg) Change

namespace Rule

/-- A rule conditioned by its own slot's argument. -/
def paradigmatic (s : Slot) (check : Option Arg → Bool) (c : Change) : Rule :=
  ⟨s, .paradigmatic check c⟩

/-- A rule conditioned by the neighborhood. -/
def syntagmatic (s : Slot) (cond : Neighborhood (Option Arg) → Bool) (c : Change) : Rule :=
  ⟨s, .syntagmatic cond c⟩

/-- Apply the rule to the prefix. -/
def apply (r : Rule) (p : Prefix) : Prefix :=
  p.set r.slot (r.rule.apply (fun a c ↦ c.apply a) (p.around r.slot))

/-- The rule is paradigmatic: its condition factors through its own slot. -/
def Paradigmatic (r : Rule) : Prop := r.rule.Paradigmatic

/-- The rule is syntagmatic: its condition reads another slot. -/
def Syntagmatic (r : Rule) : Prop := r.rule.Syntagmatic

theorem paradigmatic_isParadigmatic (s : Slot) (check : Option Arg → Bool) (c : Change) :
    (paradigmatic s check c).Paradigmatic :=
  ImpoverishmentRule.paradigmatic_isParadigmatic check c

end Rule

/-- Apply a sequence of rules in order. -/
def run (rs : List Rule) (p : Prefix) : Prefix := rs.foldl (fun p r ↦ r.apply p) p

@[simp] theorem run_nil (p : Prefix) : run [] p = p := rfl

@[simp] theorem run_cons (r : Rule) (rs : List Rule) (p : Prefix) :
    run (r :: rs) p = run rs (r.apply p) := rfl

/-! ### The block architecture

Arregi and Nevins's (72), `Exponence Conversion > Paradigmatic > Syntagmatic`: the
paradigmatic rules form a block before the syntagmatic ones. -/

/-- A rule sequence respects the block architecture: no syntagmatic rule precedes a
paradigmatic one. -/
def ParaThenSyn (rs : List Rule) : Prop :=
  rs.Pairwise fun r r' ↦ r'.Paradigmatic → r.Paradigmatic

/-- A paradigmatic block followed by a syntagmatic block respects the architecture. -/
theorem paraThenSyn_append {A B : List Rule} (hA : ∀ r ∈ A, r.Paradigmatic)
    (hB : ∀ r ∈ B, r.Syntagmatic) : ParaThenSyn (A ++ B) :=
  List.pairwise_append.mpr
    ⟨List.pairwise_of_forall_mem_list fun r hr _ _ _ ↦ hA r hr,
     List.pairwise_of_forall_mem_list fun _ _ r' hr' h ↦ absurd h (hB r' hr'),
     fun r hr _ _ _ ↦ hA r hr⟩

/-- A paradigmatic and a syntagmatic rule have exactly one order that respects the
architecture. -/
theorem ParaThenSyn.eq_of_perm {p s : Rule} (hp : p.Paradigmatic) (hs : s.Syntagmatic)
    {l : List Rule} (hl : ParaThenSyn l) (hperm : l.Perm [p, s]) : l = [p, s] := by
  rcases List.perm_pair.mp hperm with rfl | rfl
  · rfl
  · exact absurd ((List.pairwise_cons.mp hl).1 p (List.mem_singleton_self p) hp) hs

/-- Under the block architecture, a paradigmatic and a syntagmatic rule apply in that order. -/
theorem run_eq_of_paraThenSyn {p s : Rule} (hp : p.Paradigmatic) (hs : s.Syntagmatic)
    {l : List Rule} (hl : ParaThenSyn l) (hperm : l.Perm [p, s]) (q : Prefix) :
    run l q = run [p, s] q := by
  rw [hl.eq_of_perm hp hs hperm]

/-! ### The Taos rules

The paper's rules of impoverishment, by number. Each syntagmatic rule is proved syntagmatic by
two neighborhoods that share a focus and differ on the condition. -/

/-- (32a), syntagmatic: a singular object loses its third person in the presence of an
agent. -/
def thirdSingularObject : Rule :=
  .syntagmatic .object
    (fun n ↦ (Slot.object.view .agent n).isSome && n.focus.any (singular.bears ·))
    (.delete third)

/-- (32b), syntagmatic: an inverse `[−author]` object loses `[−participant]` in the presence
of an agent. -/
def inverseObject : Rule :=
  .syntagmatic .object
    (fun n ↦ (Slot.object.view .agent n).isSome &&
      n.focus.any fun o ↦ Arg.bears [FeatureVal.author false] o && decide (Inverse o))
    (.delete [FeatureVal.participant false])

/-- (35), paradigmatic: a third singular agent is obliterated, with or without an object. -/
def thirdSingularAgent : Rule :=
  .paradigmatic .agent (·.any ((third ++ singular).bears ·)) .obliterate

/-- (36a), syntagmatic: the dummy object is obliterated after a singular agent. -/
def dummyObject : Rule :=
  .syntagmatic .object
    (fun n ↦ (Slot.object.view .agent n).any (Arg.bears [FeatureVal.atomic true] ·) &&
      n.focus == some [])
    .obliterate

/-- (36b), syntagmatic: the object loses its singular features after a singular agent. -/
def singularObject : Rule :=
  .syntagmatic .object
    (fun n ↦ (Slot.object.view .agent n).any (Arg.bears [FeatureVal.atomic true] ·))
    (.delete singular)

/-- (37), syntagmatic: a first or second singular agent loses `[+minimal]` before a singular
or dummy object. -/
def agentMinimal : Rule :=
  .syntagmatic .agent
    (fun n ↦ n.focus.any (Arg.bears [FeatureVal.participant true, .atomic true] ·) &&
      (Slot.agent.view .object n).any fun o ↦ singular.bears o || o == [])
    (.delete [FeatureVal.minimal true])

/-- (39), paradigmatic: a second singular agent loses `[+participant]`. -/
def secondSingularAgent : Rule :=
  .paradigmatic .agent (·.any (Arg.bears [FeatureVal.author false, .atomic true] ·))
    (.delete [FeatureVal.participant true])

/-- (40), syntagmatic: a singular object loses its third person after a singular goal. -/
def thirdObjectOfSingularGoal : Rule :=
  .syntagmatic .object
    (fun n ↦ (Slot.object.view .goal n).any (singular.bears ·) &&
      n.focus.any (singular.bears ·))
    (.delete third)

/-- (41), syntagmatic: a `[−author]` goal loses its singular features between a dual agent
and a third singular object. -/
def singularGoal : Rule :=
  .syntagmatic .goal
    (fun n ↦ (Slot.goal.view .agent n).any (dual.bears ·) &&
      n.focus.any (Arg.bears [FeatureVal.author false] ·) &&
      (Slot.goal.view .object n).any ((third ++ singular).bears ·))
    (.delete singular)

/-- (43), paradigmatic: a first person `[+minimal]` goal loses `[+atomic]`. -/
def firstSingularGoal : Rule :=
  .paradigmatic .goal (·.any ((first ++ [FeatureVal.minimal true]).bears ·))
    (.delete [FeatureVal.atomic true])

/-- Slot `s` holds the leftmost number features of the neighborhood. -/
def leftmostNumber (s : Slot) (n : Neighborhood (Option Arg)) : Bool :=
  s.before.all fun t ↦ !(s.view t n).any Arg.hasNumber

/-- (44), syntagmatic: the leftmost number bundle, in slot `s`, loses `[+minimal]` when it is
singular and the object is third person inverse. -/
def leftmostMinimal (s : Slot) : Rule :=
  .syntagmatic s
    (fun n ↦ leftmostNumber s n && n.focus.any (Arg.bears [FeatureVal.atomic true] ·) &&
      (s.view .object n).any fun o ↦ third.bears o && decide (Inverse o))
    (.delete [FeatureVal.minimal true])

theorem thirdSingularAgent_paradigmatic : thirdSingularAgent.Paradigmatic :=
  Rule.paradigmatic_isParadigmatic _ _ _

theorem secondSingularAgent_paradigmatic : secondSingularAgent.Paradigmatic :=
  Rule.paradigmatic_isParadigmatic _ _ _

theorem firstSingularGoal_paradigmatic : firstSingularGoal.Paradigmatic :=
  Rule.paradigmatic_isParadigmatic _ _ _

/-- The 3S:3S transitive prefix, Table 15: ∅. -/
def prefix3S3S : Prefix := ⟨some (third ++ singular), none, some (third ++ singular)⟩

theorem form_3S3S :
    Taos.form ⟨some (.third, .singular), none, some (.third .singular)⟩ = some "" := by
  decide

/-- The 3S:3I transitive prefix, Table 15: *í*, for any inverse third person object. -/
def prefix3S3I (o : Arg) : Prefix := ⟨some (third ++ singular), none, some o⟩

theorem form_3S3I :
    Taos.form ⟨some (.third, .singular), none, some (.third .inverse)⟩ = some "i" := by
  decide

/-- The 3S:no transitive prefix, Table 16: ∅. -/
def prefix3Sno : Prefix := ⟨some (third ++ singular), none, some []⟩

theorem form_3Sno : Taos.form ⟨some (.third, .singular), none, some .dummy⟩ = some "" := by
  decide

/-- The 2S:3S transitive prefix, Table 17: *o*. -/
def prefix2S3S : Prefix := ⟨some (second ++ singular), none, some (third ++ singular)⟩

/-- The 2S intransitive prefix, Table 17: *ǫ*. -/
def prefix2S : Prefix := ⟨some (second ++ singular), none, none⟩

/-- The transitive and intransitive 2S prefixes differ. -/
theorem form_2S3S_ne_form_2S :
    Taos.form ⟨some (.second, .singular), none, some (.third .singular)⟩ ≠
      Taos.form ⟨some (.second, .singular), none, none⟩ := by
  decide

/-- The 1S:3S possessive prefix, Table 22: *ôn*. -/
def prefix1S3S : Prefix := ⟨none, some (first ++ singular), some (third ++ singular)⟩

/-- The 1S:3S possessive prefix has no *m*. -/
theorem form_1S3S :
    ∀ f ∈ Taos.form ⟨none, some (.first, .singular), some (.third .singular)⟩,
      f = "ôn" ∧ 'm' ∉ f.toList := by
  decide

/-- The 1S:3I possessive prefix, Table 22: *ónôm*, for any inverse third person object. -/
def prefix1S3I (o : Arg) : Prefix := ⟨none, some (first ++ singular), some o⟩

/-- The 1S:3I possessive prefix keeps *n*. -/
theorem form_1S3I :
    ∀ f ∈ Taos.form ⟨none, some (.first, .singular), some (.third .inverse)⟩,
      f = "ónôm" ∧ 'n' ∈ f.toList := by
  decide

/-- The 1D:3S:3S ditransitive prefix, Table 21: *opénôm*. -/
def prefix1D3S3S : Prefix :=
  ⟨some (first ++ dual), some (third ++ singular), some (third ++ singular)⟩

/-- The 1D:3S:3S ditransitive prefix keeps *m*. -/
theorem form_1D3S3S :
    ∀ f ∈ Taos.form
        ⟨some (.first, .dual), some (.third, .singular), some (.third .singular)⟩,
      f = "opénôm" ∧ 'm' ∈ f.toList := by
  decide

theorem thirdSingularObject_syntagmatic : thirdSingularObject.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3S3S.around .object)
    ((⟨none, none, some (third ++ singular)⟩ : Prefix).around .object) rfl).mp (by decide))
    (by decide)

theorem dummyObject_syntagmatic : dummyObject.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3Sno.around .object) ((⟨none, none, some []⟩ : Prefix).around .object)
    rfl).mp (by decide)) (by decide)

theorem singularObject_syntagmatic : singularObject.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3S3S.around .object)
    ((⟨none, none, some (third ++ singular)⟩ : Prefix).around .object) rfl).mp (by decide))
    (by decide)

theorem agentMinimal_syntagmatic : agentMinimal.Syntagmatic := by
  intro h
  exact absurd ((h (prefix2S3S.around .agent) (prefix2S.around .agent) rfl).mp (by decide))
    (by decide)

theorem thirdObjectOfSingularGoal_syntagmatic : thirdObjectOfSingularGoal.Syntagmatic := by
  intro h
  exact absurd ((h (prefix1S3S.around .object) (prefix3S3S.around .object) rfl).mp (by decide))
    (by decide)

theorem singularGoal_syntagmatic : singularGoal.Syntagmatic := by
  intro h
  exact absurd ((h (prefix1D3S3S.around .goal)
    ((⟨none, some (third ++ singular), some (third ++ singular)⟩ : Prefix).around .goal) rfl).mp
    (by decide)) (by decide)

/-! ### Case 1 (§4.2.1): object impoverishment precedes agent impoverishment

The 3S:3S prefix is ∅ (Table 15), so no *m*, the exponent of a third person object (31), is
inserted: the object's third person must be gone at Vocabulary Insertion, which (32a) does only
while the agent is still there for its context. -/

theorem case1_syn_para :
    run [thirdSingularObject, thirdSingularAgent] prefix3S3S = ⟨none, none, some singular⟩ := by
  decide

theorem case1_para_syn :
    run [thirdSingularAgent, thirdSingularObject] prefix3S3S =
      ⟨none, none, some (third ++ singular)⟩ := by
  decide

theorem case1_orders_differ :
    run [thirdSingularObject, thirdSingularAgent] prefix3S3S ≠
      run [thirdSingularAgent, thirdSingularObject] prefix3S3S := by
  decide

/-- The block architecture keeps the object's third person, and so inserts *m*. -/
theorem case1_block (l : List Rule) (hl : ParaThenSyn l)
    (hperm : l.Perm [thirdSingularAgent, thirdSingularObject]) :
    (run l prefix3S3S).object = some (third ++ singular) := by
  rw [run_eq_of_paraThenSyn thirdSingularAgent_paradigmatic thirdSingularObject_syntagmatic hl
    hperm, case1_para_syn]

/-- The same for the 3S:3I prefix and (32b): syntagmatic first, the object loses
`[−participant]`; paradigmatic first, it keeps it. -/
theorem case1_inverse (o : Arg) (ho : third.bears o ∧ Inverse o) :
    (∀ x ∈ (run [inverseObject, thirdSingularAgent] (prefix3S3I o)).object,
        FeatureVal.participant false ∉ x) ∧
      (run [thirdSingularAgent, inverseObject] (prefix3S3I o)).object = some o := by
  obtain ⟨h₁, h₂⟩ := ho
  simp only [Arg.bears, third, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.contains_iff_mem] at h₁
  simp [run, Rule.apply, Prefix.set, Prefix.around, Slot.view, inverseObject, thirdSingularAgent,
    Rule.syntagmatic, Rule.paradigmatic, ImpoverishmentRule.apply, ImpoverishmentRule.syntagmatic,
    ImpoverishmentRule.paradigmatic, Change.apply, prefix3S3I, h₁, h₂, third, singular,
    Arg.bears]

/-! ### Case 2 (§4.2.2): dummy object impoverishment precedes agent impoverishment

The 3S:no and 3S:3S prefixes are ∅ and toneless (Table 16), so the object is obliterated and its
singular features deleted by (36), which need the singular agent that (35) removes. -/

theorem case2_dummy_syn_para :
    run [dummyObject, thirdSingularAgent] prefix3Sno = ⟨none, none, none⟩ := by
  decide

theorem case2_dummy_para_syn :
    run [thirdSingularAgent, dummyObject] prefix3Sno = ⟨none, none, some []⟩ := by
  decide

theorem case2_singular_syn_para :
    run [thirdSingularObject, singularObject, thirdSingularAgent] prefix3S3S =
      ⟨none, none, some []⟩ := by
  decide

theorem case2_singular_para_syn :
    run [thirdSingularAgent, thirdSingularObject, singularObject] prefix3S3S =
      ⟨none, none, some (third ++ singular)⟩ := by
  decide

theorem case2_orders_differ :
    run [dummyObject, thirdSingularAgent] prefix3Sno ≠
      run [thirdSingularAgent, dummyObject] prefix3Sno := by
  decide

/-- The block architecture keeps the dummy object. -/
theorem case2_block (l : List Rule) (hl : ParaThenSyn l)
    (hperm : l.Perm [thirdSingularAgent, dummyObject]) :
    (run l prefix3Sno).object = some [] := by
  rw [run_eq_of_paraThenSyn thirdSingularAgent_paradigmatic dummyObject_syntagmatic hl hperm,
    case2_dummy_para_syn]

/-! ### Case 3 (§4.2.3): `[+minimal]` impoverishment precedes `[+participant]` impoverishment

The 2S:3S transitive prefix *o* differs from the 2S intransitive *ǫ* (Table 17), so the two
agents differ at Vocabulary Insertion. (37) makes them differ by deleting `[+minimal]` from the
transitive agent, and needs the `[+participant]` that (39) deletes. -/

theorem case3_syn_para :
    (run [agentMinimal, secondSingularAgent] prefix2S3S).agent =
      some [.author false, .atomic true] := by
  decide

theorem case3_para_syn :
    (run [secondSingularAgent, agentMinimal] prefix2S3S).agent =
      (run [secondSingularAgent] prefix2S).agent := by
  decide

theorem case3_orders_differ :
    run [agentMinimal, secondSingularAgent] prefix2S3S ≠
      run [secondSingularAgent, agentMinimal] prefix2S3S := by
  decide

/-- The block architecture makes the transitive and intransitive 2S agents identical. -/
theorem case3_block (l : List Rule) (hl : ParaThenSyn l)
    (hperm : l.Perm [secondSingularAgent, agentMinimal]) :
    (run l prefix2S3S).agent = (run [secondSingularAgent] prefix2S).agent := by
  rw [run_eq_of_paraThenSyn secondSingularAgent_paradigmatic agentMinimal_syntagmatic hl hperm,
    case3_para_syn]

/-! ### Case 4 (§4.2.4): third singular object impoverishment precedes possessive impoverishment

The 1S:3S possessive prefix is *ôn* (Table 22), with no *m*: the object's third person is
deleted by (40), which needs the singular goal that (43) makes non-singular. -/

theorem case4_syn_para :
    run [thirdObjectOfSingularGoal, firstSingularGoal] prefix1S3S =
      ⟨none, some (first ++ [FeatureVal.minimal true]), some singular⟩ := by
  decide

theorem case4_para_syn :
    run [firstSingularGoal, thirdObjectOfSingularGoal] prefix1S3S =
      ⟨none, some (first ++ [FeatureVal.minimal true]), some (third ++ singular)⟩ := by
  decide

theorem case4_orders_differ :
    run [thirdObjectOfSingularGoal, firstSingularGoal] prefix1S3S ≠
      run [firstSingularGoal, thirdObjectOfSingularGoal] prefix1S3S := by
  decide

/-- The block architecture keeps the object's third person, and so inserts *m*. -/
theorem case4_block (l : List Rule) (hl : ParaThenSyn l)
    (hperm : l.Perm [firstSingularGoal, thirdObjectOfSingularGoal]) :
    (run l prefix1S3S).object = some (third ++ singular) := by
  rw [run_eq_of_paraThenSyn firstSingularGoal_paradigmatic thirdObjectOfSingularGoal_syntagmatic
    hl hperm, case4_para_syn]

/-- (41) before (40) keeps the third person of the object of *opénôm* (Table 21), the *m*, by
making the goal non-singular before (40) looks at it. -/
theorem singularGoal_bleeds_thirdObjectOfSingularGoal :
    (run [singularGoal, thirdObjectOfSingularGoal] prefix1D3S3S).object =
        some (third ++ singular) ∧
      (run [thirdObjectOfSingularGoal, singularGoal] prefix1D3S3S).object = some singular := by
  decide

/-! ### Case 5 (§4.2.5): a paradigmatic rule before a syntagmatic one

The 1S:3I possessive prefix *ónôm* keeps *n*, the exponent of `[+minimal]` (21): (43) deletes
the goal's `[+atomic]` first and bleeds (44), which would delete the `[+minimal]`. -/

theorem case5_para_syn (o : Arg) (ho : third.bears o ∧ Inverse o) :
    (run [firstSingularGoal, leftmostMinimal .goal] (prefix1S3I o)).goal =
      some (first ++ [FeatureVal.minimal true]) := by
  obtain ⟨_, h₂⟩ := ho
  simp [run, Rule.apply, Prefix.set, Prefix.around, Slot.view, leftmostMinimal, leftmostNumber,
    firstSingularGoal, Rule.syntagmatic, Rule.paradigmatic,
    ImpoverishmentRule.apply, ImpoverishmentRule.syntagmatic, ImpoverishmentRule.paradigmatic,
    Change.apply, prefix1S3I, h₂, first, singular, Arg.bears, Slot.before]

theorem case5_syn_para (o : Arg) (ho : third.bears o ∧ Inverse o) :
    (run [leftmostMinimal .goal, firstSingularGoal] (prefix1S3I o)).goal =
      some (first ++ [FeatureVal.atomic true]) := by
  obtain ⟨h₁, h₂⟩ := ho
  simp only [Arg.bears, third, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    List.contains_iff_mem] at h₁
  simp [run, Rule.apply, Prefix.set, Prefix.around, Slot.view, leftmostMinimal, leftmostNumber,
    firstSingularGoal, Rule.syntagmatic, Rule.paradigmatic,
    ImpoverishmentRule.apply, ImpoverishmentRule.syntagmatic, ImpoverishmentRule.paradigmatic,
    Change.apply, prefix1S3I, h₁, h₂, first, third, singular, Arg.bears, Slot.before]

/-! ### Impoverishment precedes metathesis in Taos (§3.2)

After Linearization the prefix is a string of feature terminals, and the paper's metathesis
rules swap adjacent ones: the library's `TerminalMetathesisRule` over `FeatureVal`. *opén*
(Table 5, the 1D:3:no prefix of (25)) expones `[−atomic]` as *o*, `[−author]` as *pé* and
`[+minimal]` as *n* ((20)–(22)), so its features must stand in the order `[−atomic] [−author]
[+minimal]` at Vocabulary Insertion. -/

/-- (24): in a goal, `[−author]` swaps with a following `[−atomic]` before `[+minimal]`. -/
def dualGoalMetathesis : TerminalMetathesisRule FeatureVal :=
  .ofBool fun n ↦ n.focus == .author false && n.rightCtx.take 2 == [.atomic false, .minimal true]

/-- (26): after a dual agent's `[−atomic]`, its `[+minimal]` swaps with a following
`[−author]`. -/
def dualAgentMetathesis : TerminalMetathesisRule FeatureVal :=
  .ofBool fun n ↦ n.leftCtx.contains (.atomic false) && n.focus == .minimal true &&
    n.rightCtx.head? == some (.author false)

/-- (27), on the linearized string: a `[−author]` goal's `[−participant]` is deleted after a
dual agent. -/
def goalParticipant : ObliterationRule FeatureVal :=
  .ofBool fun n ↦ n.focus == .participant false && n.rightCtx.head? == some (.author false) &&
    n.leftCtx.contains (.atomic false) && n.leftCtx.contains (.minimal true)

/-- The 1:3D:no prefix of (23), *opén* (Table 4), with the agent's number features gone. -/
def prefix1_3D : Prefix := ⟨some first, some (third ++ dual), some []⟩

/-- The 1D:3:no prefix of (25), *opén* (Table 5), with the goal's number features gone. -/
def prefix1D_3 : Prefix := ⟨some (first ++ dual), some third, some []⟩

/-- Both prefixes of the two figures are *opén*. -/
theorem form_opén :
    Taos.form ⟨some (.first, .singular), some (.third, .dual), some .dummy⟩ = some "opén" ∧
      Taos.form ⟨some (.first, .dual), some (.third, .singular), some .dummy⟩ =
        some "opén" := by
  decide

/-- (24) puts the dual goal's features in the order of *o-pé-n*. -/
theorem dualGoalMetathesis_prefix1_3D :
    dualGoalMetathesis.apply prefix1_3D.linearize =
      [.participant true, .author true, .participant false, .atomic false, .author false,
        .minimal true] := by
  decide

/-- Impoverishment then metathesis: (27) removes the goal's `[−participant]` and (26) then
finds `[+minimal]` next to `[−author]`; the order is that of *o-pé-n*. -/
theorem taos_impoverishment_then_metathesis :
    runModules [goalParticipant.apply, dualAgentMetathesis.apply] prefix1D_3.linearize =
      [.participant true, .author true, .atomic false, .author false, .minimal true] := by
  decide

/-- Metathesis then impoverishment: (26) finds `[−participant]` in the way and does nothing,
and after (27) the order is that of the unattested *o-n-pé*. -/
theorem taos_metathesis_then_impoverishment :
    runModules [dualAgentMetathesis.apply, goalParticipant.apply] prefix1D_3.linearize =
      [.participant true, .author true, .atomic false, .minimal true, .author false] := by
  decide

theorem taos_orders_differ :
    runModules [goalParticipant.apply, dualAgentMetathesis.apply] prefix1D_3.linearize ≠
      runModules [dualAgentMetathesis.apply, goalParticipant.apply] prefix1D_3.linearize := by
  decide

/-! ### Impoverishment precedes metathesis in Basque (§3.1)

The finite auxiliary of (10) is a string of terminals: the absolutive clitic, T, and the
ergative and dative clitics. Participant Dissimilation, the paper's (16) and (18) after Arregi
and Nevins's (25), obliterates a clitic in the Feature Markedness module; T-Noninitiality, the
paper's (12), is repaired in the Linear Operations module by Ergative Metathesis (13) or
L-Support. -/

/-- A clitic: its case and person and number features. -/
def clitic (c : Case) (φ : Arg) : Arg := .case c :: φ

/-- T, past tense (see the implementation notes). -/
def pastT : Arg := [.tense true]

/-- The epenthetic L of L-Support, a terminal without features. -/
def lSupport : Arg := []

/-- Participant Dissimilation: a `[+participant +author]` clitic is obliterated when another
clitic of the word bears `trigger`. -/
def participantDissimilation (trigger : Arg) : ObliterationRule Arg :=
  .ofBool fun n ↦ first.bears n.focus && (n.leftCtx ++ n.rightCtx).any (trigger.bears ·)

/-- Ondarru, the paper's (16): the trigger is an ergative participant clitic. -/
def ondarru : ObliterationRule Arg := participantDissimilation [.case .erg, .participant true]

/-- Zamudio, the paper's (18): the trigger is any participant clitic. -/
def zamudio : ObliterationRule Arg := participantDissimilation [.participant true]

/-- Ergative Metathesis, the paper's (13) after Arregi and Nevins's (105): a word-initial T is
preceded by the first ergative clitic that follows it. -/
def ergativeMetathesis : SpelloutDomain Arg → SpelloutDomain Arg :=
  rewriteFirst
    (fun n ↦ n.leftCtx = [] ∧ n.focus.contains (.tense true) ∧
      n.rightCtx.any (·.contains (.case .erg)))
    fun n ↦ match n.rightCtx.find? (·.contains (.case .erg)) with
      | some e => n.leftCtx.reverse ++ e :: n.focus :: n.rightCtx.erase e
      | none => n.toList

/-- Ergative Metathesis preserves the number of terminals. -/
theorem length_ergativeMetathesis (d : SpelloutDomain Arg) :
    (ergativeMetathesis d).length = d.length := by
  unfold ergativeMetathesis
  refine length_rewriteFirst (fun n ↦ ?_) d
  cases h : n.rightCtx.find? (·.contains (.case .erg)) with
  | none => rfl
  | some e =>
    have hmem := List.mem_of_find?_eq_some h
    simp only [List.length_cons, Neighborhood.toList, List.length_append, List.length_reverse,
      List.length_erase_of_mem hmem]
    have := List.length_pos_of_mem hmem
    omega

/-- L-Support: an L before a word-initial T. -/
def lSupportRepair (d : SpelloutDomain Arg) : SpelloutDomain Arg :=
  if d.head?.any (·.contains (.tense true)) then lSupport :: d else d

/-- The Linear Operations module: the two repairs of T-Noninitiality. -/
def linearOperations : SpelloutDomain Arg → SpelloutDomain Arg :=
  lSupportRepair ∘ ergativeMetathesis

/-- Feature Markedness before Linear Operations, the order of Figure 1. -/
def markednessThenLinear (pd : ObliterationRule Arg) : SpelloutDomain Arg → SpelloutDomain Arg :=
  runModules [pd.apply, linearOperations]

/-- Linear Operations before Feature Markedness, the order both papers reject. -/
def linearThenMarkedness (pd : ObliterationRule Arg) : SpelloutDomain Arg → SpelloutDomain Arg :=
  runModules [linearOperations, pd.apply]

/-- The Ondarru auxiliary of (17), *s-endu-n* 'you saw us': a first plural absolutive clitic,
past T, and a second singular ergative clitic. -/
def auxiliary17 : SpelloutDomain Arg :=
  [clitic .abs (first ++ plural), pastT, clitic .erg (second ++ singular)]

/-- The Zamudio auxiliary of (19), *y-a-tzu-e-n* 'we accompanied you lot': past T, a second
plural dative clitic, and a first plural ergative clitic. -/
def auxiliary19 : SpelloutDomain Arg :=
  [pastT, clitic .dat (second ++ plural), clitic .erg (first ++ plural)]

/-- Ondarru, markedness first: Participant Dissimilation obliterates the absolutive clitic,
leaving T initial, and Ergative Metathesis then fronts the ergative clitic: *s-endu-n*. -/
theorem ondarru_markedness_then_linear :
    markednessThenLinear ondarru auxiliary17 = [clitic .erg (second ++ singular), pastT] := by
  decide

/-- Ondarru, linear module first: T is not initial, so neither repair applies, and after the
absolutive clitic goes T is stranded initial. -/
theorem ondarru_linear_then_markedness :
    linearThenMarkedness ondarru auxiliary17 = [pastT, clitic .erg (second ++ singular)] := by
  decide

theorem ondarru_orders_differ :
    markednessThenLinear ondarru auxiliary17 ≠ linearThenMarkedness ondarru auxiliary17 := by
  decide

/-- Zamudio, markedness first: Participant Dissimilation obliterates the ergative clitic, so
no ergative is left to front and L-Support repairs the initial T: *y-a-tzu-e-n*. -/
theorem zamudio_markedness_then_linear :
    markednessThenLinear zamudio auxiliary19 =
      [lSupport, pastT, clitic .dat (second ++ plural)] := by
  decide

/-- Zamudio, linear module first: Ergative Metathesis fronts the ergative clitic, which
Participant Dissimilation then obliterates, stranding T initial. -/
theorem zamudio_linear_then_markedness :
    linearThenMarkedness zamudio auxiliary19 = [pastT, clitic .dat (second ++ plural)] := by
  decide

theorem zamudio_orders_differ :
    markednessThenLinear zamudio auxiliary19 ≠ linearThenMarkedness zamudio auxiliary19 := by
  decide

end Middleton2026
