module

public import Mathlib.Data.List.Permutation
public import Linglib.Morphology.DistributedMorphology.Spellout
public import Linglib.Syntax.Minimalist.Features
public import Linglib.Fragments.Taos.Agreement

/-!
# Middleton (2026): the ordering of impoverishment rules in Taos and Basque

[arregi-nevins-2012] organise the postsyntax into modules: Feature Markedness, where
impoverishment applies, precedes Linearization and the Linear Operations module, where
metathesis applies; and within Feature Markedness the paradigmatic rules, conditioned by the
features of the node they change, apply as a block before the syntagmatic rules, conditioned by
the features of more than one node (their (72), §4.8). [middleton-2026] tests both orderings
against the verbal agreement prefixes of Taos (Kiowa-Tanoan) and finds them unequal: the
Basque and Taos data both need impoverishment before metathesis (§3), but in four Taos
interactions a syntagmatic rule must precede a paradigmatic rule that would otherwise bleed it
(§4.2.1–§4.2.4) while in a fifth the paradigmatic rule bleeds the syntagmatic one (§4.2.5), so
the two kinds of impoverishment interleave.

The paper's online appendix gives the whole analysis: thirty-odd rules of impoverishment in
seven ordered sets, three rules of metathesis, the rules of exponence with their portmanteaux,
the epenthetic vowel and the tone rules, and derives every prefix of the paradigm in
`Fragments/Taos/Agreement.lean`. This file transcribes that system. A prefix is the `Prefix`
of the paper's (1), an agent, a goal and an object, each a list of `Feat`; a rule is a `Rule`,
the slot it changes and an `ImpoverishmentRule` at that slot's `Neighborhood`, so that the
paper's paradigmatic/syntagmatic labels are the library's `Paradigmatic` and `Syntagmatic`;
the appendix's numbering names the rules (`r34a` is its (34a)) and the paper's numbering is
in each docstring. `derive` runs the pipeline from a cell of the fragment to a surface form,
and `derive_eq_form` checks it against every cell of the paradigm but the nine the appendix
itself leaves unaccounted for (`unaccounted`). The block architecture is the order
`ParaThenSyn` on rule sequences; a paradigmatic and a syntagmatic rule have one
block-conforming order (`run_eq_of_paraThenSyn`), so the five interactions of §4.2 are
theorems about which order reaches the attested cell, under the paper's own classification of
its rules (see the implementation notes on `r40` and `r26`). The Basque half runs the domain-level
rules of `Spellout.lean` over the auxiliary.

## Implementation notes

* Inverse number is one feature, `Feat.inverse`, and `Arg.has` counts the dual's values
  `[−atomic +minimal]` as present in it, the containment the appendix's §3.1 states and the
  fragment's `Taos.dual_le_inverse` derives from Harbour's valuations; so the appendix's
  bare-feature contexts are containment tests while its category labels *s*, *d*, *p*, *i*
  are exact tests on the number features (`Arg.IsSingular` and kin, which read the features in the
  order Spell-Out gives them, which deletion preserves). `r38a` alone reads *s* as
  `[+atomic]` without inverse, because of the widened `r44` below. `Feat` is a study-local
  inventory rather than `Minimalist.FeatureVal`, which has no inverse, dummy or reflexive
  feature and would cost the kernel more in `derive_eq_form`.
* The paper labels its (35) and (43), the appendix's (40) and (26), paradigmatic; as the
  appendix prints them, `3s → E / [[A __](O)]` and `[+atomic] → E / [[G 1 __ +minimal]`, each
  carries a bracket condition on another slot (no goal; no agent), under which the library
  classifies both as syntagmatic. `r40` and `r26` drop those conditions to match the paper's
  labels, `r40'` and `r26'` keep them, and `derive_eq_form_printed` shows the two rule sets
  derive the same paradigm. Cases 1, 2 and 4 therefore count against
  the block architecture under the paper's classification, not under its printed rules; case
  3, whose paradigmatic rule (11a) is conditioned by the agent alone, stands either way.
* Rules the appendix writes with an agent bracket immediately followed by an object bracket
  are confined to prefixes without a goal; the "leftmost" bundles are the first slot with a
  person, or number, feature; (2) and (3) read "3" as `[−author]`, since (24) may already
  have removed the goal's `[−participant]`, as the appendix remarks at its (33).
* Orderings within the appendix's sets. Its prose supports (33) before (32) (§3.7.1) and
  (5) bleeding (7) (the "remaining prefixes" of §3.4, so `r7b` runs before `r7a` and both
  need the agent's number); the paper's §4.2.2 supports (45) before (40). Three further
  choices are this study's repairs, forced by cells the appendix's listing would not derive:
  (32) moved from the first set to after (7), or 2:1s:3s *môm* comes out *mǫ́*; (44) moved
  from the first set to after (43), or 1s:∅ comes out *ti*; and (44)'s context widened from
  the printed intransitive `[[A +author +atomic __]]` to an absent or plural object, or 1s:3p
  comes out *pi*.
* Exponence is the appendix's rule list as a function of the token and its prefix, with three
  additions the appendix uses but never states: a portmanteau *mây* for the 2:1 prefixes
  without an object (its §3.4 says they "are exponed as mây" and §4.3 lists no exponent), the
  single-argument portmanteaux (41) and (49) matching an argument's remaining bundle exactly,
  and portmanteau forms taking no tone rule, without which (6) *ku* would come out *kú*. The
  epenthetic vowel follows an onset consonant and precedes a coda one, as *mó* and *ôn*
  show; *w* alone is *u*.
* Metathesis reorders the linearized string of feature terminals with the library's
  `TerminalMetathesisRule`; (18) and (22) act on the goal as their G subscript says, (23) on
  the second argument, goal or object, as its unlabelled bracket allows. For (50a), an object
  silenced by the allomorphs (39b,d) does not count as an argument, as the appendix's §3.11
  says of the dual-agent 3p and reflexive prefixes.
* Tone: the appendix prints (51f) as toneless but its prose and Table 3 make the ∅:3s
  possessives high, which `exception` follows; (51h) it applies as printed, against Table 3
  (see the TODO).
* The Basque terminals are clitics with a case feature and T with `[+tense]`, standing in for
  Arregi and Nevins's `[+past]`. Ergative Metathesis fronts the first ergative clitic after a
  word-initial T, their (105), without its dative-clitic conditions, and Participant
  Dissimilation omits their `[+motion]` restriction and their First Singular Clitic
  Impoverishment, none of which the two auxiliaries reach; L-Support and Ergative Metathesis
  form one module, as in their §6.2.4.

## TODO

* The nine cells in `unaccounted`, with what the pipeline gives them in
  `derive_unaccounted`: ∅:2s:∅ and 1:2s:∅ (*o*; the appendix says it will return to them and
  does not, and the rules give *kǫ*), 3i:3p (printed toneless; footnote 5 calls that a typo
  for high, but (50c) gives a closed final syllable falling, *îw*), 3i:refl (printed *ímó*;
  the rules give footnote 6's corrected *ímo*), and the three 3d possessives with an object
  (Table 3 prints *ónôm* and *ónôw*, but the tone rule (51h) and the appendix's Tables 8, 14,
  17 and 38 have *ónóm* and *ónów*, which the rules give).
* The paper's (13) is an adjacent swap; the study follows Arregi and Nevins's fronting rule,
  which the Zamudio auxiliary of (19) needs, and its rejected-order outputs are Arregi and
  Nevins's stranded forms rather than the paper's starred (17b) and (19b).

## References

* [J. Middleton, *A remark on the ordering of impoverishment rules: differences between Taos
  and Basque*][middleton-2026]
* [K. Arregi and A. Nevins, *Morphotactics*][arregi-nevins-2012]
* [D. Harbour, *Paucity, abundance, and the theory of number*][harbour-2014]
* [D. Harbour, *Impossible persons*][harbour-2016]
-/

@[expose] public section

namespace Middleton2026

open Minimalist DistributedMorphology

/-! ### Features and arguments

The paper's (2) and (3): Taos distinguishes three persons and three numbers, and inverse
agreement is the paper's (8), one feature here. The dummy object *no* and the reflexive are
the two objects without person. -/

/-- A feature of a Taos argument. -/
inductive Feat where
  | participant (b : Bool)
  | author (b : Bool)
  | atomic (b : Bool)
  | minimal (b : Bool)
  | inverse
  | dummy
  | refl
  deriving DecidableEq, Repr

namespace Feat

/-- The person features are `[±participant]` and `[±author]`. -/
def IsPerson : Feat → Prop
  | .participant _ | .author _ => True
  | _ => False

/-- The number features are `[±atomic]`, `[±minimal]` and inverse. -/
def IsNumber : Feat → Prop
  | .atomic _ | .minimal _ | .inverse => True
  | _ => False

instance : DecidablePred IsPerson := fun f ↦ by cases f <;> unfold IsPerson <;> infer_instance

instance : DecidablePred IsNumber := fun f ↦ by cases f <;> unfold IsNumber <;> infer_instance

/-- The position of a feature within its argument after Linearization, the paper's (4) and
(5): `[±participant] [±author] [±atomic] [±minimal]`. -/
def rank : Feat → ℕ
  | .participant _ => 0
  | .author _ => 1
  | .atomic _ => 2
  | .minimal _ => 3
  | .inverse => 4
  | .dummy | .refl => 5

end Feat

/-- An argument is given by its features. -/
abbrev Arg := List Feat

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

/-- Inverse. -/
def inverse : Arg := [.inverse]

namespace Arg

/-- `a` has `f`; an inverse valuation contains the dual's values (`Taos.dual_le_inverse`). -/
def Has (a : Arg) (f : Feat) : Prop :=
  f ∈ a ∨ .inverse ∈ a ∧ (f = .atomic false ∨ f = .minimal true)

instance (a : Arg) : DecidablePred a.Has := fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- `a` has every feature of `fs`. -/
def Bears (a fs : Arg) : Prop := ∀ f ∈ fs, a.Has f

instance (a fs : Arg) : Decidable (a.Bears fs) := inferInstanceAs (Decidable (∀ f ∈ fs, _))

/-- The number features. -/
def number (a : Arg) : Arg := a.filter (·.IsNumber)

/-- First person. -/
def IsFirst (a : Arg) : Prop := a.Bears first

/-- Second person. -/
def IsSecond (a : Arg) : Prop := a.Bears second

/-- Third person. -/
def IsThird (a : Arg) : Prop := a.Bears third

/-- Exactly singular. -/
def IsSingular (a : Arg) : Prop := a.number = singular

/-- Exactly dual. -/
def IsDual (a : Arg) : Prop := a.number = dual

/-- Exactly plural. -/
def IsPlural (a : Arg) : Prop := a.number = plural

/-- Inverse. -/
def IsInverse (a : Arg) : Prop := .inverse ∈ a

/-- Singular, its `[+minimal]` possibly already deleted. -/
def IsAtomicSingular (a : Arg) : Prop := .atomic true ∈ a ∧ .inverse ∉ a

/-- Has a `[±participant]` feature. -/
def HasParticipant (a : Arg) : Prop := ∃ b, .participant b ∈ a

instance : DecidablePred IsFirst := fun _ ↦ inferInstanceAs (Decidable (Bears _ _))
instance : DecidablePred IsSecond := fun _ ↦ inferInstanceAs (Decidable (Bears _ _))
instance : DecidablePred IsThird := fun _ ↦ inferInstanceAs (Decidable (Bears _ _))
instance : DecidablePred IsSingular := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred IsDual := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred IsPlural := fun _ ↦ inferInstanceAs (Decidable (_ = _))
instance : DecidablePred IsInverse := fun _ ↦ inferInstanceAs (Decidable (_ ∈ _))
instance : DecidablePred IsAtomicSingular := fun _ ↦ inferInstanceAs (Decidable (_ ∧ _))
instance : DecidablePred HasParticipant := fun _ ↦ inferInstanceAs (Decidable (∃ _, _))

/-- Delete the features of `fs`. -/
def delete (a fs : Arg) : Arg := a.filter (· ∉ fs)

end Arg

/-! ### The agreement prefix

The prefix of the paper's (1) agrees with the agent, the goal and the object, linearized in
that order. -/

/-- The three daughters of AgrP in (1), in linear order. -/
inductive Slot where
  | agent
  | goal
  | object
  deriving DecidableEq, Repr

/-- The agreement prefix of (1) has the agent, goal and object, an absent argument having no
features. -/
structure Prefix where
  /-- The agent. -/
  agent : Arg
  /-- The goal. -/
  goal : Arg
  /-- The object. -/
  object : Arg
  deriving DecidableEq, Repr

namespace Prefix

/-- The argument in a slot. -/
def get (p : Prefix) : Slot → Arg
  | .agent => p.agent
  | .goal => p.goal
  | .object => p.object

/-- Replace the argument in a slot. -/
def set (p : Prefix) : Slot → Arg → Prefix
  | .agent, a => { p with agent := a }
  | .goal, a => { p with goal := a }
  | .object, a => { p with object := a }

/-- The neighborhood of a slot has its argument in focus and the other two as context, in the order
of (1). -/
def around (p : Prefix) : Slot → Neighborhood Arg
  | .agent => ⟨p.agent, [], [p.goal, p.object]⟩
  | .goal => ⟨p.goal, [p.agent], [p.object]⟩
  | .object => ⟨p.object, [p.goal, p.agent], []⟩

/-- The prefix a slot's neighborhood came from. -/
def ofAround : Slot → Neighborhood Arg → Prefix
  | .agent, n => ⟨n.focus, n.rightCtx.getD 0 [], n.rightCtx.getD 1 []⟩
  | .goal, n => ⟨n.leftCtx.getD 0 [], n.focus, n.rightCtx.getD 0 []⟩
  | .object, n => ⟨n.leftCtx.getD 1 [], n.leftCtx.getD 0 [], n.focus⟩

@[simp] theorem ofAround_around (p : Prefix) (s : Slot) : ofAround s (p.around s) = p := by
  cases s <;> rfl

/-- The leftmost number bundle is the first slot with a number feature. -/
def leftmostNumber (p : Prefix) : Option Slot :=
  if p.agent.number = [] then
    if p.goal.number = [] then
      if p.object.number = [] then none else some .object
    else some .goal
  else some .agent

/-- The features of the leftmost number bundle. -/
def leftmostNumberArg (p : Prefix) : Arg := (p.leftmostNumber.map p.get).getD []

/-- The leftmost person bundle is the first slot with a `[±participant]` feature. -/
def leftmostPerson (p : Prefix) : Option Slot :=
  if p.agent.HasParticipant then some .agent
  else if p.goal.HasParticipant then some .goal
  else if p.object.HasParticipant then some .object else none

/-- The leftmost exponed person is second. -/
def LeftmostSecond (p : Prefix) : Prop := ∃ s ∈ p.leftmostPerson, (p.get s).IsSecond

instance : DecidablePred LeftmostSecond := fun p ↦
  inferInstanceAs (Decidable (∃ s ∈ p.leftmostPerson, _))

/-- The second argument is the goal, or the object of a prefix without a goal. -/
def secondArg (p : Prefix) : Slot := if p.goal ≠ [] then .goal else .object

/-- The present arguments. -/
def args (p : Prefix) : List Arg := [p.agent, p.goal, p.object].filter (· ≠ [])

end Prefix

/-! ### Rules of impoverishment

A rule is the appendix's `X → E / context`: the slot whose argument changes, and an
`ImpoverishmentRule` at that slot's neighborhood whose target is the structural change. -/

/-- The structural change of a rule. -/
inductive Change where
  | delete (fs : Arg)
  | deleteNumber
  | deletePerson
  | obliterate

/-- Apply a change to an argument. -/
def Change.apply : Change → Arg → Arg
  | .delete fs, a => a.delete fs
  | .deleteNumber, a => a.filter (¬ ·.IsNumber)
  | .deletePerson, a => a.filter (¬ ·.IsPerson)
  | .obliterate, _ => []

/-- A rule of impoverishment over the prefix. -/
structure Rule where
  /-- The slot whose argument the rule changes. -/
  slot : Slot
  /-- The rule at that slot's neighborhood. -/
  rule : ImpoverishmentRule Arg Change

namespace Rule

/-- A rule conditioned by its own slot's argument. -/
def paradigmatic (s : Slot) (check : Arg → Prop) [DecidablePred check] (c : Change) : Rule :=
  ⟨s, .ofFocus check c⟩

/-- A rule conditioned by the prefix. -/
def syntagmatic (s : Slot) (cond : Prefix → Prop) [DecidablePred cond] (c : Change) : Rule :=
  ⟨s, ⟨fun n ↦ cond (Prefix.ofAround s n), c⟩⟩

/-- Apply the rule to the prefix. -/
def apply (r : Rule) (p : Prefix) : Prefix :=
  p.set r.slot (r.rule.apply (fun a c ↦ c.apply a) (p.around r.slot))

/-- The rule is paradigmatic when its condition factors through its own slot. -/
def Paradigmatic (r : Rule) : Prop := r.rule.Paradigmatic

/-- The rule is syntagmatic when its condition reads another slot. -/
def Syntagmatic (r : Rule) : Prop := r.rule.Syntagmatic

theorem paradigmatic_isParadigmatic (s : Slot) (check : Arg → Prop) [DecidablePred check]
    (c : Change) : (paradigmatic s check c).Paradigmatic :=
  ImpoverishmentRule.paradigmatic_ofFocus check c

end Rule

/-- Apply a sequence of rules in order. -/
def run (rs : List Rule) (p : Prefix) : Prefix := rs.foldl (fun p r ↦ r.apply p) p

@[simp] theorem run_nil (p : Prefix) : run [] p = p := rfl

@[simp] theorem run_cons (r : Rule) (rs : List Rule) (p : Prefix) :
    run (r :: rs) p = run rs (r.apply p) := rfl

/-! ### The block architecture

Arregi and Nevins's (72), `Exponence Conversion > Paradigmatic > Syntagmatic`: the
paradigmatic rules form a block before the syntagmatic ones. -/

/-- A rule sequence respects the block architecture when no syntagmatic rule precedes a
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

The appendix's rules of impoverishment, by its numbering; the paper's numbers are in the
docstrings. -/

/-- By rule (1), the goal loses its number after an inverse agent, with an object. -/
def r1 : Rule :=
  .syntagmatic .goal (fun p ↦ p.agent.IsInverse ∧ p.goal.IsThird ∧ p.object ≠ []) .deleteNumber

/-- By rule (4), a first person agent loses its number before a second person goal. -/
def r4 : Rule :=
  .syntagmatic .agent (fun p ↦ p.agent.Has (.author true) ∧ p.goal.IsSecond) .deleteNumber

/-- By the optional rule (5), a second person agent loses its number before a first dual or inverse
goal with no object; the prefix is then the portmanteau *ku*. -/
def r5 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.IsSecond ∧ p.goal.IsFirst ∧ p.goal.Has (.atomic false) ∧
      p.goal.Has (.minimal true) ∧ p.object = [])
    .deleteNumber

/-- By rule (9), a first singular possessive goal loses `[+participant]`. -/
def r9 : Rule :=
  .syntagmatic .goal
    (fun p ↦ p.agent = [] ∧ p.goal.Has (.author true) ∧ p.goal.Has (.atomic true))
    (.delete [.participant true])

/-- By rule (12), a first person agent loses `[+participant]` before a second dual or inverse goal.
-/
def r12 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author true) ∧ p.goal.IsSecond ∧ p.goal.Has (.atomic false) ∧
      p.goal.Has (.minimal true))
    (.delete [.participant true])

/-- By rule (24), the paper's (27), a `[−author]` goal loses `[−participant]` after a dual agent. -/
def r24 : Rule :=
  .syntagmatic .goal (fun p ↦ p.agent.IsDual ∧ p.goal.Has (.author false))
    (.delete [.participant false])

/-- By rule (33), the paper's (41), a `[−author]` goal loses its singular features between a dual
agent and a third singular object. -/
def r33 : Rule :=
  .syntagmatic .goal
    (fun p ↦ p.agent.IsDual ∧ p.goal.Has (.author false) ∧ p.object.IsThird ∧ p.object.IsSingular)
    (.delete singular)

/-- By rule (34a), the paper's (32a), a singular object loses its person after an agent. -/
def r34a : Rule :=
  .syntagmatic .object (fun p ↦ p.goal = [] ∧ p.agent ≠ [] ∧ p.object.IsSingular)
    .deletePerson

/-- By rule (34b), the paper's (32b), an inverse `[−author]` object loses `[−participant]` after an
agent. -/
def r34b : Rule :=
  .syntagmatic .object
    (fun p ↦ p.goal = [] ∧ p.agent ≠ [] ∧ p.object.Has (.author false) ∧
      p.object.IsInverse)
    (.delete [.participant false])

/-- By rule (14), a first dual or inverse agent loses its person before no object, or a singular,
dummy or inverse one. -/
def r14 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author true) ∧ p.agent.Has (.atomic false) ∧
      p.agent.Has (.minimal true) ∧ p.goal = [] ∧
      (p.object = [] ∨ p.object.IsSingular ∨ p.object = [.dummy] ∨ p.object.IsInverse))
    .deletePerson

/-- By rule (35), a singular object loses its person after a first inverse possessive goal. -/
def r35 : Rule :=
  .syntagmatic .object
    (fun p ↦ p.agent = [] ∧ p.goal.IsFirst ∧ p.goal.IsInverse ∧ p.object.IsSingular)
    .deletePerson

/-- By rule (46), the paper's (37), a first or second singular agent loses `[+minimal]` before a
singular or dummy object. -/
def r46 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.participant true) ∧ p.agent.Has (.atomic true) ∧
      p.goal = [] ∧ (p.object.IsSingular ∨ p.object = [.dummy]))
    (.delete [.minimal true])

/-- By rule (2), the agent loses its number before a third dual or inverse goal, with an object. -/
def r2 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.goal.Has (.author false) ∧ p.goal.Has (.atomic false) ∧
      p.goal.Has (.minimal true) ∧ p.object ≠ [])
    .deleteNumber

/-- By rule (7), on the agent, a second person agent with number and a first person goal both lose
their number; the optional (5) bleeds it, leaving the goal's number for *ku*. -/
def r7a : Rule :=
  .syntagmatic .agent (fun p ↦ p.agent.IsSecond ∧ p.agent.number ≠ [] ∧ p.goal.IsFirst)
    .deleteNumber

/-- (7), on the goal, before the agent's half so that the agent's number is still there to
condition it. -/
def r7b : Rule :=
  .syntagmatic .goal (fun p ↦ p.agent.IsSecond ∧ p.agent.number ≠ [] ∧ p.goal.IsFirst)
    .deleteNumber

/-- By rule (32), the paper's (40), a singular object loses its person after a singular goal. -/
def r32 : Rule :=
  .syntagmatic .object (fun p ↦ p.goal.IsSingular ∧ p.object.IsSingular) .deletePerson

/-- By rule (15), a first person agent is obliterated before a second singular goal. -/
def r15 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author true) ∧ p.goal.IsSecond ∧ p.goal.Has (.atomic true))
    .deletePerson

/-- By the paradigmatic rule (26), the paper's (43), a first person `[+minimal]` goal loses
`[+atomic]`. -/
def r26 : Rule :=
  .paradigmatic .goal (fun a ↦ a.Has (.author true) ∧ a.Has (.minimal true))
    (.delete [.atomic true])

/-- By rule (45a), the paper's (36b), the object loses its singular features after a `[+atomic]`
agent. -/
def r45a : Rule :=
  .syntagmatic .object
    (fun p ↦ p.agent.Has (.atomic true) ∧ p.goal = [] ∧ p.object ≠ [])
    (.delete singular)

/-- By rule (45b), the paper's (36a), the dummy object is obliterated after a `[+atomic]` agent. -/
def r45b : Rule :=
  .syntagmatic .object
    (fun p ↦ p.agent.Has (.atomic true) ∧ p.goal = [] ∧ p.object = [.dummy]) .obliterate

/-- By the paradigmatic rule (40), the paper's (35), a third singular agent is obliterated. -/
def r40 : Rule := .paradigmatic .agent (fun a ↦ a.IsThird ∧ a.IsSingular) .obliterate

/-- Rule (40) as the appendix prints it, `[[A __](O)]`, applies with no goal. -/
def r40' : Rule :=
  .syntagmatic .agent (fun p ↦ p.agent.IsThird ∧ p.agent.IsSingular ∧ p.goal = []) .obliterate

/-- Rule (26) as the appendix prints it, `[[G 1 __ +minimal]`, applies with no agent. -/
def r26' : Rule :=
  .syntagmatic .goal
    (fun p ↦ p.agent = [] ∧ p.goal.Has (.author true) ∧ p.goal.Has (.minimal true))
    (.delete [.atomic true])

/-- By rule (47), an inverse object loses `[−author]` after a singular agent. -/
def r47 : Rule :=
  .syntagmatic .object (fun p ↦ p.agent.IsSingular ∧ p.goal = [] ∧ p.object.IsInverse)
    (.delete [.author false])

/-- By rule (3), a first person agent loses `[+participant]` before a third person goal and an
object when the leftmost number is dual or inverse. -/
def r3 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author true) ∧ p.goal.Has (.author false) ∧ p.object ≠ [] ∧
      p.leftmostNumberArg.Has (.atomic false) ∧ p.leftmostNumberArg.Has (.minimal true))
    (.delete [.participant true])

/-- By the paradigmatic rule (11a), the paper's (39), a second singular agent loses
`[+participant]`. -/
def r11a : Rule :=
  .paradigmatic .agent (fun a ↦ a.Has (.author false) ∧ a.Has (.atomic true))
    (.delete [.participant true])

/-- By rule (11b), a second singular possessive goal loses `[−author]`. -/
def r11b : Rule :=
  .syntagmatic .goal
    (fun p ↦ p.agent = [] ∧ p.goal.Has (.participant true) ∧ p.goal.Has (.atomic true))
    (.delete [.author false])

/-- By rule (29), the paper's (44), at slot `s`, the leftmost number bundle, when singular, loses
`[+minimal]` before a third inverse object. -/
def r29 (s : Slot) : Rule :=
  .syntagmatic s
    (fun p ↦ p.leftmostNumber = some s ∧ (p.get s).IsSingular ∧ p.object.IsThird ∧
      p.object.IsInverse)
    (.delete [.minimal true])

/-- By rule (43), a first singular agent loses `[+participant]` before no object or a `[−atomic]`
one. -/
def r43 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author true) ∧ p.agent.IsSingular ∧ p.goal = [] ∧
      (p.object = [] ∨ p.object.Has (.atomic false)))
    (.delete [.participant true])

/-- By rule (44), a first singular agent loses `[+minimal]` before no object or, this study's
widening, a plural one. -/
def r44 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author true) ∧ p.agent.Has (.atomic true) ∧ p.goal = [] ∧
      (p.object = [] ∨ p.object.IsPlural))
    (.delete [.minimal true])

/-- By rule (38b), the reflexive object is obliterated after a singular agent. -/
def r38b : Rule :=
  .syntagmatic .object (fun p ↦ p.agent.IsSingular ∧ p.goal = [] ∧ p.object = [.refl]) .obliterate

/-- By rule (42), a second singular intransitive agent loses `[−author]`. -/
def r42 : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.IsSingular ∧ p.agent.Has (.author false) ∧ p.goal = [] ∧
      p.object = [])
    (.delete [.author false])

/-- By rule (38a), a third plural object is obliterated after a singular agent. -/
def r38a : Rule :=
  .syntagmatic .object
    (fun p ↦ p.agent.IsAtomicSingular ∧ p.goal = [] ∧ p.object.IsThird ∧ p.object.IsPlural)
    .obliterate

/-- By rule (48a), an inverse object loses its number after a first singular agent. -/
def r48a : Rule :=
  .syntagmatic .object
    (fun p ↦ p.agent.Has (.author true) ∧ p.agent.IsSingular ∧ p.goal = [] ∧ p.object.IsInverse)
    .deleteNumber

/-- By rule (48b), a second singular agent loses its singular features before an inverse object. -/
def r48b : Rule :=
  .syntagmatic .agent
    (fun p ↦ p.agent.Has (.author false) ∧ p.agent.IsSingular ∧ p.goal = [] ∧ p.object.IsInverse)
    (.delete singular)

/-- The appendix's seven sets of rules of impoverishment in order, with its optional (5)
included or not. -/
def impoverishment (optional : Bool) : List Rule :=
  [r1, r4] ++ (if optional then [r5] else []) ++
    [r9, r12, r24, r33, r34a, r34b, r14, r35, r46,
     r2, r7b, r7a, r32, r15, r26, r45a, r45b, r40, r47,
     r3, r11a, r11b, r29 .agent, r29 .goal, r43, r44,
     r38b, r42, r38a, r48a, r48b]

/-- The same sets with (40) and (26) as printed. -/
def impoverishmentPrinted (optional : Bool) : List Rule :=
  [r1, r4] ++ (if optional then [r5] else []) ++
    [r9, r12, r24, r33, r34a, r34b, r14, r35, r46,
     r2, r7b, r7a, r32, r15, r26', r45a, r45b, r40', r47,
     r3, r11a, r11b, r29 .agent, r29 .goal, r43, r44,
     r38b, r42, r38a, r48a, r48b]

theorem r40_paradigmatic : r40.Paradigmatic := Rule.paradigmatic_isParadigmatic _ _ _

theorem r11a_paradigmatic : r11a.Paradigmatic := Rule.paradigmatic_isParadigmatic _ _ _

theorem r26_paradigmatic : r26.Paradigmatic := Rule.paradigmatic_isParadigmatic _ _ _

/-- The 3S:3S transitive prefix is ∅ (Table 15). -/
def prefix3S3S : Prefix := ⟨third ++ singular, [], third ++ singular⟩

/-- The 3S:3I transitive prefix is *í* (Table 15). -/
def prefix3S3I : Prefix := ⟨third ++ singular, [], third ++ inverse⟩

/-- The 3S:no transitive prefix is ∅ (Table 16). -/
def prefix3Sno : Prefix := ⟨third ++ singular, [], [.dummy]⟩

/-- The 2S:3S transitive prefix is *o* (Table 17). -/
def prefix2S3S : Prefix := ⟨second ++ singular, [], third ++ singular⟩

/-- The 2S intransitive prefix is *ǫ* (Table 17). -/
def prefix2S : Prefix := ⟨second ++ singular, [], []⟩

/-- The 1S:3S possessive prefix is *ôn* (Table 22). -/
def prefix1S3S : Prefix := ⟨[], first ++ singular, third ++ singular⟩

/-- The 1S:3I possessive prefix is *ónôm* (Table 22). -/
def prefix1S3I : Prefix := ⟨[], first ++ singular, third ++ inverse⟩

/-- The 1D:3S:3S ditransitive prefix is *opénôm* (Table 21). -/
def prefix1D3S3S : Prefix := ⟨first ++ dual, third ++ singular, third ++ singular⟩

theorem r34a_syntagmatic : r34a.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3S3S.around .object)
    ((⟨[], [], third ++ singular⟩ : Prefix).around .object) rfl).mp (by decide)) (by decide)

theorem r45b_syntagmatic : r45b.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3Sno.around .object) ((⟨[], [], [.dummy]⟩ : Prefix).around .object)
    rfl).mp (by decide)) (by decide)

theorem r45a_syntagmatic : r45a.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3S3S.around .object)
    ((⟨[], [], third ++ singular⟩ : Prefix).around .object) rfl).mp (by decide)) (by decide)

theorem r46_syntagmatic : r46.Syntagmatic := by
  intro h
  exact absurd ((h (prefix2S3S.around .agent) (prefix2S.around .agent) rfl).mp (by decide))
    (by decide)

theorem r32_syntagmatic : r32.Syntagmatic := by
  intro h
  exact absurd ((h (prefix1S3S.around .object) (prefix3S3S.around .object) rfl).mp (by decide))
    (by decide)

theorem r40'_syntagmatic : r40'.Syntagmatic := by
  intro h
  exact absurd ((h (prefix3S3S.around .agent)
    ((⟨third ++ singular, third ++ singular, third ++ singular⟩ : Prefix).around .agent) rfl).mp
    (by decide)) (by decide)

theorem r26'_syntagmatic : r26'.Syntagmatic := by
  intro h
  exact absurd ((h (prefix1S3S.around .goal)
    ((⟨third ++ singular, first ++ singular, third ++ singular⟩ : Prefix).around .goal) rfl).mp
    (by decide)) (by decide)

theorem r33_syntagmatic : r33.Syntagmatic := by
  intro h
  exact absurd ((h (prefix1D3S3S.around .goal)
    ((⟨[], third ++ singular, third ++ singular⟩ : Prefix).around .goal) rfl).mp (by decide))
    (by decide)

/-! ### Case 1 (§4.2.1): object impoverishment precedes agent impoverishment

The 3S:3S prefix is ∅ (Table 15), so no *m*, the exponent of a third person object (31), is
inserted: the object's third person must be gone at Vocabulary Insertion, which (34a) does only
while the agent is still there for its context. The theorems are about the feature bundles the
two orders leave; that the block order conflicts with Arregi and Nevins rests on the paper's
labelling of (40) as paradigmatic (see the implementation notes). -/

theorem form_3S3S :
    Taos.form ⟨some (.third, .singular), none, some (.third .singular)⟩ = some "" := by
  decide

theorem case1_syn_para : run [r34a, r40] prefix3S3S = ⟨[], [], singular⟩ := by decide

theorem case1_para_syn : run [r40, r34a] prefix3S3S = ⟨[], [], third ++ singular⟩ := by decide

theorem case1_orders_differ : run [r34a, r40] prefix3S3S ≠ run [r40, r34a] prefix3S3S := by
  decide

/-- The block architecture keeps the object's third person, which (31) would expone as *m*. -/
theorem case1_block (l : List Rule) (hl : ParaThenSyn l) (hperm : l.Perm [r40, r34a]) :
    (run l prefix3S3S).object = third ++ singular := by
  rw [run_eq_of_paraThenSyn r40_paradigmatic r34a_syntagmatic hl hperm, case1_para_syn]

/-- The same holds for the 3S:3I prefix and (34b). Syntagmatic first, the object loses
`[−participant]`; paradigmatic first, it keeps it. -/
theorem case1_inverse :
    run [r34b, r40] prefix3S3I = ⟨[], [], [.author false, .inverse]⟩ ∧
      run [r40, r34b] prefix3S3I = ⟨[], [], third ++ inverse⟩ := by
  decide

/-! ### Case 2 (§4.2.2): dummy object impoverishment precedes agent impoverishment

The 3S:no and 3S:3S prefixes are ∅ and toneless (Table 16), so the paper has the object
obliterated and its singular features deleted by (45), which need the singular agent that (40)
removes. The 3S:3S half reaches the surface (the block order leaves a singular object, which
would be exponed); the dummy half is featural only, since a one-argument prefix with a
featureless dummy object is ∅ and toneless under either order. -/

theorem form_3Sno : Taos.form ⟨some (.third, .singular), none, some .dummy⟩ = some "" := by
  decide

theorem case2_dummy_syn_para : run [r45b, r40] prefix3Sno = ⟨[], [], []⟩ := by decide

theorem case2_dummy_para_syn : run [r40, r45b] prefix3Sno = ⟨[], [], [.dummy]⟩ := by decide

theorem case2_singular_syn_para : run [r34a, r45a, r40] prefix3S3S = ⟨[], [], []⟩ := by
  decide

theorem case2_singular_para_syn :
    run [r40, r34a, r45a] prefix3S3S = ⟨[], [], third ++ singular⟩ := by
  decide

theorem case2_orders_differ : run [r45b, r40] prefix3Sno ≠ run [r40, r45b] prefix3Sno := by
  decide

/-- The block architecture keeps the dummy object. -/
theorem case2_block (l : List Rule) (hl : ParaThenSyn l) (hperm : l.Perm [r40, r45b]) :
    (run l prefix3Sno).object = [.dummy] := by
  rw [run_eq_of_paraThenSyn r40_paradigmatic r45b_syntagmatic hl hperm, case2_dummy_para_syn]

/-! ### Case 3 (§4.2.3): `[+minimal]` impoverishment precedes `[+participant]` impoverishment

The 2S:3S transitive prefix *o* differs from the 2S intransitive *ǫ* (Table 17), so the two
agents differ at Vocabulary Insertion. (46) makes them differ by deleting `[+minimal]` from the
transitive agent, and needs the `[+participant]` that (11a) deletes. -/

/-- The transitive and intransitive 2S prefixes differ. -/
theorem form_2S3S_ne_form_2S :
    Taos.form ⟨some (.second, .singular), none, some (.third .singular)⟩ ≠
      Taos.form ⟨some (.second, .singular), none, none⟩ := by
  decide

theorem case3_syn_para : (run [r46, r11a] prefix2S3S).agent = [.author false, .atomic true] := by
  decide

theorem case3_para_syn : (run [r11a, r46] prefix2S3S).agent = (run [r11a] prefix2S).agent := by
  decide

theorem case3_orders_differ : run [r46, r11a] prefix2S3S ≠ run [r11a, r46] prefix2S3S := by
  decide

/-- The block architecture makes the transitive and intransitive 2S agents identical. -/
theorem case3_block (l : List Rule) (hl : ParaThenSyn l) (hperm : l.Perm [r11a, r46]) :
    (run l prefix2S3S).agent = (run [r11a] prefix2S).agent := by
  rw [run_eq_of_paraThenSyn r11a_paradigmatic r46_syntagmatic hl hperm, case3_para_syn]

/-! ### Case 4 (§4.2.4): third singular object impoverishment precedes possessive impoverishment

The 1S:3S possessive prefix is *ôn* (Table 22), with no *m*: the object's third person is
deleted by (32), which needs the singular goal that (26) makes non-singular. -/

/-- The 1S:3S possessive prefix has no *m*. -/
theorem form_1S3S :
    Taos.form ⟨none, some (.first, .singular), some (.third .singular)⟩ = some "ôn" ∧
      'm' ∉ "ôn".toList := by
  decide

theorem case4_syn_para :
    run [r32, r26] prefix1S3S = ⟨[], first ++ [.minimal true], singular⟩ := by
  decide

theorem case4_para_syn :
    run [r26, r32] prefix1S3S = ⟨[], first ++ [.minimal true], third ++ singular⟩ := by
  decide

theorem case4_orders_differ : run [r32, r26] prefix1S3S ≠ run [r26, r32] prefix1S3S := by
  decide

/-- The block architecture keeps the object's third person, which (31) would expone as *m*. -/
theorem case4_block (l : List Rule) (hl : ParaThenSyn l) (hperm : l.Perm [r26, r32]) :
    (run l prefix1S3S).object = third ++ singular := by
  rw [run_eq_of_paraThenSyn r26_paradigmatic r32_syntagmatic hl hperm, case4_para_syn]

/-- (33) before (32) keeps the third person of the object of *opénôm* (Table 21), the *m*, by
making the goal non-singular before (32) looks at it. -/
theorem r33_bleeds_r32 :
    (run [r33, r32] prefix1D3S3S).object = third ++ singular ∧
      (run [r32, r33] prefix1D3S3S).object = singular := by
  decide

/-- The 1D:3S:3S ditransitive prefix keeps *m*. -/
theorem form_1D3S3S :
    Taos.form ⟨some (.first, .dual), some (.third, .singular), some (.third .singular)⟩ =
        some "opénôm" ∧
      'm' ∈ "opénôm".toList := by
  decide

/-! ### Case 5 (§4.2.5): a paradigmatic rule before a syntagmatic one

The 1S:3I possessive prefix *ónôm* keeps *n*, the exponent of `[+minimal]` (20): (26) deletes
the goal's `[+atomic]` first and bleeds (29), which would delete the `[+minimal]`. -/

/-- The 1S:3I possessive prefix keeps *n*. -/
theorem form_1S3I :
    Taos.form ⟨none, some (.first, .singular), some (.third .inverse)⟩ = some "ónôm" ∧
      'n' ∈ "ónôm".toList := by
  decide

theorem case5_para_syn :
    (run [r26, r29 .goal] prefix1S3I).goal = first ++ [.minimal true] := by
  decide

theorem case5_syn_para :
    (run [r29 .goal, r26] prefix1S3I).goal = first ++ [.atomic true] := by
  decide

/-! ### Linearization, metathesis and exponence

After Linearization the prefix is a string of feature terminals, each tagged with its slot,
in the order of (4) and (5); the appendix's rules of metathesis swap adjacent terminals, the
library's `TerminalMetathesisRule`. Exponence then reads each terminal in its prefix. -/

/-- A terminal of the linearized prefix is a slot with a feature. -/
abbrev Tok := Slot × Feat

/-- The linearized prefix. -/
def linearize (p : Prefix) : List Tok :=
  [Slot.agent, .goal, .object].flatMap fun s ↦
    ((List.range 6).flatMap fun k ↦ (p.get s).filter (Feat.rank · == k)).map ((s, ·))

/-- By rule (18), the goal's `[−author]` swaps with its following inverse feature, when an agent is
present. -/
def m18 (p : Prefix) : TerminalMetathesisRule Tok :=
  ⟨fun n ↦ p.agent ≠ [] ∧ n.focus = (.goal, .author false) ∧
    n.rightCtx.head? = some (.goal, .inverse)⟩

/-- By rule (23), the paper's (26), a `[−atomic]` agent's `[+minimal]` swaps with the second
argument's following `[−author]`. -/
def m23 (p : Prefix) : TerminalMetathesisRule Tok :=
  ⟨fun n ↦ p.agent.Has (.atomic false) ∧ n.focus = (.agent, .minimal true) ∧
    n.rightCtx.head? = some (p.secondArg, .author false)⟩

/-- By rule (22), the paper's (24), the goal's `[−author]` swaps with its following `[−atomic]`
before `[+minimal]`, when an agent is present. -/
def m22 (p : Prefix) : TerminalMetathesisRule Tok :=
  ⟨fun n ↦ p.agent ≠ [] ∧ n.focus = (.goal, .author false) ∧
    n.rightCtx.take 2 = [(.goal, .atomic false), (.goal, .minimal true)]⟩

/-- The appendix's two sets of rules of metathesis in order. -/
def metathesis (p : Prefix) : List Tok → List Tok :=
  runModules [(m18 p).apply, (m23 p).apply, (m22 p).apply]

/-- The phonological role of an exponent, for the epenthetic vowel. -/
inductive Role where
  | onset
  | coda
  | full
  deriving DecidableEq

/-- An exponent and its role. -/
abbrev Morph := String × Role

/-- The exponents of one terminal in its prefix follow the appendix's rules of exponence (8), (10),
(13), (16), (17), (19), (20), (25), (30), (31), (36), (37) and (39). -/
def exponeTok (p : Prefix) (t : Tok) : List Morph :=
  let s := t.1
  let a := p.get s
  let leftmostω := decide (p.leftmostNumber = some s)
  let object3 := decide (s = .object ∧ a.IsThird)
  let transitiveDual := decide (p.agent.IsDual ∧ p.goal = [])
  if a.IsThird ∧ a.IsPlural then
    if t.2 = .participant false ∧ !transitiveDual then [("w", .coda)] else []
  else match t.2 with
  | .refl => if transitiveDual then [] else [("mo", .full)]
  | .dummy => []
  | .participant true =>
    if p.leftmostPerson == some s then
      if a.Has (.author false) then [("m", .onset)]
      else if a.Has (.author true) ∧ a.Has (.atomic true) then [("t", .onset)]
      else [("k", .onset)]
    else []
  | .participant false => if object3 then [("m", .coda)] else []
  | .author true => []
  | .author false =>
    if object3 ∨ s = .agent ∨ p.agent = [] then []
    else
      let l := p.leftmostNumberArg
      if l.IsInverse then [("pi", .full)] else if l.IsDual then [("pé", .full)] else []
  | .inverse =>
    if leftmostω && !object3 then [(if p.LeftmostSecond then "o" else "i", .full)] else []
  | .atomic _ => if leftmostω && !object3 then [(if a.IsSingular then "ǫ" else "o", .full)] else []
  | .minimal true => if leftmostω ∧ ¬ object3 ∧ ¬ a.IsSingular then [("n", .coda)] else []
  | .minimal false => []

/-- The exponents of a linearized prefix, the portmanteaux (6), (41) and (49) and *mây*
first; the flag marks a portmanteau form, which takes no tone rule. -/
def expone (p : Prefix) (toks : List Tok) : List Morph × Bool :=
  if p.agent = second ∧ p.object = [] then
    if p.goal = first ++ dual ∨ p.goal = first ++ inverse then ([("ku", .full)], true)
    else if p.goal = first then ([("mây", .full)], true)
    else (toks.flatMap (exponeTok p), false)
  else match p.args with
  | [a] =>
    if a = [.participant true, .author true, .atomic true] then ([("ti", .full)], true)
    else if a = [.author true, .atomic true, .minimal true] then ([("pi", .full)], true)
    else if a = [.author false, .atomic true, .minimal true] then ([("ki", .full)], true)
    else (toks.flatMap (exponeTok p), false)
  | _ => (toks.flatMap (exponeTok p), false)

/-! ### Epenthesis and tone -/

/-- The concatenation of a list of strings (`String.join` does not reduce under `decide`). -/
def concat (l : List String) : String := l.foldl (· ++ ·) ""

/-- A vowel of the exponents, before tone is assigned. -/
def isVowel (c : Char) : Bool := "aeiouǫé".toList.contains c

/-- By the epenthesis rule (27), an onset consonant with no vowel after it, or a coda consonant with
none before it, takes the vowel *o*. -/
def epenthesis : Option Char → List Morph → List String
  | _, [] => []
  | prev, (m, r) :: rest =>
    let before := if r == .coda && !(prev.any isVowel) then ["o"] else []
    let next := (rest.head?.map (·.1)).bind fun n ↦ n.toList.head?
    let after := if r == .onset && !(next.any isVowel) then ["o"] else []
    let out := before ++ [m] ++ after
    out ++ epenthesis (concat out).toList.getLast? rest

/-- A tone. -/
inductive Tone where
  | high
  | falling
  deriving DecidableEq

/-- A toned vowel, as the fragment prints it. -/
def mark : Tone → Char → String
  | .high, 'o' => "ó"
  | .high, 'ǫ' => "ǫ́"
  | .high, 'i' => "í"
  | .high, 'e' | .high, 'é' => "é"
  | .high, 'u' => "ú"
  | .high, 'a' => "á"
  | .falling, 'o' => "ô"
  | .falling, 'ǫ' => "ǫ̂"
  | .falling, 'i' => "î"
  | .falling, 'e' | .falling, 'é' => "ê"
  | .falling, 'u' => "û"
  | .falling, 'a' => "â"
  | _, c => c.toString

/-- The syllable nuclei of a string from index `i`, each with whether its syllable is
closed. -/
def syllables : List Char → ℕ → List (ℕ × Bool)
  | [], _ => []
  | c :: rest, i =>
    if !isVowel c then syllables rest (i + 1)
    else match rest with
      | d :: e :: rest' =>
        if !isVowel d && !isVowel e then (i, true) :: syllables (e :: rest') (i + 2)
        else (i, false) :: syllables (d :: e :: rest') (i + 1)
      | [d] => if !isVowel d then [(i, true)] else (i, false) :: syllables [d] (i + 1)
      | [] => [(i, false)]

/-- The appendix's context-specific tone rules (51b)–(51h), read off the cell: a tone for the
final syllable, `some none` for none, `none` where no rule applies. -/
def exception (c : Taos.Cell) : Option (Option Tone) :=
  match c.agent, c.goal, c.object with
  | some (_, .dual), none, some .dummy | some (_, .dual), none, some (.third .singular) =>
    some (some .high)
  | some (.first, .dual), none, some (.third .plural)
  | some (.second, .dual), none, some (.third .plural)
  | some (.first, .dual), none, some .reflexive
  | some (.second, .dual), none, some .reflexive => some (some .falling)
  | none, some (.third, .singular), some (.third .singular) => some none
  | some (_, .singular), some (.third, .singular), some (.third .singular) => some none
  | none, some (.third, .singular), some _ => some (some .high)
  | some (_, .singular), some (.third, .singular), some _ => some (some .high)
  | none, some (.third, .dual), some _ => some (some .high)
  | _, _, _ => none

/-- By the tone rules (50) and (51), a one-argument prefix is toneless; otherwise the final
syllable, *mo* aside, is high if open and falling if closed, *pé* is high, and the syllable before
it is high unless it precedes *pi* or *pé*. -/
def tone (c : Taos.Cell) (nargs : ℕ) (morphs : List String) (fixed : Bool) : String :=
  let s := concat morphs
  if fixed then s else
  let hasMo := morphs.getLast? == some "mo" && morphs.length > 1
  let chars := if hasMo then s.toList.take (s.toList.length - 2) else s.toList
  let syl := syllables chars 0
  match syl.getLast? with
  | none => s
  | some (vf, closed) =>
    let pOnset := chars[vf - 1]? == some 'p'
    let final : Option Tone := match exception c with
      | some t => t
      | none =>
        if nargs ≤ 1 then none
        else if pOnset && chars[vf]? == some 'é' then some .high
        else if closed then some .falling else some .high
    let vp := ((syl.getD (syl.length - 2) (0, false)).1)
    let penult := final.isSome && syl.length ≥ 2 && !pOnset
    let out := concat (chars.mapIdx fun i ch ↦
      if i == vf then (match final with | some t => mark t ch | none => ch.toString)
      else if penult && i == vp then mark .high ch else ch.toString)
    out ++ (if hasMo then "mo" else "")

/-! ### The derivation -/

/-- The person features of a cell's argument. -/
def personFeats : Person → Arg
  | .first => first
  | .second => second
  | .third => third
  | _ => []

/-- The number features of a cell's argument. -/
def numberFeats : Number.Inverse.Category → Arg
  | .singular => singular
  | .dual => dual
  | .plural => plural
  | .inverse => inverse

/-- Spell-Out: the prefix of a cell of the paradigm. -/
def spellOut (c : Taos.Cell) : Prefix where
  agent := (c.agent.map fun a ↦ personFeats a.1 ++ numberFeats a.2).getD []
  goal := (c.goal.map fun a ↦ personFeats a.1 ++ numberFeats a.2).getD []
  object := match c.object with
    | none => []
    | some .dummy => [.dummy]
    | some .reflexive => [.refl]
    | some (.third n) => third ++ numberFeats n

/-- A prefix expones its present arguments, less an object silenced by the allomorphs (39b,d). -/
def Prefix.exponed (p : Prefix) : ℕ :=
  p.args.length -
    if p.agent.IsDual ∧ p.goal = [] ∧ (p.object = [.refl] ∨ p.object.IsThird ∧ p.object.IsPlural)
    then 1 else 0

/-- The surface form of a cell under a rule system results from Spell-Out, impoverishment,
Linearization, metathesis, exponence, epenthesis and tone. -/
def deriveWith (rules : List Rule) (c : Taos.Cell) : String :=
  let p := run rules (spellOut c)
  let (morphs, fixed) := expone p (metathesis p (linearize p))
  let morphs := if morphs.map (·.1) == ["w"] then [("u", .full)] else morphs
  tone c p.exponed (epenthesis none morphs) fixed

/-- The surface form of a cell under the appendix's seven sets, with or without the optional
(5). -/
def derive (optional : Bool) : Taos.Cell → String := deriveWith (impoverishment optional)

/-- The cells of the paradigm the appendix leaves unaccounted for (see the TODO). -/
def unaccounted : List Taos.Cell :=
  [⟨none, some (.second, .singular), none⟩,
   ⟨some (.first, .singular), some (.second, .singular), none⟩,
   ⟨some (.first, .dual), some (.second, .singular), none⟩,
   ⟨some (.first, .inverse), some (.second, .singular), none⟩,
   ⟨some (.third, .inverse), none, some (.third .plural)⟩,
   ⟨some (.third, .inverse), none, some .reflexive⟩,
   ⟨none, some (.third, .dual), some (.third .singular)⟩,
   ⟨none, some (.third, .dual), some (.third .inverse)⟩,
   ⟨none, some (.third, .dual), some (.third .plural)⟩]

/-- Every other cell of the paradigm derives, with or without the optional (5). -/
theorem derive_eq_form :
    ∀ r ∈ Taos.prefixes, r.1 ∉ unaccounted →
      r.2 = derive false r.1 ∨ r.2 = derive true r.1 := by
  decide +kernel

/-- What the pipeline gives the unaccounted cells. -/
theorem derive_unaccounted :
    unaccounted.map (derive false) =
      ["kǫ", "kǫ", "kǫ", "kǫ", "îw", "ímo", "ónóm", "ónóm", "ónów"] := by
  decide +kernel

/-- With (40) and (26) as printed, the same cells derive; the bundles differ only where a
3S:3S:O ditransitive keeps its agent, whose exponent is ∅ anyway. -/
theorem derive_eq_form_printed :
    ∀ r ∈ Taos.prefixes, r.1 ∉ unaccounted →
      r.2 = deriveWith (impoverishmentPrinted false) r.1 ∨
        r.2 = deriveWith (impoverishmentPrinted true) r.1 := by
  decide +kernel

/-! ### Impoverishment precedes metathesis in Taos (§3.2)

*opén*, the 1D:3:no prefix of the paper's (25), needs (24) to remove the goal's
`[−participant]` before (23) can swap the agent's `[+minimal]` with the goal's `[−author]`;
without (24) the two are not adjacent and the string stays in the order of *o-n-pé*. -/

/-- The 1D:3S:no prefix after impoverishment. -/
def prefix1D3no : Prefix :=
  run (impoverishment false)
    (spellOut ⟨some (.first, .dual), some (.third, .singular), some .dummy⟩)

theorem metathesis_prefix1D3no :
    (metathesis prefix1D3no (linearize prefix1D3no)).map (·.2) =
      [.author true, .atomic false, .author false, .minimal true, .atomic true, .minimal true,
        .dummy] := by
  decide

/-- Without (24), (23) finds `[−participant]` in the way and does nothing. -/
theorem metathesis_without_r24 :
    let p := run [r1, r4, r9, r12, r33, r34a, r34b, r14, r35, r46, r2, r7b, r7a, r32, r15,
        r26, r45a, r45b, r40, r47, r3, r11a, r11b, r29 .agent, r29 .goal, r43, r44, r38b, r42,
        r38a, r48a, r48b]
      (spellOut ⟨some (.first, .dual), some (.third, .singular), some .dummy⟩)
    metathesis p (linearize p) = linearize p := by
  decide

theorem derive_prefix1D3no :
    derive false ⟨some (.first, .dual), some (.third, .singular), some .dummy⟩ = "opén" := by
  decide

/-! ### Impoverishment precedes metathesis in Basque (§3.1)

The finite auxiliary of (10) is a string of terminals: the absolutive clitic, T, and the
ergative and dative clitics. Participant Dissimilation, the paper's (16) and (18) after Arregi
and Nevins's (25), obliterates a clitic in the Feature Markedness module; T-Noninitiality, the
paper's (12), is repaired in the Linear Operations module by Ergative Metathesis (13) or
L-Support. -/

/-- A Basque terminal is a list of Minimalist features. -/
abbrev Terminal := List FeatureVal

/-- A clitic bears its case and its person and number features. -/
def clitic (c : Case) (φ : Terminal) : Terminal := ⟨.case, c⟩ :: φ

/-- First person, in the Minimalist inventory. -/
def firstφ : Terminal := [⟨.participant, true⟩, ⟨.author, true⟩]

/-- Second person, in the Minimalist inventory. -/
def secondφ : Terminal := [⟨.participant, true⟩, ⟨.author, false⟩]

/-- T, past tense (see the implementation notes). -/
def pastT : Terminal := [⟨.tense, true⟩]

/-- The epenthetic L of L-Support, a terminal without features. -/
def lSupport : Terminal := []

/-- Under Participant Dissimilation a `[+participant +author]` clitic is obliterated when another
clitic of the word bears `trigger`; Arregi and Nevins's `[+motion]` restriction and their First
Singular Clitic Impoverishment, which keep first singular clitics out of it, are not modelled. -/
def participantDissimilation (trigger : Terminal) : ObliterationRule Terminal :=
  ⟨fun n ↦ firstφ ⊆ n.focus ∧ ∃ t ∈ n.leftCtx ++ n.rightCtx, trigger ⊆ t⟩

/-- In Ondarru, the paper's (16), the trigger is an ergative participant clitic. -/
def ondarru : ObliterationRule Terminal :=
  participantDissimilation [⟨.case, .erg⟩, ⟨.participant, true⟩]

/-- In Zamudio, the paper's (18), the trigger is any participant clitic. -/
def zamudio : ObliterationRule Terminal := participantDissimilation [⟨.participant, true⟩]

/-- Under Ergative Metathesis, the paper's (13) after Arregi and Nevins's (105), a word-initial T is
preceded by the first ergative clitic that follows it, without (105a)'s conditions on an intervening
dative clitic. -/
def ergativeMetathesis : SpelloutDomain Terminal → SpelloutDomain Terminal :=
  rewriteFirst
    (fun n ↦ n.leftCtx = [] ∧ ⟨.tense, true⟩ ∈ n.focus ∧ ∃ t ∈ n.rightCtx, ⟨.case, .erg⟩ ∈ t)
    fun n ↦ match n.rightCtx.find? (·.contains (⟨.case, .erg⟩)) with
      | some e => n.leftCtx.reverse ++ e :: n.focus :: n.rightCtx.erase e
      | none => n.toList

/-- Ergative Metathesis preserves the number of terminals. -/
theorem length_ergativeMetathesis (d : SpelloutDomain Terminal) :
    (ergativeMetathesis d).length = d.length := by
  unfold ergativeMetathesis
  refine length_rewriteFirst (fun n ↦ ?_) d
  cases h : n.rightCtx.find? (·.contains (⟨.case, .erg⟩)) with
  | none => rfl
  | some e =>
    have hmem := List.mem_of_find?_eq_some h
    simp only [List.length_cons, Neighborhood.toList, List.length_append, List.length_reverse,
      List.length_erase_of_mem hmem]
    have := List.length_pos_of_mem hmem
    omega

/-- L-Support: an L before a word-initial T. -/
def lSupportRepair (d : SpelloutDomain Terminal) : SpelloutDomain Terminal :=
  if ∃ t ∈ d.head?, ⟨.tense, true⟩ ∈ t then lSupport :: d else d

/-- The Linear Operations module applies the two repairs of T-Noninitiality. -/
def linearOperations : SpelloutDomain Terminal → SpelloutDomain Terminal :=
  lSupportRepair ∘ ergativeMetathesis

/-- Feature Markedness before Linear Operations, the order of Figure 1. -/
def markednessThenLinear (pd : ObliterationRule Terminal) :
    SpelloutDomain Terminal → SpelloutDomain Terminal :=
  runModules [pd.apply, linearOperations]

/-- Linear Operations before Feature Markedness, the order both papers reject. -/
def linearThenMarkedness (pd : ObliterationRule Terminal) :
    SpelloutDomain Terminal → SpelloutDomain Terminal :=
  runModules [linearOperations, pd.apply]

/-- The Ondarru auxiliary of (17), *s-endu-n* 'you saw us': a first plural absolutive clitic,
past T, and a second singular ergative clitic. -/
def auxiliary17 : SpelloutDomain Terminal :=
  [clitic .abs (firstφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩]), pastT,
   clitic .erg (secondφ ++ [⟨.atomic, true⟩, ⟨.minimal, true⟩])]

/-- The Zamudio auxiliary of (19), *y-a-tzu-e-n* 'we accompanied you lot': past T, a second
plural dative clitic, and a first plural ergative clitic. -/
def auxiliary19 : SpelloutDomain Terminal :=
  [pastT, clitic .dat (secondφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩]),
   clitic .erg (firstφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩])]

/-- In Ondarru with markedness first, Participant Dissimilation obliterates the absolutive clitic,
leaving T initial, and Ergative Metathesis then fronts the ergative clitic, giving *s-endu-n*. -/
theorem ondarru_markedness_then_linear :
    markednessThenLinear ondarru auxiliary17 =
      [clitic .erg (secondφ ++ [⟨.atomic, true⟩, ⟨.minimal, true⟩]), pastT] := by
  decide

/-- In Ondarru with the linear module first, T is not initial, so neither repair applies, and after
the absolutive clitic goes T is stranded initial, Arregi and Nevins's (17b) *eu-su-n*. -/
theorem ondarru_linear_then_markedness :
    linearThenMarkedness ondarru auxiliary17 =
      [pastT, clitic .erg (secondφ ++ [⟨.atomic, true⟩, ⟨.minimal, true⟩])] := by
  decide

theorem ondarru_orders_differ :
    markednessThenLinear ondarru auxiliary17 ≠ linearThenMarkedness ondarru auxiliary17 := by
  decide

/-- In Zamudio with markedness first, Participant Dissimilation obliterates the ergative clitic, so
no ergative is left to front and L-Support repairs the initial T, giving *y-a-tzu-e-n*. -/
theorem zamudio_markedness_then_linear :
    markednessThenLinear zamudio auxiliary19 =
      [lSupport, pastT, clitic .dat (secondφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩])] := by
  decide

/-- In Zamudio with the linear module first, Ergative Metathesis fronts the ergative clitic, which
Participant Dissimilation then obliterates, stranding T initial, the form Arregi and Nevins's §6.2.4
rejects. -/
theorem zamudio_linear_then_markedness :
    linearThenMarkedness zamudio auxiliary19 =
      [pastT, clitic .dat (secondφ ++ [⟨.atomic, false⟩, ⟨.minimal, false⟩])] := by
  decide

theorem zamudio_orders_differ :
    markednessThenLinear zamudio auxiliary19 ≠ linearThenMarkedness zamudio auxiliary19 := by
  decide

end Middleton2026
