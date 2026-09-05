import Linglib.Syntax.Minimalist.Agree.Cyclic
import Linglib.Syntax.Agreement.PersonCaseConstraint
import Linglib.Morphology.Exponence.Select
import Linglib.Studies.BejarRezac2003
import Linglib.Data.Examples.CoonKeine2021

/-!
# Coon and Keine 2021: feature gluttony

[coon-keine-2021] argue that hierarchy effects, the Person Case Constraint on clitic clusters,
the person restriction on Icelandic dative-nominative agreement and the person and number
restrictions on German assumed-identity copulas, come not from failed Agree but from too much
of it. A probe is a hierarchy of segments, each of which agrees on its own with the closest
accessible DP bearing it and copies that DP's whole geometry back, so when the lower of two DPs
bears segments the higher lacks, distinct segments agree with distinct DPs and the probe is
gluttonous, which happens in inverse configurations only. Gluttony is harmless in itself: a
clitic-doubling probe crashes because every DP it agreed with must cliticize and binary Merge
cannot move two heads at once, while an agreement probe crashes only if the values it carries
demand different Vocabulary items, so syncretism or the absence of an item lets a gluttonous
probe converge. Articulating the person probe further along the speaker and addressee leaves of
the person geometry derives the Weak, Ultrastrong and Me-First constraints, datives that expose
their person node alone turn the Weak pattern into the Strong one, and since a nonfinite clause
has no probe and a PP, a strong pronoun or absolutive displacement leaves no second goal, the
absence of the effects there follows without the caveats a Person Licensing Condition needs.

## Implementation notes

Goals are position-indexed so that two DPs with the same features stay distinct, and a
segment's Agree is the relativized search of the probe substrate over that list, so the
two-goal characterization of gluttony rests on the substrate's search. Person geometries are
the branching geometry of the cyclic-Agree substrate and number the two-segment geometry of the
paper; the model pairs a number probe with every person probe, one direction of the paper's
probe-specification hierarchy. A K-encapsulated dative exposes its person node and no number:
the paper leaves the dative's number open in a footnote and says a quirky DP externally bears
at most a person feature, and the choice is what puts the nominative's number in the context
the paper's diagrams caption. The crash of a gluttonous clitic-doubling probe is taken as the
paper argues it, from its cliticization requirement, binary Merge and a Markovian derivation,
rather than derived. A paradigm holds the forms the paper glosses, with German present *bin*
added since the past-tense improvement the paper reports presupposes it, and is undefined in
number contexts the paper does not gloss, so that an unglossed cell cannot converge by
accident; the item a value demands is the score selection of the exponence substrate with the
segment count as specificity, and a value demanding no item, the Kichean singular, competes
with nothing. The person-case-constraint grammars of the substrate parametrize the descriptive
table the probes derive; the Ultrastrong probe parts from that parametrization at 2 > 2 and the
Me-First probe from the table itself at 1 > 1, a cell the paper does not remark on. The
comparison with the Person Licensing Condition is the paper's own argument from probeless
clauses, and the restricted condition keeps the escape through a Case-valuing head that the
substrate formalization of the original condition has. Examples the paper records without an
account, the Icelandic copulas, default agreement, participle agreement and the expletive, carry
no configuration and enter no theorem.

## TODO

- Fission and portmanteau realization of a gluttonous agreement probe (§5.2) are not modelled.

## References

* [J. Coon and S. Keine, *Feature Gluttony* (2021)][coon-keine-2021]
* [S. Béjar and M. Rezac, *Cyclic Agree* (2009)][bejar-rezac-2009]
* [H. Harley and E. Ritter, *Person and number in pronouns: A feature-geometric analysis*
  (2002)][harley-ritter-2002]
* [S. Béjar and M. Rezac, *Person licensing and the derivation of PCC effects*
  (2003)][bejar-rezac-2003]
* [O. Preminger, *Asymmetries between person and number in syntax* (2011)][preminger-2011]
* [O. Preminger, *Agreement and Its Failures* (2014)][preminger-2014]
* [O. Preminger, *What the PCC tells us about "abstract" agreement, head movement, and
  locality* (2019)][preminger-2019]
* [A. R. Deal, *Interaction and satisfaction in φ-agreement* (2015)][deal-2015a-nels]
* [R. Pancheva and M. L. Zubizarreta, *The Person Case Constraint: The syntactic encoding of
  perspective* (2018)][pancheva-zubizarreta-2018]
* [A. Stegovec, *Taking case out of the Person-Case Constraint* (2020)][stegovec-2020]
* [H. Á. Sigurðsson and A. Holmberg, *Icelandic dative intervention: Person and number are
  separate probes* (2008)][sigurdsson-holmberg-2008]
* [C. T. Schütze, *Syncretism and double agreement with Icelandic nominative objects*
  (2003)][schutze-2003]
* [J. Coon, S. Keine and M. Wagner, *Hierarchy effects in copular constructions: The PCC corner
  of German* (2017)][coon-keine-wagner-2017]
* [S. Keine, M. Wagner and J. Coon, *Hierarchy effects in copula constructions*
  (2019)][keine-wagner-coon-2019]
* [H. Thráinsson, *Icelandic* (1994)][thrainsson-1994]
-/

namespace CoonKeine2021

open Minimalist Minimalist.CyclicAgree Morphology.Exponence Data.Examples

/-! ### Goals and their visible geometries -/

/-- A goal DP, with the K(ase) shell that encapsulates a dative so that only its person node is
visible from outside (§3.4.1: Basque and Icelandic datives). -/
structure Goal where
  /-- The DP's person. -/
  person : Person
  /-- Whether the DP is plural. -/
  plural : Bool := false
  /-- Whether a K shell hides everything but the person node. -/
  encapsulated : Bool := false
  deriving DecidableEq, Repr

/-- A φ-transparent goal. -/
def dp (p : Person) : Goal := { person := p }

/-- A φ-transparent plural goal. -/
def dpPl (p : Person) : Goal := { person := p, plural := true }

/-- A K-encapsulated dative goal. -/
def dat (p : Person) : Goal := { person := p, encapsulated := true }

/-- The person segments a goal exposes: its geometry under (11), or its person node alone. -/
def Goal.personSegments (g : Goal) : List Segment :=
  if g.encapsulated then [.pi] else personSpec .branching g.person

/-- Number geometry (12). -/
inductive NumberSegment where
  /-- [NUM], borne by every DP. -/
  | num
  /-- [PL], borne by plurals. -/
  | pl
  deriving DecidableEq, Repr

/-- The number segments a goal exposes; an encapsulated goal exposes none. -/
def Goal.numberSegments (g : Goal) : List NumberSegment :=
  if g.encapsulated then [] else if g.plural then [.num, .pl] else [.num]

theorem pi_mem_personSegments (g : Goal) : Segment.pi ∈ g.personSegments := by
  unfold Goal.personSegments
  split <;> [exact .head _; exact pi_mem_personSpec _ _]

/-- The goal as a φ-goal of [bejar-rezac-2003]: an encapsulated dative has its Case valued by
its own head, a transparent goal has unvalued Case. -/
def Goal.toPhiGoal (g : Goal) : PhiGoal :=
  let cell := Agreement.Cell.pn g.person.toUD (if g.plural then .Plur else .Sing)
  if g.encapsulated then .valued .dat cell else .unvalued cell

/-! ### Segment-based Agree and gluttony (their (14)–(16)) -/

section Agree

variable {σ : Type*} [DecidableEq σ]

/-- A probe segment as a relativized probe over position-indexed goals: it sees the goals
whose geometry bears it. -/
def segmentProbe (geo : Goal → List σ) (s : σ) : Probe (Goal × ℕ) :=
  .ofVis λ t => decide (s ∈ geo t.1)

/-- Agree (14) for one probe segment: the closest accessible goal whose geometry bears it. -/
def segmentAgree (geo : Goal → List σ) (s : σ) (goals : List Goal) : Option (Goal × ℕ) :=
  (segmentProbe geo s).search goals.zipIdx

/-- The goals some segment of the probe has agreed with. -/
def agreed (geo : Goal → List σ) (P : List σ) (goals : List Goal) : List (Goal × ℕ) :=
  goals.zipIdx.filter λ t => P.any λ s => segmentAgree geo s goals == some t

/-- Feature gluttony (16): the probe has agreed with more than one DP. -/
def Gluttonous (geo : Goal → List σ) (P : List σ) (goals : List Goal) : Prop :=
  ∃ t ∈ agreed geo P goals, ∃ u ∈ agreed geo P goals, t ≠ u

instance (geo : Goal → List σ) (P : List σ) (goals : List Goal) :
    Decidable (Gluttonous geo P goals) := by
  unfold Gluttonous; infer_instance

/-- The values the probe carries after Agree, one whole geometry per agreed goal ((16),
(58)). -/
def values (geo : Goal → List σ) (P : List σ) (goals : List Goal) : List (List σ) :=
  (agreed geo P goals).map (geo ·.1)

variable {geo : Goal → List σ} {P : List σ} {goals : List Goal} {s : σ}

theorem mem_agreed {t : Goal × ℕ} :
    t ∈ agreed geo P goals ↔
      t ∈ goals.zipIdx ∧ ∃ s ∈ P, segmentAgree geo s goals = some t := by
  simp [agreed]

/-- Agree over two goals: the higher if it bears the segment, else the lower if it does. -/
theorem segmentAgree_pair {hi lo : Goal} :
    segmentAgree geo s [hi, lo] =
      if s ∈ geo hi then some (hi, 0) else if s ∈ geo lo then some (lo, 1) else none := by
  by_cases h₁ : s ∈ geo hi <;> by_cases h₂ : s ∈ geo lo <;>
    simp [segmentAgree, segmentProbe, Probe.search, Probe.ofVis, h₁, h₂]

theorem segmentAgree_pair_eq_higher_iff {hi lo : Goal} :
    segmentAgree geo s [hi, lo] = some (hi, 0) ↔ s ∈ geo hi := by
  rw [segmentAgree_pair]; split_ifs <;> simp_all

theorem segmentAgree_pair_eq_lower_iff {hi lo : Goal} :
    segmentAgree geo s [hi, lo] = some (lo, 1) ↔ s ∉ geo hi ∧ s ∈ geo lo := by
  rw [segmentAgree_pair]; split_ifs <;> simp_all

/-- Gluttony over two goals is an inverse configuration: some segment finds the higher goal,
and some segment the higher goal lacks finds the lower. -/
theorem gluttonous_pair_iff {hi lo : Goal} :
    Gluttonous geo P [hi, lo] ↔
      (∃ s ∈ P, s ∈ geo hi) ∧ ∃ s ∈ P, s ∉ geo hi ∧ s ∈ geo lo := by
  constructor
  · rintro ⟨t, ht, u, hu, hne⟩
    obtain ⟨ht₀, s₁, hs₁, h₁⟩ := mem_agreed.1 ht
    obtain ⟨hu₀, s₂, hs₂, h₂⟩ := mem_agreed.1 hu
    simp only [List.zipIdx_cons, List.zipIdx_nil, zero_add, List.mem_cons, List.not_mem_nil,
      or_false] at ht₀ hu₀
    rcases ht₀ with rfl | rfl <;> rcases hu₀ with rfl | rfl
    · exact absurd rfl hne
    · exact ⟨⟨s₁, hs₁, segmentAgree_pair_eq_higher_iff.1 h₁⟩,
        s₂, hs₂, segmentAgree_pair_eq_lower_iff.1 h₂⟩
    · exact ⟨⟨s₂, hs₂, segmentAgree_pair_eq_higher_iff.1 h₂⟩,
        s₁, hs₁, segmentAgree_pair_eq_lower_iff.1 h₁⟩
    · exact absurd rfl hne
  · rintro ⟨⟨s, hs, hsh⟩, s', hs', hs'h, hs'l⟩
    exact ⟨(hi, 0), mem_agreed.2 ⟨by simp, s, hs, segmentAgree_pair_eq_higher_iff.2 hsh⟩,
      (lo, 1), mem_agreed.2 ⟨by simp, s', hs', segmentAgree_pair_eq_lower_iff.2 ⟨hs'h, hs'l⟩⟩,
      by simp⟩

/-- Gluttony arises only in inverse configurations: when the lower goal bears no segment the
higher lacks, no probe gluttons over them. -/
theorem not_gluttonous_of_subset {hi lo : Goal} (h : geo lo ⊆ geo hi) :
    ¬ Gluttonous geo P [hi, lo] :=
  λ hg => let ⟨_, _, _, hsh, hsl⟩ := gluttonous_pair_iff.1 hg; hsh (h hsl)

/-- A probe over at most one goal never gluttons: the repairs of §3.5 and the multiply
agreed-with DP of (86). -/
theorem not_gluttonous_of_length_le_one (h : goals.length ≤ 1) : ¬ Gluttonous geo P goals := by
  rintro ⟨t, ht, u, hu, hne⟩
  have ht' := (mem_agreed.1 ht).1
  have hu' := (mem_agreed.1 hu).1
  match goals, h with
  | [], _ => exact nomatch ht'
  | [_], _ => exact hne ((List.mem_singleton.1 ht').trans (List.mem_singleton.1 hu').symm)

/-- A single-segment probe never gluttons (their fn. 21). -/
theorem not_gluttonous_singleton : ¬ Gluttonous geo [s] goals := by
  rintro ⟨t, ht, u, hu, hne⟩
  simp only [mem_agreed, List.mem_singleton, exists_eq_left] at ht hu
  exact hne (Option.some.inj (ht.2.symm.trans hu.2))

end Agree

/-- Gluttony over a higher goal transfers to a bare 3rd person one: whichever segment reached
the lower goal past the higher reaches it past a lone person node. -/
theorem gluttonous_third_of_gluttonous {P : Probe.Articulation} {hi lo : Goal}
    (hpi : Segment.pi ∈ P) (h : Gluttonous Goal.personSegments P [hi, lo]) :
    Gluttonous Goal.personSegments P [dp .third, lo] := by
  obtain ⟨-, s, hs, hsh, hsl⟩ := gluttonous_pair_iff.1 h
  refine gluttonous_pair_iff.2 ⟨⟨.pi, hpi, pi_mem_personSegments _⟩, s, hs, λ hmem => ?_, hsl⟩
  rw [show (dp .third).personSegments = [.pi] from rfl, List.mem_singleton] at hmem
  exact hsh (hmem ▸ pi_mem_personSegments hi)

/-! ### The Person Case Constraint from probe articulation (§3) -/

/-- The PCC configuration: a clitic-doubling probe over IO > DO, the IO optionally
K-encapsulated. By (30) each agreed-with DP must cliticize, which a gluttonous probe cannot
satisfy, so gluttony is the violation. -/
def PCCViolation (P : Probe.Articulation) (ioOpaque : Bool) (io do_ : Person) : Prop :=
  Gluttonous Goal.personSegments P [{ person := io, encapsulated := ioOpaque }, dp do_]

instance (P : Probe.Articulation) (b : Bool) (io do_ : Person) :
    Decidable (PCCViolation P b io do_) :=
  inferInstanceAs (Decidable (Gluttonous _ _ _))

/-- [uPERS [uPART]], their (39a): the Weak PCC, and the person probe of German and Icelandic T
((55), (79)). -/
abbrev weakProbe : Probe.Articulation := partialProbe

/-- [uPERS [uPART [uSPKR]]], their (39b): the Ultrastrong PCC. -/
abbrev ultrastrongProbe : Probe.Articulation := fullProbeStd

/-- [uPERS [uSPKR]], their (39c): the Me-First PCC, with a missing intermediate segment. -/
def meFirstProbe : Probe.Articulation := [.pi, .speaker]

/-- [uPERS [uPART [uSPKR] [uADDR]]], their fn. 22 (i): the Strong PCC over transparent datives,
and Slovenian's reversible Strong PCC (fn. 26). -/
def branchingProbe : Probe.Articulation := [.pi, .participant, .speaker, .addressee]

/-- The person grid the PCC varieties are stated over. -/
def persons : List Person := [.first, .second, .third]

/-- The Weak PCC (22): *3 > 1/2. -/
theorem weak_pcc : ∀ io ∈ persons, ∀ do_ ∈ persons,
    PCCViolation weakProbe false io do_ ↔ io = .third ∧ do_ ≠ .third := by
  decide

/-- The Strong PCC through datives that expose their person node alone (§3.4.1):
*1/2/3 > 1/2. -/
theorem strong_pcc : ∀ io ∈ persons, ∀ do_ ∈ persons,
    PCCViolation weakProbe true io do_ ↔ do_ ≠ .third := by
  decide

/-- The Ultrastrong PCC (39b): the Weak bans and *2 > 1. -/
theorem ultrastrong_pcc : ∀ io ∈ persons, ∀ do_ ∈ persons,
    PCCViolation ultrastrongProbe false io do_ ↔
      io = .third ∧ do_ ≠ .third ∨ io = .second ∧ do_ = .first := by
  decide

/-- The Me-First probe (39c) bans a 1st person direct object under a 2nd or 3rd person
indirect object; the 1 > 1 cell of table 1 is beyond it. -/
theorem meFirst_pcc : ∀ io ∈ persons, ∀ do_ ∈ persons,
    PCCViolation meFirstProbe false io do_ ↔ do_ = .first ∧ io ≠ .first := by
  decide

/-- The branching probe over transparent datives bans every distinct-person cluster with a
1st or 2nd person direct object. -/
theorem branching_pcc : ∀ io ∈ persons, ∀ do_ ∈ persons,
    PCCViolation branchingProbe false io do_ ↔ do_ ≠ .third ∧ io ≠ do_ := by
  decide

/-- No probe bans a direct or balanced configuration (§3.4.2): a 3rd person direct object
exposes nothing the indirect object lacks. -/
theorem direct_never_banned (P : Probe.Articulation) (b : Bool) (io : Person) :
    ¬ PCCViolation P b io .third :=
  not_gluttonous_of_subset λ s hs => by
    rw [show (dp .third).personSegments = [.pi] from rfl, List.mem_singleton] at hs
    exact hs ▸ pi_mem_personSegments _

/-- A probe rooted in [uPERS] that bans a cluster bans its direct object under a 3rd person
indirect object (§3.4.2): a ban on [PART] > [PART] entails the ban on 3 > [PART]. -/
theorem pccViolation_third_of_pccViolation {P : Probe.Articulation} (hpi : Segment.pi ∈ P)
    {b : Bool} {io do_ : Person} (h : PCCViolation P b io do_) :
    PCCViolation P false .third do_ :=
  gluttonous_third_of_gluttonous hpi h

section Typology

open PCC

/-- The Weak and Strong probes against the descriptive typology of table 1 as
[pancheva-zubizarreta-2018] parametrize it, cell for cell. -/
theorem weak_strong_typology :
    (∀ io ∈ persons, ∀ do_ ∈ persons,
      (PCCViolation weakProbe false io do_ ↔ ¬ IsLicit weakGrammar io do_)) ∧
    ∀ io ∈ persons, ∀ do_ ∈ persons,
      (PCCViolation weakProbe true io do_ ↔ ¬ IsLicit strongGrammar io do_) := by
  decide

/-- The Ultrastrong probe against that parametrization: every cell but 2 > 2, on which table 1
is silent, P-Uniqueness bans it, and the probe, matched throughout by the indirect object,
permits it. -/
theorem ultrastrong_typology :
    (∀ io ∈ persons, ∀ do_ ∈ persons, (io, do_) ≠ (.second, .second) →
      (PCCViolation ultrastrongProbe false io do_ ↔ ¬ IsLicit ultraStrongGrammar io do_)) ∧
    ¬ PCCViolation ultrastrongProbe false .second .second ∧
      ¬ IsLicit ultraStrongGrammar .second .second := by
  decide

/-- The Me-First probe against the typology: every cell but 1 > 1, which table 1 bans and the
probe, whose [uSPKR] the indirect object matches, permits. -/
theorem meFirst_typology :
    (∀ io ∈ persons, ∀ do_ ∈ persons, (io, do_) ≠ (.first, .first) →
      (PCCViolation meFirstProbe false io do_ ↔ ¬ IsLicit meFirstGrammar io do_)) ∧
    ¬ PCCViolation meFirstProbe false .first .first ∧
      ¬ IsLicit meFirstGrammar .first .first := by
  decide

end Typology

/-- The Reverse PCC (44)–(45) and its diagnosis (fn. 26): the branching probe over transparent
goals bans the lower [PART] DP whichever object it is, while a dative exposing its person node
alone cannot be banned when it is the lower one, so Slovenian's Strong PCC is the branching
probe. -/
theorem reverse_pcc :
    Gluttonous Goal.personSegments branchingProbe [dp .third, dp .second] ∧
    Gluttonous Goal.personSegments branchingProbe [dp .second, dp .first] ∧
    Gluttonous Goal.personSegments branchingProbe [dp .first, dp .second] ∧
    ¬ Gluttonous Goal.personSegments weakProbe [dp .second, dat .first] := by
  decide

/-! ### Against licensing (§2.3) -/

/-- The Person Licensing Condition of [preminger-2011], their (9): the condition of
[bejar-rezac-2003], their (6), restricted to clauses with a person probe. -/
def RevisedPLC (cycles : List (List PhiGoal)) (args : List PhiGoal) : Prop :=
  cycles ≠ [] → BejarRezac2003.PLCOk cycles args

instance (cycles : List (List PhiGoal)) (args : List PhiGoal) :
    Decidable (RevisedPLC cycles args) :=
  inferInstanceAs (Decidable (_ → _))

/-- Basque (10), the paper's argument against the original condition: the 3DAT > 1ABS cluster
is gluttonous in a finite clause and has no probe to glutton in a nonfinite one, whereas the
original condition leaves the 1st person object unlicensed in both and needs the restriction of
(9) to exempt the probeless clause. -/
theorem nonfinite_obviation :
    PCCViolation weakProbe true .third .first ∧
    ¬ Gluttonous Goal.personSegments [] [dat .third, dp .first] ∧
    ¬ BejarRezac2003.PLCOk [[dat .third, dp .first].map Goal.toPhiGoal]
        [(dp .first).toPhiGoal] ∧
    ¬ BejarRezac2003.PLCOk [] [(dp .first).toPhiGoal] ∧
    RevisedPLC [] [(dp .first).toPhiGoal] := by
  decide

/-! ### Number and clitic doubling (§3.4.3, §4.1.3) -/

/-- The articulated number probe [uNUM [uPL]] of (23) and (55), paired with a person probe:
the probe-specification hierarchy (40) makes a number probe entail a person one. -/
def numberProbe (P : Probe.Articulation) : List NumberSegment :=
  if P = [] then [] else [.num, .pl]

/-- Clitic doubling removes the doubled DP from later probing (§3.2): what the number probe
sees after the person probe. -/
def afterDoubling (P : Probe.Articulation) (goals : List Goal) : List Goal :=
  (goals.zipIdx.filter (· ∉ agreed Goal.personSegments P goals)).map (·.1)

/-- No Number Case Constraint ((40)–(42)): over two clitic-doubled objects the person probe,
rooted in [uPERS], doubles the higher one, so the number probe sees one goal. -/
theorem no_number_case_constraint {P : Probe.Articulation} (hpi : Segment.pi ∈ P)
    {goals : List Goal} (h : goals.length ≤ 2) :
    ¬ Gluttonous Goal.numberSegments (numberProbe P) (afterDoubling P goals) := by
  apply not_gluttonous_of_length_le_one
  rcases goals with _ | ⟨g, rest⟩
  · simp [afterDoubling]
  · have hg : (g, 0) ∈ agreed Goal.personSegments P (g :: rest) :=
      mem_agreed.2 ⟨List.mem_cons_self, .pi, hpi, by
        simp [segmentAgree, segmentProbe, Probe.search, Probe.ofVis, pi_mem_personSegments]⟩
    simp only [afterDoubling, List.zipIdx_cons, List.filter_cons, hg, not_true_eq_false,
      decide_false, Bool.false_eq_true, ↓reduceIte, List.length_map]
    exact (List.length_filter_le _ _).trans (by simpa using h)

/-- With a third accessible DP, their (43): the number probe sees two goals after doubling and
gluttons over SG > PL. -/
theorem three_goal_number :
    Gluttonous Goal.numberSegments (numberProbe weakProbe)
      (afterDoubling weakProbe [dp .third, dp .third, dpPl .third]) := by
  decide

/-- German copulas double nothing, so the number probe sees both nominatives (67): gluttony in
SG > PL (64) but not in PL > SG. -/
theorem copula_number :
    Gluttonous Goal.numberSegments (numberProbe weakProbe) [dp .third, dpPl .third] ∧
    ¬ Gluttonous Goal.numberSegments (numberProbe weakProbe) [dpPl .third, dp .third] := by
  decide

/-! ### Gluttony and Vocabulary insertion (§4, §5.2) -/

/-- A Vocabulary item for an agreement head. -/
structure VI (σ : Type*) where
  /-- The geometry the item is specified for; `[]` is the elsewhere item. -/
  spec : List σ
  /-- The form inserted. -/
  exponent : String
  deriving DecidableEq, Repr

section Vocabulary

variable {σ : Type*} [DecidableEq σ]

/-- An item applies to a value when its specification is a subset of the value. -/
instance : Rule (VI σ) (List σ) String where
  exponent := VI.exponent
  Applies vi value := vi.spec ⊆ value

instance : DecidableRel (Applies : VI σ → List σ → Prop) := λ vi value =>
  inferInstanceAs (Decidable (vi.spec ⊆ value))

/-- The item a value demands: the most specific applicable one. -/
abbrev demand (vocab : List (VI σ)) (value : List σ) : Option (VI σ) :=
  selectBy (·.spec.length) vocab value

/-- The values a probe carries are resolvable when the items they demand are all the same one
(85); a value that demands no item, as in (88), competes with nothing. -/
def Resolvable (vocab : List (VI σ)) (vals : List (List σ)) : Prop :=
  (vals.filterMap (demand vocab)).Pairwise (· = ·)

instance (vocab : List (VI σ)) (vals : List (List σ)) : Decidable (Resolvable vocab vals) :=
  inferInstanceAs (Decidable (List.Pairwise _ _))

/-- The exponent inserted for resolvable values. -/
def realization (vocab : List (VI σ)) (vals : List (List σ)) : Option String :=
  (vals.filterMap (demand vocab)).head?.map (·.exponent)

end Vocabulary

/-- The paradigms the paper realizes gluttonous probes in, each holding the forms it glosses:
the Icelandic past mediopassive (81), *líka* and *þykja* of (76b) and (78), the German present
and past copula ((51), (52), fn. 32), the Hindi-Urdu present and past copula ((68), (69),
fn. 34) and the Brazilian Portuguese copula (70). -/
inductive Paradigm where
  /-- Icelandic past mediopassive, their (81). -/
  | icelandicMediopassivePast
  /-- Icelandic *líka* 'like' in the past, their (73) and (76b). -/
  | icelandicLikaPast
  /-- Icelandic *þykja* 'think' in the present, their (78). -/
  | icelandicThykjaPresent
  /-- German present copula, their (51)–(52). -/
  | germanPresent
  /-- German past copula, their fn. 32. -/
  | germanPast
  /-- Hindi-Urdu present copula, their (68)–(69). -/
  | hindiPresent
  /-- Hindi-Urdu past copula, their fn. 34. -/
  | hindiPast
  /-- Brazilian Portuguese present copula, their (70). -/
  | portuguesePresent
  deriving DecidableEq, Repr

private def spkr : List Segment := [.pi, .participant, .speaker]

private def addr : List Segment := [.pi, .participant, .addressee]

/-- The person items of a paradigm in the context of the number probe's value (82), undefined
where the paper glosses no forms. -/
def Paradigm.person : Paradigm → Bool → Option (List (VI Segment))
  | .icelandicMediopassivePast, false => some [⟨[], "-ist"⟩]
  | .icelandicMediopassivePast, true => some [⟨[], "-ust"⟩, ⟨spkr, "-umst"⟩]
  | .icelandicLikaPast, false => some [⟨[], "líkaði"⟩, ⟨addr, "líkaðir"⟩]
  | .icelandicThykjaPresent, false => some [⟨[], "þykir"⟩, ⟨spkr, "þyki"⟩]
  | .icelandicThykjaPresent, true => some [⟨[], "þykja"⟩]
  | .germanPresent, false => some [⟨[], "ist"⟩, ⟨spkr, "bin"⟩, ⟨addr, "bist"⟩]
  | .germanPresent, true => some [⟨[], "sind"⟩]
  | .germanPast, false => some [⟨[], "war"⟩]
  | .hindiPresent, false => some [⟨[], "hai"⟩, ⟨spkr, "hũ:"⟩]
  | .hindiPresent, true => some [⟨[], "hẼ"⟩]
  | .hindiPast, false => some [⟨[], "tha:"⟩]
  | .portuguesePresent, false => some [⟨[], "é"⟩, ⟨spkr, "sou"⟩]
  | _, _ => none

/-- The number items of a paradigm, where the paper gives them. -/
def Paradigm.number : Paradigm → List (VI NumberSegment)
  | .germanPresent => [⟨[.num], "ist"⟩, ⟨[.num, .pl], "sind"⟩]
  | .hindiPresent => [⟨[.num], "hai"⟩, ⟨[.num, .pl], "hẼ"⟩]
  | _ => []

/-- The number context of person insertion: the number probe's first value is plural. -/
def pluralContext (P : Probe.Articulation) (goals : List Goal) : Bool :=
  (values Goal.numberSegments (numberProbe P) goals).head?.any λ v =>
    decide (NumberSegment.pl ∈ v)

/-- What becomes of a probe after Agree: cliticization of what it agreed with (30), or
Vocabulary insertion in a paradigm. -/
inductive Aftermath where
  /-- Each agreed-with DP cliticizes onto the probe's host. -/
  | cliticize
  /-- The probe is realized by one item of the paradigm. -/
  | realize (paradigm : Paradigm)
  deriving DecidableEq, Repr

/-- Convergence of a person probe over its goals: no gluttony for a clitic-doubling probe;
resolvable person and number demands, in a glossed number context, for an agreement probe. -/
def Aftermath.Converges : Aftermath → Probe.Articulation → List Goal → Prop
  | .cliticize, P, goals => ¬ Gluttonous Goal.personSegments P goals
  | .realize par, P, goals =>
      (∃ vocab ∈ par.person (pluralContext P goals),
        Resolvable vocab (values Goal.personSegments P goals)) ∧
        Resolvable par.number (values Goal.numberSegments (numberProbe P) goals)

instance (a : Aftermath) (P : Probe.Articulation) (goals : List Goal) :
    Decidable (a.Converges P goals) := by
  cases a <;> simp only [Aftermath.Converges] <;> infer_instance

/-- Icelandic dative-nominative agreement (76)–(85) in the past mediopassive: a 1st person
plural nominative crashes on *-ust* against *-umst* (83), a 2nd person plural one converges on
*-ust* (85), and in the singular, where every cell is *-ist*, the restriction is lifted. -/
theorem icelandic_syncretism :
    ¬ (Aftermath.realize .icelandicMediopassivePast).Converges weakProbe
        [dat .third, dpPl .first] ∧
    (Aftermath.realize .icelandicMediopassivePast).Converges weakProbe
        [dat .third, dpPl .second] ∧
    ∀ p ∈ persons,
      (Aftermath.realize .icelandicMediopassivePast).Converges weakProbe [dat .third, dp p] := by
  decide

/-- Kichean Agent Focus number agreement (88): one item, realizing plural. -/
def kicheanAgentFocus : List (VI NumberSegment) := [⟨[.num, .pl], "-e"⟩]

/-- Two 3rd person goals of the given numbers, the cells of (88). -/
private def kicheanGoals (s o : Bool) : List Goal := [⟨.third, s, false⟩, ⟨.third, o, false⟩]

/-- Omnivorous number (§5.2): with no singular item, a number probe gluttonous over SG > PL
converges on the plural item, and the table of (88) follows. -/
theorem kichean_omnivorous :
    Gluttonous Goal.numberSegments (numberProbe weakProbe) (kicheanGoals false true) ∧
    ∀ s ∈ [false, true], ∀ o ∈ [false, true],
      Resolvable kicheanAgentFocus
        (values Goal.numberSegments (numberProbe weakProbe) (kicheanGoals s o)) ∧
      realization kicheanAgentFocus
          (values Goal.numberSegments (numberProbe weakProbe) (kicheanGoals s o)) =
        if s || o then some "-e" else none := by
  decide

/-! ### The paper's examples -/

/-- A configuration the paper assigns an example. -/
structure Config where
  /-- The person probe, empty when the clause has none. -/
  probe : Probe.Articulation
  /-- The accessible goals from higher to lower. -/
  goals : List Goal
  /-- What follows Agree. -/
  aftermath : Aftermath
  deriving DecidableEq

/-- The configuration converges. -/
def Config.Converges (c : Config) : Prop := c.aftermath.Converges c.probe c.goals

instance (c : Config) : Decidable c.Converges :=
  inferInstanceAs (Decidable (Aftermath.Converges _ _ _))

private def probes : List (String × Probe.Articulation) :=
  [("weak", weakProbe), ("branching", branchingProbe), ("none", [])]

private def paradigms : List (String × Paradigm) :=
  [("icelandicMediopassivePast", .icelandicMediopassivePast),
    ("icelandicLikaPast", .icelandicLikaPast),
    ("icelandicThykjaPresent", .icelandicThykjaPresent), ("germanPresent", .germanPresent),
    ("germanPast", .germanPast), ("hindiPresent", .hindiPresent), ("hindiPast", .hindiPast),
    ("portuguesePresent", .portuguesePresent)]

/-- The goal a row's `higher` or `lower` features describe, absent when shielded from the
probe. -/
private def rowGoal (row : LinguisticExample) (k : String) : Option (List Goal) := do
  let p ← row.parse? k [("1", Person.first), ("2", .second), ("3", .third)]
  return if row.feature? (k ++ "Shielded") = some "yes" then []
    else [⟨p, decide (row.feature? (k ++ "Number") = some "pl"),
      decide (row.feature? (k ++ "Opaque") = some "yes")⟩]

/-- The configuration of a row that the paper analyses. -/
def Config.ofRow (row : LinguisticExample) : Option Config := do
  let aftermath ← match ← row.feature? "aftermath" with
    | "clitic" => some Aftermath.cliticize
    | "agreement" => (row.parse? "paradigm" paradigms).map .realize
    | _ => none
  return ⟨← row.parse? "probe" probes, (← rowGoal row "higher") ++ (← rowGoal row "lower"),
    aftermath⟩

/-- A row the paper judges grammatical or at most marginal: its `?` examples, (77) and fn. 32,
it calls quite acceptable and much improved, while `*?` and `??` carry its star. -/
def Grammatical (row : LinguisticExample) : Prop :=
  row.judgment = .acceptable ∨ row.judgment = .marginal

instance : DecidablePred Grammatical := λ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Every analysed example is grammatical exactly when its configuration converges. -/
theorem analysed_rows : ∀ row ∈ Examples.all, (row.feature? "aftermath").isSome = true →
    ∃ c ∈ Config.ofRow row, (Grammatical row ↔ c.Converges) := by
  decide

end CoonKeine2021
