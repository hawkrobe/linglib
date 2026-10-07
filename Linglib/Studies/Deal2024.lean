module

public import Linglib.Syntax.Agreement.PersonCaseConstraint
public import Linglib.Syntax.Minimalist.Probe.Basic
public import Linglib.Syntax.Minimalist.Phi.PersonSegment
public import Linglib.Studies.CoonKeine2021
public import Linglib.Studies.Haspelmath2021
public import Linglib.Syntax.Clause.Scenario
public import Linglib.Syntax.Person.Class
public import Linglib.Data.Examples.Deal2024

/-!
# Deal (2024): Interaction, Satisfaction, and the PCC

The interaction–satisfaction theory of the Person Case Constraint of [deal-2024]. A probe is
specified by an interaction condition, the features it copies from a goal, and a satisfaction
condition, the feature that halts its search, with no uninterpretable features anywhere.
Cliticization of both objects requires Agree with both, and the probe meets the direct object
first, so a direct object that satisfies the probe bleeds Agree with the indirect object:
satisfaction by [PART] gives the strong PCC, by [SPKR] the me-first PCC, and an insatiable probe
no PCC. Dynamic interaction lets a feature copied from the direct object narrow the interaction
condition, so that the indirect object must bear it too: [PART] interacting dynamically on an
insatiable probe gives the weak PCC and on a [SPKR]-satisfied probe the strictly descending PCC.
The probe's walk over the goal sequence is run, and the paper's typology tables, (53) over [PART]
and [SPKR] and (57) over [ADDR] as well, are derived from the runs by classifying each grammar's
licit region over the six cells of table (1) against the descriptive statements (2), you-first
and A-descending. A probe that meets the indirect object first yields the reverse PCC of section
6.2. The clitic combinations of French, Bulgarian, Italian, Spanish, Shapsug Adyghe and Slovenian
are rows, and on the six cells the four varieties coincide with the P-Constraint grammars of
[pancheva-zubizarreta-2018] and the gluttony probes of [coon-keine-2021], the competitors of
section 7. The cells of table (1) are scenarios (`Clause.Scenario`), and read as an argument
coding, the clitic cluster where licit and the longer repair where not (`PCCType.coding`), each
variety is checked against [haspelmath-2021]'s scenario universal, which section 7.1 there claims
the person-case constraint instantiates: under 1 > 2 > 3 the strong, weak, me-first and strictly
descending varieties obey it and the addressee-first ones do not, under 2 > 1 > 3 the reverse
(`universal5_prominence`, `universal5_addressee`); every variety allows the participant-over-
third cells, the person-role universal 9b (`participant_third_licit`); the strong variety is
Modern Greek's T coding (`strong_iff_greekT`), and the two descending statements are the
condition that the scenario be downstream under their rankings
(`strictlyDescending_iff_downstream`, `aDescending_iff_downstream`).

## Implementation notes

The features of the geometry (7) are the person segments of `Minimalist.PersonSegment`, [φ] its
root `π`, [PART] `participant`, [SPKR] `speaker` and [ADDR] `addressee`, so a second person and an
inclusive first person bear [ADDR]. The interaction condition is the set of features copied so
far, a goal being visible when it bears them all, which is the set conception the paper's
footnote 10 allows; the paper's single interaction feature is the most specific one copied.
Table (1) has no reflexive cells, so the classification of grammars ranges over its six cells;
the mechanism's verdicts on reflexive combinations are not stated.

## References

* [deal-2024]
* [haspelmath-2021]
* [pancheva-zubizarreta-2018]
* [coon-keine-2021]
-/

@[expose] public section

namespace Deal2024

open Minimalist PersonSegment

/-! ### Probes and their runs -/

/-- A grammar fixes the satisfaction condition, none for an insatiable probe, and the features
that interact dynamically, copied into the interaction condition when a goal bears them. -/
structure Grammar where
  satisfaction : Option PersonSegment
  dynamic : Finset PersonSegment
  deriving DecidableEq, Fintype

/-- The state of a probe during its walk over the goals records the interaction condition,
whether the probe has been satisfied, and the positions of the goals it has interacted with. -/
structure ProbeState where
  int : Finset PersonSegment
  satisfied : Bool
  agreed : List ℕ
  deriving DecidableEq

/-- The initial state is [INT:φ], unsatisfied, with nothing agreed. -/
def ProbeState.initial : ProbeState := ⟨{.pi}, false, []⟩

/-- The probe a state denotes sees a goal when the goal bears every feature of the interaction
condition. -/
def ProbeState.probe (st : ProbeState) : Probe Person :=
  .relativized fun p ↦ decide (st.int ⊆ spec p)

/-- In one step of the walk a satisfied probe is inert, (8b); otherwise a visible goal is
interacted with, its position recorded, the goal's dynamic features are copied into the
interaction condition, and the probe is satisfied when the goal bears the satisfaction
feature, (44) and (45). -/
def step (g : Grammar) (st : ProbeState) (t : Person × ℕ) : ProbeState :=
  if st.satisfied || !st.probe.sat t.1 then st
  else
    { int := st.int ∪ g.dynamic ∩ spec t.1
      satisfied := g.satisfaction.any (· ∈ spec t.1)
      agreed := st.agreed ++ [t.2] }

/-- The run of a probe over a goal sequence in interaction order. -/
def runProbe (g : Grammar) (goals : List Person) : ProbeState :=
  goals.zipIdx.foldl (step g) .initial

/-- Dynamic interaction only narrows: the interaction condition only grows along a run. -/
theorem int_subset_step (g : Grammar) (st : ProbeState) (t : Person × ℕ) :
    st.int ⊆ (step g st t).int := by
  unfold step
  split
  · exact subset_rfl
  · exact Finset.subset_union_left

/-- The probe a later state denotes sees no more than an earlier one. -/
theorem probe_sat_antitone (g : Grammar) (st : ProbeState) (t : Person × ℕ) (a : Person)
    (h : (step g st t).probe.sat a = true) : st.probe.sat a = true := by
  simp only [ProbeState.probe, Probe.relativized, decide_eq_true_eq] at h ⊢
  exact (int_subset_step g st t).trans h

/-- A satisfied probe is inert. -/
theorem step_of_satisfied (g : Grammar) (st : ProbeState) (t : Person × ℕ)
    (h : st.satisfied = true) : step g st t = st := by
  simp [step, h]

/-- A clitic combination ⟨IO, DO⟩ is licit when the probe, meeting the direct object first,
interacts with both objects, section 3.1; the reverse PCC of section 6.2, where the probe meets
the indirect object first, is licitness of the swapped pair. -/
def Licit (g : Grammar) (io do_ : Person) : Prop := (runProbe g [do_, io]).agreed = [0, 1]

instance (g : Grammar) (io do_ : Person) : Decidable (Licit g io do_) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### The grammars -/

/-- The strong PCC is the probe [INT:φ, SAT:PART], (15). -/
def strong : Grammar := ⟨some .participant, ∅⟩

/-- The me-first PCC is the probe [INT:φ, SAT:SPKR], (33). -/
def meFirst : Grammar := ⟨some .speaker, ∅⟩

/-- The insatiable probe [INT:φ, SAT:-] of Ubykh and Moro derives no PCC. -/
def noPCC : Grammar := ⟨none, ∅⟩

/-- The weak PCC is an insatiable probe with [PART] interacting dynamically, (38). -/
def weak : Grammar := ⟨none, {.participant}⟩

/-- The strictly descending PCC is [SAT:SPKR] with [PART] interacting dynamically, (50). -/
def strictlyDescending : Grammar := ⟨some .speaker, {.participant}⟩

/-- The you-first PCC is [SAT:ADDR], section 6.1. -/
def youFirst : Grammar := ⟨some .addressee, ∅⟩

/-- The A-descending PCC is [SAT:ADDR] with [PART] interacting dynamically, section 6.1. -/
def aDescending : Grammar := ⟨some .addressee, {.participant}⟩

/-! ### The typology -/

open Clause (Scenario)

/-- The six cells of table (1), the IO–DO combinations as scenarios. -/
def cells : List (Scenario Person) :=
  [⟨.first, .third⟩, ⟨.first, .second⟩, ⟨.second, .first⟩, ⟨.second, .third⟩,
    ⟨.third, .first⟩, ⟨.third, .second⟩]

/-- The rank of a person on the hierarchy 2 > 1 > 3 of the A-descending PCC. -/
def addresseeRank : Person → ℕ
  | .second => 2
  | .first | .firstInclusive | .firstExclusive => 1
  | .third => 0

/-- The PCC varieties are the four of table (1), the two the feature [ADDR] adds, and none. -/
inductive PCCType where
  | strong
  | weak
  | meFirst
  | strictlyDescending
  | youFirst
  | aDescending
  | none
  deriving DecidableEq, Repr, Fintype

/-- The descriptive statements of (2) and section 6.1, one per variety, say that the direct
object must be third person; that if there is a third person, the direct object must be third
person; that if there is a first person, it must be the indirect object; that the indirect object
must outrank the direct object on 1 > 2 > 3; that if there is a second person, it must be the
indirect object; that the indirect object must outrank the direct object on 2 > 1 > 3; and
nothing. -/
def PCCType.Licit : PCCType → Person → Person → Prop
  | .strong, _, do_ => ¬ do_.IsSAP
  | .weak, io, do_ => ¬ io.IsSAP → ¬ do_.IsSAP
  | .meFirst, _, do_ => ¬ do_.IncludesSpeaker
  | .strictlyDescending, io, do_ => do_.prominence < io.prominence
  | .youFirst, _, do_ => addressee ∉ spec do_
  | .aDescending, io, do_ => addresseeRank do_ < addresseeRank io
  | .none, _, _ => True

instance : (t : PCCType) → (io do_ : Person) → Decidable (t.Licit io do_)
  | .strong, _, _ => inferInstanceAs (Decidable (¬ _))
  | .weak, _, _ => inferInstanceAs (Decidable (_ → _))
  | .meFirst, _, _ => inferInstanceAs (Decidable (¬ _))
  | .strictlyDescending, _, _ => inferInstanceAs (Decidable (_ < _))
  | .youFirst, _, _ => inferInstanceAs (Decidable (¬ _))
  | .aDescending, _, _ => inferInstanceAs (Decidable (_ < _))
  | .none, _, _ => inferInstanceAs (Decidable True)

/-- The strictly descending PCC holds of an IO–DO combination exactly when the scenario is
downstream on 1 > 2 > 3. -/
theorem strictlyDescending_iff_downstream (io do_ : Person) :
    PCCType.Licit .strictlyDescending io do_ ↔
      (Clause.Scenario.mk io do_).kindBy Person.prominence = .downstream :=
  (Clause.Scenario.kindBy_eq_downstream_iff (s := ⟨io, do_⟩) _).symm

/-- The A-descending PCC holds exactly when the scenario is downstream on 2 > 1 > 3. -/
theorem aDescending_iff_downstream (io do_ : Person) :
    PCCType.Licit .aDescending io do_ ↔
      (Clause.Scenario.mk io do_).kindBy addresseeRank = .downstream :=
  (Clause.Scenario.kindBy_eq_downstream_iff (s := ⟨io, do_⟩) _).symm

/-- A variety codes a combination as the clitic cluster where it is licit and as the longer
repair where it is not. -/
def PCCType.coding (t : PCCType) (s : Scenario Person) : ℕ :=
  if t.Licit s.high s.low then 0 else 1

/-- Under a person ranking, a cell of table (1) is more usual than another when its kind is
higher. -/
def MoreUsualOn {β : Type*} [LinearOrder β] (rank : Person → β) (s t : Scenario Person) : Prop :=
  s ∈ cells ∧ t ∈ cells ∧ t.kindBy rank < s.kindBy rank

instance {β : Type*} [LinearOrder β] (rank : Person → β) (s t : Scenario Person) :
    Decidable (MoreUsualOn rank s t) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Under the person scale 1 > 2 > 3, a variety never bans a more usual combination of table (1)
while allowing a less usual one exactly when it is the strong, weak, me-first or strictly
descending PCC, as section 7.1 of [haspelmath-2021] requires. The addressee-first varieties ban
the downstream `1 > 2`. -/
theorem universal5_prominence (t : PCCType) :
    Haspelmath2021.RoleReferenceUniversal (MoreUsualOn Person.prominence) t.coding ↔
      t ∈ [PCCType.strong, .weak, .meFirst, .strictlyDescending, .none] := by
  revert t; decide +kernel

/-- Under the ranking 2 > 1 > 3 it is the strong, weak, you-first and A-descending varieties
that obey the scenario universal; me-first and strictly descending ban the then-downstream
`2 > 1`. -/
theorem universal5_addressee (t : PCCType) :
    Haspelmath2021.RoleReferenceUniversal (MoreUsualOn addresseeRank) t.coding ↔
      t ∈ [PCCType.strong, .weak, .youFirst, .aDescending, .none] := by
  revert t; decide +kernel

/-- Every variety allows a participant IO with a third-person DO, the `⟨⊤, ⊥⟩` of the binary
person scale, as the person-role universal 9b of [haspelmath-2021] requires. -/
theorem participant_third_licit (t : PCCType) (io : Person) (h : io.IsSAP) :
    t.Licit io .third := by
  revert h; cases t <;> cases io <;> decide

/-- The strong PCC is Modern Greek's T coding in [haspelmath-2021]'s (45): the clitic is
available exactly where the DO is aliophoric. -/
theorem strong_iff_greekT (io do_ : Person) :
    PCCType.Licit .strong io do_ ↔
      Haspelmath2021.greekT ((Scenario.mk io do_).map Person.toClass) = 0 := by
  revert io do_; decide

def PCCType.all : List PCCType :=
  [.strong, .weak, .meFirst, .strictlyDescending, .youFirst, .aDescending, .none]

/-- The variety a grammar derives is the one whose statement it matches on the six cells. -/
def Grammar.pattern (g : Grammar) : Option PCCType :=
  PCCType.all.find? fun t ↦ decide (∀ c ∈ cells, Licit g c.high c.low ↔ t.Licit c.high c.low)

/-- Table (57), the typology by satisfaction condition and dynamic interaction features, with
table (53) as its rows and columns without [ADDR]; a probe satisfied by [φ] Agrees with the
direct object alone and derives no variety, and dynamic [φ] changes nothing. -/
def table57 (g : Grammar) : Option PCCType :=
  match g.satisfaction with
  | some .pi => none
  | some .participant => some .strong
  | some .speaker =>
      some (if .addressee ∈ g.dynamic then .strong
        else if .participant ∈ g.dynamic then .strictlyDescending else .meFirst)
  | some .addressee =>
      some (if .speaker ∈ g.dynamic then .strong
        else if .participant ∈ g.dynamic then .aDescending else .youFirst)
  | none =>
      some (if .speaker ∈ g.dynamic ∧ .addressee ∈ g.dynamic then .strong
        else if .participant ∈ g.dynamic ∧ .speaker ∈ g.dynamic then .strictlyDescending
        else if .participant ∈ g.dynamic ∧ .addressee ∈ g.dynamic then .aDescending
        else if .participant ∈ g.dynamic then .weak
        else if .speaker ∈ g.dynamic then .meFirst
        else if .addressee ∈ g.dynamic then .youFirst
        else .none)

/-- The runs derive the tables: every grammar derives the variety table (57) gives it. -/
theorem typology (g : Grammar) : g.pattern = table57 g := by
  revert g
  decide +kernel

/-- Satisfaction by [PART] absorbs dynamic interaction: a direct object bearing a dynamic
feature bears [PART] and satisfies the probe first, so every column-one grammar of the table
licenses exactly what the strong PCC does, for every pair of persons. -/
theorem licit_of_sat_part (d : Finset PersonSegment) (io do_ : Person) :
    Licit ⟨some .participant, d⟩ io do_ ↔ Licit strong io do_ := by
  revert d io do_
  decide +kernel

/-- Off the diagonal, for objects of distinct person, the strictly descending PCC requires the
indirect object to outrank the direct object on 1 > 2 > 3. -/
theorem sd_off_diagonal_iff_outranks (io do_ : Person)
    (h : io.prominence ≠ do_.prominence) :
    Licit strictlyDescending io do_ ↔ do_.prominence < io.prominence := by
  revert io do_
  decide +kernel

/-! ### The competitors (section 7) -/

/-- On the six cells of table (1) the four varieties coincide with the P-Constraint grammars of
[pancheva-zubizarreta-2018], strictly descending with ultra-strong. -/
theorem agrees_with_pConstraint :
    ∀ c ∈ cells,
      (Licit strong c.high c.low ↔ PCC.IsLicit PCC.strongGrammar c.high c.low) ∧
        (Licit weak c.high c.low ↔ PCC.IsLicit PCC.weakGrammar c.high c.low) ∧
        (Licit meFirst c.high c.low ↔ PCC.IsLicit PCC.meFirstGrammar c.high c.low) ∧
        (Licit strictlyDescending c.high c.low ↔
          PCC.IsLicit PCC.ultraStrongGrammar c.high c.low) := by
  decide +kernel

/-- On the six cells the four varieties coincide with the gluttony probes of
[coon-keine-2021]: a probe that stops too early and one that agrees too much draw the same
lines there. -/
theorem agrees_with_gluttony :
    ∀ c ∈ cells,
      (Licit strong c.high c.low ↔
          ¬ CoonKeine2021.PCCViolation CoonKeine2021.weakProbe true c.high c.low) ∧
        (Licit weak c.high c.low ↔
          ¬ CoonKeine2021.PCCViolation CoonKeine2021.weakProbe false c.high c.low) ∧
        (Licit meFirst c.high c.low ↔
          ¬ CoonKeine2021.PCCViolation CoonKeine2021.meFirstProbe false c.high c.low) ∧
        (Licit strictlyDescending c.high c.low ↔
          ¬ CoonKeine2021.PCCViolation CoonKeine2021.ultrastrongProbe false c.high c.low) := by
  decide +kernel

/-! ### The rows -/

def personOf (e : Datum) (key : String) : Option Person :=
  match e.feature? key with
  | some "1" => some .first
  | some "2" => some .second
  | some "3" => some .third
  | _ => none

/-- The grammars of a row's language are listed by its pattern, Slovenian speakers having a strong
or a weak PCC. -/
def grammarsOf (e : Datum) : List Grammar :=
  match e.feature? "pattern" with
  | some "strong" => [strong]
  | some "weak" => [weak]
  | some "meFirst" => [meFirst]
  | some "strictlyDescending" => [strictlyDescending]
  | some "strongOrWeak" => [strong, weak]
  | _ => []

/-- Every clitic combination of the rows is grammatical exactly when the language's grammar
licenses it, the probe meeting the indirect object first in the reverse-PCC rows of Shapsug
Adyghe and of Slovenian with the direct object clitic first. -/
theorem rows :
    ∀ e ∈ Examples.all, ∀ g ∈ grammarsOf e, ∀ io ∈ personOf e "io", ∀ do_ ∈ personOf e "do",
      (e.judgment = .acceptable ↔
        if e.feature? "preference" = some "io" then Licit g do_ io else Licit g io do_) := by
  decide +kernel

end Deal2024
