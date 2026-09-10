import Linglib.Discourse.Gameboard.Defs
import Linglib.Data.Examples.GinzburgCooper2004

/-!
# Ginzburg and Cooper (2004): Clarification, Ellipsis, and the Nature of Contextual Updates in Dialogue

This file formalizes the account of clarification ellipsis of [ginzburg-cooper-2004], on which a
sign carries the contextual parameters its sub-utterances introduce (`LocProp.cparams`,
`LocProp.constits`), grounding an utterance is finding an assignment for all of them (`Grounds`),
and an addressee who cannot updates the context instead by a coercion operation on the sign:
parameter focussing raises the question `?i.p`, the content with the problematic parameter
abstracted (`parameterFocussing`), parameter identification the question what the speaker meant by
the sub-utterance (`parameterIdentification`), both making that sub-utterance salient
(`salUtt_parameterFocussing`), and contextual existential generalization quantifies the parameter
away so that the weaker content can be grounded (`existentialGeneralization`,
`grounds_existentialGeneralization`). Since the operations read the constituents of the sign,
utterances with the same content have different clarification potentials
(`potential_ne_of_constits`): the Hybrid Content Hypothesis, against the purely semantic updates
of dynamic semantics.

The utterance-processing protocol integrates a pending utterance whose parameters the
participant's assignment resolves and otherwise clarifies it (`IS.ground`, `IS.clarify`); after
"Did Bo leave?" the speaker's and the addressee's information states differ in MAX-QUD and
SAL-UTT (`Ex32.differ`), and the speaker comprehends the addressee's fragment by applying the
coercion to her own latest move (`IS.backtrack`, `backtrack_eq_clarify`). A fragment resolves
against the clarification context when it matches the salient sub-utterance in category
(`DeclFrag`); the clausal reading identifies its index with the parameter and so presupposes that
the participants share the sub-utterance's content, the constituent reading does not
(`rows_clausal`, `rows_constituent`), and a fragment of the wrong category has neither
(`rows_parallelism`).

## Implementation notes

* Signs are the substrate's `LocProp`, whose `constits` name the parameter each sub-utterance
  contributes; contents are opaque, so existential generalization takes the binder as an argument
  and the running example writes contents as strings.
* The information state keeps the components that (82) displays: LATEST-MOVE as a sign with its
  assignment, PENDING, MAX-QUD and SAL-UTT; the FACTS update (81) and the grounding conditions
  (80) are not modelled.
* The constituent reading is licensed by categorial parallelism alone, the reformulation without
  utterance anaphora of footnote 55, so that the non-identical fragments of (8) get it; the
  categories of (10) are annotated with the case or verb form the contrasts turn on.

## References

* [ginzburg-cooper-2004]
* [ginzburg-sag-2000]
* [purver-ginzburg-2004]
* [ginzburg-2012]
-/

namespace GinzburgCooper2004

open Discourse.Gameboard Data.Examples

variable {V Cont : Type}

/-! ### Contextual parameters and grounding -/

/-- A contextual assignment: values for parameter indices. -/
abbrev Assignment (V : Type) := List (String × V)

/-- `f` resolves the parameter `c`. -/
def Assignment.Resolves (f : Assignment V) (c : CParam) : Prop := c.index ∈ f.map Prod.fst

instance (f : Assignment V) (c : CParam) : Decidable (f.Resolves c) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-- `f` grounds `σ`: it resolves every contextual parameter of the sign. -/
def Grounds (f : Assignment V) (σ : LocProp Cont) : Prop := ∀ c ∈ σ.cparams, f.Resolves c

instance (f : Assignment V) (σ : LocProp Cont) : Decidable (Grounds f σ) :=
  inferInstanceAs (Decidable (∀ c ∈ _, _))

/-- The parameters of `σ` that `f` leaves unresolved. -/
def unresolved (f : Assignment V) (σ : LocProp Cont) : CParamSet :=
  σ.cparams.filter (λ c => !decide (f.Resolves c))

theorem grounds_iff (f : Assignment V) (σ : LocProp Cont) :
    Grounds f σ ↔ unresolved f σ = [] := by
  simp [Grounds, unresolved, List.filter_eq_nil_iff]

/-! ### Sign coercion -/

/-- The issues a clarification context makes maximal: the content posed, `?i.p` with the
problematic parameter abstracted from the content (focussing), and `?c.Mean(addr, u, c)`, what the
speaker meant by the sub-utterance `u` (identification). -/
inductive Issue (Cont : Type)
  | posed (p : Cont)
  | focus (i : String) (p : Cont)
  | meaning (u : SubUtterance)
  deriving DecidableEq, Repr

/-- The partial specification a coercion operation yields for the clarification: the salient
sub-utterance and the maximal question under discussion. -/
structure Clarification (Cont : Type) where
  salUtt : SubUtterance
  maxQud : Issue Cont
  deriving DecidableEq, Repr

/-- The sub-utterance contributing the contextual parameter `i` of `σ`: the left-hand side the
coercion rules share. -/
def constitOf (σ : LocProp Cont) (i : String) : Option SubUtterance :=
  if i ∈ σ.cparams.map CParam.index then σ.constits.find? (λ u => decide (u.cont = i)) else none

/-- Parameter focussing: MAX-QUD is the content with `i` abstracted, `?i.p`. -/
def parameterFocussing (σ : LocProp Cont) (i : String) : Option (Clarification Cont) :=
  (constitOf σ i).map λ u => ⟨u, .focus i σ.cont⟩

/-- Parameter identification: MAX-QUD asks what the speaker meant by the sub-utterance. -/
def parameterIdentification (σ : LocProp Cont) (i : String) : Option (Clarification Cont) :=
  (constitOf σ i).map λ u => ⟨u, .meaning u⟩

/-- The two operations differ only in MAX-QUD: they make the same sub-utterance salient. -/
theorem salUtt_parameterFocussing (σ : LocProp Cont) (i : String) :
    (parameterFocussing σ i).map (·.salUtt) = (parameterIdentification σ i).map (·.salUtt) := by
  unfold parameterFocussing parameterIdentification
  cases constitOf σ i <;> rfl

/-- Contextual existential generalization: the parameter leaves the sign's parameters and the
content becomes `bind i p`, the content with `i` existentially bound with widest scope. -/
def existentialGeneralization (bind : String → Cont → Cont) (σ : LocProp Cont) (i : String) :
    LocProp Cont :=
  { σ with cparams := σ.cparams.filter (λ c => decide (c.index ≠ i)), cont := bind i σ.cont }

/-- An assignment resolving every parameter but `i` grounds the generalized sign. -/
theorem grounds_existentialGeneralization {bind : String → Cont → Cont} {σ : LocProp Cont}
    {i : String} {f : Assignment V} (h : ∀ c ∈ σ.cparams, c.index ≠ i → f.Resolves c) :
    Grounds f (existentialGeneralization bind σ i) := by
  intro c hc
  simp only [existentialGeneralization, List.mem_filter, decide_eq_true_eq] at hc
  exact h c hc.1 hc.2

/-- The clarification potential of a sign: the clarification contexts its coercion operations make
available, one of each kind per contextual parameter. -/
def potential (σ : LocProp Cont) : List (Clarification Cont) :=
  σ.cparams.filterMap (λ c => parameterFocussing σ c.index) ++
    σ.cparams.filterMap (λ c => parameterIdentification σ c.index)

/-- The Hybrid Content Hypothesis as the paper argues it from (19)–(20): "Jill is the president"
and "She is the president", with the same content, differ in clarification potential, because the
potential reads the sub-utterances. -/
theorem potential_ne_of_constits (p : Cont) :
    ∃ σ σ' : LocProp Cont, σ.cont = σ'.cont ∧ potential σ ≠ potential σ' :=
  ⟨{ phon := "Jill is the president", cat := "S", cont := p, cparams := [⟨"j", "named(Jill)(j)"⟩],
      constits := [⟨"Jill", "NP", "j"⟩] },
    { phon := "She is the president", cat := "S", cont := p, cparams := [⟨"j", "demonstrated(j)"⟩],
      constits := [⟨"She", "NP", "j"⟩] },
    rfl, λ h => by
      have := congrArg (λ l => l.head?.map Clarification.salUtt) h
      change some (⟨"Jill", "NP", "j"⟩ : SubUtterance) = some ⟨"She", "NP", "j"⟩ at this
      exact absurd this (by decide)⟩

/-! ### Integrating utterances in information states -/

/-- The components of a participant's information state that utterance processing reads and
writes: LATEST-MOVE as the sign with its assignment, the utterances PENDING, and the clarification
context MAX-QUD and SAL-UTT. -/
structure IS (V Cont : Type) where
  latestMove : Option (LocProp Cont × Assignment V) := none
  pending : List (LocProp Cont) := []
  maxQud : Option (Issue Cont) := none
  salUtt : Option SubUtterance := none
  deriving DecidableEq

/-- Protocol (84a): the maximal pending utterance, once `f` grounds it, becomes LATEST-MOVE and
its content the issue posed. -/
def IS.ground (s : IS V Cont) (f : Assignment V) : Option (IS V Cont) :=
  match s.pending with
  | σ :: rest =>
    if Grounds f σ then
      some { latestMove := some (σ, f), pending := rest, maxQud := some (.posed σ.cont) }
    else none
  | [] => none

/-- A coercion operation: a partial map from signs and parameters to clarification contexts. -/
abbrev Coercion (Cont : Type) := LocProp Cont → String → Option (Clarification Cont)

/-- Protocol (84c): the maximal pending utterance stays pending, and MAX-QUD and SAL-UTT take the
values the coercion specifies for the parameter `i`. -/
def IS.clarify (s : IS V Cont) (coe : Coercion Cont) (i : String) : Option (IS V Cont) :=
  match s.pending with
  | σ :: _ => (coe σ i).map λ c => { s with maxQud := some c.maxQud, salUtt := some c.salUtt }
  | [] => none

/-- Protocol (84b): the coercion applied to the sign of LATEST-MOVE, by which the speaker of an
utterance comprehends a clarification of it. -/
def IS.backtrack (s : IS V Cont) (coe : Coercion Cont) (i : String) : Option (IS V Cont) :=
  s.latestMove.bind λ m =>
    (coe m.1 i).map λ c => { s with maxQud := some c.maxQud, salUtt := some c.salUtt }

/-- A coercion reads only the sign, so the speaker backtracking over her latest move and the
addressee clarifying the same sign, pending for him, reach the same clarification context. -/
theorem backtrack_eq_clarify {s s' : IS V Cont} {σ : LocProp Cont} (coe : Coercion Cont)
    (i : String) (hs : s.latestMove.map Prod.fst = some σ) (hs' : s'.pending.head? = some σ) :
    (s.backtrack coe i).map (λ t => (t.maxQud, t.salUtt)) =
      (s'.clarify coe i).map (λ t => (t.maxQud, t.salUtt)) := by
  obtain ⟨⟨τ, f⟩, hm, hτ⟩ := Option.map_eq_some_iff.1 hs
  cases hτ
  obtain ⟨ρ, rest, hp⟩ : ∃ ρ rest, s'.pending = ρ :: rest := by
    cases h : s'.pending with
    | nil => simp [h] at hs'
    | cons ρ rest => exact ⟨ρ, rest, rfl⟩
  have hρ : ρ = τ := by simpa [hp] using hs'
  subst hρ
  simp only [IS.backtrack, IS.clarify, hm, hp, Option.bind_some]
  cases coe ρ i <;> rfl

/-! ### The running example, "Did Bo leave?" (32) -/

namespace Ex32

/-- The sub-utterances of (32), each with the parameter or relation it contributes. -/
def did : SubUtterance := ⟨"Did", "V[fin]", "ask"⟩

def bo : SubUtterance := ⟨"Bo", "NP", "b"⟩

def leave : SubUtterance := ⟨"leave", "V[bse]", "leave"⟩

def clause : SubUtterance := ⟨"Did Bo leave", "S", "ask(i,j,?.leave(b,t))"⟩

/-- A's utterance: the root clause's parameters are the referent of "Bo", the time, the speaker,
the addressee and the utterance time (28), (32). -/
def σ : LocProp String :=
  { phon := "did bo leave", cat := "V[+fin]", cont := "ask(i,j,?.leave(b,t))",
    cparams := [⟨"b", "named(Bo)(b)"⟩, ⟨"t", "precedes(t,k)"⟩, ⟨"i", "spkr(i)"⟩,
      ⟨"j", "addr(j)"⟩, ⟨"k", "utt-time(k)"⟩],
    constits := [did, bo, leave, clause] }

/-- A's assignment (82b). -/
def fA : Assignment String :=
  [("b", "B"), ("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1"), ("s", "S0")]

/-- B's assignment (82c), with no value for the referent of "Bo". -/
def fB : Assignment String := [("t", "T0"), ("i", "A"), ("j", "B"), ("k", "T1"), ("s", "S0")]

theorem grounds_fA : Grounds fA σ := by decide

theorem unresolved_fB : unresolved fB σ = [⟨"b", "named(Bo)(b)"⟩] := by decide

/-- (54): focussing on `b` makes "Bo" salient and asks who, named Bo, A is asking about. -/
theorem focussing_b : parameterFocussing σ "b" = some ⟨bo, .focus "b" σ.cont⟩ := by decide

/-- (60): identification asks whom A meant by "Bo". -/
theorem identification_b : parameterIdentification σ "b" = some ⟨bo, .meaning bo⟩ := by decide

/-- (78): with `b` generalized away, B's assignment grounds the weaker content. -/
theorem grounds_fB_generalized (bind : String → String → String) :
    Grounds fB (existentialGeneralization bind σ "b") :=
  grounds_existentialGeneralization (by decide)

/-- The state after A's utterance, pending for both participants. -/
def initial : IS String String := { pending := [σ] }

/-- (82b): A grounds her own utterance. -/
theorem speaker : initial.ground fA =
    some { latestMove := some (σ, fA), maxQud := some (.posed σ.cont) } := by decide

/-- B cannot ground it. -/
theorem addressee_ground : initial.ground fB = none := by decide

/-- (82c): B clarifies by parameter focussing. -/
theorem addressee : initial.clarify parameterFocussing "b" =
    some { pending := [σ], maxQud := some (.focus "b" σ.cont), salUtt := some bo } := by decide

/-- The same utterance leaves the two participants with distinct MAX-QUD and SAL-UTT. -/
theorem differ :
    (initial.ground fA).map (·.maxQud) ≠ (initial.clarify parameterFocussing "b").map (·.maxQud) ∧
    (initial.ground fA).map (·.salUtt) ≠
      (initial.clarify parameterFocussing "b").map (·.salUtt) := by
  decide

/-- (83): backtracking with the same coercion, A reaches B's clarification context and can read
"Bo?" as a clarification of her utterance. -/
theorem backtrack :
    ((initial.ground fA).bind (·.backtrack parameterFocussing "b")).map
        (λ s => (s.maxQud, s.salUtt)) =
      (initial.clarify parameterFocussing "b").map (λ s => (s.maxQud, s.salUtt)) := by
  decide

end Ex32

/-! ### Clarification ellipsis and its readings -/

/-- decl-frag-cl (47): the fragment resolves against the clarification context when it matches the
salient sub-utterance in category. -/
def DeclFrag (c : Clarification Cont) (frag : SubUtterance) : Prop := frag.cat = c.salUtt.cat

instance (c : Clarification Cont) (frag : SubUtterance) : Decidable (DeclFrag c frag) :=
  inferInstanceAs (Decidable (_ = _))

/-- Whether the participants share (a belief about) the content of the sub-utterance. -/
inductive Access
  | shared
  | distinct
  deriving DecidableEq, Repr

/-- The clausal reading: the fragment resolves against a focussing context to the polar question
whether the speaker is asking about this value of the parameter (58), identifying the fragment's
index with the sub-utterance's, which presupposes shared content. -/
def Clausal (σ : LocProp Cont) (i : String) (frag : SubUtterance) (a : Access) : Prop :=
  match parameterFocussing σ i with
  | some c => DeclFrag c frag ∧ a = .shared
  | none => False

/-- The constituent reading: the fragment resolves against an identification context to the
question what the speaker meant (68), presupposing nothing about the value. -/
def Constituent (σ : LocProp Cont) (i : String) (frag : SubUtterance) : Prop :=
  match parameterIdentification σ i with
  | some c => DeclFrag c frag
  | none => False

instance (σ : LocProp Cont) (i : String) (frag : SubUtterance) (a : Access) :
    Decidable (Clausal σ i frag a) := by
  unfold Clausal; split <;> infer_instance

instance (σ : LocProp Cont) (i : String) (frag : SubUtterance) :
    Decidable (Constituent σ i frag) := by
  unfold Constituent; split <;> infer_instance

/-- A dialogue of §1.2: the sub-utterance clarified and the fragment, whether the participants
share the sub-utterance's content, the readings the paper judges available, and the acceptability
of the ellipsis. -/
structure Row where
  antecedent : SubUtterance
  fragment : SubUtterance
  access : Access
  clausal : Option Features.Judgment
  constituent : Option Features.Judgment
  judgment : Features.Judgment
  deriving DecidableEq

def Row.ofExample (ex : LinguisticExample) : Option Row := do
  let ant ← ex.feature? "antecedent"
  let antCat ← ex.feature? "antecedentCat"
  let frag ← ex.feature? "fragment"
  let fragCat ← ex.feature? "fragmentCat"
  let access ← ex.parse? "access" [("shared", .shared), ("distinct", .distinct)]
  pure ⟨⟨ant, antCat, "x"⟩, ⟨frag, fragCat, ""⟩, access, ex.readings.lookup "clausal",
    ex.readings.lookup "constituent", ex.judgment⟩

/-- The sign of the row's first turn as far as the clarification reads it: the sub-utterance
contributing the parameter `x`. -/
def Row.sign (r : Row) : LocProp Unit :=
  { phon := "", cat := "S", cont := (), cparams := [⟨"x", ""⟩], constits := [r.antecedent] }

/-- The nineteen dialogues of (4), (6), (8)–(13). -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- The clausal reading is judged available exactly when the fragment resolves against the
focussing context with shared content. -/
theorem rows_clausal : ∀ r ∈ rows, r.clausal = none ∨
    (r.clausal = some .acceptable ↔ Clausal r.sign "x" r.fragment r.access) := by decide

/-- The constituent reading is judged available exactly when the fragment resolves against the
identification context. -/
theorem rows_constituent : ∀ r ∈ rows, r.constituent = none ∨
    (r.constituent = some .acceptable ↔ Constituent r.sign "x" r.fragment) := by decide

/-- Categorial parallelism (10): the ellipsis is acceptable exactly when some reading resolves
it. -/
theorem rows_parallelism : ∀ r ∈ rows, r.judgment = .acceptable ↔
    (Clausal r.sign "x" r.fragment r.access ∨ Constituent r.sign "x" r.fragment) := by decide

end GinzburgCooper2004
