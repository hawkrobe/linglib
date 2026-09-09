import Linglib.Data.Examples.ErlewineSommerlot2025
import Linglib.Syntax.Minimalist.Linearization.Cyclic

/-!
# Erlewine and Sommerlot (2025): Voice and Extraction in Malayic

This file formalizes [erlewine-sommerlot-2025]'s account of the interaction between voice
morphology and Ā-extraction in Malayic. The verbal domain (§3.1) has two heads, following
[nomoto-2015] and [nomoto-2021]: a lower v that introduces the agent, the active v licensing the
theme it c-commands and the passive v the agent in its specifier, and a higher Voice that heads
a phase and hosts exactly one nominal specifier, with any nonnominal specifiers besides. Every
nominal must be licensed, by v or by the T that attracts it to Spec,TP, so the nominal v leaves
unlicensed moves to Spec,VoiceP and on to the subject position; this yields the active, the
*di-* passive and the bare passive and rules out the mismatched derivations. Vocabulary items
realize Voice and v by linear adjacency at VoiceP Spell-out: in Desa Voice is *me-* before the
active v, optionally, and *di-* before the passive v, null elsewhere, and the active v is *N-*;
in Standard Indonesian and Malay (§4.1) *me-* and *N-* each require the other's adjacency, so
*meN-* appears whole or not at all. Word order is fixed phase by phase by cyclic linearization
([fox-pesetsky-2005], §4.2), null heads pruned, and an overt Voice prefix must be adjacent to the
verb to affix to it. The subject-only restriction follows (§3.2), and so does its exception: a
theme moved to Spec,VoiceP can be Ā-extracted while the agent moves to Spec,TP, in the standard
languages (§4.2), or stays in situ, in Desa (§3.3), but only with Voice null, since an overt
Voice ordered before the agent at VoiceP and after it at CP is an ordering paradox (§4.3); the
agent of a bare passive cannot be extracted across its theme for the same reason (§4.4); PP
extraction is free (§3.2); Jakarta Indonesian's *N-* on Voice blocks object extraction while
Kuching Malay's *N-* on v does not (§5.2); and the polite and familiar registers of Madurese
([jeoung-2017]) differ only in whether Voice has a null allomorph (§5.3).

## Implementation notes

* A derivation records the flavour of v, whether the passive v projects the agent, the nominal
  in Spec,VoiceP, the nominal in Spec,TP if any, what is Ā-extracted if anything, and the
  exponents chosen for Voice and v. Its two Spell-outs are computed from it, moved material
  preceding the remainder of VoiceP at CP, and grammaticality is licensing, the EPP as the
  language sets it, the vocabulary items, local dislocation, and `Consistent`.
* The paper leaves the ungrammaticality of agent extraction with the passive v (§3.3) open and
  offers Ā-anti-locality as one possibility; that ban, on an agent licensed in Spec,vP moving to
  Spec,VoiceP, is adopted.
* Desa relaxes the EPP under nominal Ā-extraction, T licensing a nominal in situ (§3.3); the
  other languages attract a nominal to Spec,TP in every clause.
* Ditransitive, possessor and embedded-argument extraction (§4.4), ellipsis (§4.5) and the
  Kendayan passives (§5.2) are not modelled.
* The examples are `Data.Examples.ErlewineSommerlot2025`.

## References

* [erlewine-sommerlot-2025]
* [nomoto-2015]
* [nomoto-2021]
* [fox-pesetsky-2005]
* [embick-noyer-2001]
* [jeoung-2017]
-/

namespace ErlewineSommerlot2025

open Minimalist.Linearization Data.Examples ErlewineSommerlot2025.Examples

/-- The two flavours of v (§3.1). -/
inductive VFlavor
  | act
  | pass
  deriving DecidableEq, Repr

/-- The nominal arguments of a bivalent verb. -/
inductive Nominal
  | agent
  | theme
  deriving DecidableEq, Repr

/-- The overt terminals a Spell-out orders: a nominal, a nonnominal specifier, an overt Voice,
the verb complex v+V, and the auxiliaries. -/
inductive Term
  | dp (n : Nominal)
  | pp
  | voice
  | verb
  | aux
  deriving DecidableEq, Repr

/-- The exponents of Voice and v across the languages. -/
inductive Exponent
  | me
  | n
  | di
  | e
  deriving DecidableEq, Repr

/-- What is Ā-extracted to Spec,CP. -/
inductive Extracted
  | nominal (n : Nominal)
  | pp
  deriving DecidableEq, Repr

/-- A derivation of a bivalent clause: the flavour of v, whether the passive v projects the
agent, the nominal moved to Spec,VoiceP, the nominal T attracts to Spec,TP if any, what is
Ā-extracted if anything, and the exponents of Voice and v. -/
structure Derivation where
  flavor : VFlavor
  agentProjected : Bool
  spec : Nominal
  subject : Option Nominal
  extracted : Option Extracted
  voiceExp : Option Exponent
  vExp : Option Exponent
  deriving DecidableEq, Repr

namespace Derivation

variable (d : Derivation)

/-- The nominals the clause projects. -/
def nominals : List Nominal := if d.agentProjected then [.agent, .theme] else [.theme]

/-- v licenses a nominal inside VoiceP: the active v the theme, the passive v its projected
agent (§3.1). -/
def LicensedByV : Nominal → Prop
  | .theme => d.flavor = .act
  | .agent => d.flavor = .pass ∧ d.agentProjected = true

instance (n : Nominal) : Decidable (d.LicensedByV n) := by
  cases n <;> unfold LicensedByV <;> infer_instance

/-- The agent stays in Spec,vP at VoiceP Spell-out, between Voice and v. -/
def agentInSitu : Bool := d.agentProjected && d.spec != .agent

/-- The Ā-extracted nominal, if any. -/
def aBar : Option Nominal :=
  match d.extracted with
  | some (.nominal n) => some n
  | _ => none

/-- The terminals moved out of VoiceP by CP Spell-out, in their order there: Spec,CP, then
Spec,TP. -/
def moved : List Term :=
  ((match d.extracted with
    | some (.nominal n) => [Term.dp n]
    | some .pp => [Term.pp]
    | none => []) ++ (d.subject.map Term.dp).toList).dedup

/-- VoiceP Spell-out, null heads pruned: the nonnominal specifier, the nominal specifier, Voice
if overt, the agent if it stays in Spec,vP, v+V, and the theme if it stays in situ. -/
def voicePSpellout : List Term :=
  (if d.extracted = some .pp then [Term.pp] else []) ++ [.dp d.spec] ++
    (if d.voiceExp.isSome then [.voice] else []) ++ (if d.agentInSitu then [.dp .agent] else []) ++
    [.verb] ++ (if d.spec = .theme then [] else [.dp .theme])

/-- CP Spell-out: the moved material, the auxiliaries, and what remains of VoiceP in its
order. -/
def cpSpellout : List Term := d.moved ++ [.aux] ++ d.voicePSpellout.filter (· ∉ d.moved)

/-- An overt Voice prefixes to the verb by local dislocation, which needs adjacency (§3.1). -/
def LocalDislocation : Prop := d.voiceExp.isSome → d.agentInSitu = false

/-- The specifier of VoiceP, the subject and the extracted nominal are arguments the clause
projects, and no agent licensed by the passive v Ā-moves out of Spec,vP (§3.3). -/
def WellFormed : Prop :=
  d.spec ∈ d.nominals ∧ (∀ s ∈ d.subject, s ∈ d.nominals) ∧ (∀ n ∈ d.aBar, n ∈ d.nominals) ∧
    ¬ (d.flavor = .pass ∧ d.spec = .agent)

instance : Decidable d.LocalDislocation := by unfold LocalDislocation; infer_instance
instance : Decidable d.WellFormed := by unfold WellFormed; infer_instance

end Derivation

/-! ### Grammars -/

/-- A language's vocabulary items (§3.1, §4.1, §5): the exponents Voice may take, by the flavour
of v and whether the two heads are linearly adjacent, likewise for v, and whether T licenses a
nominal in situ under nominal Ā-extraction instead of attracting one to Spec,TP. -/
structure Grammar where
  voice : VFlavor → Bool → List (Option Exponent)
  v : VFlavor → Bool → List (Option Exponent)
  inSitu : Bool

/-- Desa (32): *me-* optionally before the active v, *di-* before the passive v, Voice null
elsewhere; the active v is *N-*; T licenses in situ under Ā-extraction (§3.3). -/
def desa : Grammar where
  voice
    | .act, true => [some .me, none]
    | .pass, true => [some .di]
    | _, false => [none]
  v
    | .act, _ => [some .n]
    | .pass, _ => [none]
  inSitu := true

/-- Standard Indonesian and Malay (49): *me-* and *N-* each only next to the other. -/
def standard : Grammar where
  voice
    | .act, true => [some .me]
    | .pass, true => [some .di]
    | _, false => [none]
  v
    | .act, true => [some .n]
    | _, _ => [none]
  inSitu := false

/-- Jakarta Indonesian (§5.2): the optional *N-* realizes Voice. -/
def jakarta : Grammar where
  voice
    | .act, true => [some .n, none]
    | .pass, true => [some .di]
    | _, false => [none]
  v _ _ := [none]
  inSitu := false

/-- Kuching Malay (§5.2): the optional *N-* realizes v, Voice being always null. -/
def kuching : Grammar where
  voice
    | .pass, true => [some .di]
    | _, _ => [none]
  v
    | .act, _ => [some .n, none]
    | .pass, _ => [none]
  inSitu := false

/-- Polite Madurese (82): Voice is *N-* or *e-* next to v and null elsewhere. -/
def politeMadurese : Grammar where
  voice
    | .act, true => [some .n]
    | .pass, true => [some .e]
    | _, false => [none]
  v _ _ := [none]
  inSitu := false

/-- Familiar Madurese (83): Voice is *N-* or *e-* by the flavour of v alone, with no null
allomorph. -/
def familiarMadurese : Grammar where
  voice
    | .act, _ => [some .n]
    | .pass, _ => [some .e]
  v _ _ := [none]
  inSitu := false

namespace Grammar

variable (g : Grammar) (d : Derivation)

/-- T licenses the nominal it attracts, or, where the EPP is relaxed under Ā-extraction, the one
nominal it c-commands that v leaves unlicensed. -/
def TLicenses (n : Nominal) : Prop :=
  match d.subject with
  | some s => n = s
  | none => g.inSitu = true ∧ d.aBar.isSome = true ∧ ¬ d.LicensedByV n

instance (n : Nominal) : Decidable (g.TLicenses d n) := by
  unfold TLicenses; split <;> infer_instance

/-- Every nominal is licensed, by v or by T (§3.1). -/
def Licensed : Prop := ∀ n ∈ d.nominals, d.LicensedByV n ∨ g.TLicenses d n

/-- The EPP: T attracts a nominal, unless the language licenses in situ under nominal
Ā-extraction, when it attracts none. -/
def EPP : Prop :=
  if g.inSitu && d.aBar.isSome then d.subject = none else d.subject.isSome = true

/-- The exponents are those the vocabulary items allow at VoiceP Spell-out. -/
def Vocabulary : Prop :=
  d.voiceExp ∈ g.voice d.flavor (!d.agentInSitu) ∧ d.vExp ∈ g.v d.flavor (!d.agentInSitu)

/-- A derivation is grammatical when it is well formed, licenses every nominal, satisfies the
EPP, realizes the heads as the vocabulary allows, affixes an overt Voice, and linearizes. -/
def Grammatical : Prop :=
  d.WellFormed ∧ g.Licensed d ∧ g.EPP d ∧ g.Vocabulary d ∧ d.LocalDislocation ∧
    Consistent [d.voicePSpellout, d.cpSpellout]

instance : Decidable (g.Licensed d) := by unfold Licensed; infer_instance
instance : Decidable (g.EPP d) := by unfold EPP; infer_instance
instance : Decidable (g.Vocabulary d) := by unfold Vocabulary; infer_instance
instance : Decidable (g.Grammatical d) := by unfold Grammatical; infer_instance

/-- Every derivation of a bivalent clause the grammar's vocabulary can realize. -/
def derivations : List Derivation :=
  [VFlavor.act, .pass].flatMap λ f => [true, false].flatMap λ ag =>
    [Nominal.agent, .theme].flatMap λ sp => [none, some Nominal.agent, some .theme].flatMap λ su =>
      [none, some (Extracted.nominal .agent), some (.nominal .theme), some .pp].flatMap λ ex =>
        let adj := !(ag && sp != .agent)
        (g.voice f adj).flatMap λ ve => (g.v f adj).map λ vx => ⟨f, ag, sp, su, ex, ve, vx⟩

end Grammar

/-! ### Surface forms -/

/-- The prefix on the verb. -/
inductive Prefix
  | meN
  | n
  | di
  | e
  | bare
  deriving DecidableEq, Repr

/-- The prefix the exponents of Voice and v spell out together. -/
def Prefix.ofExponents : Option Exponent → Option Exponent → Option Prefix
  | some .me, some .n => some .meN
  | none, some .n => some .n
  | some .n, none => some .n
  | some .di, none => some .di
  | some .e, none => some .e
  | none, none => some .bare
  | _, _ => none

/-- What a clause shows: what is Ā-extracted, the nominal before the auxiliaries, whether the
agent sits between the auxiliaries and the verb, and the verb's prefix. -/
structure Surface where
  extracted : Option Extracted
  subject : Option Nominal
  lowAgent : Bool
  form : Prefix
  deriving DecidableEq, Repr

/-- The surface form of a derivation, if its exponents spell out a prefix. -/
def Derivation.surface (d : Derivation) : Option Surface :=
  (Prefix.ofExponents d.voiceExp d.vExp).map λ p =>
    ⟨d.extracted, d.subject, d.agentProjected && d.subject != some .agent && d.aBar != some .agent,
      p⟩

/-! ### The rows -/

/-- The grammars as named in the rows. -/
def grammarTable : List (String × Grammar) :=
  [("desa", desa), ("standard", standard), ("jakarta", jakarta), ("kuching", kuching),
    ("politeMadurese", politeMadurese), ("familiarMadurese", familiarMadurese)]

/-- The extracted phrases as named in the rows. -/
def extractedTable : List (String × Option Extracted) :=
  [("none", none), ("agent", some (.nominal .agent)), ("theme", some (.nominal .theme)),
    ("pp", some .pp)]

/-- The subjects as named in the rows. -/
def subjectTable : List (String × Option Nominal) :=
  [("none", none), ("agent", some .agent), ("theme", some .theme)]

/-- Whether the agent is low, as named in the rows. -/
def lowAgentTable : List (String × Bool) := [("yes", true), ("no", false)]

/-- The prefixes as named in the rows. -/
def prefixTable : List (String × Prefix) :=
  [("meN", .meN), ("N", .n), ("di", .di), ("e", .e), ("bare", .bare)]

/-- A row: the grammar, the surface form, and the judgment. -/
structure Row where
  grammar : Grammar
  surface : Surface
  judgment : Features.Judgment

/-- A row from an example. -/
def Row.ofExample (ex : LinguisticExample) : Option Row := do
  pure ⟨← ex.parse? "grammar" grammarTable,
    ⟨← ex.parse? "extracted" extractedTable, ← ex.parse? "subject" subjectTable,
      ← ex.parse? "lowAgent" lowAgentTable, ← ex.parse? "prefix" prefixTable⟩,
    ex.judgment⟩

theorem row_ofExample_isSome : ∀ ex ∈ Examples.all, (Row.ofExample ex).isSome := by decide

/-- The rows of the six grammars. -/
def rows : List Row := Examples.all.filterMap Row.ofExample

/-- Every row: the surface form is grammatical exactly when some derivation the grammar
generates has it. -/
theorem rows_grammatical :
    ∀ r ∈ rows, r.judgment = .acceptable ↔
      ∃ d ∈ r.grammar.derivations, d.surface = some r.surface ∧ r.grammar.Grammatical d := by
  decide +kernel

/-! ### The ordering paradoxes -/

/-- (57): with Voice overt and the agent left in Spec,vP at VoiceP Spell-out, the agent's later
movement to Spec,TP orders it before Voice at CP, against VoiceP; the derivation cannot
linearize, whatever else it contains. -/
theorem overt_voice_paradox (d : Derivation) (hv : d.voiceExp.isSome = true)
    (hi : d.agentInSitu = true) (hs : d.subject = some .agent) :
    ¬ Consistent [d.voicePSpellout, d.cpSpellout] := by
  have hvP : Term.voice ∈ d.voicePSpellout := by simp [Derivation.voicePSpellout, hv]
  have hnot : Term.voice ∉ d.moved := by
    unfold Derivation.moved
    rcases d.extracted with _ | ⟨_⟩ | _ <;> rcases d.subject with _ | _ <;> simp
  have hagent : Term.dp .agent ∈ d.moved := by simp [Derivation.moved, hs]
  refine not_consistent_of_pair (p := d.voicePSpellout) (q := d.cpSpellout) (a := .voice)
    (b := .dp .agent) List.mem_cons_self (by simp) ?_ ?_
  · unfold Derivation.voicePSpellout
    rw [if_pos hv, if_pos hi]
    exact (((List.sublist_append_right _ [Term.voice]).append_right [Term.dp .agent]).trans
      (List.sublist_append_left _ [Term.verb])).trans (List.sublist_append_left _ _)
  · unfold Derivation.cpSpellout
    exact List.Sublist.append
      ((List.singleton_sublist.mpr hagent).trans (List.sublist_append_left _ [Term.aux]))
      (List.singleton_sublist.mpr (List.mem_filter.mpr ⟨hvP, by simpa using hnot⟩))

/-- (60): the agent of a bare passive cannot be Ā-extracted, since the theme precedes it at
VoiceP Spell-out but would follow it at CP. -/
theorem bare_passive_agent_paradox (d : Derivation) (ha : d.agentProjected = true)
    (hsp : d.spec = .theme) (he : d.extracted = some (.nominal .agent))
    (hs : d.subject = some .theme) : ¬ Consistent [d.voicePSpellout, d.cpSpellout] := by
  have hi : d.agentInSitu = true := by simp [Derivation.agentInSitu, ha, hsp]
  have hm : d.moved = [.dp .agent, .dp .theme] := by
    unfold Derivation.moved; rw [he, hs]; decide
  refine not_consistent_of_pair (p := d.voicePSpellout) (q := d.cpSpellout) (a := .dp .theme)
    (b := .dp .agent) List.mem_cons_self (by simp) ?_ ?_
  · unfold Derivation.voicePSpellout
    rw [if_pos hi, if_pos hsp, hsp]
    exact ((((List.sublist_append_right _ [Term.dp .theme]).trans
      (List.sublist_append_left _ _)).append_right [Term.dp .agent]).trans
      (List.sublist_append_left _ [Term.verb])).trans (List.sublist_append_left _ _)
  · unfold Derivation.cpSpellout
    rw [hm]
    exact (List.sublist_append_left _ [Term.aux]).trans (List.sublist_append_left _ _)

/-! ### The predictions of §5 -/

/-- §5.2: with *N-* on v, object extraction crosses an *N-* verb, as in Kuching Malay; with *N-*
on Voice it cannot, as in Jakarta Indonesian. -/
theorem n_on_v_allows_object_extraction :
    (∃ d ∈ kuching.derivations,
        d.surface = some ⟨some (.nominal .theme), some .agent, false, .n⟩ ∧
          kuching.Grammatical d) ∧
      ¬ ∃ d ∈ jakarta.derivations,
        d.surface = some ⟨some (.nominal .theme), some .agent, false, .n⟩ ∧
          jakarta.Grammatical d := by
  decide +kernel

/-- §5.3: the registers of Madurese differ in the bare passive and object extraction alone,
both of which need a null Voice. -/
theorem madurese_registers :
    (∃ d ∈ politeMadurese.derivations,
        d.surface = some ⟨none, some .theme, true, .bare⟩ ∧ politeMadurese.Grammatical d) ∧
      (∃ d ∈ politeMadurese.derivations,
        d.surface = some ⟨some (.nominal .theme), some .agent, false, .bare⟩ ∧
          politeMadurese.Grammatical d) ∧
      (¬ ∃ d ∈ familiarMadurese.derivations,
        d.surface = some ⟨none, some .theme, true, .bare⟩ ∧ familiarMadurese.Grammatical d) ∧
      ¬ ∃ d ∈ familiarMadurese.derivations,
        d.surface = some ⟨some (.nominal .theme), some .agent, false, .bare⟩ ∧
          familiarMadurese.Grammatical d := by
  decide +kernel

end ErlewineSommerlot2025
