import Linglib.Fragments.Uyghur.Complementizers
import Linglib.Data.Examples.Major2024

/-!
# Major (2024): Re-analyzing *say* Complementation

This file formalizes [major-2024]'s analysis of Uyghur *dep* clauses. They look like
complementizer-headed complements but are converbial adjunct clauses headed by the verb *de*
'say' with the converb *-(I)p*, merging at VP or TP; because the linker contains the verb,
main-verb properties of *de-* persist inside *dep* clauses, and because it is a converb,
*dep* clauses are barred from argument positions. The merge behaviour is read off the
fragment entries' recorded morphology (`mergeMode`, `licensedIn`), and the ban is derived
for any analysis of that shape (`SayConverbAnalysis.argument_ban`, `dep_never_argument`),
with the participial complements as the contrast (`participial_licensed_iff_argument`). The
Washo parallel is the modifier analysis of non-factive embedding of [bochnak-hanink-2021].

## Implementation notes

The case-theoretic consequences for Sakha *dien* and the accusative subjects of
[baker-vinokurova-2010] are not represented; the examples are rows of
`Data/Examples/Major2024.json`.

## References

* [major-2024]
* [bochnak-hanink-2021]
* [baker-vinokurova-2010]
-/

namespace Major2024

open Morphology (Morph)

/-! ### Merge modes read off the morphology (§2)

Converbial -(I)p clauses adjoin at two heights (4): VP-level
-(I)p is a manner modifier interpreted under matrix aspect (his
10–13), answers *qandaq* 'how' (15)–(16), and sits below the matrix
accusative position (19); TP-level -(I)p precedes the whole matrix
clause (29), tolerates aspect and voice mismatches (12), (30),
and merges at (at least) TP (31). Dep clauses replicate both
profiles (37)–(38), (52)–(56). -/

/-- Structural positions at issue for an embedded clause: the two
converb adjunction heights (4) and the two argument positions the
paper tests — complement of V (59a), (61a), (73) and grammatical
subject (49). -/
inductive ClausePosition where
  | complementOfV
  | subject
  | vpAdjunct
  | tpAdjunct
  deriving DecidableEq, Fintype, Repr

/-- Argument positions: those saturating a θ-position of the matrix
predicate. -/
def ClausePosition.isArgument : ClausePosition → Prop
  | .complementOfV | .subject => True
  | .vpAdjunct | .tpAdjunct => False

instance : DecidablePred ClausePosition.isArgument
  | .complementOfV => isTrue trivial
  | .subject       => isTrue trivial
  | .vpAdjunct     => isFalse id
  | .tpAdjunct     => isFalse id

/-- How a clause-forming morpheme merges the clause it heads: a
converb builds an adjunct to a verbal projection (4); a
nominalizer builds a case-bearing nominal that saturates an argument
position (49a), (59a). -/
inductive MergeMode where
  | converbAdjunction
  | nominalArgument
  deriving DecidableEq, Repr

/-- Converbial adjuncts modify, never saturate ("dep clauses are never
internal arguments", §3.2; subject ban (49b); nominalized clauses
saturate. Oblique case-marked participial adjuncts (50b) go
through case morphology, outside this position set. -/
def MergeMode.admits : MergeMode → ClausePosition → Prop
  | .converbAdjunction, pos => ¬ pos.isArgument
  | .nominalArgument,   pos => pos.isArgument

instance (m : MergeMode) (pos : ClausePosition) : Decidable (m.admits pos) :=
  match m with
  | .converbAdjunction => inferInstanceAs (Decidable ¬pos.isArgument)
  | .nominalArgument   => inferInstanceAs (Decidable pos.isArgument)

/-- The merge mode of a clause-forming morpheme, read off its recorded
morphology — the paper's "morphology at face value" (§1): a converbial
suffix (`verbForm = .Conv`) builds adjuncts; a nominalizing
clause-typer (`coding = .nominalized`) builds arguments. `none`
for morphemes heading no clause of their own. -/
def mergeMode (c : Complementizer) : Option MergeMode :=
  if c.verbForm = some .Conv then some .converbAdjunction
  else if c.coding = some .nominalized then some .nominalArgument
  else none

/-- A clause headed by `c` is licensed in `pos` iff `c`'s merge mode
admits it. No matrix-verb parameter: dep clauses appear regardless of
matrix transitivity (44a) *söz qil-* vs. unaccusative 44b *söz
bol-*) and with unaccusative 'be surprised' (50c). -/
def licensedIn (c : Complementizer) (pos : ClausePosition) : Prop :=
  match mergeMode c with
  | some m => m.admits pos
  | none   => False

instance (c : Complementizer) (pos : ClausePosition) : Decidable (licensedIn c pos) :=
  match hm : mergeMode c with
  | some m => decidable_of_iff (m.admits pos) (by unfold licensedIn; rw [hm])
  | none   => decidable_of_iff False (by unfold licensedIn; rw [hm])

/-- The say-root heads no clause of its own — the linker is the
converb, not 'say' (2)–(3). -/
theorem de_no_mergeMode : mergeMode Uyghur.de = none := rfl

/-! ### The say-converb witness (2)–(3), (9) -/

/-- A say-converb re-analysis of an apparent complementizer
([major-2024]; cf. `Bondarenko2022.ContAnalysis` for the rival
Cont-exponence carving): the linker decomposes into a say-root and a
converbial suffix drawn from the language's inventory, and the
say-root is the independently attested main verb 'say' — one lexical
item, so main-verb properties persist inside the adjunct by
construction (39)–(41). A structure, not a class: rival frameworks
construct rival witnesses. -/
structure SayConverbAnalysis where
  /-- The fragment inventory analyzed. -/
  inventory : List Complementizer
  /-- The say-root inside the complex linker. -/
  sayRoot : Complementizer
  /-- The converbial suffix heading the adjunct clause. -/
  converb : Complementizer
  /-- The main verb 'say' — the same lexical item as `sayRoot`. -/
  say : Verb
  sayRoot_mem : sayRoot ∈ inventory
  converb_mem : converb ∈ inventory
  /-- Morphology at face value: the linker is a converb. -/
  converb_conv : converb.verbForm = some UD.VerbForm.Conv
  /-- 'say' is transitive with an obligatory internal argument
      (39a), (40a), a requirement that persists inside the adjunct
      (41): `*(birnémi-ler-ni) de-p warqiri-di`). -/
  say_transitive : say.complementType ≠ ComplementType.none ∧ say.implicitObj = none

/-- The complex linker: the say-root's morphs followed by the converb's
(*de-p*; Sakha *die-n*). -/
def SayConverbAnalysis.linker (a : SayConverbAnalysis) : List Morph :=
  a.sayRoot.morphs ++ a.converb.morphs

/-- Any say-converb analysis fixes adjunction as the linker's merge
mode. -/
theorem SayConverbAnalysis.mergeMode_converb (a : SayConverbAnalysis) :
    mergeMode a.converb = some .converbAdjunction := by
  simp [mergeMode, a.converb_conv]

/-- Any say-converb analysis licenses the say-clause at both
adjunction heights (4), (51), (56). -/
theorem SayConverbAnalysis.adjoins (a : SayConverbAnalysis) :
    licensedIn a.converb .vpAdjunct ∧ licensedIn a.converb .tpAdjunct := by
  unfold licensedIn
  rw [a.mergeMode_converb]
  exact ⟨λ h => h, λ h => h⟩

/-- The argument-position ban, derived for any witness: the converb
morphology fixes adjunction, and adjuncts never saturate. -/
theorem SayConverbAnalysis.argument_ban (a : SayConverbAnalysis)
    (pos : ClausePosition) (h : pos.isArgument) :
    ¬ licensedIn a.converb pos := by
  unfold licensedIn
  rw [a.mergeMode_converb]
  exact λ hn => hn h

/-- The Uyghur witness: *dep* = *de* 'say' + -(I)p (2)–(3), over the
fragment inventory. -/
def depAnalysis : SayConverbAnalysis where
  inventory := Uyghur.complementizers
  sayRoot := Uyghur.de
  converb := Uyghur.ip
  say := Uyghur.deVerb
  sayRoot_mem := .head _
  converb_mem := .tail _ (.head _)
  converb_conv := rfl
  say_transitive := ⟨by decide, rfl⟩

example : depAnalysis.linker = [.root "de", .suff "(I)p"] := rfl

/-- Dep clauses adjoin at VP and TP (4), (37), (51), (56). -/
theorem dep_adjoins_vp_and_tp :
    licensedIn Uyghur.ip .vpAdjunct ∧ licensedIn Uyghur.ip .tpAdjunct :=
  depAnalysis.adjoins

/-- The argument ban (subject: (49b); internal argument: §3.2):
derived from -(I)p's converb morphology, and independent of the matrix
verb — dep clauses occur in clearly unselected environments, as
reasons or excuses (5), (53). -/
theorem dep_never_argument (pos : ClausePosition) (h : pos.isArgument) :
    ¬ licensedIn Uyghur.ip pos :=
  depAnalysis.argument_ban pos h

/-- (49b): a dep clause cannot be the grammatical subject of
'make surprised' — unlike the participial clause (49a). -/
theorem dep_not_subject : ¬ licensedIn Uyghur.ip .subject :=
  dep_never_argument .subject trivial

/-- The participial strategy is the mirror image: nominalized clauses
are licensed exactly in argument positions — subject (49a) and
complement of V (59a), (61a) — never at the converb adjunction
sites. Dep clauses also fail N-complement constituency: the head noun
scrambles away from a dep clause (45)–(46) but never from a genuine
N-complement (47)–(48). -/
theorem participial_licensed_iff_argument :
    ∀ pos, licensedIn Uyghur.lik pos ↔ pos.isArgument := by decide

/-! ### Say-properties persist: coerced speech readings (§3.1)

The persistence claim is carried by `depAnalysis` housing the single
lexical entry `Uyghur.deVerb`: whatever the fragment records of
main-verb 'say' holds of 'say' inside dep clauses. The same holds of
any converb-suffixed verb — 'think' imposes its own frame inside an
adjunct (42) — so the persistence is converbial, not dep-magic. -/

/-- (38)–(41): *warqira-* 'scream' has no complement frame (his
39b, 40b), yet 'scream' + dep reports propositional content — the
content sits in the obligatory complement of *de-* inside the
VP-adjoined say-clause, which "coerces it into a verb of speech"
(§3.1). No hidden frame of 'scream' is needed. -/
theorem coerced_speech_reading :
    Uyghur.warqira.complementType = .none ∧
    Uyghur.deVerb.complementType ≠ .none ∧
    licensedIn Uyghur.ip .vpAdjunct :=
  ⟨rfl, depAnalysis.say_transitive.1, dep_adjoins_vp_and_tp.1⟩

/-! ### The two heights diagnosed (54)–(55) -/

/-- Positions inside the matrix clausemate domain for NCI licensing:
Uyghur *héch-* items need clausemate negation (20). Everything
merged below matrix T is in the domain; the TP-adjunct, which precedes
the entire matrix clause (29), (31), is outside. -/
def ClausePosition.clausemateWithMatrixNeg : ClausePosition → Prop
  | .tpAdjunct => False
  | _ => True

instance : DecidablePred ClausePosition.clausemateWithMatrixNeg
  | .complementOfV => isTrue trivial
  | .subject       => isTrue trivial
  | .vpAdjunct     => isTrue trivial
  | .tpAdjunct     => isFalse id

/-- (54): matrix negation licenses an NCI inside a dep clause
exactly at the VP site — replicating the bare -(I)p contrast (his
22–26) — so NCI licensing diagnoses a dep clause's attachment height.
The *shundaq*-anaphora contrast (55) draws the same line. -/
theorem dep_nci_diagnoses_height :
    ∀ pos, licensedIn Uyghur.ip pos →
      (pos.clausemateWithMatrixNeg ↔ pos = .vpAdjunct) := by decide

/-! ### The factivity alternation, derived (61)–(65) -/

/-- Positions feeding a factive predicate's presupposition: only its
complement — "factive interpretations arise from predicates taking a
nominal complement, while non-factive interpretations arise via
adjunction", the adjunction site being "outside the scope of the
factive predicate" (§3.2). -/
def ClausePosition.feedsFactivity : ClausePosition → Prop
  | .complementOfV => True
  | _ => False

instance : DecidablePred ClausePosition.feedsFactivity
  | .complementOfV => isTrue trivial
  | .subject       => isFalse id
  | .vpAdjunct     => isFalse id
  | .tpAdjunct     => isFalse id

/-- Factive scope is a subrelation of argumenthood. -/
theorem feedsFactivity_isArgument :
    ∀ pos : ClausePosition, pos.feedsFactivity → pos.isArgument := by decide

/-- 'know' + dep is non-factive (61b) across the whole factive
class (63), and 'forget' + dep loses the forget-that reading (his
65): a dep clause can occupy no factivity-feeding position — a
corollary of the argument ban, contra a per-verb homophony account the
paper rejects (§3.2; 'know' stays presuppositional about its own
object even with dep present, (62). -/
theorem dep_never_feeds_factivity (pos : ClausePosition)
    (h : licensedIn Uyghur.ip pos) : ¬ pos.feedsFactivity :=
  λ hf => dep_never_argument pos (feedsFactivity_isArgument pos hf) h

/-- The participial contrast (61a), (63a–b): the nominalized clause
sits in complement position, where factivity is fed. -/
theorem participial_feeds_factivity :
    licensedIn Uyghur.lik .complementOfV ∧
    ClausePosition.feedsFactivity .complementOfV := by decide

end Major2024
