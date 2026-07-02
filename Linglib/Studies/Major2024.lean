import Linglib.Fragments.Uyghur.Complementizers
import Linglib.Data.Examples.Major2024

/-!
# Major 2024: Re-analyzing 'say' complementation
[major-2024]

Uyghur *dep* clauses look like complementizer-headed CP complements
but are converbial adjunct clauses headed by the verb *de* 'say' plus
the converb -(I)p, merging at VP or TP (his 4, 9). Because the linker
contains the verb 'say', main-verb properties of *de-* persist inside
dep clauses (his 39–41), and because the linker is a converb, dep
clauses are banned from argument positions: they cannot be grammatical
subjects (his 49b) and "are never internal arguments" (§3.2). The
paper's methodological point — "taking the morphology at face value
(i.e. dep is 'say' + CNV)" (§1) — is rendered literally here:
`mergeMode` reads a morpheme's merge behavior off its recorded
morphology (`verbForm`, `noonanType`), and the ban is derived, not
stipulated per position. The Washo parallel is [bochnak-hanink-2021]'s
modifier analysis of non-factive embedding, which Major extends with
the verb 'say' inside the linker.

The case-theoretic payoff (his §§4–6) is out of scope here: the same
decomposition holds of Sakha *dien* = *die* 'say' + converb -(E)n, so
[baker-vinokurova-2010]'s accusative subjects under *dien* reduce to
ECM by the v of 'say', resurrecting Case-by-Agree where B&V argued
for Dependent Case Theory.

## Main declarations

- `ClausePosition`, `MergeMode`, `mergeMode`, `licensedIn` — merge
  behavior read off the fragment entries' morphology
- `SayConverbAnalysis` — witness record for the re-analysis (cf.
  `Bondarenko2022.ContAnalysis` for the rival carving); `depAnalysis`
  is the Uyghur witness, and `SayConverbAnalysis.argument_ban` derives
  the ban for any witness
- `dep_never_argument`, `participial_licensed_iff_argument` — the
  argument-position asymmetry (his 49, 59, 61)
- `coerced_speech_reading` — unergative 'scream' + dep (his 38–41)
- `dep_nci_diagnoses_height` — the VP/TP height contrast (his 54)
- `dep_never_feeds_factivity` — the factivity alternation as a
  corollary of the ban (his 61–65)

## The rival carving (docstring-only, per the chronology rule)

[bondarenko-2022] assigns the structurally parallel Buryat say-complex
*gɘ-žɘ* to functional heads: the say-root expones Cont and the converb
is a Comp allomorph (`Bondarenko2022.buryatAnalysis`), so the complex
heads a selected complement. Major's carving keeps both pieces
lexical — verb plus adjunct-forming converb — and denies complement
status altogether. Major does not engage that analysis (he cites only
[bondarenko-2020] among factivity-alternation accounts, §3.2), so no
divergence theorem is stated here; the two witnesses coexist as rival
records over their respective fragment inventories.

Typed paradigm sentences (his 2, 38–41, 49) live in `Major2024.Examples`,
generated from `Data/Examples/Major2024.json`.
-/

namespace Major2024

/-! ### Merge modes read off the morphology (§2)

Converbial -(I)p clauses adjoin at two heights (his 4): VP-level
-(I)p is a manner modifier interpreted under matrix aspect (his
10–13), answers *qandaq* 'how' (his 15–16), and sits below the matrix
accusative position (his 19); TP-level -(I)p precedes the whole matrix
clause (his 29), tolerates aspect and voice mismatches (his 12, 30),
and merges at (at least) TP (his 31). Dep clauses replicate both
profiles (his 37–38, 52–56). -/

/-- Structural positions at issue for an embedded clause: the two
converb adjunction heights (his 4) and the two argument positions the
paper tests — complement of V (his 59a, 61a, 73) and grammatical
subject (his 49). -/
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
converb builds an adjunct to a verbal projection (his 4); a
nominalizer builds a case-bearing nominal that saturates an argument
position (his 49a, 59a). -/
inductive MergeMode where
  | converbAdjunction
  | nominalArgument
  deriving DecidableEq, Repr

/-- Converbial adjuncts modify, never saturate ("dep clauses are never
internal arguments", §3.2; subject ban his 49b); nominalized clauses
saturate. Oblique case-marked participial adjuncts (his 50b) go
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
clause-typer (`noonanType = .nominalized`) builds arguments. `none`
for morphemes heading no clause of their own. -/
def mergeMode (c : Complementizer) : Option MergeMode :=
  if c.verbForm = some .Conv then some .converbAdjunction
  else if c.noonanType = some .nominalized then some .nominalArgument
  else none

/-- A clause headed by `c` is licensed in `pos` iff `c`'s merge mode
admits it. No matrix-verb parameter: dep clauses appear regardless of
matrix transitivity (his 44a *söz qil-* vs. unaccusative 44b *söz
bol-*) and with unaccusative 'be surprised' (his 50c). -/
def licensedIn (c : Complementizer) (pos : ClausePosition) : Prop :=
  match mergeMode c with
  | some m => m.admits pos
  | none   => False

instance (c : Complementizer) (pos : ClausePosition) : Decidable (licensedIn c pos) :=
  match hm : mergeMode c with
  | some m => decidable_of_iff (m.admits pos) (by unfold licensedIn; rw [hm])
  | none   => decidable_of_iff False (by unfold licensedIn; rw [hm])

/-- The say-root heads no clause of its own — the linker is the
converb, not 'say' (his 2–3). -/
theorem de_no_mergeMode : mergeMode Uyghur.de = none := rfl

/-! ### The say-converb witness (his 2–3, 9) -/

/-- A say-converb re-analysis of an apparent complementizer
([major-2024]; cf. `Bondarenko2022.ContAnalysis` for the rival
Cont-exponence carving): the linker decomposes into a say-root and a
converbial suffix drawn from the language's inventory, and the
say-root is the independently attested main verb 'say' — one lexical
item, so main-verb properties persist inside the adjunct by
construction (his 39–41). A structure, not a class: rival frameworks
construct rival witnesses. -/
structure SayConverbAnalysis where
  /-- The fragment inventory analyzed. -/
  inventory : List Complementizer
  /-- The apparent complementizer being decomposed (*dep*; Sakha *dien*). -/
  surface : String
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
      (his 39a, 40a), a requirement that persists inside the adjunct
      (his 41: `*(birnémi-ler-ni) de-p warqiri-di`). -/
  say_transitive : say.complementType ≠ ComplementType.none ∧ say.implicitObj = none

/-- Any say-converb analysis fixes adjunction as the linker's merge
mode. -/
theorem SayConverbAnalysis.mergeMode_converb (a : SayConverbAnalysis) :
    mergeMode a.converb = some .converbAdjunction := by
  simp [mergeMode, a.converb_conv]

/-- Any say-converb analysis licenses the say-clause at both
adjunction heights (his 4, 51, 56). -/
theorem SayConverbAnalysis.adjoins (a : SayConverbAnalysis) :
    licensedIn a.converb .vpAdjunct ∧ licensedIn a.converb .tpAdjunct := by
  unfold licensedIn
  rw [a.mergeMode_converb]
  exact ⟨fun h => h, fun h => h⟩

/-- The argument-position ban, derived for any witness: the converb
morphology fixes adjunction, and adjuncts never saturate. -/
theorem SayConverbAnalysis.argument_ban (a : SayConverbAnalysis)
    (pos : ClausePosition) (h : pos.isArgument) :
    ¬ licensedIn a.converb pos := by
  unfold licensedIn
  rw [a.mergeMode_converb]
  exact fun hn => hn h

/-- The Uyghur witness: *dep* = *de* 'say' + -(I)p (his 2–3), over the
fragment inventory. -/
def depAnalysis : SayConverbAnalysis where
  inventory := Uyghur.complementizers
  surface := "dep"
  sayRoot := Uyghur.de
  converb := Uyghur.ip
  say := Uyghur.deVerb
  sayRoot_mem := .head _
  converb_mem := .tail _ (.head _)
  converb_conv := rfl
  say_transitive := ⟨by decide, rfl⟩

/-- Dep clauses adjoin at VP and TP (his 4, 37, 51, 56). -/
theorem dep_adjoins_vp_and_tp :
    licensedIn Uyghur.ip .vpAdjunct ∧ licensedIn Uyghur.ip .tpAdjunct :=
  depAnalysis.adjoins

/-- The argument ban (subject: his 49b; internal argument: §3.2):
derived from -(I)p's converb morphology, and independent of the matrix
verb — dep clauses occur in clearly unselected environments, as
reasons or excuses (his 5, 53). -/
theorem dep_never_argument (pos : ClausePosition) (h : pos.isArgument) :
    ¬ licensedIn Uyghur.ip pos :=
  depAnalysis.argument_ban pos h

/-- His (49b): a dep clause cannot be the grammatical subject of
'make surprised' — unlike the participial clause (his 49a). -/
theorem dep_not_subject : ¬ licensedIn Uyghur.ip .subject :=
  dep_never_argument .subject trivial

/-- The participial strategy is the mirror image: nominalized clauses
are licensed exactly in argument positions — subject (his 49a) and
complement of V (his 59a, 61a) — never at the converb adjunction
sites. Dep clauses also fail N-complement constituency: the head noun
scrambles away from a dep clause (his 45–46) but never from a genuine
N-complement (his 47–48). -/
theorem participial_licensed_iff_argument :
    ∀ pos, licensedIn Uyghur.lik pos ↔ pos.isArgument := by decide

/-! ### Say-properties persist: coerced speech readings (§3.1)

The persistence claim is carried by `depAnalysis` housing the single
lexical entry `Uyghur.deVerb`: whatever the fragment records of
main-verb 'say' holds of 'say' inside dep clauses. The same holds of
any converb-suffixed verb — 'think' imposes its own frame inside an
adjunct (his 42) — so the persistence is converbial, not dep-magic. -/

/-- His (38)–(41): *warqira-* 'scream' has no complement frame (his
39b, 40b), yet 'scream' + dep reports propositional content — the
content sits in the obligatory complement of *de-* inside the
VP-adjoined say-clause, which "coerces it into a verb of speech"
(§3.1). No hidden frame of 'scream' is needed. -/
theorem coerced_speech_reading :
    Uyghur.warqira.complementType = .none ∧
    Uyghur.deVerb.complementType ≠ .none ∧
    licensedIn Uyghur.ip .vpAdjunct :=
  ⟨rfl, depAnalysis.say_transitive.1, dep_adjoins_vp_and_tp.1⟩

/-! ### The two heights diagnosed (his 54–55) -/

/-- Positions inside the matrix clausemate domain for NCI licensing:
Uyghur *héch-* items need clausemate negation (his 20). Everything
merged below matrix T is in the domain; the TP-adjunct, which precedes
the entire matrix clause (his 29, 31), is outside. -/
def ClausePosition.clausemateWithMatrixNeg : ClausePosition → Prop
  | .tpAdjunct => False
  | _ => True

instance : DecidablePred ClausePosition.clausemateWithMatrixNeg
  | .complementOfV => isTrue trivial
  | .subject       => isTrue trivial
  | .vpAdjunct     => isTrue trivial
  | .tpAdjunct     => isFalse id

/-- His (54): matrix negation licenses an NCI inside a dep clause
exactly at the VP site — replicating the bare -(I)p contrast (his
22–26) — so NCI licensing diagnoses a dep clause's attachment height.
The *shundaq*-anaphora contrast (his 55) draws the same line. -/
theorem dep_nci_diagnoses_height :
    ∀ pos, licensedIn Uyghur.ip pos →
      (pos.clausemateWithMatrixNeg ↔ pos = .vpAdjunct) := by decide

/-! ### The factivity alternation, derived (his 61–65) -/

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

/-- 'know' + dep is non-factive (his 61b) across the whole factive
class (his 63), and 'forget' + dep loses the forget-that reading (his
65): a dep clause can occupy no factivity-feeding position — a
corollary of the argument ban, contra a per-verb homophony account the
paper rejects (§3.2; 'know' stays presuppositional about its own
object even with dep present, his 62). -/
theorem dep_never_feeds_factivity (pos : ClausePosition)
    (h : licensedIn Uyghur.ip pos) : ¬ pos.feedsFactivity :=
  fun hf => dep_never_argument pos (feedsFactivity_isArgument pos hf) h

/-- The participial contrast (his 61a, 63a–b): the nominalized clause
sits in complement position, where factivity is fed. -/
theorem participial_feeds_factivity :
    licensedIn Uyghur.lik .complementOfV ∧
    ClausePosition.feedsFactivity .complementOfV := by decide

end Major2024
