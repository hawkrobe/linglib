import Linglib.Syntax.DependencyGrammar.Basic

/-!
# Government in Dependency Grammar

Formalizes government ([osborne-2019], Ch. 4 §4.8 and Ch. 5): the
mechanism by which a head determines the morphosyntactic form of its
dependent — case on a complement of a preposition, verb form on the
complement of a control verb, finiteness of a clausal complement.

Government is orthogonal to valency: "want to go" and "enjoy swimming"
share an `xcomp` slot but require different forms (`infinitive` vs.
`gerund`) on the complement.

## Main declarations

* `GovernedFeature`, `GovernedValue` — the morphosyntactic dimensions a
  head can govern, with a typed value space (no `String` tags).
* `GovRequirement` — one head-cat / dep-rel / feature / required-value
  4-tuple, with five English instances from [osborne-2019].
* `checkGovernment` — Bool checker that verifies every dependency in a
  `DepTree` honours every requirement that applies to it.
* `withHim_govOk` / `withHe_govFail` etc. — small fixtures exercising
  the checker on accusative-vs-nominative preposition complements and
  infinitive-vs-gerund verb complements.

## Implementation notes

* Bool checker, not Prop predicate: matches the substrate-wide
  convention in this directory; Prop+Decidable migration is out of
  scope for the cleanup pass.
* No bridge theorems to `HeadCriteria`. The audit flagged the previous
  `government_implies_head` and `argslot_agnostic_to_government` as
  rfl-on-stipulation tautologies; cross-framework rivalry against
  HPSG `COMPS|VFORM` or Minimalist selectional features belongs in a
  paper-anchored Studies file, not the substrate.
-/

namespace DepGrammar.Government

open DepGrammar

/-! ### Government dimensions and values -/

/-- A morphosyntactic feature a head can govern on its dependent.
    [osborne-2019]. -/
inductive GovernedFeature where
  | Case
  | VForm
  | Mood
  | Finiteness
  deriving Repr, DecidableEq

/-- The typed value space for governed features (replaces stringly-typed
    requirement tags). [osborne-2019]. -/
inductive GovernedValue where
  | acc | nom | gen
  | infinitive | base | gerund | participle
  | finite | nonfinite
  deriving Repr, DecidableEq

/-- A government requirement: a head of category `headCat` requires its
    dependent on relation `depRel` to have value `requiredValue` of
    feature `feature`. [osborne-2019]. -/
structure GovRequirement where
  headCat : UD.UPOS
  depRel : UD.DepRel
  feature : GovernedFeature
  requiredValue : GovernedValue
  deriving Repr, DecidableEq

/-! ### English government data -/

/-- "want to go" — `want` governs the infinitival form of its `xcomp`. -/
def govVerbInfinitive : GovRequirement :=
  ⟨.VERB, .xcomp, .VForm, .infinitive⟩

/-- "make him go" — `make` governs the bare form of its `xcomp`. -/
def govVerbBareInf : GovRequirement :=
  ⟨.VERB, .xcomp, .VForm, .base⟩

/-- "enjoy swimming" — `enjoy` governs the gerund form of its `xcomp`. -/
def govVerbGerund : GovRequirement :=
  ⟨.VERB, .xcomp, .VForm, .gerund⟩

/-- "think that ..." — `think` governs a finite `ccomp`. -/
def govVerbFinite : GovRequirement :=
  ⟨.VERB, .ccomp, .Finiteness, .finite⟩

/-- "with him / *with he" — preposition governs accusative on its `obj`. -/
def govPrepAcc : GovRequirement :=
  ⟨.ADP, .obj, .Case, .acc⟩

/-- The English government patterns from [osborne-2019]. -/
def englishGovRequirements : List GovRequirement :=
  [govVerbInfinitive, govVerbBareInf, govVerbGerund, govVerbFinite, govPrepAcc]

/-! ### Government checking -/

/-- Does the word `w` carry the value `reqVal` of feature `feat`?
    Returns `true` when the relevant feature slot is unspecified
    (vacuous satisfaction); a *marked* slot whose value differs from the
    requirement fails. -/
def matchGovFeature (w : Word) (feat : GovernedFeature) (reqVal : GovernedValue) : Bool :=
  match feat with
  | .Case =>
    -- Route case extraction through the `HasCase` mixin (analytical
    -- inventory), not raw UD constructors. An unmarked slot is vacuously
    -- satisfied; a marked case that differs from the requirement fails — so
    -- e.g. a dative object does *not* satisfy an accusative requirement.
    match HasCase.caseOf w, reqVal with
    | none, _ => true
    | some c, .acc => c = .acc
    | some c, .nom => c = .nom
    | some c, .gen => c = .gen
    | some _, _ => true
  | .VForm =>
    match w.features.verbForm with
    | some .Inf => reqVal = .infinitive
    | some .Part => reqVal = .gerund || reqVal = .participle
    | some .Fin => reqVal = .finite || reqVal = .base
    | _ => true
  | .Finiteness =>
    -- finiteness is read off verbForm (no stored finiteness flag); only an explicit
    -- infinitive counts as nonfinite, matching the old default-finite behavior
    if w.features.verbForm != some .Inf then reqVal = .finite else reqVal = .nonfinite
  | .Mood => true

/-- A dependency tree satisfies its government requirements when every
    matching head-cat / dep-rel pair carries the required value. -/
def checkGovernment (t : DepTree) (govReqs : List GovRequirement) : Bool :=
  t.deps.all λ d =>
    govReqs.all λ req =>
      if d.depType = req.depRel then
        match t.words[d.headIdx]?, t.words[d.depIdx]? with
        | some hw, some dw =>
            if hw.cat = req.headCat then
              matchGovFeature dw req.feature req.requiredValue
            else true
        | _, _ => true
      else true

/-! ### Example trees -/

/-- "She wants to go": `wants(1)` heads `she(0)` (nsubj) and `go(3)`
    (xcomp); `go(3)` heads `to(2)` (mark). -/
def exSheWantsToGo : DepTree :=
  { words := [ { form :="she", cat := .PRON, features := { case_ := some .Nom }}
             , { form :="wants", cat := .VERB}
             , { form :="to", cat := .PART, features := {}}
             , { form :="go", cat := .VERB, features := { verbForm := some .Inf }} ]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 3, .xcomp⟩, ⟨3, 2, .mark⟩]
    rootIdx := 1 }

/-- "She enjoys swimming": `enjoys(1)` heads `she(0)` (nsubj) and
    `swimming(2)` (xcomp). -/
def exSheEnjoysSwimming : DepTree :=
  { words := [ { form :="she", cat := .PRON, features := { case_ := some .Nom }}
             , { form :="enjoys", cat := .VERB}
             , { form :="swimming", cat := .VERB, features := { verbForm := some .Part }} ]
    deps := [⟨1, 0, .nsubj⟩, ⟨1, 2, .xcomp⟩]
    rootIdx := 1 }

/-- "with him": preposition governs accusative — well-formed. -/
def exWithHim : DepTree :=
  { words := [ { form :="with", cat := .ADP, features := {}}
             , { form :="him", cat := .PRON, features := { case_ := some .Acc }} ]
    deps := [⟨0, 1, .obj⟩]
    rootIdx := 0 }

/-- "with he": preposition government violation (nominative for accusative). -/
def exWithHe : DepTree :=
  { words := [ { form :="with", cat := .ADP, features := {}}
             , { form :="he", cat := .PRON, features := { case_ := some .Nom }} ]
    deps := [⟨0, 1, .obj⟩]
    rootIdx := 0 }

/-- Regression guard for `matchGovFeature`: a preposition's `obj` bearing a
    *marked* case other than the required accusative (here dative) violates
    government. The earlier checker fell through to `true` for any case outside
    {nom, acc, gen}, so a dative object spuriously satisfied `govPrepAcc`. -/
def exPrepDatObj : DepTree :=
  { words := [ { form :="with", cat := .ADP, features := {}}
             , { form :="X", cat := .PRON, features := { case_ := some .Dat }} ]
    deps := [⟨0, 1, .obj⟩]
    rootIdx := 0 }

/-! ### Checker behaviour on the fixtures -/

theorem withHim_govOk :
    checkGovernment exWithHim [govPrepAcc] = true := by decide

theorem withHe_govFail :
    checkGovernment exWithHe [govPrepAcc] = false := by decide

theorem prepDatObj_govFail :
    checkGovernment exPrepDatObj [govPrepAcc] = false := by decide

theorem wantsToGo_govOk :
    checkGovernment exSheWantsToGo [govVerbInfinitive] = true := by decide

theorem enjoysSwimming_govOk :
    checkGovernment exSheEnjoysSwimming [govVerbGerund] = true := by decide

end DepGrammar.Government
