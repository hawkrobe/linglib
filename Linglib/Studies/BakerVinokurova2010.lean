import Linglib.Fragments.Yakut.Case
import Linglib.Data.Examples.BakerVinokurova2010

/-!
# Baker & Vinokurova 2010: two modalities of case assignment in Sakha

Sakha's four structural cases split in half. Accusative and dative are dependent cases: an NP
is valued accusative when a distinct caseless NP c-commands it in the same phase, and dative
when it c-commands one in the same VP phase, the dative rule bleeding the accusative rule on
the VP cycle. Nominative and genitive are assigned by T and D under agreement, and there is
no default case: an NP that no rule reaches must be pseudo-incorporated into the verb — an
unshifted VP-internal NP adjacent to it — or the structure is out. Object shift makes
differential object marking a phase effect; the causee of a causative is dative exactly when
the base verb is transitive; a passive theme is accusative exactly when a covert agent is
present; the object of an agentive nominalization is accusative though no v is present; a
subject raised into an impersonal clause stays unmarked; and a finite verb agrees with an NP
exactly when it values that NP nominative. A purely configurational grammar with a default
nominative overgenerates the Case-filter and agreement violations, and a purely Agree-based
grammar undergenerates the datives.

## Main definitions

* `Slot`, `candidates`: the NPs of a row's domain, highest first, from its stated roles; the
  covert agent and object shift are the free choices where the paper leaves them free.
* `derive`: `assignCasesPhased` on the Yakut configuration, with T-Agree switched off in a
  domain without an agreeing T-like head and D reaching into a relative or nominalized clause
  whose head noun agrees with its subject.
* `Licensed`, `Agrees`: the Case filter and the case–agreement link.
* `Derivable`: some choice of structure yields the row's cases.
* `rows_case`: acceptability is derivability under the two-modality grammar.
* `pure_marantz_overgenerates`, `pure_chomsky_undergenerates`: each modality alone fails.

## References

* [baker-vinokurova-2010]
* [marantz-1991] — dependent case
* [chomsky-2000], [chomsky-2001] — case under Agree and phases
* [diesing-1992] — object shift of specific objects
* [vinokurova-2005] — the source of much of the data
-/

namespace BakerVinokurova2010

open Data.Examples Syntax.Case Yakut.Case

/-- The argument roles a row states, in c-command order. -/
inductive Role
  | subject
  | causee
  | goal
  | raised
  | object
  | pObject
  | possessor
  deriving DecidableEq, Repr

/-- The prefix of a role's feature keys. -/
def Role.key : Role → String
  | .subject => "subject"
  | .causee => "causee"
  | .goal => "goal"
  | .raised => "raised"
  | .object => "object"
  | .pObject => "pObject"
  | .possessor => "possessor"

/-- The roles highest first. -/
def Role.all : List Role :=
  [.subject, .causee, .goal, .raised, .object, .pObject, .possessor]

/-- The case a gloss shows; a bare NP shows the nominative. -/
def parseCase? : String → Option Case
  | "NOM" | "bare" => some .nom
  | "ACC" => some .acc
  | "DAT" => some .dat
  | "GEN" => some .gen
  | _ => none

/-- A row states a yes/no property. -/
def yes (r : LinguisticExample) (k : String) : Bool := r.feature? k = some "yes"

/-- An NP of a row's domain: its phase data, whether it is covert, whether it is adjacent to
    the verb, and the case its gloss shows. -/
structure Slot where
  np : PhasedNP
  covert : Bool := false
  adjacent : Bool := false
  observed : Case := .nom
  deriving DecidableEq, Repr

/-- Where a role is merged: a possessor inside DP, the objects, goal, causee and raised
    subject inside VP, and the subject outside it unless the predicate is unaccusative or
    takes a dative subject. -/
def Role.basePhase (r : LinguisticExample) : Role → CasePhase
  | .subject =>
    if yes r "unaccusative" || r.feature? "subjectPosition" = some "internal" then .vp else .cp
  | .causee | .goal | .raised | .object => .vp
  | .pObject | .possessor => .cp

/-- Whether a VP-merged NP shifts to the phase edge: a specific one does, a nonspecific one
    does not, a raised subject always does, and the paper leaves the rest free. -/
def Role.shifts (r : LinguisticExample) (ρ : Role) : List Bool :=
  match ρ.basePhase r with
  | .cp => [false]
  | .vp =>
    if ρ = .raised then [true]
    else match r.feature? (ρ.key ++ "Specific") with
      | some "yes" => [true]
      | some "no" => [false]
      | _ => [false, true]

/-- The slots a stated role contributes, one per shift option. -/
def Role.slots (r : LinguisticExample) (ρ : Role) : Option (List Slot) :=
  ((r.feature? (ρ.key ++ "Case")).bind parseCase?).map λ c =>
    (ρ.shifts r).map λ sh =>
      { np := { label := ρ.key, lexicalCase := none, basePhase := ρ.basePhase r, shifted := sh,
                inDP := ρ = .possessor },
        adjacent := yes r (ρ.key ++ "Adjacent"), observed := c }

/-- The covert agent, merged above VP: forced in a passive with an agent-oriented adverb and
    in an agentive nominalization, excluded when the subject is overt or the predicate
    unaccusative, and otherwise free in a passive or event nominalization. -/
def agentOptions (r : LinguisticExample) : List (List Slot) :=
  let pro : Slot :=
    { np := { label := "PRO", lexicalCase := none, basePhase := .cp }, covert := true }
  if (r.feature? "subjectCase").isSome || yes r "unaccusative" then [[]]
  else if yes r "agentOrientedAdverb" || r.feature? "construction" = some "agentiveNominal" then
    [[pro]]
  else match r.feature? "construction" with
    | some "passive" | some "eventNominal" => [[pro], []]
    | _ => [[]]

/-- The domains a row may have: the covert agent, then each stated role under each of its
    shift options. -/
def candidates (r : LinguisticExample) : List (List Slot) :=
  (Role.all.foldr (λ ρ acc => match ρ.slots r with
      | none => acc
      | some vs => vs.flatMap λ s => acc.map (s :: ·)) [[]]).flatMap λ d =>
    (agentOptions r).map (· ++ d)

/-- The grammar a domain is evaluated under: T-Agree only where the verb bears an agreeing
    T-like head, D-Agree on a possessor only where the possessed noun agrees. -/
def config (cfg : CaseSystemConfig) (r : LinguisticExample) : CaseSystemConfig :=
  { cfg with
    nomMode := if yes r "verbAgreement" then cfg.nomMode else .unmarkedDefault
    genMode := if yes r "possesseeAgreement" then cfg.genMode else .nonstructural }

/-- D on a head noun that agrees with the clause's subject reaches into the relative or
    nominalized clause and values its highest caseless overt NP genitive. -/
def dProbe : List (Slot × CasedNP) → List (Slot × CasedNP)
  | [] => []
  | (s, c) :: rest =>
    if !s.covert && c.source == .unmarked && s.np.visibleOnCP then
      (s, { c with case := .gen, source := .agree }) :: rest
    else (s, c) :: dProbe rest

/-- The cases of a domain, paired with its slots. -/
def derive (cfg : CaseSystemConfig) (r : LinguisticExample) (d : List Slot) :
    List (Slot × CasedNP) :=
  let out := d.zip (assignCasesPhased (config cfg r) (d.map (·.np)))
  if yes r "headNounAgreement" && cfg.genMode == .agreeD then dProbe out else out

/-- The Case filter: a caseless overt NP must be pseudo-incorporated — an unshifted
    VP-internal NP adjacent to the verb. -/
def Licensed (s : Slot) (c : CasedNP) : Prop :=
  s.covert = true ∨ c.source ≠ .unmarked ∨
    (s.np.basePhase = .vp ∧ s.np.shifted = false ∧ s.adjacent = true)

instance (s : Slot) (c : CasedNP) : Decidable (Licensed s c) := by
  unfold Licensed; infer_instance

/-- T agrees with the NP it values nominative: where a row states the verb's agreement target,
    an overt NP is nominative by Agree exactly when it is that target, so default agreement
    means no NP is. -/
def Agrees (r : LinguisticExample) (out : List (Slot × CasedNP)) : Prop :=
  (r.feature? "agreesWith").isSome → ∀ p ∈ out, p.1.covert = false →
    ((p.2.case = .nom ∧ p.2.source = .agree) ↔ r.feature? "agreesWith" = some p.1.np.label)

instance (r : LinguisticExample) (out : List (Slot × CasedNP)) : Decidable (Agrees r out) := by
  unfold Agrees; infer_instance

/-- A domain derives the row under a grammar: every overt NP gets the case its gloss shows,
    and under the Chomskian half — the Case filter and the case–agreement link — is licensed
    and agreed with accordingly. -/
def Derives (cfg : CaseSystemConfig) (chomskian : Bool) (r : LinguisticExample)
    (d : List Slot) : Prop :=
  (∀ p ∈ derive cfg r d, p.1.covert = false →
    p.2.case = p.1.observed ∧ (chomskian = true → Licensed p.1 p.2)) ∧
  (chomskian = true → Agrees r (derive cfg r d))

instance (cfg : CaseSystemConfig) (chomskian : Bool) (r : LinguisticExample) (d : List Slot) :
    Decidable (Derives cfg chomskian r d) := by
  unfold Derives; infer_instance

/-- Some choice of structure derives the row. -/
def Derivable (cfg : CaseSystemConfig) (chomskian : Bool) (r : LinguisticExample) : Prop :=
  ∃ d ∈ candidates r, Derives cfg chomskian r d

instance (cfg : CaseSystemConfig) (chomskian : Bool) (r : LinguisticExample) :
    Decidable (Derivable cfg chomskian r) := by
  unfold Derivable; infer_instance

/-- Each of the paper's Sakha examples is acceptable exactly when some structure derives the
    cases it shows under the two-modality grammar with the Case filter and the
    case–agreement link. -/
theorem rows_case :
    ∀ r ∈ Examples.all, r.judgment = .acceptable ↔ Derivable yakutCaseConfig true r := by
  decide

/-- A purely configurational grammar: dependent accusative and dative, nominative as the
    default, no structural genitive. -/
def pureMarantz : CaseSystemConfig where
  langType := .accusative
  nomMode := .unmarkedDefault
  datMode := .dependent
  accMode := .dependent
  genMode := .nonstructural

/-- A purely Agree-based grammar: accusative from v, nominative from T, genitive from D, and
    no structural dative. -/
def pureChomsky : CaseSystemConfig where
  langType := .accusative
  nomMode := .agreeT
  datMode := .nonstructural
  accMode := .agreeV
  genMode := .agreeD

/-- Without the Case filter and the case–agreement link, the configurational grammar derives
    a rejected example — a bare object separated from the verb, an unagreed-with subject of a
    participial clause, a passive whose verb agrees with nothing though its theme is
    nominative. -/
theorem pure_marantz_overgenerates :
    ∃ r ∈ Examples.all, r.judgment = .unacceptable ∧ Derivable pureMarantz false r := by
  decide

/-- The Agree-based grammar, with no structural dative, fails an accepted example with a
    dative goal. -/
theorem pure_chomsky_undergenerates :
    ∃ r ∈ Examples.all, r.judgment = .acceptable ∧ r.feature? "goalCase" = some "DAT" ∧
      ¬ Derivable pureChomsky true r := by
  decide

end BakerVinokurova2010
