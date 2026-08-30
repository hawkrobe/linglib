import Linglib.Fragments.Yakut.Case
import Linglib.Data.Examples.BakerVinokurova2010

/-!
# Baker & Vinokurova 2010: two modalities of case assignment in Sakha

Sakha's four structural cases split in half. Accusative and dative are dependent cases: an NP
is valued accusative when a distinct caseless NP c-commands it in the clause, and dative when
it c-commands one in the verb phrase, where there is no accusative rule. Nominative and
genitive are assigned by T and D under agreement, and there is no elsewhere case: an NP that no
rule and no head reaches must be pseudo-incorporated into the verb — an unshifted VP-internal
NP adjacent to it — or the structure is out. Object shift makes differential object marking a
phase effect; the causee of a causative is dative exactly when the base verb is transitive; a
passive theme is accusative exactly when a covert agent is present; the object of an agentive
nominalization is accusative though no v is present; a subject raised into an impersonal clause
stays unmarked; and a finite verb agrees with an NP exactly when it values that NP nominative.
A purely configurational grammar with elsewhere cases overgenerates the Case-filter and
agreement violations, and a purely Agree-based grammar never values a dative.

## Main definitions

* `pureMarantz`, `pureChomsky`: the two pure grammars beside the Yakut fragment's.
* `subject`, `internal`, `possessor`, `pro`, `finite`: the NP positions and the finite probe
  the paper's derivations use.
* `Slot`, `candidates`: the NPs of a row's domain from the slots the rows name, highest first;
  the covert agent and object shift are the free choices where the paper leaves them free.
* `derive`, `Licensed`, `Agrees`, `Derivable`: assignment with the probes a row's morphology
  shows, the Case filter, the case–agreement link, and derivability under some choice.

## Main results

* `dom`, `ditransitive`, `causative`, `passive`, `agentive_nominal`, `raising`, `promise`,
  `possessed`: the paper's constructions, for any labels.
* `no_elsewhere_case`, `pureChomsky_no_dative`: Sakha values nothing as unmarked, and an
  Agree-only grammar values nothing dative, whatever the domain.
* `rows_case`: acceptability is derivability under the two-modality grammar.
* `pure_marantz_overgenerates`: without the Case filter and the agreement link, the
  configurational grammar derives rejected examples.

## References

* [baker-vinokurova-2010]
* [marantz-1991] — dependent case
* [chomsky-2000], [chomsky-2001] — case under Agree and phases
* [diesing-1992] — object shift of specific objects
* [vinokurova-2005] — the source of much of the data
-/

namespace BakerVinokurova2010

open Data.Examples Minimalist Case Yakut.Case

/-! ### The grammars -/

/-- A purely configurational grammar: dependent dative and accusative with elsewhere
    nominative in the clause and verb phrase, elsewhere genitive in the noun phrase, and no
    Agree. -/
def pureMarantz : CaseGrammar where
  domains := [(.D, { unmarked := some .gen }), (.v, { high := some .dat, unmarked := some .nom }),
    (.C, { low := some .acc, unmarked := some .nom })]

/-- A purely Agree-based grammar: nominative from T, accusative from v, genitive from D, and
    no dependent rule. -/
def pureChomsky : CaseGrammar where
  domains := [(.D, {}), (.v, {}), (.C, {})]
  agree := [(.T, .nom), (.v, .acc), (.D, .gen)]

/-- Sakha values nothing as unmarked: an NP no rule and no head reaches stays caseless. -/
theorem no_elsewhere_case (probes : List (Cat × Cat)) {nps : List PhasedNP} {i : ℕ} {np : NP}
    {c : Case} {m : Mechanism} (h : (grammar.assign probes nps)[i]? = some (np, some (c, m))) :
    m ≠ .unmarked :=
  grammar.mechanism_ne_unmarked probes (by decide) h

/-- The Agree-based grammar values nothing dative: a dative NP brought it from the lexicon. -/
theorem pureChomsky_no_dative (probes : List (Cat × Cat)) {nps : List PhasedNP} {i : ℕ}
    {np : PhasedNP} {m : Mechanism} (hnp : nps[i]? = some np)
    (h : (pureChomsky.assign probes nps)[i]? = some (np.toNP, some (.dat, m))) :
    np.lexicalCase = some .dat := by
  rcases hlex : np.lexicalCase with _ | c
  · exact absurd (pureChomsky.case_mem_cases probes hlex h) (by decide)
  · have := pureChomsky.assign_getElem?_of_some probes hnp hlex
    rw [this] at h
    simp only [Option.some.injEq, Prod.mk.injEq, true_and] at h
    rw [h.1]

/-! ### Positions -/

/-- A caseless NP merged in the clause. -/
def subject (label : String) : PhasedNP := { label }

/-- A caseless NP merged in the verb phrase, shifted to the clause edge or not. -/
def internal (label : String) (shifted : Bool) : PhasedNP := { label, phase := .v, shifted }

/-- A caseless NP inside a noun phrase. -/
def possessor (label : String) : PhasedNP := { label, phase := .D }

/-- The covert agent, merged in the clause. -/
def pro : PhasedNP := { label := "PRO" }

/-- Finite T probing the clause. -/
def finite : List (Cat × Cat) := [(.T, .C)]

/-- The cases of a derivation, positionally. -/
def cases (g : CaseGrammar) (probes : List (Cat × Cat)) (nps : List PhasedNP) :
    List (Option Case) :=
  (g.assign probes nps).map (·.2.map (·.1))

/-! ### The constructions -/

attribute [local simp] cases CaseGrammar.assign domainPass probePass agreePass
  Rules.dependentPass Rules.unmarkedPass eligible markBy markByFrom initial CaseGrammar.rules
  CaseGrammar.agreeCase grammar pureMarantz PhasedNP.visible PhasedNP.spellOut subject internal
  possessor pro finite


/-- Differential object marking: a shifted object is accusative and an unshifted one caseless,
    the subject nominative from T either way. -/
theorem dom (s o : String) (shifted : Bool) :
    cases grammar finite [subject s, internal o shifted] =
      [some .nom, if shifted then some .acc else none] := by
  cases shifted <;> simp

/-- A ditransitive: the goal is dative on the verb-phrase cycle whether or not the theme
    shifts, and the theme accusative exactly when it does; a causative of a transitive base
    is the same configuration, with the causee the higher of the two. -/
theorem ditransitive (s g t : String) (shifted : Bool) :
    cases grammar finite [subject s, internal g false, internal t shifted] =
      [some .nom, some .dat, if shifted then some .acc else none] := by
  cases shifted <;> simp

/-- A causative: the causee of a transitive base is dative, c-commanding the theme in the
    verb phrase, and the causee of an intransitive base, alone there, is accusative once it
    shifts and never dative. -/
theorem causative (c e t : String) (shifted : Bool) :
    cases grammar finite [subject c, internal e false, internal t shifted] =
      [some .nom, some .dat, if shifted then some .acc else none] ∧
    cases grammar finite [subject c, internal e shifted] =
      [some .nom, if shifted then some .acc else none] :=
  ⟨ditransitive c e t shifted, dom c e shifted⟩

/-- A passive: the shifted theme is accusative exactly when a covert agent is present, and
    nominative from T otherwise; a goal is dative either way. -/
theorem passive (g t : String) :
    cases grammar finite [pro, internal t true] = [some .nom, some .acc] ∧
    cases grammar finite [internal t true] = [some .nom] ∧
    cases grammar finite [pro, internal g false, internal t true] =
      [some .nom, some .dat, some .acc] ∧
    cases grammar finite [internal g false, internal t true] = [some .dat, some .nom] := by
  simp

/-- An agentive nominalization: no T, but the covert agent makes the shifted object
    accusative; without the agent the object is caseless. -/
theorem agentive_nominal (o : String) :
    cases grammar [] [pro, internal o true] = [none, some .acc] ∧
    cases grammar [] [internal o true] = [none] := by
  simp

/-- A subject raised to the clause edge is accusative exactly when the matrix clause has
    another NP; into an impersonal clause it is valued by T alone. -/
theorem raising (s r : String) :
    cases grammar finite [subject s, internal r true] = [some .nom, some .acc] ∧
    cases grammar finite [internal r true] = [some .nom] := by
  simp

/-- Raising into the complement of *promise*: the goal is dative once the raised subject is
    below it in the verb phrase, and accusative when nothing is. -/
theorem promise (s g r : String) :
    cases grammar finite [subject s, internal g false, internal r true] =
      [some .nom, some .dat, some .acc] ∧
    cases grammar finite [subject s, internal g true] = [some .nom, some .acc] := by
  simp

/-- A possessor is genitive from its D, and invisible to the clause. -/
theorem possessed (s p o : String) :
    cases grammar (finite ++ [(.D, .D)]) [subject s, possessor p, internal o true] =
      [some .nom, some .gen, some .acc] := by
  simp

/-- Without an elsewhere case, a caseless NP left in the verb phrase or a subject without an
    agreeing head stays caseless — the Case filter's bite — where the configurational grammar
    values both. -/
theorem elsewhere_contrast (s o : String) :
    cases grammar finite [subject s, internal o false] = [some .nom, none] ∧
    cases grammar [] [subject s] = [none] ∧
    cases pureMarantz finite [subject s, internal o false] = [some .nom, some .nom] ∧
    cases pureMarantz [] [subject s] = [some .nom] := by
  simp

/-! ### The rows -/

/-- The NP slots the rows name, in c-command order. -/
inductive Slot
  | subject
  | causee
  | goal
  | raised
  | object
  | pObject
  | possessor
  deriving DecidableEq, Repr

/-- The prefix of a slot's feature keys. -/
def Slot.key : Slot → String
  | .subject => "subject"
  | .causee => "causee"
  | .goal => "goal"
  | .raised => "raised"
  | .object => "object"
  | .pObject => "pObject"
  | .possessor => "possessor"

/-- The slots highest first. -/
def Slot.all : List Slot :=
  [.subject, .causee, .goal, .raised, .object, .pObject, .possessor]

/-- The case a gloss shows, or nothing for a bare NP. -/
def parseCase? : String → Option (Option Case)
  | "NOM" => some (some .nom)
  | "bare" => some none
  | "ACC" => some (some .acc)
  | "DAT" => some (some .dat)
  | "GEN" => some (some .gen)
  | _ => none

/-- A valuation realizes a gloss: the case it shows, or, for a bare NP, no case or the
    nominative, which is unmarked. -/
def Realizes (v : Valuation) : Option Case → Prop
  | some c => v.map (·.1) = some c
  | none => v.map (·.1) = none ∨ v.map (·.1) = some .nom

instance (v : Valuation) (o : Option Case) : Decidable (Realizes v o) := by
  cases o <;> simp only [Realizes] <;> infer_instance

/-- A row states a yes/no property. -/
def yes (r : LinguisticExample) (k : String) : Bool := r.feature? k = some "yes"

/-- An NP of a row's domain: its position, whether it is covert, whether it is adjacent to
    the verb, and the case its gloss shows. -/
structure Occupant where
  np : PhasedNP
  covert : Bool := false
  adjacent : Bool := false
  observed : Option Case := none
  deriving DecidableEq, Repr

/-- Where a slot is merged: a possessor in the noun phrase, the objects, goal, causee and
    raised subject in the verb phrase, the subject in the clause unless the predicate is
    unaccusative or takes a dative subject. -/
def Slot.phase (r : LinguisticExample) : Slot → Cat
  | .subject =>
    if yes r "unaccusative" || r.feature? "subjectPosition" = some "internal" then .v else .C
  | .causee | .goal | .raised | .object => .v
  | .pObject => .C
  | .possessor => .D

/-- Whether a VP-merged NP shifts to the clause edge: a specific one does, a nonspecific one
    does not, a raised subject always does, and the paper leaves the rest free. -/
def Slot.shifts (r : LinguisticExample) (s : Slot) : List Bool :=
  match s.phase r with
  | .v =>
    if s = .raised then [true]
    else match r.feature? (s.key ++ "Specific") with
      | some "yes" => [true]
      | some "no" => [false]
      | _ => [false, true]
  | _ => [false]

/-- The occupants a stated slot contributes, one per shift option. -/
def Slot.occupants (r : LinguisticExample) (s : Slot) : Option (List Occupant) :=
  ((r.feature? (s.key ++ "Case")).bind parseCase?).map λ c =>
    (s.shifts r).map λ sh =>
      { np := { label := s.key, phase := s.phase r, shifted := sh },
        adjacent := yes r (s.key ++ "Adjacent"), observed := c }

/-- The covert agent: forced in a passive with an agent-oriented adverb and in an agentive
    nominalization, excluded when the subject is overt or the predicate unaccusative, and
    otherwise free in a passive or event nominalization. -/
def agentOptions (r : LinguisticExample) : List (List Occupant) :=
  if (r.feature? "subjectCase").isSome || yes r "unaccusative" then [[]]
  else if yes r "agentOrientedAdverb" || r.feature? "construction" = some "agentiveNominal" then
    [[{ np := pro, covert := true }]]
  else match r.feature? "construction" with
    | some "passive" | some "eventNominal" => [[{ np := pro, covert := true }], []]
    | _ => [[]]

/-- The domains a row may have: the covert agent, then each stated slot under each of its
    shift options. -/
def candidates (r : LinguisticExample) : List (List Occupant) :=
  (Slot.all.foldr (λ s acc => match s.occupants r with
      | none => acc
      | some vs => vs.flatMap λ o => acc.map (o :: ·)) [[]]).flatMap λ d =>
    (agentOptions r).map (· ++ d)

/-- The probes a row's morphology shows: finite T where the verb agrees, the head noun's D
    reaching into the clause where it agrees with the subject, and the possessed noun's D
    where it agrees with its possessor. -/
def probes (r : LinguisticExample) : List (Cat × Cat) :=
  (if yes r "verbAgreement" then [(Cat.T, Cat.C)] else []) ++
    (if yes r "headNounAgreement" then [(Cat.D, Cat.C)] else []) ++
    (if yes r "possesseeAgreement" then [(Cat.D, Cat.D)] else [])

/-- The valuations of a domain, paired with its occupants. -/
def derive (g : CaseGrammar) (r : LinguisticExample) (d : List Occupant) :
    List (Occupant × Valuation) :=
  d.zip ((g.assign (probes r) (d.map (·.np))).map (·.2))

/-- The Case filter: a caseless overt NP must be pseudo-incorporated — an unshifted
    VP-internal NP adjacent to the verb. -/
def Licensed (o : Occupant) (v : Valuation) : Prop :=
  o.covert = true ∨ v.isSome ∨ (o.np.phase = .v ∧ o.np.shifted = false ∧ o.adjacent = true)

instance (o : Occupant) (v : Valuation) : Decidable (Licensed o v) := by
  unfold Licensed; infer_instance

/-- T agrees with the NP it values nominative: where a row states the verb's agreement
    target, an overt NP is nominative by Agree exactly when it is that target, so default
    agreement means no NP is. -/
def Agrees (r : LinguisticExample) (out : List (Occupant × Valuation)) : Prop :=
  (r.feature? "agreesWith").isSome → ∀ p ∈ out, p.1.covert = false →
    (p.2 = some (.nom, .agree) ↔ r.feature? "agreesWith" = some p.1.np.label)

instance (r : LinguisticExample) (out : List (Occupant × Valuation)) :
    Decidable (Agrees r out) := by
  unfold Agrees; infer_instance

/-- A domain derives the row under a grammar: every overt NP gets the case its gloss shows,
    and under the Chomskian half — the Case filter and the case–agreement link — is licensed
    and agreed with accordingly. -/
def Derives (g : CaseGrammar) (chomskian : Bool) (r : LinguisticExample) (d : List Occupant) :
    Prop :=
  (∀ p ∈ derive g r d, p.1.covert = false →
    Realizes p.2 p.1.observed ∧ (chomskian = true → Licensed p.1 p.2)) ∧
  (chomskian = true → Agrees r (derive g r d))

instance (g : CaseGrammar) (chomskian : Bool) (r : LinguisticExample) (d : List Occupant) :
    Decidable (Derives g chomskian r d) := by
  unfold Derives; infer_instance

/-- Some choice of structure derives the row. -/
def Derivable (g : CaseGrammar) (chomskian : Bool) (r : LinguisticExample) : Prop :=
  ∃ d ∈ candidates r, Derives g chomskian r d

instance (g : CaseGrammar) (chomskian : Bool) (r : LinguisticExample) :
    Decidable (Derivable g chomskian r) := by
  unfold Derivable; infer_instance

/-- Each of the paper's Sakha examples is acceptable exactly when some structure derives the
    cases it shows under the two-modality grammar with the Case filter and the
    case–agreement link. -/
theorem rows_case :
    ∀ r ∈ Examples.all, r.judgment = .acceptable ↔ Derivable grammar true r := by
  decide

/-- Without the Case filter and the case–agreement link, the configurational grammar derives
    a rejected example — a bare object separated from the verb, an unagreed-with subject of a
    participial clause, a passive whose verb agrees with nothing though its theme is
    nominative. -/
theorem pure_marantz_overgenerates :
    ∃ r ∈ Examples.all, r.judgment = .unacceptable ∧ Derivable pureMarantz false r := by
  decide

end BakerVinokurova2010
