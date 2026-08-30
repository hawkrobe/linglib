import Linglib.Core.Optimization.Linearization
import Linglib.Fragments.Turkish.Anaphors
import Linglib.Data.Examples.BakayEtAl2026
import Mathlib.Tactic.DeriveFintype

/-!
# Bakay, Akkuş & Dillon 2026: hierarchical relations in antecedent retrieval

Three visual-world experiments ask whether c-command between noun phrases within one clause
guides antecedent retrieval for the Turkish reciprocal *birbirleri*, deconfounded from
clause-mateness, case marking, subjecthood and linear order, which earlier studies had let
stand in for hierarchy and which can be stored as item-level features. Targets and distractors
share the embedded clause and the case ending: an embedded subject against a possessor inside
the subject or inside an adjunct, and an indirect object against the complement of a
postposition. Looks go to the c-commanding target immediately at the reciprocal, whether it
precedes or follows the distractor and whether or not the distractor matches the reciprocal in
number; a pre-registered replication confirms it. A cue-based account can carry this only if a
dynamically assigned feature approximates c-command and hierarchical cues weigh more than the
rest; a representational account instead grants c-commanding items a privileged store. Both
predict the target advantage and part company only on interference from feature-matching
distractors, which the paper finds limited and inconsistent.

## Main definitions

* `Cue`, `matchCount`, `weightedActivation`, `dominance`: activation as a weighted cue-match
  count, and pointwise dominance of match vectors.
* `Configuration`, `Role`: the three stimulus structures, with `Role.available` and
  `Role.features` read off the geometry.
* `birbirleriCues`: the cue bundle, with the number cue supplied by the fragment.
* `privileged`: the representational rival.
* `rows_available`, `rows_target_retrieved`: the paper's coindexations and the target
  advantage, per stimulus.

## References

* [bakay-etal-2026]
* [lewis-vasishth-2005] — cue-based retrieval
* [kush-2013] — the dynamically assigned locality feature
* [mcelree-2006], [oberauer-2002] — direct access and the privileged region
* [reinhart-1976], [barker-pullum-1990] — c-command on tree addresses
* [pollard-sag-1994] — the coargumenthood alternative
-/

namespace BakayEtAl2026

open Data.Examples

/-- A direction in a binary tree. -/
inductive Dir
  | L
  | R
  deriving DecidableEq

/-- A tree address: the path from the root. -/
abbrev Address := List Dir

/-- The sister of an address: its last direction flipped. -/
def sister : Address → Option Address
  | [] => none
  | [.L] => some [.R]
  | [.R] => some [.L]
  | d :: rest => (sister rest).map (d :: ·)

/-- C-command on addresses ([reinhart-1976]): the sister of `a` dominates `b`. -/
def cCommand (a b : Address) : Bool := (sister a).elim false (·.isPrefixOf b)

/-! ### Cue-based retrieval -/

/-- Where a retrieval cue comes from: a relation between the retrieval site and the candidate,
    a feature stored with the candidate, or the candidate's position. -/
inductive CueSource
  | relational
  | itemLevel
  | positional
  deriving DecidableEq, Fintype, Repr

/-- A retrieval cue: a required feature tagged with its source. -/
structure Cue (F : Type*) where
  source : CueSource
  feature : F
  deriving Repr

variable {F : Type*} [DecidableEq F]

/-- The cues from source `s` that a memory item's feature bundle matches. -/
def matchCount (feats : List F) (cues : List (Cue F)) (s : CueSource) : ℕ :=
  cues.countP λ c => decide (c.source = s ∧ c.feature ∈ feats)

/-- Activation as a weighted count of cue matches. -/
def weightedActivation (w : CueSource → ℕ) (feats : List F) (cues : List (Cue F)) : ℕ :=
  ∑ s, w s * matchCount feats cues s

/-- An item whose match vector pointwise dominates another's, strictly at a positively
    weighted source, out-activates it under every such weighting. -/
theorem dominance {w : CueSource → ℕ} {a b : List F} {cues : List (Cue F)}
    (hle : ∀ s, matchCount b cues s ≤ matchCount a cues s)
    (hlt : ∃ s, 0 < w s ∧ matchCount b cues s < matchCount a cues s) :
    weightedActivation w b cues < weightedActivation w a cues :=
  Core.Optimization.sum_mul_lt_sum_mul hle hlt

/-! ### The stimuli -/

/-- Grammatical number. -/
inductive Number
  | plural
  | singular
  deriving DecidableEq, Repr

/-- The case endings the stimuli carry. -/
inductive Marking
  | genitive
  | dative
  deriving DecidableEq, Repr

/-- Features relevant to retrieving an antecedent for *birbirleri*; `cCommanding` is the
    dynamically assigned feature that approximates the relation. -/
inductive Feature
  | cCommanding
  | clauseMate
  | number (n : Number)
  | marking (m : Marking)
  deriving DecidableEq, Repr

/-- The item-level number cue, generated exactly when the fragment's anaphor type imposes a
    plurality requirement on its antecedent. -/
def numberCues : List (Cue Feature) :=
  if Turkish.Anaphors.birbirleriAcc.anaphorType.requiresPluralAntecedent then
    [⟨.itemLevel, .number .plural⟩]
  else []

/-- The cues generated on encountering *birbirleri*: Principle A supplies the relational
    c-command cue and the clause-mate cue, the fragment the number cue. -/
def birbirleriCues : List (Cue Feature) :=
  ⟨.relational, .cCommanding⟩ :: ⟨.itemLevel, .clauseMate⟩ :: numberCues

/-- The three embedded-clause structures: a possessor inside the subject, or a second noun
    phrase inside the verb phrase — an indirect object, or the complement of a postposition or
    a possessed adjunct noun. -/
inductive Configuration
  | possessorInSubject
  | secondInVP
  deriving DecidableEq

/-- The noun phrases of a stimulus. -/
inductive Role
  | matrixSubject
  | embeddedSubject
  | indirectObject
  | distractor
  deriving DecidableEq

/-- Whether a noun phrase shares the reciprocal's clause. -/
def Role.clauseMate : Role → Bool
  | .matrixSubject => false
  | _ => true

/-- Tree addresses within the embedded clause: the subject is its left daughter; a second
    noun phrase is the left daughter of the verb phrase, a possessor or a postposition's
    complement one step further down; the reciprocal is the left daughter of the lowest verbal
    projection. -/
def Configuration.anaphor : Configuration → Address
  | .possessorInSubject => [.R, .L]
  | .secondInVP => [.R, .R, .L]

/-- The address of a clause-mate noun phrase. -/
def Configuration.address : Configuration → Role → Address
  | _, .embeddedSubject => [.L]
  | .possessorInSubject, _ => [.L, .L]
  | .secondInVP, .indirectObject => [.R, .L]
  | .secondInVP, _ => [.R, .L, .L]

/-- Principle A: an available antecedent is a clause-mate that c-commands the reciprocal. -/
def Role.available (cfg : Configuration) (r : Role) : Prop :=
  r.clauseMate = true ∧ cCommand (cfg.address r) cfg.anaphor = true

instance (cfg : Configuration) (r : Role) : Decidable (r.available cfg) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The feature bundle of a clause-mate noun phrase: the c-command feature read off the
    geometry, the clause index, its number, and its case. -/
def Role.features (cfg : Configuration) (r : Role) (n : Number) (m : Marking) : List Feature :=
  (if cCommand (cfg.address r) cfg.anaphor then [.cCommanding] else []) ++
    [.clauseMate, .number n, .marking m]

/-- A subject and an indirect object c-command the reciprocal; a possessor and a postposition's
    complement do not. -/
theorem available_iff (cfg : Configuration) (r : Role) :
    r.available cfg ↔ (r = .embeddedSubject ∨ (cfg = .secondInVP ∧ r = .indirectObject)) := by
  cases cfg <;> cases r <;> decide

/-- The target out-activates a distractor of any number and case, for every weighting with
    positive relational weight: with item-level cues tied, only the relational cue separates
    them. -/
theorem target_retrieved (cfg : Configuration) (w : CueSource → ℕ) (hw : 0 < w .relational)
    (n : Number) (mT mD : Marking) :
    weightedActivation w (Role.features cfg .distractor n mD) birbirleriCues <
      weightedActivation w (Role.features cfg .embeddedSubject .plural mT) birbirleriCues := by
  refine dominance (λ s => ?_) ⟨.relational, hw, ?_⟩
  · cases cfg <;> cases s <;> cases n <;> cases mD <;> cases mT <;> decide
  · cases cfg <;> cases n <;> cases mD <;> cases mT <;> decide

/-! ### The privileged representation -/

/-- Direct access by structural position: a noun phrase is privileged at a retrieval site iff
    it c-commands it, whatever its features. -/
def privileged (cfg : Configuration) (r : Role) : Prop :=
  cCommand (cfg.address r) cfg.anaphor = true

/-- The privileged region holds exactly the c-commanders: the subject and, in the verb
    phrase, the indirect object. -/
theorem privileged_iff (cfg : Configuration) (r : Role) (hr : r ≠ .matrixSubject) :
    privileged cfg r ↔ r.available cfg := by
  cases r <;> simp_all [privileged, Role.available, Role.clauseMate]

/-! ### The paper's stimuli -/

/-- A row's configuration, from its distractor or second noun phrase. -/
def configuration? (r : LinguisticExample) : Option Configuration :=
  match r.feature? "distractor", r.feature? "second" with
  | some "possessor in subject", _ => some .possessorInSubject
  | some "possessor in adjunct", _ | some "postpositional adjunct", _ => some .secondInVP
  | _, some "indirect object" => some .secondInVP
  | _, _ => none

/-- A reading's noun phrase. -/
def Role.parse? : String → Option Role
  | "matrix subject" => some .matrixSubject
  | "embedded subject" => some .embeddedSubject
  | "indirect object" => some .indirectObject
  | "distractor" => some .distractor
  | _ => none

/-- A row's distractor number. -/
def distractorNumber? (r : LinguisticExample) : Option Number :=
  match r.feature? "distractorNumber" with
  | some "plural" => some .plural
  | some "singular" => some .singular
  | _ => none

/-- A row's distractor case: genitive on possessors, dative under a postposition. -/
def distractorCase? (r : LinguisticExample) : Option Marking :=
  match r.feature? "distractor" with
  | some "possessor in subject" | some "possessor in adjunct" => some .genitive
  | some "postpositional adjunct" => some .dative
  | _ => none

/-- Each row's coindexation is Principle A on its geometry: the embedded subject and an
    indirect object are available, the matrix subject and the distractors are not. -/
theorem rows_available :
    ∀ r ∈ Examples.all, ∀ cfg ∈ configuration? r, ∀ x ∈ r.readings, ∀ role ∈ Role.parse? x.1,
      (x.2 = .acceptable ↔ role.available cfg) := by
  decide

/-- In every stimulus with a distractor, the plural embedded subject out-activates it under
    any positive relational weight, whatever the distractor's number or case. -/
theorem rows_target_retrieved (w : CueSource → ℕ) (hw : 0 < w .relational) :
    ∀ r ∈ Examples.all, ∀ cfg ∈ configuration? r, ∀ num ∈ distractorNumber? r,
      ∀ cas ∈ distractorCase? r,
        weightedActivation w (Role.features cfg .distractor num cas) birbirleriCues <
          weightedActivation w (Role.features cfg .embeddedSubject .plural .genitive)
            birbirleriCues :=
  λ _ _ cfg _ num _ cas _ => target_retrieved cfg w hw num .genitive cas

end BakayEtAl2026
