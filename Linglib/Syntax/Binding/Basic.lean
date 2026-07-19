import Linglib.Data.UD.Basic
import Linglib.Features.CoreferenceStatus
import Linglib.Morphology.Word.Basic

open Morphology (Word)

/-!
# Binding principles over a command relation
[barker-pullum-1990] [chomsky-1981] [pollard-sag-1994]

A framework-neutral binding engine. The binding principles (A/B/C) and the
coreference-status computation are stated **once**, parameterized by a
`CommandRelation` — the structural-prominence order they range over. The three
syntactic frameworks formalized in linglib supply that relation and inherit the
principles unchanged:

* Minimalism — c-command (tree geometry)
* HPSG — ARG-ST outranking (obliqueness)
* Dependency grammar — d-command (dependency subgraph)

[barker-pullum-1990] give the general notion of which c-command,
m-command, and the rest are instances; the linglib frameworks' command notions
are further instances. Stating the principles over the abstract relation makes
the cross-framework convergence a theorem rather than a coincidence: any two
`CommandRelation`s that agree on a clause predict the same binding facts.

## Main declarations

* `Pos` — a binding position in a simple clause (subject / object).
* `SimpleClause` / `parseSimpleClause` — the clause representation the
  principles range over, and a surface-list parser.
* `CommandRelation` — the abstract command relation + locality (the only piece
  a framework supplies).
* `reflexiveLicensed` / `reciprocalLicensed` / `pronounLocallyFree` /
  `rExpressionFree` — Principles A / B / C, derived over `[CommandRelation]`,
  `Word.Agree`, and a binding-class classifier.
* `grammaticalForCoreference`, `computeCoreferenceStatus` — top-level
  predictions, derived once.

## Implementation notes

The binding-class classifier (`Word → Option BindingClass`) is a *language*
parameter, orthogonal to the *framework* parameter `CommandRelation`; it is
passed explicitly rather than baked in, so the engine imports no Fragment.
A language (English, …) supplies the classifier; a framework supplies the
command relation; a study combines them.
-/

/-- The φ-feature subset (person, number, gender) of a word. -/
def Morphology.Word.phi (w : Word) : UD.MorphFeatures :=
  { person := w.features.person, number := w.features.number,
    gender := w.features.gender }

/-- φ-agreement between two words: their person/number/gender features are
    compatible (an unspecified feature is a wildcard). A reflexive, symmetric
    *tolerance* relation on `Word` (not transitive), decided by the shared
    `UD.MorphFeatures.compatible`. The feature-based agreement check binding
    and concord consumers share — no surface-form gender lookup. -/
def Morphology.Word.Agree (w1 w2 : Word) : Prop := w1.phi.compatible w2.phi

instance (w1 w2 : Word) : Decidable (Word.Agree w1 w2) := by
  unfold Morphology.Word.Agree; infer_instance

@[refl] theorem Morphology.Word.Agree.refl (w : Word) : Word.Agree w w :=
  UD.MorphFeatures.compatible_self w.phi

/-- φ-agreement is symmetric — the docstring's "symmetric tolerance relation",
    as a theorem. -/
@[symm] theorem Morphology.Word.Agree.symm {w1 w2 : Word} (h : Word.Agree w1 w2) :
    Word.Agree w2 w1 := by
  unfold Morphology.Word.Agree at h ⊢
  rwa [UD.MorphFeatures.compatible_comm]

/-- φ-agreement is *not* transitive: an unspecified feature is a wildcard, so
    underspecified *they* agrees with both *she* and *he* while *she ≁ he*. -/
theorem Morphology.Word.Agree.not_transitive :
    ¬ ∀ w1 w2 w3 : Word, Word.Agree w1 w2 → Word.Agree w2 w3 → Word.Agree w1 w3 := by
  intro h
  exact absurd
    (h ⟨"she", .PRON, { person := some .third, number := some .Sing, gender := some .Fem }⟩
       ⟨"they", .PRON, { person := some .third }⟩
       ⟨"he", .PRON, { person := some .third, number := some .Sing, gender := some .Masc }⟩
       (by decide) (by decide))
    (by decide)

/-- φ-agreement entails number compatibility: the `HasNumber` mixin never
    diverges from the agreement check on `Word`. -/
theorem Morphology.Word.Agree.hasNumber_compatible {w1 w2 : Word} (h : w1.Agree w2) :
    HasNumber.Compatible w1 w2 :=
  UD.MorphFeatures.compatible_hasNumber (f1 := w1.phi) (f2 := w2.phi) h

-- `reflex` is deliberately not an agreement feature: a reflexive-marked token still
-- agrees with an unmarked one (the φ-projection drops it).
example : Word.Agree ⟨"sich", .PRON, { reflex := true }⟩ ⟨"Kind", .NOUN, {}⟩ := by decide

namespace Binding


open Features (BindingClass CoreferenceStatus)

/-- A binding position in a simple clause. The verb is not a binding position. -/
inductive Pos where
  | subject
  | object
  deriving DecidableEq, Repr

/-- A simple (mono-clausal, transitive-or-intransitive) clause: the
    representation binding principles range over. `semanticPl` records whether
    the subject *denotes* a plurality, which can diverge from morphosyntactic
    number ([rakosi-2019]); it defaults to the syntactic number. -/
structure SimpleClause where
  subject : Word
  verb : Word
  object : Option Word
  semanticPl : Bool := subject.features.number == some .Plur
  deriving Repr

/-- The `Word` at a position, if present. -/
def SimpleClause.at? (c : SimpleClause) : Pos → Option Word
  | .subject => some c.subject
  | .object => c.object

/-- Is this a nominal part-of-speech (proper noun, common noun, or pronoun)? A
    theory-neutral UPOS check the clause parser uses to recognize arguments. -/
def isNominalCat (cat : UD.UPOS) : Bool :=
  cat == .PROPN || cat == .NOUN || cat == .PRON

/-- The canonical, language-neutral binding-class source: a word's Principle A/B/C class read off
    its own UD morphology (`Reflex`, `PronType`) and category — *no* lexicon and *no* surface-form
    lookup. Reflexive morphology → anaphor; reciprocal `PronType` → reciprocal anaphor; any other
    pronoun → pronominal; a proper/common-noun category → R-expression; a non-nominal → `none`.
    This is the framework- *and* language-neutral default `Features.BindingSource Word`, replacing
    per-language form-string classifiers ([chomsky-1981]'s A/B/C classes as morphology). -/
def bindingClassOf : Features.BindingSource Word := fun w =>
  if w.features.reflex then some .reflexive
  else match w.features.pronType with
    | some .Rcp => some .reciprocal
    | _ =>
      if w.cat == .PRON then some .pronoun
      else if isNominalCat w.cat then some .rExpression
      else none

/-- Parse a surface word list into a simple clause: `[subj, verb, obj]` or
    `[subj, verb]`, requiring nominal subject/object and a verb. -/
def parseSimpleClause (ws : List Word) : Option SimpleClause :=
  match ws with
  | [subj, v, obj] =>
    if isNominalCat subj.cat && v.cat == .VERB && isNominalCat obj.cat then
      some { subject := subj, verb := v, object := some obj }
    else none
  | [subj, v] =>
    if isNominalCat subj.cat && v.cat == .VERB then
      some { subject := subj, verb := v, object := none }
    else none
  | _ => none

/-- A **command relation** ([barker-pullum-1990]): the structural-prominence
    order binding principles are defined over, together with the locality
    (same-binding-domain) restriction. The frameworks' c-command, ARG-ST
    outranking, and d-command are instances. This is the *only* component a
    syntactic framework must supply to obtain the binding principles. -/
class CommandRelation where
  /-- Does the element at position `i` structurally command the element at `j`? -/
  commands : SimpleClause → Pos → Pos → Prop
  /-- Are positions `i` and `j` within the same binding (locality) domain? -/
  sameDomain : SimpleClause → Pos → Pos → Prop
  /-- `commands` is decidable — frameworks compute it from concrete structure. -/
  commandsDec : (c : SimpleClause) → (i j : Pos) → Decidable (commands c i j)
  /-- `sameDomain` is decidable. -/
  sameDomainDec : (c : SimpleClause) → (i j : Pos) → Decidable (sameDomain c i j)

instance [CommandRelation] (c : SimpleClause) (i j : Pos) :
    Decidable (CommandRelation.commands c i j) := CommandRelation.commandsDec c i j

instance [CommandRelation] (c : SimpleClause) (i j : Pos) :
    Decidable (CommandRelation.sameDomain c i j) := CommandRelation.sameDomainDec c i j

variable [CommandRelation]

-- The classifier mapping a word to its binding class is a language parameter
-- (English supplies one); the engine stays Fragment-free.
variable (classify : Word → Option BindingClass)

/-! ### Principle A (anaphors) -/

/-- **Principle A.** A reflexive object is licensed iff it is commanded by the
    subject within the local domain *and* agrees with it in φ-features
    (`Word.Agree`). Vacuously true when the object is not a reflexive. -/
def reflexiveLicensed (c : SimpleClause) : Prop :=
  match c.object with
  | none => False
  | some obj =>
    match classify obj with
    | some .reflexive =>
      CommandRelation.commands c .subject .object ∧
      CommandRelation.sameDomain c .subject .object ∧
      Word.Agree c.subject obj
    | _ => True

instance (c : SimpleClause) : Decidable (reflexiveLicensed classify c) := by
  unfold reflexiveLicensed; split
  · infer_instance
  · split <;> infer_instance

/-- **Principle A** for reciprocals: licensed iff commanded by the subject in
    the local domain and the subject denotes a *plurality* (an LF condition —
    semantic, not morphosyntactic, plurality; [rakosi-2019]). -/
def reciprocalLicensed (c : SimpleClause) : Prop :=
  match c.object with
  | none => False
  | some obj =>
    match classify obj with
    | some .reciprocal =>
      CommandRelation.commands c .subject .object ∧
      CommandRelation.sameDomain c .subject .object ∧
      c.semanticPl = true
    | _ => True

instance (c : SimpleClause) : Decidable (reciprocalLicensed classify c) := by
  unfold reciprocalLicensed; split
  · infer_instance
  · split <;> infer_instance

/-! ### Principle B (pronouns) -/

/-- **Principle B.** A pronoun object must be free in its local domain: it must
    *not* be both commanded by the subject and in the same domain. -/
def pronounLocallyFree (c : SimpleClause) : Prop :=
  match c.object with
  | none => True
  | some obj =>
    match classify obj with
    | some .pronoun =>
      ¬ (CommandRelation.commands c .subject .object ∧
         CommandRelation.sameDomain c .subject .object)
    | _ => True

instance (c : SimpleClause) : Decidable (pronounLocallyFree classify c) := by
  unfold pronounLocallyFree; split
  · infer_instance
  · split <;> infer_instance

/-! ### Principle C (R-expressions) -/

/-- **Principle C.** An R-expression object coindexed with a pronominal subject
    is blocked when the subject commands it. -/
def rExpressionFree (c : SimpleClause) : Prop :=
  match classify c.subject with
  | some .pronoun =>
    match c.object with
    | some obj =>
      match classify obj with
      | some .rExpression => ¬ CommandRelation.commands c .subject .object
      | _ => True
    | none => True
  | _ => True

instance (c : SimpleClause) : Decidable (rExpressionFree classify c) := by
  unfold rExpressionFree
  split
  · split
    · split <;> infer_instance
    · infer_instance
  · infer_instance

/-! ### Top-level acceptability -/

/-- Is a surface word list grammatical for coreference? Anaphors cannot be
    subjects (no commander); a pronoun object locally commanded by the subject
    violates Principle B; reflexive/reciprocal objects must be licensed. -/
def grammaticalForCoreference (ws : List Word) : Prop :=
  match parseSimpleClause ws with
  | none => False
  | some c =>
    match classify c.subject with
    | some .reflexive => False
    | some .reciprocal => False
    | _ =>
      match c.object with
      | none => True
      | some obj =>
        match classify obj with
        | some .reflexive => reflexiveLicensed classify c
        | some .reciprocal => reciprocalLicensed classify c
        | some .pronoun => False
        | _ => True

instance (ws : List Word) : Decidable (grammaticalForCoreference classify ws) := by
  unfold grammaticalForCoreference; split
  · infer_instance
  · split
    · infer_instance
    · infer_instance
    · split
      · infer_instance
      · split <;> infer_instance

/-- Coreference status of positions `i`, `j` under the command relation:
    Principle A makes a commanded anaphor obligatorily coreferent; Principle B/C
    block a commanded pronoun/R-expression; otherwise coreference is possible. -/
def computeCoreferenceStatus (c : SimpleClause) (i j : Pos) : CoreferenceStatus :=
  match c.at? j with
  | none => .unspecified
  | some tgt =>
    if CommandRelation.commands c i j ∧ CommandRelation.sameDomain c i j then
      match classify tgt with
      | some .reflexive => .obligatory
      | some .reciprocal => .obligatory
      | some .pronoun => .blocked
      | some .rExpression => .blocked
      | none => .unspecified
    else
      match classify tgt with
      | some .reflexive => .blocked
      | some .reciprocal => .blocked
      | some .pronoun => .possible
      | some .rExpression => .possible
      | none => .unspecified

/-! ### Cross-framework convergence

Stated over the abstract relation, the principles depend on the framework only
through `CommandRelation`. Two frameworks that agree on a clause's command and
locality facts therefore make identical binding predictions — by construction,
not coincidence. -/

omit [CommandRelation] in
/-- If two command relations agree on the relevant command and locality facts
    of a clause, they license a reflexive identically. The cross-framework
    convergence the prose comparisons assert, made a theorem. -/
theorem reflexiveLicensed_congr
    (R₁ R₂ : CommandRelation) (classify : Word → Option BindingClass)
    (c : SimpleClause)
    (hc : R₁.commands c .subject .object ↔ R₂.commands c .subject .object)
    (hd : R₁.sameDomain c .subject .object ↔ R₂.sameDomain c .subject .object) :
    @reflexiveLicensed R₁ classify c ↔ @reflexiveLicensed R₂ classify c := by
  rcases hobj : c.object with _ | obj
  · simp only [reflexiveLicensed, hobj]
  · rcases hbc : classify obj with _ | bc
    · simp only [reflexiveLicensed, hobj, hbc]
    · cases bc <;> simp only [reflexiveLicensed, hobj, hbc, hc, hd]

end Binding
