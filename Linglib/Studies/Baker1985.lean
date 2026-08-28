import Linglib.Data.Examples.Baker1985
import Linglib.Morphology.Morphotactics.MirrorPrinciple

/-!
# Baker 1985: the Mirror Principle

Processes like passive, causative, applicative and reciprocal formation each add an affix to
the verb and rearrange the grammatical functions of its arguments. The Mirror Principle says
the two derivations must match: affix order outward from the root is the order in which the
syntactic components applied. Given the independently known behaviour of each process, this
explains why Chamorro's plural agreement *fan-* registers the surface subject outside the
passive marker, the semantic subject inside the causative marker, and an intermediate subject
between the two; why a reciprocal inside a causative links the root's agent and patient while a
causative inside a reciprocal links the causer to the patient in Quechua but to the agent in
Bemba, whose causative makes the old subject the object; and why an applied argument becomes
the passive subject only with the applied affix inside the passive affix, so that the
patient-subject reading is out in Chi-Mwi:ni and in only in Kinyarwanda, whose passive reaches
a second object independently. Across languages, an agreement morpheme inside a GF-rule
morpheme references semantic functions and one outside it surface functions; the other two
combinations do not occur.

## Main definitions

* `Stage`, `Grammar`, `Process.apply`: grammatical functions at a derivational stage and the
  syntactic component of each process, with the two causative types and the Kinyarwanda
  passive as language settings.
* `processes`, `derivation`: a row's processes in order of attachment, read off its
  segmentation, and the derivation they form; `outcomes` runs them.
* `IsAttested`, `isAttested_iff_deriveReference`: the agreement restriction, derived from
  derivational timing.
* `rows_surface`, `rows_agreement`, `rows_links`, `rows_subject`: the paper's examples, each
  derived from its morphology.

## References

* [baker-1985]
* [gibson-1980] — Chamorro
* [muysken-1981] — Quechua
* [givon-1976] — Bemba
* [comrie-1982], [kisseberth-abasheikh-1977], [kimenyi-1980] — Huichol, Chi-Mwi:ni,
  Kinyarwanda
-/

namespace Baker1985

open Morphology.MirrorPrinciple Data.Examples

/-! ### Grammatical-function rules -/

/-- The arguments a clause may host: the root's agent and patient, a causer, and the oblique an
    applicative promotes. -/
inductive Arg
  | agent
  | patient
  | causer
  | applied
  deriving DecidableEq, Repr

/-- Grammatical functions at a derivational stage, with the referential dependencies and the
    agreement registrations made so far; `second` holds an object an applicative displaced. -/
structure Stage where
  subj : Arg
  obj : Option Arg := none
  second : Option Arg := none
  obl : List Arg := []
  links : List (Arg × Arg) := []
  registered : List Arg := []
  deriving DecidableEq, Repr

/-- The two causative types: the Quechua type leaves a transitive root's object in place and
    demotes its subject, the Chamorro type makes the old subject the object. -/
inductive CausativeType
  | quechua
  | chamorro
  deriving DecidableEq

/-- What a language's rules consult: its causative type, and whether its passive can promote
    the object an applicative displaced. -/
structure Grammar where
  causative : CausativeType
  passivizeSecond : Bool := false

/-- A process with a morphological and a syntactic component: a GF-rule, or number
    agreement. -/
inductive Process
  | gf (r : GFRuleType)
  | agreement
  deriving DecidableEq, Repr

/-- The syntactic component of each process, as the stages it can yield: passive promotes the
    object (or, where the grammar allows, a displaced object) and demotes the subject; a
    causative adds the causer as subject; an applicative promotes the oblique to object,
    displacing the old one; reciprocal formation binds subject to object and makes the object
    the subject; number agreement registers the subject of an intransitive stage. -/
def Process.apply (g : Grammar) : Process → Stage → List Stage
  | .gf .passive, s =>
    (match s.obj with
      | some o => [{ s with subj := o, obj := none, obl := s.subj :: s.obl }]
      | none => []) ++
    (match s.second, g.passivizeSecond with
      | some o, true => [{ s with subj := o, second := none, obl := s.subj :: s.obl }]
      | _, _ => [])
  | .gf .causative, s =>
    match g.causative, s.obj with
    | .quechua, none => [{ s with subj := .causer, obj := some s.subj }]
    | .quechua, some _ => [{ s with subj := .causer, obl := s.subj :: s.obl }]
    | .chamorro, o => [{ s with subj := .causer, obj := some s.subj, obl := o.toList ++ s.obl }]
  | .gf .applicative, s =>
    if s.obl.contains .applied then
      [{ s with obj := some .applied, second := s.obj, obl := s.obl.erase .applied }]
    else []
  | .gf .reflexReciprocal, s =>
    match s.obj with
    | some o => [{ s with subj := o, obj := none, links := (s.subj, o) :: s.links }]
    | none => []
  | .agreement, s =>
    match s.obj with
    | none => [{ s with registered := s.subj :: s.registered }]
    | some _ => []

/-- The stages a sequence of processes can reach from a start. -/
def outcomes (g : Grammar) (ps : List Process) (s : Stage) : List Stage :=
  ps.foldl (λ ss p => ss.flatMap (p.apply g)) [s]

/-- An applied argument becomes the subject only with the applied affix inside the passive
    affix: with the passive applied first, no grammar yields it. -/
theorem applied_subject_needs_applicative_first (g : Grammar) (s : Stage)
    (hs : s.subj ≠ .applied) (ho : s.obj ≠ some .applied) (h2 : s.second ≠ some .applied) :
    ∀ st ∈ outcomes g [.gf .passive, .gf .applicative] s, st.subj ≠ .applied := by
  intro st hst
  obtain ⟨subj, obj, second, obl, links, registered⟩ := s
  rcases g with ⟨c, ps⟩
  cases obj <;> cases second <;> cases ps <;> aesop (add simp [outcomes, Process.apply])

/-! ### Agreement and derivational timing -/

/-- The attested agreement patterns: inner agreement referencing semantic functions and outer
    agreement referencing surface functions. -/
def IsAttested (p : AgreementPattern) : Prop :=
  p = ⟨.inner, .semantic⟩ ∨ p = ⟨.outer, .surface⟩

instance : DecidablePred IsAttested := λ p =>
  inferInstanceAs (Decidable (p = ⟨.inner, .semantic⟩ ∨ p = ⟨.outer, .surface⟩))

/-- The Mirror Principle derives the restriction: a pattern is attested exactly when its
    reference is the one derivational timing dictates for its position. -/
theorem isAttested_iff_deriveReference {p : AgreementPattern} :
    IsAttested p ↔ p.reference = deriveReference p.position := by
  obtain ⟨pos, ref⟩ := p
  cases pos <;> cases ref <;> decide

/-! ### The paper's examples -/

/-- A row's segmentation, as gloss labels in surface order. -/
def morphs (r : LinguisticExample) : List String :=
  ["m1", "m2", "m3", "m4", "m5", "m6"].filterMap r.feature?

/-- A row's root. -/
def root (r : LinguisticExample) : String := (r.feature? "root").getD ""

/-- The affixes before the root, outermost first. -/
def prefixes (r : LinguisticExample) : List String := (morphs r).takeWhile (· ≠ root r)

/-- The affixes after the root, innermost first. -/
def suffixes (r : LinguisticExample) : List String :=
  ((morphs r).dropWhile (· ≠ root r)).drop 1

/-- The process a gloss label marks. -/
def process? : String → Option Process
  | "PASS" => some (.gf .passive)
  | "CAUS" => some (.gf .causative)
  | "APPL" | "BEN" | "INSTR" => some (.gf .applicative)
  | "RECP" | "REFL" => some (.gf .reflexReciprocal)
  | "PL" => some .agreement
  | _ => none

/-- A row's derivation: its process-marking affixes in order of attachment — prefixes from the
    root outward, then suffixes — each on its side. -/
def derivation (r : LinguisticExample) : Derivation :=
  ((prefixes r).reverse.filterMap λ m => (process? m).map (·, m, Morphology.Morph.Side.before)) ++
    ((suffixes r).filterMap λ m => (process? m).map (·, m, Morphology.Morph.Side.after))
  |>.filterMap λ (x : Process × String × Morphology.Morph.Side) =>
    match x with
    | (.gf g, m, side) => some ⟨g, m, side⟩
    | (.agreement, _, _) => none

/-- A row's processes in order of attachment, agreement included. -/
def processes (r : LinguisticExample) : List Process :=
  ((prefixes r).reverse ++ suffixes r).filterMap process?

/-- The stage a root starts from: an agent, a patient if transitive, and an oblique for an
    applicative to promote. -/
def initial (r : LinguisticExample) : Stage :=
  { subj := .agent, obj := if r.feature? "valence" = some "transitive" then some .patient else none,
    obl := [.applied] }

/-- A row's language settings: Chamorro and Bemba have the Chamorro causative, Quechua its
    own; Kinyarwanda's passive reaches a displaced object. -/
def grammar? (r : LinguisticExample) : Option Grammar :=
  match r.language with
  | "cham1312" | "bemb1257" | "huic1243" | "chim1312" => some ⟨.chamorro, false⟩
  | "quec1387" => some ⟨.quechua, false⟩
  | "kiny1244" => some ⟨.chamorro, true⟩
  | _ => none

/-- The GF-rule affixes of a row's derivation, on their sides around the root, are a
    subsequence of its segmentation: the Mirror Principle's linearization. -/
theorem rows_surface :
    ∀ r ∈ Examples.all, (surface (root r) (derivation r)).Sublist (morphs r) := by
  decide +kernel

/-- Which subject a registration matches: the surface subject, the semantic subject, or
    neither. -/
def agreesWith (start final : Stage) : Option String :=
  match final.registered with
  | [x] =>
    some (if x = final.subj then "surface subject"
      else if x = start.subj then "semantic subject" else "intermediate subject")
  | _ => none

/-- Every Chamorro row's *fan-* registers the subject the paper says it does: the surface
    subject outside the passive, the semantic subject inside the causative, and the subject
    between passive and causative in their combination. -/
theorem rows_agreement :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ w ∈ r.feature? "agreesWith",
      ∀ st ∈ outcomes g (processes r) (initial r), agreesWith (initial r) st = some w := by
  decide

/-- A row's agreement pattern relative to its single GF-rule: position from the affix order,
    reference from the registration. -/
def pattern? (r : LinguisticExample) (st : Stage) : Option AgreementPattern :=
  match (processes r).filter (· ≠ .agreement), agreesWith (initial r) st with
  | [g], some "surface subject" =>
    some ⟨if (processes r).idxOf .agreement < (processes r).idxOf g then .inner else .outer,
      .surface⟩
  | [g], some "semantic subject" =>
    some ⟨if (processes r).idxOf .agreement < (processes r).idxOf g then .inner else .outer,
      .semantic⟩
  | _, _ => none

/-- The Chamorro passive and causative rows instantiate the two attested patterns. -/
theorem rows_pattern_attested :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ st ∈ outcomes g (processes r) (initial r),
      ∀ p ∈ pattern? r st, IsAttested p := by
  decide

/-- The dependency a row's translation records. -/
def links? (r : LinguisticExample) : Option (Arg × Arg) :=
  match r.feature? "links" with
  | some "agent-patient" => some (.agent, .patient)
  | some "causer-patient" => some (.causer, .patient)
  | some "causer-agent" => some (.causer, .agent)
  | _ => none

/-- Reciprocal formation links the root's agent and patient when it applies before the
    causative, and the causer to the patient (Quechua) or the agent (Bemba) when after. -/
theorem rows_links :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ l ∈ links? r,
      ∀ st ∈ outcomes g (processes r) (initial r), st.links = [l] := by
  decide

/-- The surface subject a row reports. -/
def surfaceSubject? (r : LinguisticExample) : Option Arg :=
  match r.feature? "surfaceSubject" with
  | some "applied object" => some .applied
  | some "patient" => some .patient
  | _ => none

/-- A passive of an applicative is acceptable exactly when some derivation in the affix order
    makes the reported argument the subject: the applied object everywhere, the patient only in
    Kinyarwanda. -/
theorem rows_subject :
    ∀ r ∈ Examples.all, ∀ g ∈ grammar? r, ∀ a ∈ surfaceSubject? r,
      (r.judgment = .acceptable ↔ ∃ st ∈ outcomes g (processes r) (initial r), st.subj = a) := by
  decide

end Baker1985
