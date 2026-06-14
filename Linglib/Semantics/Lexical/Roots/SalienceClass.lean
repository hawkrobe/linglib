import Linglib.Semantics.Lexical.Roots.Typology
import Linglib.Semantics.Lexical.Roots.Arity

/-!
# Lexical Salience Classes

[lucy-1994]'s classification of verbal roots by which argument(s) the
underived root form makes "salient" (default case-role assignment at
the propositional level): a 3-way salience cut by required
transitiviser — agent (`=t`), agent-patient (`=∅`), patient (`=s`) —
plus the separately-derived positional class (`-tal`), systematized
here as one enum.

The structural characterization of each class needs **two**
dimensions. Agent-patient salience is *root transitivity*: these roots
"require two arguments and refer to events involving the action of one
entity on another" ([lucy-1994]) — `Verb.Root.Arity.selectsTheme`, the
Mayan root-transitive class of [coon-2019]. It is NOT a B&K-G feature
configuration: *p'is* 'measure' and *lo'š* 'punch' are manner roots
with no entailed change of state. The two intransitive classes are
then separated by the signature (manner vs result), matching the
Sapir/Perlmutter unaccusativity split [lucy-1994] cites. This
two-dimensional characterization is a cross-framework reconstruction
([lucy-1994] predates both [coon-2019] and
[beavers-koontz-garboden-2020]), not Lucy's own formulation.

The full [lucy-1994] analysis — operator applicability,
motion-roots-non-class theorem, per-root verifications — lives in
`Studies/Lucy1994.lean`.

## Main declarations

* `SalienceClass`
* `IsAgentSalient`, `IsAgentPatientSalient`, `IsPatientSalient`,
  `IsPositional` — conditions over (signature × arity)
* `classOf` — the salience classifier
-/

/-- Salience classification of verbal roots ([lucy-1994]): the 3-way
    transitiviser cut plus the positional class. "Salience" is shorthand
    for "default case-role assignment at the propositional level" — *not*
    a substantive feature `[±agent]` written into the root. -/
inductive SalienceClass where
  /-- Underived intransitive whose argument is the agent. -/
  | agent
  /-- Underived transitive — both arguments lexically salient. -/
  | agentPatient
  /-- Underived intransitive whose argument is the patient. -/
  | patient
  /-- Stative root (positional / configurational). -/
  | positional
  deriving DecidableEq, Repr

/-! ### Named class conditions

Structural conditions characterising membership in each [lucy-1994]
salience class, over the pair (B&K-G feature signature × Coon arity).
These conditions are language-independent: the same conditions
characterise the class in any inventory whose transitivisers respect
the diagnostic. They appear directly as the `applies` field of each
Yukatek operator in `Fragments/Mayan/Yukatek/Operators.lean`, making
the operator-applicability ↔ salience-class connection true *by
construction* rather than only provable per-case. -/

/-- Agent-salient: intransitive manner-of-action root (requires `=t`
    to transitivise; [lucy-1994]: "actions or activities that some
    entity undertakes"). -/
def IsAgentSalient (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) : Prop :=
  ar = .noTheme ∧ .manner ∈ s ∧ .result ∉ s

instance (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) :
    Decidable (IsAgentSalient s ar) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Agent-patient salient: the root is lexically transitive — it
    "require[s] two arguments" ([lucy-1994]), i.e. selects a theme
    ([coon-2019]'s √TV). Signature-independent: root transitives need
    not entail any change of state (*p'is* 'measure'). -/
def IsAgentPatientSalient (ar : Verb.Root.Arity) : Prop :=
  ar = .selectsTheme

instance (ar : Verb.Root.Arity) : Decidable (IsAgentPatientSalient ar) :=
  inferInstanceAs (Decidable (_ = _))

/-- Patient-salient: intransitive change-of-state root (requires `=s`
    to transitivise; [lucy-1994]: "state changes that some entity
    undergoes more or less spontaneously"). -/
def IsPatientSalient (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) : Prop :=
  ar = .noTheme ∧ .manner ∉ s ∧ .result ∈ s

instance (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) :
    Decidable (IsPatientSalient s ar) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Positional: pure stative configurational root (requires `-tal`
    for the inchoative; [lucy-1994]). -/
def IsPositional (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) : Prop :=
  ar = .noTheme ∧ s = {.state}

instance (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) :
    Decidable (IsPositional s ar) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-! ### Salience classifier -/

/-- Map a (B&K-G feature signature × Coon arity) pair to its salience
    class ([lucy-1994]) by dispatching on the four named conditions,
    which align with operator applicability conditions in
    `Fragments/Mayan/Yukatek/Operators.lean`. -/
def classOf (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity) :
    Option SalienceClass :=
  if IsAgentPatientSalient ar then some .agentPatient
  else if IsAgentSalient s ar then some .agent
  else if IsPatientSalient s ar then some .patient
  else if IsPositional s ar then some .positional
  else none

/-! ### Pairwise disjointness of class conditions -/

/-- The four named conditions are pairwise disjoint: at most one fires
    on any (signature, arity) pair. (They are *jointly* not exhaustive
    — intransitive signatures with neither manner nor result that are
    not pure `{state}` fall outside all four; see
    `classOf_eq_none_iff`.) -/
theorem classes_pairwise_disjoint :
    ∀ (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity),
      ¬ (IsAgentSalient s ar ∧ IsAgentPatientSalient ar) ∧
      ¬ (IsAgentSalient s ar ∧ IsPatientSalient s ar) ∧
      ¬ (IsAgentSalient s ar ∧ IsPositional s ar) ∧
      ¬ (IsAgentPatientSalient ar ∧ IsPatientSalient s ar) ∧
      ¬ (IsAgentPatientSalient ar ∧ IsPositional s ar) ∧
      ¬ (IsPatientSalient s ar ∧ IsPositional s ar) := by
  decide

/-- `classOf s ar = none` iff the pair falls outside all four named
    conditions. Characterises the gap in the diagnostic: intransitive
    roots with neither a manner nor a result kind, other than pure
    `{state}`, are unclassified by Lucy's Yukatek diagnostic. -/
theorem classOf_eq_none_iff :
    ∀ (s : Verb.Root.FeatureSignature) (ar : Verb.Root.Arity),
      classOf s ar = none ↔
        ¬ IsAgentSalient s ar ∧ ¬ IsAgentPatientSalient ar ∧
        ¬ IsPatientSalient s ar ∧ ¬ IsPositional s ar := by
  decide
