import Linglib.Features.Definiteness
import Linglib.Semantics.Definiteness.Description
import Linglib.Semantics.Definiteness.Interpret
import Linglib.Semantics.Presupposition.MaximizePresupposition
import Linglib.Semantics.Kinds.MeaningPreservation
import Linglib.Semantics.Classifier.Basic
import Linglib.Studies.Schwarz2009
import Linglib.Syntax.Determiner.Basic
import Linglib.Semantics.Definiteness.DeterminerLicensing
import Linglib.Fragments.Mandarin.Definiteness
import Linglib.Fragments.Cantonese.Definiteness

/-!
# Jenks (2018): Articulated Definiteness without Articles
[jenks-2018]

Mandarin distinguishes **unique** definites (bare N) from **anaphoric**
definites (Dem-Clf-N), with a documented exception for matrix subjects
(§5.3). A Chierchia-style ι type-shift handles the bare-N route
([chierchia-1998], [yang-2001], [dayal-2004],
[jiang-2012]); demonstratives carry an indexical argument supplying
ι^x (a Schwarz-style strong article); an `Index!` principle (Heim 1990
Maximize Presupposition + [schlenker-2012] Gricean reduction)
selects between them.

The substrate already operationalizes the inventory layer:
`Semantics.Definiteness.Description.{unique,anaphoric}` are ι and ι^x;
`Semantics.Definiteness.Determiner.markingStrategy` derives the four-cell
typology directly named after Jenks 2018 in `Features.Definiteness`.
The Mandarin Fragment commits `marking := .markedAnaphoric`.
This file focuses on what is distinctly Jenks: the typological
prediction (§3 + §6), the bare/Dem competition (§5 paper), the
covarying-readings argument for index binding (§4.3 paper), and the
subject-as-topic exception (§5.3 paper). The post-Jenks Shan refutation
lives in `Moroney2021.lean` per chronology discipline.
-/

namespace Jenks2018

open Features.Definiteness
open Intensional
open Intensional.Variables
open Semantics.Definiteness

abbrev mandarinDets := Mandarin.Definiteness.determiners
abbrev cantoneseDets := Cantonese.Definiteness.determiners

-- ════════════════════════════════════════════════════════════════
-- §1: The Jenks Four-Cell Typology and Mandarin's Cell
-- ════════════════════════════════════════════════════════════════

/-! Jenks 2018 §6.2 (Table 2) lays out a four-cell typology of
definiteness marking. The cells in linglib substrate vocabulary:

| Inventory                       | Strategy            | Languages            |
|---------------------------------|---------------------|----------------------|
| both forms, distinct            | `.bipartite`        | German, Lakhota      |
| only anaphoric form             | `.markedAnaphoric`  | Mandarin, Akan, Wu   |
| both forms, syncretic           | `.generallyMarked`  | Cantonese, English   |
| only unique form                | (unattested)        | —                    |

Jenks proposes the unattested fourth cell as a typological gap and
gives it a historical explanation (Greenberg 1978: definite articles
typically grammaticalize from demonstratives and so first appear in
anaphoric contexts). -/

/-- The three Jenks-attested marking strategies (Table 2). Lifted to
    the substrate level here so consumers (e.g. Moroney's refutation)
    can `import` the prediction without reciting the list. -/
def jenksAttestedStrategies : List DefMarkingStrategy :=
  [.bipartite, .markedAnaphoric, .generallyMarked]

/-- Jenks's three attested cells are pairwise distinct. -/
theorem jenks_attested_distinct :
    DefMarkingStrategy.bipartite ≠ .markedAnaphoric ∧
    DefMarkingStrategy.bipartite ≠ .generallyMarked ∧
    DefMarkingStrategy.markedAnaphoric ≠ .generallyMarked := by decide

/-- Mandarin's determiner set derives `.markedAnaphoric` — its
    Jenks (2018) Table 2 cell. -/
theorem mandarin_jenks_cell :
    Determiner.markingStrategy mandarinDets = .markedAnaphoric :=
  Mandarin.Definiteness.marking

/-- Mandarin's strategy is in the Jenks-attested set. -/
theorem mandarin_attested :
    Determiner.markingStrategy mandarinDets ∈ jenksAttestedStrategies := by
  rw [mandarin_jenks_cell]; decide

/-- Cantonese's determiner set derives `.generallyMarked` — paper §6
    (Table 1, Table 2): [Clf-N] is an ambiguous definite like English *the*,
    covering both unique and anaphoric environments. -/
theorem cantonese_jenks_cell :
    Determiner.markingStrategy cantoneseDets = .generallyMarked :=
  Cantonese.Definiteness.marking

/-- Mandarin and Cantonese instantiate distinct Jenks cells — the
    central typological contrast of paper §6. -/
theorem mandarin_cantonese_distinct_cells :
    Determiner.markingStrategy mandarinDets ≠ Determiner.markingStrategy cantoneseDets := by
  rw [mandarin_jenks_cell, cantonese_jenks_cell]; decide

-- ════════════════════════════════════════════════════════════════
-- §2: Inventory-Licensing Predictions (paper §3)
-- ════════════════════════════════════════════════════════════════

variable {E W : Type}

/-- Bare N is universally licensed by the article inventory; in
    Mandarin it serves unique definites (paper §3.1 examples 10–11:
    `yueliang sheng shang lai le` 'the moon has risen';
    `Hufei he-wan-le tang` 'Hufei finished the soup';
    `Gou yao guo malu` 'the dog wants to cross the road'). -/
theorem bare_licensed (R : DenotGS E W .et) :
    Determiner.licenses (E := E) (W := W) mandarinDets (.bare R) := trivial

/-- The anaphoric kind (`.anaphoric R d`) is licensed in Mandarin via
    the demonstrative paradigm (paper §3.2: anaphoric definites surface
    as Dem-Clf-N constructions). The licensing holds because the
    demonstrative obligatorily expones a familiarity (anaphoric) use, so
    `Determiner.MarksPresup mandarinDets .familiarity`. -/
theorem anaphoric_licensed (R : DenotGS E W .et) (d : Nat) :
    Determiner.licenses (E := E) (W := W) mandarinDets (.anaphoric R d) := by
  show Determiner.MarksPresup mandarinDets .familiarity
  decide

/-- Mandarin demonstratives are licensed (the *na*/*zhe* paradigm —
    paper fn. 8: speakers prefer *na* 'that' to *zhe* 'this' in most
    simple anaphoric environments). -/
theorem demonstrative_licensed
    (R : DenotGS E W .et) (deictic : Features.Deixis.Feature) (sIdx d : Nat) :
    Determiner.licenses (E := E) (W := W) mandarinDets
      (.demonstrative R deictic sIdx d) := by
  show ∃ e ∈ mandarinDets, Determiner.Entry.IsDemonstrative e
  decide

/-- A Mandarin bare definite and its `.unique` counterpart over the
    same restrictor pick the same referent — the bare-N route to
    unique definiteness (paper §4.1: ι via Chierchia type-shift) is
    extensionally the `Description.unique` denotation at the API
    layer. Parallels `Moroney2021.shan_bare_unique_agreement`. -/
theorem bare_unique_agreement
    (R : DenotGS E W .et) (sIdx : Nat)
    (g : Core.Assignment E)
    (gs : SitAssignment W) :
    interpret (.bare R) g gs = interpret (.unique R sIdx) g gs := rfl

/-- A Mandarin demonstrative-marked anaphoric and the bare anaphoric
    over the same restrictor and discourse index pick the same entity:
    the deictic feature is a presupposition filter, not a referent
    selector (paper §4.2 cited Hanink/Schwarz analysis). Parallels
    `Moroney2021.shan_demonstrative_anaphoric_agreement`. -/
theorem demonstrative_anaphoric_agreement
    (R : DenotGS E W .et) (deictic : Features.Deixis.Feature) (sIdx d : Nat)
    (g : Core.Assignment E)
    (gs : SitAssignment W) :
    interpret (.demonstrative R deictic sIdx d) g gs =
      interpret (.anaphoric R d) g gs := rfl

-- ════════════════════════════════════════════════════════════════
-- §3: Bridging and Donkey (paper §3.1, §3.3)
-- ════════════════════════════════════════════════════════════════

/-! Paper §3.1 (Mandarin): part-whole bridging takes bare N
(`chezi … paizhao` 'car … license plate'); producer-product bridging
takes Dem-Clf-N (`shi … #(na wei) shiren` 'poem … #(that) poet').
Paper §3.3 (Mandarin donkey): demonstratives required in both
*ruguo*/*dou*-conditionals (example 18) and relative-clause donkey
configurations (example 20: `Mei ge … #(na zhi) shuiniu`); bare N is
infelicitous (example 19). The substrate's
`Features.Definiteness.bridgingPresupType` and `useTypeToPresupType`
encode these splits at the use-type level — proved here for Mandarin
by re-using `Schwarz2009.lean` lemmas. -/

open Schwarz2009

/-- Part-whole bridging projects uniqueness (paper §3.1 example 14a:
    `chezi … paizhao` — bare-N realization). -/
theorem partWhole_is_uniqueness :
    bridgingPresupType .partWhole = .uniqueness := rfl

/-- Producer-product bridging projects familiarity (paper §3.1
    example 14b: `shi … #(na wei) shiren` — Dem-Clf-N realization). -/
theorem relational_is_familiarity :
    bridgingPresupType .relational = .familiarity := rfl

/-- The two bridging realizations diverge — same `.uniqueness ≠
    .familiarity` fault Schwarz argues for German articles. -/
theorem bridging_split_distinct :
    bridgingPresupType .partWhole ≠ bridgingPresupType .relational :=
  bridging_subtypes_realize_both_presup_types

/-- Donkey anaphora projects familiarity at the use-type layer (paper
    §3.3; [schwarz-2009] §3). For Mandarin's `.markedAnaphoric`
    strategy this predicts demonstrative use in both donkey
    sub-configurations.

    Paper §3.3 distinguishes two donkey environments: bare conditionals
    (use indeterminate pronouns only — no def expression) and
    *ruguo*/*dou*-conditionals plus relative-clause donkey
    (definite expression required, instantiated as Dem-Clf-N).
    [cheng-huang-1996] originally observed the contrast. The
    use-type collapse to `.familiarity` covers the second environment
    (the one where definite expressions are licensed); bare conditionals
    are out of the scope of `useTypeToPresupType` because they involve
    no definite at all. -/
theorem donkey_is_familiarity :
    useTypeToPresupType .donkey = .familiarity :=
  donkey_use_is_familiarity

/-- Donkey patterns with discourse anaphora at the use-type level —
    both require Mandarin's anaphoric form (Dem-Clf-N). -/
theorem donkey_patterns_with_anaphoric :
    useTypeToPresupType .donkey = useTypeToPresupType .anaphoric :=
  Schwarz2009.donkey_patterns_with_anaphoric

-- ════════════════════════════════════════════════════════════════
-- §4: ι as Last-Resort Type-Shift; Blocking Principle
-- ════════════════════════════════════════════════════════════════

/-! Paper p. 514 introduces the **Blocking Principle** (eq. 23: "Don't
do covertly what you can do overtly"), inherited from
[chierchia-1998]. In Mandarin, the absence of an overt unique
article means ι is unblocked — bare N can route to a unique-definite
reading via the type-shift hierarchy of [dayal-2004].

The substrate has Dayal's hierarchy (`Semantics/Kinds/MeaningPreservation.lean`),
already used by `Moroney2021.lean`. The Mandarin parallel theorem is
the same `selectShift` instance: when no shift is blocked, ι is
selected first (Meaning Preservation). -/

open Semantics.Kinds

/-- Mandarin's number-neutral nouns under no blocking select ι as the
    preferred type-shift — paper p. 514's "ι is the type-shifter
    relevant for definite type-shifting", lifted to the Dayal substrate
    Moroney2021 already consumes. -/
theorem iota_is_last_resort :
    MeaningPreservation.selectShift {
      number := .neutral, downDefined := false
      iotaBlocked := false, iotaAnaphoricBlocked := false
      existsBlocked := false, instantiationAccessible := true
    } = some .iota := rfl

/-- Bridge to Mandarin's classifier strategy: per
    `NMP.mandarinStrategy`,
    Mandarin's classifier denotation atomizes the noun (CLF-for-N).
    This is the Trinh 2011 / Krifka 1995 / Chierchia 1998 denotation
    Jenks adopts in §4.1 (eq. 21). Parallels
    `Moroney2021.shan_clf_is_atomization`. -/
theorem clf_is_atomization {α : Type*} [PartialOrder α]
    (P : α → Prop) :
    Semantics.Classifier.classifierDenot
      NounCategorization.ClassifierStrategy.forNoun P
      (fun _ => 0) 0
    = Semantics.Classifier.clfForNoun P := rfl

-- ════════════════════════════════════════════════════════════════
-- §5: Type Discipline — ι^x as Property-Indexed (paper p. 513)
-- ════════════════════════════════════════════════════════════════

/-! Jenks (2018, p. 513) is explicit that his anaphoric article ι^x
takes an index argument of type ⟨e,t⟩ (a property), departing from
[schwarz-2009]/[schwarz-2013]'s type ⟨e⟩ (an individual).
The substrate's `Description.anaphoric R d` carries `d : Nat` — a
discourse-index slot resolved through the entity assignment, which
matches Schwarz's individual-typed index, not Jenks's property-typed
one. For Schwarz-style and ordinary demonstrative cases this divergence
is inert (the assignment returns an entity), but the property-typed
index is load-bearing in paper §4.4 (Pred type-shift, examples 32–38:
proper names + demonstratives composing as `Pred(Zhangsan) +
Dem-Clf-N`).

Faithfully formalizing §4.4 requires a property-typed-index variant
on `Description.anaphoric`. This is recorded as a TODO at the substrate
level (`Semantics/Definiteness/Description.lean`) rather than encoded as a
placeholder theorem. -/

-- ════════════════════════════════════════════════════════════════
-- §6: Index! as Maximize Presupposition Instance (paper §5.2)
-- ════════════════════════════════════════════════════════════════

/-! Paper p. 524 (eq. 50): **Index! = "Represent and bind all possible
indices"**. Jenks derives this from Heim 1990 Maximize Presupposition
via Schlenker 2012's Gricean reduction. The substrate provides
`Semantics.Presupposition.MaximizePresupposition.mpConstraintOf`,
parametric over an arbitrary candidate type and strength function —
the natural slot for any MP-instance.

The `IndexCandidate` carrier below is a minimal 2-bit witness type
sufficient to demonstrate the principle's qualitative behavior
(prefer indexed when index is available; neutral otherwise). A
fuller instantiation would parameterize over `Description E W` and the
discourse-context predicate licensing the index — that refactor
belongs in a substrate file (`Semantics/Presupposition/Index.lean`)
when a second consumer needs it. -/

/-- Index! candidate: an indexed alternative is in the running only
    when an index can be supplied (paper p. 523-524: "an index is
    required to be licensed by explicit prior mention in discourse"). -/
structure IndexCandidate where
  isIndexed : Bool
  indexAvailable : Bool
  deriving DecidableEq, Repr

/-- Index! strength function: an indexed candidate gets strength 1
    only when an index can actually be supplied (paper's prior-mention
    condition). Bare candidates always get strength 0. -/
def indexStrength (c : IndexCandidate) : Nat :=
  if c.isIndexed && c.indexAvailable then 1 else 0

/-- **Index! as MP**: the principle is `mpConstraintOf 1 indexStrength`
    — the substrate's general MP construction at strength 1, applied
    to the binary indexed/non-indexed competition. Per paper p. 524,
    "Index! is a specific instance of Maximize Presupposition!
    (Heim 1990)". -/
def indexConstraint : Constraints.Constraint IndexCandidate :=
  Semantics.Presupposition.MaximizePresupposition.mpConstraintOf
    1 indexStrength

/-- When both candidates are available and an index can be supplied
    (a discourse antecedent exists), the indexed candidate has fewer
    Index! violations than the bare candidate. -/
theorem index_prefers_indexed_when_available :
    indexConstraint { isIndexed := true,  indexAvailable := true } <
    indexConstraint { isIndexed := false, indexAvailable := true } := by
  decide

/-- When no index can be supplied (no discourse antecedent), Index! is
    neutral — both candidates incur the same number of violations,
    correctly leaving bare N as the only option in unique-definite
    contexts (paper §3.1; explains why ι^x is unavailable there). -/
theorem index_neutral_when_unavailable :
    indexConstraint { isIndexed := true,  indexAvailable := false } =
    indexConstraint { isIndexed := false, indexAvailable := false } := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §7: Subject-Position Exception (paper §5.3)
-- ════════════════════════════════════════════════════════════════

/-! Paper §5.3 documents the exception to Index!'s prediction: in
matrix subject position, bare N is licensed for *anaphoric* reference
(not just unique). Examples 51–53 establish that the exception is
pragmatic — bare N in subject position marks the noun as a *continuing
topic* (in the sense of [roberts-2003] QUD-relativized topics),
which short-circuits Index! because the topic-marking pragmatic
function takes precedence.

Two empirical points the paper makes (p. 524-526):
- Example 52a/b: the demonstrative is preferred for left-dislocated
  topics (which are *new* topics, not continuing).
- Example 53: bare N is licensed under the contrastive-topic marker
  *ne* (continuing topic + alternative-set).

The substrate has `Roberts2012` QUD machinery in
`Discourse/QUDStack.lean`. A faithful formalization of paper §5.3
would need a topic predicate over `Description` configurations
co-occurring with QUD-stack state — substrate the linglib has but
that this study file does not yet plug into.

Stated below as a sorry'd theorem to mark the analytical commitment
without forcing the discharge. -/

/-- A topic-aware Index! candidate carries the additional `isTopic`
    flag (continuing-topic status under Roberts QUD). -/
structure TopicCandidate where
  isIndexed : Bool
  indexAvailable : Bool
  isTopic : Bool
  deriving DecidableEq, Repr

/-- Topic-overridden Index! strength: the topic-marking pragmatic
    function (paper §5.3) neutralizes Index!'s preference. A bare
    candidate marked as a continuing topic gets the same strength as
    an indexed candidate when an index is available. -/
def topicAwareIndexStrength (c : TopicCandidate) : Nat :=
  if c.isTopic then 1
  else if c.isIndexed && c.indexAvailable then 1
  else 0

/-- The topic-aware Index! constraint. -/
def topicAwareIndexConstraint :
    Constraints.Constraint TopicCandidate :=
  Semantics.Presupposition.MaximizePresupposition.mpConstraintOf
    1 topicAwareIndexStrength

/-- **Subject-position exception (paper §5.3)**: when a bare-N candidate
    is marked as a continuing topic, Index!'s preference for the
    indexed alternative is neutralized. Both candidates incur the
    same number of violations, restoring the apparent free variation
    paper §3.2 documents for matrix subjects.

    Decision-procedure proof over the four relevant `TopicCandidate`
    configurations. -/
theorem subject_topic_overrides_index :
    topicAwareIndexConstraint
      { isIndexed := false, indexAvailable := true, isTopic := true } =
    topicAwareIndexConstraint
      { isIndexed := true,  indexAvailable := true, isTopic := true } := by
  decide

/-- Without topic marking, the original Index! preference holds (paper
    §5.2): the indexed candidate has strictly fewer violations than the
    bare candidate when an index is available. -/
theorem non_topic_keeps_index_preference :
    topicAwareIndexConstraint
      { isIndexed := true,  indexAvailable := true, isTopic := false } <
    topicAwareIndexConstraint
      { isIndexed := false, indexAvailable := true, isTopic := false } := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §8: Covarying Readings (paper §4.3)
-- ════════════════════════════════════════════════════════════════

/-! Paper §4.3 (examples 27–30) is the empirical anchor for treating
ι^x's index as a *bound* variable: bare N can covary with a
quantificational topic, demonstratives in the same configuration
cannot. The covarying part-whole bridging (example 30: `Mei ge mai le
fangzi de ren dou xuyao xiuli #(na ge) wuding` 'every house-buyer
needed to fix the/#that roof') is the load-bearing case — the bare
restrictor's resource situation can vary with the topic adverb's
binding, while the demonstrative's index forces a strict reading.

The substrate has Hanink-style resource-situation binding in
`Hanink2021.lean` (`tableAtSit0` over a `Room` index, with `gsKitchen`
/`gsLiving` as situation assignments). A Mandarin parallel theorem
would instantiate that pattern with a Mandarin restrictor and a
quantificational topic situation; left as a sorry pending the
property-typed-index substrate gap (the demonstrative side of the
contrast requires the §5 ⟨e,t⟩-typed index to forbid covariation
properly). -/

/-- **Strict reading of demonstratives across situation variation**:
    a `.demonstrative`/`.anaphoric` description's referent is fixed
    by the entity assignment `g` at index `d`, independent of the
    situation assignment `gs`. Concretely: if the predicate `R` is
    *itself* invariant across two situation assignments at the indexed
    entity, then both demonstratives return the same referent — the
    demonstrative cannot covary through the situation slot.

    This is one half of paper §4.3's covariation contrast (the
    *strict* half). The other half — bare N covarying via situation
    binding — requires the property-typed index variant on
    `Description.anaphoric` flagged in §5 to express cleanly, and is
    deferred. -/
theorem demonstrative_strict_under_situation_variation
    (R : DenotGS E W .et) (deictic : Features.Deixis.Feature)
    (sIdx d : Nat)
    (g : Core.Assignment E)
    (gs₁ gs₂ : SitAssignment W)
    (hR : R g gs₁ (g d) = R g gs₂ (g d)) :
    interpret (.demonstrative R deictic sIdx d) g gs₁ =
      interpret (.demonstrative R deictic sIdx d) g gs₂ := by
  rw [demonstrative_anaphoric_agreement, demonstrative_anaphoric_agreement,
      interpret_anaphoric, interpret_anaphoric, hR]

end Jenks2018
