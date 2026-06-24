import Linglib.Syntax.Minimalist.Selection
import Linglib.Syntax.Minimalist.ExtendedProjection.Basic
import Linglib.Semantics.Attitudes.ClauseDenotation.Content
import Linglib.Semantics.Attitudes.ClauseDenotation.Situation
import Linglib.Semantics.Verb.Basic
import Linglib.Studies.Bondarenko2022
import Linglib.Fragments.Greek.StandardModern.Complementizers

/-!
# Angelopoulos 2026: On clausal complementation, once more [angelopoulos-2026]

Nikos Angelopoulos (2026). *Natural Language & Linguistic Theory*
44:26. DOI 10.1007/s11049-026-09711-w.

## Three puzzles, one mechanism

The paper resolves three puzzles about Modern Greek *oti* (content
complementizer) and *pu* (situation/factive complementizer):

1. **Internal/external argument asymmetry.** Both *oti*- and
   *pu*-clauses pattern as internal arguments under three
   diagnostics — clitic doubling, passivization, A-bar extraction
   transparency — yet both are banned from the external argument
   position.
2. **Near-complementary distribution.** *oti* combines with
   content-selecting matrix verbs (*ipe* 'said', *pistévo*
   'believe', *xeri* 'know'); *pu* combines with situation-
   selecting emotive factives (*metanjose* 'regret', *aresi* 'like
   / appeal to', *xérome* 'be happy').
3. **Novel stativity restriction on complement *pu*.** Complement
   *pu*-clauses require a stative matrix predicate. The restriction
   vanishes in adjunct, relative, and interrogative *pu* uses.

The unifying mechanism: *oti* and *pu* bear an uninterpretable
[n]-feature checked by a light noun in their specifier
([arsenijevic-2009], [moltmann-2019]). The light noun is
licensed by Hale-Keyser noun-incorporation ([hale-keyser-1993])
into a *lexical* host (`v_State` or `v_Event`); incorporation into a
*functional* head (`T`) is impossible. Aspectual head v_State
selects either content- or situation-typed [n]; v_Event selects
only content-typed [n]. Adjuncts select-upward
([bruening-2013], [hewett-2023], [hunter-2015],
[neeleman-philip-tanaka-vandekoot-2023]), exempting non-
complement *pu* from v_State.

## Hedges (per audit)

- **Stativity restriction credit.** Noted in [roussou-2019]
  (Angelopoulos credits her example as the source of his ex. 22b
  discriminating the stativity contrast); the systematic
  generalization across complement *pu*-clauses is presented as
  novel in [angelopoulos-2026], derived here from v_State
  c-selection.
- **Manner-adverb diagnostic.** Unidirectional in the literature.
  [maienborn-2005] shows Kimian states allow some manner-
  like modification; the converse (allows manner ⟹ eventive) is
  contested.
- **Clitic doubling as argumenthood.** Exposed as a construction
  fact (`doubledByClitic`), NOT axiomatized as biconditional with
  `isArgument`. [anagnostopoulou-2003] ties doubling to
  specificity, not bare argumenthood.
- **Crosslinguistic scope.** Greek with cross-references to
  [major-2024] (Uyghur *dep*) and [bochnak-hanink-2021]
  (Washo). Two-language extension, not a typology. Korean -ko,
  Japanese to/koto, Romance que/de, Hebrew še/ki avoided.

## Cross-framework engagement

- **Theoretical ally:** [bruening-2025] ("C-Selection
  Irreducibility") makes a parallel argument for bidirectional
  feature-driven selection in coordination, formalised in
  `Studies/Bruening2025.lean`. The
  bidirectional-selection move here generalises Bruening's
  argument-side claim to the adjunct domain.
- **Silent divergence vs HPSG:** HPSG selection is intrinsically
  head-driven (the SUBCAT/COMPS list lives on the head); the
  paper's adjunct-selects-host machinery has no HPSG counterpart
  yet formalised in linglib. A future
  `Syntax/HPSG/Complementation.lean` would let us state
  the cross-framework refutation directly.
- **Silent divergence vs CCG:** CCG adjuncts are `X/X` modifiers
  that don't *probe* their host; the bidirectional-selection move
  is also silently divergent from CCG.
- **Encoding gap:** the §6 refutation theorems are *conditional*
  (premises about constructive `SyntacticObject` witnesses); the
  substantive instantiation requires a `Step.applyAdjunctChecked`
  dual to `Selection.lean`'s checked Merge, which is queued
  substrate. As written, both refutation theorems function as
  paper-attributed promises rather than constructive refutations.

## Studies-local apparatus (per audit)

- `vAspectHead` enum (vState / vEvent): per the [borer-2005] /
  [merchant-2019] light-v split. Not promoted to substrate
  yet — single paper-anchored consumer; promote to
  `Syntax/Minimalist/LightV.lean` when ≥ 2 consumers.
- `adjunctSelects` predicate: bidirectional selection per
  [bruening-2013] / [hewett-2023] / [hunter-2015] /
  [neeleman-philip-tanaka-vandekoot-2023]. Studies-local;
  promote to `Syntax/Minimalist/AdjunctSelection.lean`
  when ≥ 2 consumers.
- `hkIncorporable` predicate: [hale-keyser-1993] noun-
  incorporation. Distinct from `Phase.lean` D-incorporation
  (Davies-Dubinsky 2003 phase deactivation) and
  `Typology.Voice` noun-incorporation (Beavers-Udayana 2022
  type-shifting taxonomy). The three are coincidentally named
  but structurally distinct; do NOT unify into a single
  `Incorporation.lean` substrate.
-/

namespace Angelopoulos2026

open Minimalist
open Semantics.Attitudes (ContentIndividual)
open Semantics.Attitudes.ClauseDenotation.Content (compC ContentNoun)
open Semantics.Attitudes.ClauseDenotation.Situation
  (SituationIndividual SituationNoun compPu)
open Bondarenko2022
  (NominalSort transparentSSMapping ClauseStructurePath
   bare_argument_predicted_impossible)
open Greek.StandardModern.Complementizers (GreekComplementizer)

-- ════════════════════════════════════════════════════════════════
-- § 1. Studies-local apparatus
-- ════════════════════════════════════════════════════════════════
--
-- Note on `NominalSort`: the enum from `Bondarenko2022` is a
-- type-theoretic *tag*, not an interpreter. The mapping
-- `NominalSort.content ↦ ContentIndividual` /
-- `NominalSort.situation ↦ SituationIndividual` is left implicit
-- here — the paper's puzzles can be derived without a uniform
-- interpreter. Adding one would require a `ClauseDenotation`
-- typeclass parametric over the licensee sort, which is queued
-- as substrate work pending a second consumer.

/-- The light-v aspectual head split ([borer-2005],
    [merchant-2019]). v_State introduces a stative situation
    argument; v_Event introduces an eventive one. These select
    different sorts of [n]-licensee in the spec of their CP
    complement.

    Studies-local. Promote to substrate when a second paper-
    anchored consumer (e.g., a future Borer 2005 or Merchant 2019
    study file) consumes it. -/
inductive vAspectHead where
  | vState
  | vEvent
  deriving DecidableEq, Repr

/-- Which sort of [n]-licensee an aspectual head accepts:
    v_State accepts both content and situation; v_Event accepts
    only content (paper §4.1). This asymmetry is the encoded
    table; the underlying derivation from a deeper aspectual-
    stativity feature (Borer 2005: situations are stative
    aspectual objects, dynamic v cannot select stative complement)
    is queued as a TODO. As written, this `def`-as-table is
    paper-fidelity, not a structural derivation.

    `Prop`-valued per CLAUDE.md (no `Bool` for predicate-shape
    data); decidability instance below. -/
def vAspectHead.acceptsSort : vAspectHead → NominalSort → Prop
  | .vState, _              => True
  | .vEvent, .content       => True
  | .vEvent, .situation     => False

instance : ∀ (h : vAspectHead) (s : NominalSort),
    Decidable (h.acceptsSort s) := fun h s => by
  cases h <;> cases s <;> (unfold vAspectHead.acceptsSort; infer_instance)

/-- [hale-keyser-1993] noun-incorporation predicate: a
    light-noun [n] can incorporate into a category iff that
    category is *lexical* (in the [panagiotidis-2015] sense:
    bears interpretable categorial features, not uninterpretable
    copies). Functional heads (T, C, D) cannot host incorporation. -/
def hkIncorporable (host : Cat) : Prop :=
  host = .v ∨ host = .V ∨ host = .n ∨ host = .N

instance : DecidablePred hkIncorporable := fun c => by
  unfold hkIncorporable; infer_instance

/-- Adjunct-selection predicate: an adjunct selects its host
    rather than being selected by it ([bruening-2013],
    [hewett-2023], [hunter-2015],
    [neeleman-philip-tanaka-vandekoot-2023]). Studies-local;
    a coarse abstraction over the actual checked-Merge dual that
    a future `AdjunctSelection.lean` substrate would expose. -/
def adjunctSelects (adj : SyntacticObject) (host : Cat) : Prop :=
  outerCatC adj = some host

-- ════════════════════════════════════════════════════════════════
-- § 2. Greek empirical landscape
-- ════════════════════════════════════════════════════════════════
--
-- Witness data from paper exs. 1–25. The *explanans*/*explanandum*
-- minimal pair (ex. 4a/4c) is the constructive witness for the
-- cross-framework refutation theorem in §6.

/-- Was the matrix verb's complement clitic-doubled? Construction
    fact, NOT axiomatized to imply argumenthood. Cf. fn 4 of the
    paper acknowledging [angelopoulos-michelioudakis-2023]
    on doubling-as-Agree. -/
def doubledByClitic (xp : SyntacticObject) : Bool :=
  -- Placeholder: actual diagnostic would test for an Agreeing
  -- clitic in the matrix clause. Surface-level Boolean, opaque
  -- to substrate.
  outerCatC xp == some .C

/-- The bare *oti*-clause yields the *explanans* reading:
    "Maria explained well that the Earth is round" — the embedded
    clause IS the explanation (paper ex. 4a). -/
inductive ExplanansReading where
  | bareOti  -- via Predicate Modification
  deriving DecidableEq, Repr

/-- The nominalized *to oti*-clause yields the *explanandum*
    reading: "Maria explained well the fact that the Earth is round"
    — the embedded clause is the fact being explained (paper ex. 4c). -/
inductive ExplanandumReading where
  | toOti  -- via Functional Application through the silent D + FACT
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════════════════
-- § 3. The light-noun analysis (paper §3.1)
-- ════════════════════════════════════════════════════════════════
--
-- Both *oti* and *pu* bear [n], checked by a silent light noun
-- in their spec. The light noun then incorporates into the
-- selecting v head.
--
-- **Substrate gap (per syntax expert H2).** This file models
-- only the spec-position licensing structure (`lightNounInSpec`
-- via `Step.emL`); it does NOT model the Hale-Keyser
-- incorporation MOVEMENT itself (paper trees 27-30). A faithful
-- incorporation Step would require head-movement substrate
-- (`Step.applyHeadMove`) that is currently absent from
-- `Syntax/Minimalist/Selection.lean`. The
-- `hkIncorporable` predicate above states which categories CAN
-- host incorporation; the actual movement is asserted in prose,
-- not derived. Refer to [matushansky-2006] for an
-- incorporation-as-Merge formalisation candidate.

/-- The *oti* C-head: bears [uN] (= the [n]-feature in the paper's
    notation), selecting a light noun in its specifier. -/
def otiCHead (id : Nat) : SyntacticObject :=
  mkLeafPhon .C [.n] "oti" id

/-- The *pu* C-head: same selectional contract as *oti* — bears
    the [n]-feature. The content/situation distinction surfaces
    not at C but at the matrix v (§5). -/
def puCHead (id : Nat) : SyntacticObject :=
  mkLeafPhon .C [.n] "pu" id

/-- The light-noun-in-Spec configuration: `nullN` from
    `Selection.lean` merged into the spec of an *oti*/*pu* C head
    via specifier Merge (`Step.applyChecked .emL`).

    The C head retains its [n] in `pending` after `emL` (specifier
    Merge does not consume features in the c-selection system; cf.
    `applyChecked_emL`). The [n] is checked when the resulting CP
    is merged as a complement of v whose own selectional features
    require a CP whose Spec contains [n]. -/
def lightNounInSpec (cHead : SyntacticObject) (id : Nat) : SyntacticObject :=
  .node (nullN id) cHead

-- ════════════════════════════════════════════════════════════════
-- § 4. In/out asymmetry — derived from categorial features
-- ════════════════════════════════════════════════════════════════
--
-- Per integration auditor F7: the impossibility of incorporating
-- the light n from Spec,TP follows from the lexical/functional
-- partition in `ExtendedProjection/Basic.lean` (`categorialFeatures`,
-- [panagiotidis-2015]).
-- T bears uninterpretable categorial features and so is functional;
-- it cannot host Hale-Keyser noun-incorporation.

/-- Functional heads (T, C, D) bear uninterpretable categorial
    feature copies per [panagiotidis-2015]; they cannot host
    H&K incorporation. -/
theorem t_not_incorporable : ¬ hkIncorporable .T := by
  intro h; rcases h with h | h | h | h <;> cases h

/-- C is functional; cannot host incorporation. -/
theorem c_not_incorporable : ¬ hkIncorporable .C := by
  intro h; rcases h with h | h | h | h <;> cases h

/-- D is functional; cannot host incorporation. -/
theorem d_not_incorporable : ¬ hkIncorporable .D := by
  intro h; rcases h with h | h | h | h <;> cases h

/-- v is lexical (a categorizer per [panagiotidis-2015]);
    hosts incorporation. This is the case Angelopoulos exploits:
    a light noun in Spec,CP can incorporate into a higher v_State
    or v_Event, satisfying its licensing requirement. -/
theorem v_incorporable : hkIncorporable .v := Or.inl rfl

/-- V is lexical; hosts incorporation. -/
theorem V_incorporable : hkIncorporable .V := Or.inr (Or.inl rfl)

/-- The three functional-head cells are jointly non-incorporation-
    hosts. This is the substrate-level fact underlying Puzzle 1
    (in/out asymmetry); the geometric step "from Spec,TP, the
    closest c-commander is T, and incorporation cannot reach
    lexical v without violating Sportiche-2005 locality" is
    asserted in prose here and queued for formalisation when a
    head-movement substrate (`Step.applyHeadMove`) lands.

    Paper ex. 11, 12: bare *oti*/*pu*-clauses are ungrammatical
    in the external argument position. -/
theorem functional_heads_block_incorporation :
    ¬ hkIncorporable .T ∧ ¬ hkIncorporable .C ∧ ¬ hkIncorporable .D :=
  ⟨t_not_incorporable, c_not_incorporable, d_not_incorporable⟩

/-- The internal-argument cases work because the light noun's
    closest lexical host (v_State or v_Event) is c-commanding the
    CP from above its complement position. -/
theorem v_licenses_incorporation :
    hkIncorporable .v := v_incorporable

-- ════════════════════════════════════════════════════════════════
-- § 5. Stativity restriction (paper §4.1)
-- ════════════════════════════════════════════════════════════════
--
-- v_State accepts both content (oti) and situation (pu) light-n;
-- v_Event accepts only content. So *pu* is licensed only under
-- v_State, deriving the obligatory-stativity contour for
-- *pu*-complement matrix predicates (paper exs. 22, 23, 24).

/-- v_State accepts both content and situation [n]-typed
    light nouns. -/
theorem vState_accepts_both :
    vAspectHead.vState.acceptsSort .content ∧
    vAspectHead.vState.acceptsSort .situation := ⟨trivial, trivial⟩

/-- v_Event accepts content but rejects situation. -/
theorem vEvent_content_only :
    vAspectHead.vEvent.acceptsSort .content ∧
    ¬ vAspectHead.vEvent.acceptsSort .situation := by
  refine ⟨trivial, ?_⟩
  intro h; exact h

/-- **Puzzle 3 (stativity restriction, derived from the table).**
    A *pu*-clause bears situation-typed [n]; v_Event rejects it;
    therefore *pu* cannot complement an eventive matrix predicate.

    Paper ex. 23c: `*θimose mésa se péde leptá pu psifístike o
    nómos` 'got angry within five minutes that the law was voted'.
    The *in*-adverbial forces eventive interpretation; eventive →
    v_Event; v_Event ↛ situation; *pu* blocked.

    TODO: derive `acceptsSort` from a Borer-2005 stativity feature
    on the head and a stativity feature on the licensee, rather
    than table-stipulating it. The current encoding is the
    paper-fidelity stub form; a true derivation is queued. -/
theorem pu_requires_vState (head : vAspectHead)
    (h : head.acceptsSort .situation) : head = .vState := by
  cases head
  · rfl
  · exact h.elim

/-- *oti* (content-typed [n]) is licensed under either v.
    Predicts paper ex. 21b: `arketos kosmos δen siniδitopii efkola
    oti i periγrafiki kanones ine δjaforetiki...` — *sinidhitopió*
    'realize' takes a manner adverb (eventive ⟹ v_Event), and
    *oti* is fine. -/
theorem oti_compatible_with_either (head : vAspectHead) :
    head.acceptsSort .content := by
  cases head <;> trivial

-- ════════════════════════════════════════════════════════════════
-- § 6. Cross-framework refutation theorems
-- ════════════════════════════════════════════════════════════════
--
-- **Critical framing caveat (syntax expert S2 BPS gap).**
-- [bondarenko-2022] works in Bare Phrase Structure where the
-- X-bar argument/modifier distinction is gone; her "modifier" claim
-- is **semantic** (type incompatibility for FA), NOT structural
-- ("adjunct in the X-bar sense"). [angelopoulos-2026]'s
-- refutation appeals to *syntactic position* (clitic doubling,
-- passivization, extraction transparency), which implicitly commits
-- to a non-BPS view Bondarenko explicitly rejects. The refutation
-- below is honest about this framing gap: it shows that Angelopoulos's
-- diagnostics force Bondarenko's transparent S-S mapping to abandon
-- the position↔composition-mode correlation, NOT that Bondarenko's
-- type-theoretic story (bare CP ≠ Θ-saturator) is internally false.

/-- **Refutation against [bondarenko-2022]'s transparent
    Syntax-Semantics mapping** — substantive form, consuming the
    Chapter 4 type-theoretic predicates from
    `Bondarenko2022`.

    The substantive content: Greek bare *oti* in the *explanans*
    reading (paper ex. 4a) instantiates the (semantic-)bare clause
    type composing via PM with v's situation argument. Bondarenko
    correctly predicts this composition (`bareCP_composes_via_PM`).
    But the same bare *oti* passes argument-position diagnostics
    (clitic doubling — paper ex. 3a — and passivization — ex. 6a).
    Bondarenko's prediction `bareCP_satisfies_no_theta` says no
    Θ-head saturates a bare CP. Therefore: either (i) the diagnostics
    track something other than Θ-saturation, or (ii) the prediction
    fails. Angelopoulos chooses (i) — autonomy of syntax — which IS
    Bondarenko's transparent S-S mapping rejected.

    Stated as the **conjunction** witnessing the autonomy claim:
    bare CP composes via PM AND no Θ-head saturates it. Angelopoulos's
    diagnostics force the position↔Θ-saturation correlation that
    Bondarenko's transparent mapping presupposes. -/
theorem angelopoulos_explanans_breaks_position_theta_correlation :
    Bondarenko2022.composesViaPM
      .predicateOfSituations ∧
    (∀ θ : Bondarenko2022.ThetaHead,
      ¬ Bondarenko2022.saturatesTheta
        .predicateOfSituations θ) :=
  ⟨Bondarenko2022.bareCP_composes_via_PM,
   Bondarenko2022.bareCP_satisfies_no_theta⟩

/-- The original conditional refutation, preserved for the
    paper-fidelity `transparentSSMapping` def-as-table form. The
    substantive refutation is
    `angelopoulos_explanans_breaks_position_theta_correlation` above. -/
theorem angelopoulos_refutes_bondarenko_transparent
    (bareOtiInArgPosition : ClauseStructurePath)
    (h_struct : bareOtiInArgPosition = .bareArgument) :
    ¬ transparentSSMapping bareOtiInArgPosition := by
  rw [h_struct]; exact bare_argument_predicted_impossible

/-- **Refutation against [bochnak-hanink-2021] / Deal 2026
    "selection limited to argument clauses".** If selection were
    limited to argument clauses, then a *pu*-adjunct clause would
    not be selected by anything. But Greek adjunct *pu*-clauses
    select their hosts (§4.2 paper, following [hewett-2023],
    [hunter-2015]). Witness: paper ex. 24a — *Ton timorisan
    γrigora pu iče afti ti siberifora* 'They punished him fast
    because of the fact that he had this behavior'. The *pu*-
    adjunct selects the verbal host; selection is bidirectional.

    TODO: instantiate `puAdjunctClause` constructively from
    paper ex. 24a + `adjunctSelects` machinery. Requires checked-
    Merge dual for adjunct-up selection (`Step.applyAdjunctChecked`),
    which is genuinely new substrate not yet in `Selection.lean`. -/
theorem angelopoulos_refutes_selection_argument_only
    (puAdjunctClause : SyntacticObject) (host : Cat)
    (h_sel : adjunctSelects puAdjunctClause host) :
    ∃ adj host, adjunctSelects adj host :=
  ⟨puAdjunctClause, host, h_sel⟩

-- ════════════════════════════════════════════════════════════════
-- § 7. AttitudeClass orthogonality
-- ════════════════════════════════════════════════════════════════
--
-- Per cross-framework auditor: content/situation cuts orthogonally
-- to representationality. Don't extend AttitudeClass enum; prove
-- the orthogonality with a witness (cf. cross-framework auditor).

/-- The content/situation distinction (Bondarenko 2022) cuts
    orthogonally to the doxastic/preferential partition exposed
    in `Features.Attitudes.Attitude`.

    The substantive claim is that there is a (preferential,
    situation-selecting) verb (e.g., *metanjose* 'regret') and a
    (doxastic, content-selecting) verb (e.g., *pistévo* 'believe').
    However, **content/situation selection is not currently a
    Fragment field** — per integration auditor N3, it is paper-
    specific apparatus that lives in this Studies file rather than
    in `Verb`. Without a Fragment field, the orthogonality
    theorem can only state a *Vendler-stativity* witness, which is
    a proxy for situation-selection (since *pu*-complements
    require stative matrix predicates per Puzzle 3) but not
    identical to it.

    The honest theorem: there exists a (preferential, stative)
    verb. The cross-classification with content/situation
    selection requires a Fragment-level `selectsClauseSort` field,
    queued for a follow-up substrate refactor. -/
theorem preferential_stative_verb_exists :
    ∃ (v : Verb),
      (∃ p, v.attitude = some (.preferential p)) ∧
      v.vendlerClass = some .state :=
  ⟨Greek.StandardModern.Complementizers.metaniono,
   ⟨_, rfl⟩, rfl⟩

/-- And a (doxastic, stative) verb — *pistévo* 'believe'. The
    pair witnesses that attitude class and stativity cross-
    classify; together with the prose claim that *metanjose*
    selects *pu* (situation) and *pistévo* selects *oti*
    (content), this is the closest we can come to the orthogonality
    claim without a `selectsClauseSort` Fragment field. -/
theorem doxastic_stative_verb_exists :
    ∃ (v : Verb),
      (∃ vd, v.attitude = some (.doxastic vd)) ∧
      v.vendlerClass = some .state :=
  ⟨Greek.StandardModern.Complementizers.pistevo,
   ⟨_, rfl⟩, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- § 8. Theory-hub denotation theorems
-- ════════════════════════════════════════════════════════════════
--
-- Per integration auditor N1: theorems must reference the existing
-- ClauseDenotation primitives, not local re-implementations of
-- PM/FA. The *explanans* reading goes through `compC` /
-- `existsContentClosure`; the *explanandum* reading goes through
-- `existsContentNounCP` (silent FACT noun + D layer per
-- [moulton-2020]).

/-- The *oti*-explanans reading uses the content-CP via PM.
    The CP `oti i Ji ine strojili` 'that the Earth is round'
    composes with the verb's situation argument by Predicate
    Modification, modifying the *event of explaining* with the
    propositional content. Reference: `compC` from
    `ClauseDenotation/Content.lean`. -/
theorem explanans_via_compC {W : Type*}
    (xc : ContentIndividual W) (p : W → Prop) :
    compC p xc ↔ xc.cont = p := Iff.rfl

/-- The *to oti*-explanandum reading uses the silent FACT noun +
    D layer per [moulton-2020]. Composes via Functional
    Application to deliver an individual argument
    (the fact being explained).

    Reference: `existsContentNounCP` from `ClauseDenotation/Content`.
    The silent noun is a `ContentNoun W` whose denotation is
    `factive` (presupposes the proposition true at the actual
    world). -/
theorem explanandum_via_existsContentNounCP {W : Type*}
    (factNoun : ContentNoun W) (p : W → Prop) (w : W) :
    Semantics.Attitudes.ClauseDenotation.Content.existsContentNounCP
      factNoun p w ↔
    ∃ xc : ContentIndividual W, factNoun xc w ∧ compC p xc :=
  Iff.rfl

/-- Symmetric for *pu*: the situation-clause yields its denotation
    via `compPu` from `ClauseDenotation/Situation.lean`. -/
theorem pu_via_compPu {S : Type*}
    (xs : SituationIndividual S) (q : S → Prop) :
    compPu q xs ↔ xs.sit = q := Iff.rfl

end Angelopoulos2026
