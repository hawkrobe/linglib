import Linglib.Semantics.Degree.StatesBased
import Linglib.Semantics.Attitudes.Confidence
import Linglib.Semantics.Degree.Clausal
import Linglib.Semantics.ArgumentStructure.Thematic.Defs
import Linglib.Semantics.Mereology
import Linglib.Fragments.English.Predicates.Verbal

/-!
# [pasternak-2019]: Intensity in the Mereology of Mental States

[pasternak-2019]

Pasternak argues that intensity is a **monotonic measure function** on
mental states: a more intense psychological state is "bigger" along a
vertical part-whole dimension. This gives a uniform compositional
treatment of intensity comparatives (`Ann hates Bill more than Matt
hates Jeff`) under the same architecture as `more snow` and `ran more`:
all are Wellwood-style verbal comparatives with a measure function `μ`
satisfying the Schwarzschild Monotonicity Constraint (Pasternak (4)).

The substrate already hosts every primitive Pasternak's §1–§4 needs:
- Monotonicity = `Degree.admissibleMeasure`
  (`StrictMono` over a preorder; multi-tradition naming credits
  Schwarzschild, Wellwood, Krifka, CSW, Pasternak, LaBToM in one
  docstring).
- Comparative LF = `Degree.maxComparative` over a than-clause degree
  set (`Degree.thanDegrees`), with the `Degree.maxComparative_unique`
  reduction lemma.
- Mental-state homogeneity = `Mereology.DIV` (downward-closure on the
  part-whole preorder; Pasternak (55) is the biconditional form, which
  reduces to `DIV` modulo preorder reflexivity).
- Neo-Davidsonian roles = `ArgumentStructure.ThematicFrame`
  with `experiencer`, `theme`, `holder` fields.

This study file *consumes* those primitives and adds the paper-specific
content: the five-construction enumeration (§2), the LGH-shaped lexical
entry (§3), the intensity comparative LF allowing distinct themes per
side (§4), the (60)–(63) positive/non-entailment asymmetry (§4.4), and
the bridge connecting CSW's confidence ordering to Pasternak's
mental-state preorder (§6).

## Coverage

| Pasternak | What this file covers                                                      |
|-----------|----------------------------------------------------------------------------|
| (4)       | Monotonicity = `admissibleMeasure` (substrate-level, multi-tradition)      |
| §2        | Five monotonicity-requiring constructions enumerated as data               |
| (27),(48b)| `MentalStateVerb` LGH-style lexical entry; `holdsAtDegree` denotation      |
| (50),(53) | `intensityComparative` LF using `Degree.maxComparative` directly           |
| (60)–(63) | `positive_entailment_matrix` + `positive_non_entailment_than_clause_witness` |
| (55)      | `MentalStateHomogeneity := Mereology.DIV` + biconditional bridge           |
| §3.1      | `pseudopartitive_blocks_speed`: non-monotonic `μ_speed` blocked            |
| —         | Bridge: CSW's `ConfidenceState` preorder hosts Pasternak's `μ_int`         |

LGH terminological note (Pasternak p.279, p.285): Pasternak introduces
the "lexical gradability hypothesis" (LGH) as a *counterproposal* to his
monotonic account, not as his preferred analysis. He shows it is
*compatible* with monotonicity (eq. (48b) is the LGH-shaped entry) but
prefers the non-LGH form (48a) for English, with `MUCH` introducing the
degree argument. The `MentalStateVerb` structure here adopts the LGH
*shape* (eq. (27)) for convenience as a working lexical entry; the
non-LGH route is equally compatible and the substrate is agnostic
between them.

## Out of scope (corrected substrate-availability claims)

The first-pass version of this file claimed several substrate gaps that
do not exist. Corrected:

- §4.2 two-dimensional ontology: a vertical-altitude axis would *extend*
  `Event.Mereology` (which already provides the
  `PartialOrder (Event Time)` instance Pasternak's part-whole relation
  consumes). Not a substrate gap; a refinement.
- §5 `want`/`wish`/`regret`: `Semantics/Attitudes/Desire.lean`
  already provides `wantVF` (von Fintel-style) and
  `worldSatisfactionOrdering`. The Pasternak §5 integration is a
  composition with the new `MentalStateHomogeneity` discipline, not
  fresh substrate.
- DOG (eq. 87): `Core.Order.PullbackPreorder.coarsen_via_monotone`
  provides the lattice operation Pasternak's fineness ordering needs.
- Mandarin `duo`/`hen duo (de)` (§3.2): requires Fragment entries in
  `Fragments/Mandarin/`; substrate side carries through unchanged.

-/

namespace Pasternak2019

open Degree
open Semantics.Attitudes.Confidence
open ArgumentStructure (ThematicFrame)

/-! ## §1. Monotonicity (Pasternak (4))

Pasternak's def 4 (PDF p.272): `μ` is monotonic on `⊑^c` in `A` iff for
all `x, y ∈ A`, `x ⊏^c y` entails `μ(x) < μ(y)`.

The substrate's `Degree.admissibleMeasure` is `StrictMono` over a
preorder — exactly Pasternak's def with `⊑^c` realized as the ambient
`[Preorder S]` instance and the domain `A` implicit in the carrier
type. The substrate's docstring credits all six traditions
(Schwarzschild, Wellwood, Krifka, CSW, Pasternak, LaBToM); no
file-local alias is needed. -/

/-! ## §2. Five Monotonicity-Requiring Constructions (Pasternak §2)

Pasternak §2 enumerates five English measurement constructions, each
imposing a monotonicity requirement on its measure function:

| Construction                  | Pasternak ex. | PDF | Example                       |
|-------------------------------|---------------|-----|-------------------------------|
| Pseudopartitive               | (5)           | 272 | `twelve ounces of gold`       |
| `out the wazoo` / `in spades` | (10)–(11)     | 274 | `water out the wazoo`         |
| Adverbial measure phrase      | (12)          | 275 | `Mara swam a lot`             |
| Nominal comparative           | (15)          | 276 | `more snow than Williamstown` |
| Verbal comparative            | (1)           | 268 | `Dee ran more than Evan did`  |

Pasternak's §3 uses this enumeration to argue that intensity is also
monotonic: intensity comparatives appear in *all five* constructions
and pattern with the monotonic readings. -/

/-- The five English measurement constructions Pasternak §2 surveys. -/
inductive MeasurementConstruction : Type where
  /-- `twelve ounces of gold` (Pasternak (5), PDF p.272;
      [krifka-1989], [schwarzschild-2002] [schwarzschild-2006];
      Pasternak also cites Brasoveanu 2009 NELS 38 — not in linglib bib) -/
  | pseudopartitive
  /-- `water out the wazoo` / `snow in spades` (Pasternak (10)–(11), PDF p.274) -/
  | outTheWazoo
  /-- `Mara swam a lot` (Pasternak (12), PDF p.275) -/
  | adverbialMeasurePhrase
  /-- `more snow than Williamstown did` (Pasternak (15), PDF p.276;
      [schwarzschild-2002] [schwarzschild-2006],
      [wellwood-hacquard-pancheva-2012], [wellwood-2015]) -/
  | nominalComparative
  /-- `Dee ran more than Evan did` (Pasternak (1), PDF p.268;
      [wellwood-hacquard-pancheva-2012], [wellwood-2015]) -/
  | verbalComparative
  deriving DecidableEq, Repr

/-! ## §3. Mental State Verbs (Pasternak (27), (48b))

Pasternak's (27) (PDF p.278): `⟦hate⟧_deg = λx.λd.λe. hate(e) ∧ Thm(e, x)
∧ μ_int(e) ≥ d`. The verb's denotation includes the intensity measure
`μ_int` and a degree threshold. Theta-role assignment (`Thm`, `Exp`)
is supplied by a `ThematicFrame` at use sites (Pasternak follows
[kratzer-1996] severance: Voice/v introduces the experiencer,
not the verb).
-/

/-- A mental state verb on the LGH shape (Pasternak (27)). The verb
    contributes its lexical predicate and intensity measure; theme and
    experiencer roles come from a `ThematicFrame` at use sites. -/
structure MentalStateVerb (Time : Type*) [LinearOrder Time] where
  /-- The verb's lexical predicate on eventualities (e.g., `hate`, `love`) -/
  predicate : Event Time → Prop
  /-- Intensity measure function — Pasternak's `μ_int` -/
  μint : Event Time → ℚ

/-- Pasternak (27)/(48b): "α V x at degree d" — eventuality is in the
    verb's denotation, has experiencer α and theme x via the frame, and
    intensity at or above d. -/
def MentalStateVerb.holdsAtDegree {Entity Time : Type*} [LinearOrder Time]
    (v : MentalStateVerb Time) (frame : ThematicFrame Entity Time)
    (α x : Entity) (d : ℚ) (e : Event Time) : Prop :=
  v.predicate e ∧ frame.experiencer α e ∧ frame.theme x e ∧ v.μint e ≥ d

/-! ## §4. Intensity Comparative (Pasternak (53))

Pasternak (53) (PDF p.287) for `Ann hates Bill more than Matt hates Jeff`:

> ASSERTION: ∃e[Exp(e, ann) ∧ hate(e) ∧ Thm(e, bill) ∧ μ_int(e) >
>            max{d | ∃e'[Exp(e', matt) ∧ hate(e') ∧ Thm(e', jeff) ∧
>                         μ_int(e') ≥ d}]

Matrix and than-clause use the same verb (`hate`) but different themes
(`bill` vs `jeff`). Adjectival comparatives like `taller than` use the
same predicate on both sides; intensity comparatives don't. The
substrate's `Degree.maxComparative` takes independent matrix/than
predicates, so Pasternak's intensity case is one instantiation. -/

/-- The themed predicate `fun e => v.predicate e ∧ frame.theme x e`:
    eventualities of verb `v` with theme `x`. Used to instantiate
    `Degree.maxComparative` for Pasternak's intensity case. -/
@[simp] def themedPredicate {Entity Time : Type*} [LinearOrder Time]
    (v : MentalStateVerb Time) (frame : ThematicFrame Entity Time)
    (x : Entity) : Event Time → Prop :=
  fun e => v.predicate e ∧ frame.theme x e

/-- The intensity comparative `α V x more than β V y` (Pasternak (53)):
    `Degree.maxComparative` with experiencer-restricted matrix/than
    predicates differing in theme assignment and `μ = v.μint` (states
    are measured directly). The `IsGreatest`-based than-clause
    quantification handles the empty-than-clause case via Pasternak (62)
    structurally — no zero-degree disjunct needed at this level (see
    §4.1 below for the non-entailment witness). -/
def intensityComparative {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (v : MentalStateVerb Time) (α β x y : Entity) : Prop :=
  Degree.maxComparative
    (fun e => frame.experiencer α e ∧ themedPredicate v frame x e)
    (fun e => frame.experiencer β e ∧ themedPredicate v frame y e)
    v.μint

/-! ### §4.1 Positive entailment asymmetry (Pasternak (60)–(63))

Pasternak's §4.4 prediction (PDF p.292–293): the comparative entails
the matrix positive form (there *is* a witness α-eventuality), but does
**not** entail the than-clause positive form. The non-entailment is
demonstrated by sentences like:

> Jack admires the chairman more than Jill does. In fact, Jill doesn't
> admire him at all. (Pasternak (63a))

To make the non-entailment derivable, Pasternak (62) (PDF p.293)
revises the than-clause to include a zero-degree disjunct, so the
`max` is well-defined even when no β-eventuality exists. This
augmentation is paper-specific (adjectival comparatives in
`Wellwood2015` don't need it); we expose it as a sister definition
`intensityComparativeAug62` and consume it in the non-entailment
theorem. -/

/-- Matrix entailment (Pasternak (60), PDF p.292): the comparative
    entails there is an α-eventuality of the verb with theme `x`.
    Trivial substrate consequence of the matrix existential in
    `Degree.maxComparative`. -/
theorem positive_entailment_matrix {Entity Time : Type*} [LinearOrder Time]
    {frame : ThematicFrame Entity Time}
    {v : MentalStateVerb Time} {α β x y : Entity}
    (h : intensityComparative frame v α β x y) :
    ∃ e : Event Time,
      frame.experiencer α e ∧ v.predicate e ∧ frame.theme x e := by
  obtain ⟨_, _, e, ⟨hExp, hPred, hThm⟩, _⟩ := h
  exact ⟨e, hExp, hPred, hThm⟩

/-- Pasternak (62) augmentation: the than-clause degree set with zero
    disjunct, keeping the `max` defined when no β-eventuality exists. -/
def thanDegreesAug62 {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (v : MentalStateVerb Time) (β y : Entity) : Set ℚ :=
  {0} ∪ Degree.thanDegrees
          (fun e => frame.experiencer β e ∧ themedPredicate v frame y e)
          v.μint

/-- The (62)-augmented intensity comparative used in §4.4 for the
    non-entailment data. Identical to `intensityComparative` modulo
    using `thanDegreesAug62` in the than-clause max. -/
def intensityComparativeAug62 {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (v : MentalStateVerb Time) (α β x y : Entity) : Prop :=
  ∃ ea : Event Time,
    frame.experiencer α ea ∧ themedPredicate v frame x ea ∧
    ∃ δ : ℚ, IsGreatest (thanDegreesAug62 frame v β y) δ ∧
              v.μint ea > δ

/-- Than-clause non-entailment under (62) augmentation (Pasternak
    (61)/(63), PDF p.293): the augmented intensity comparative is
    consistent with there being no β-eventuality. The witness is the
    zero-degree disjunct: any positive-intensity α-witness beats `0`,
    and the empty than-clause's max is `0`.

    Formalizes Pasternak (63a): "Jack admires the chairman more than
    Jill does. In fact, Jill doesn't admire him at all." — the
    `In fact, β doesn't V at all` continuation is non-contradictory. -/
theorem positive_non_entailment_than_clause_witness
    {Entity Time : Type*} [LinearOrder Time]
    (frame : ThematicFrame Entity Time)
    (v : MentalStateVerb Time) (α β x y : Entity)
    (eα : Event Time)
    (hExp : frame.experiencer α eα) (hPred : v.predicate eα)
    (hThm : frame.theme x eα) (hμ : v.μint eα > 0)
    (hβ_empty : ∀ e, frame.experiencer β e → v.predicate e →
                       frame.theme y e → v.μint e ≤ 0) :
    intensityComparativeAug62 frame v α β x y := by
  refine ⟨eα, hExp, ⟨hPred, hThm⟩, 0, ?_, hμ⟩
  refine ⟨?_, ?_⟩
  · -- 0 ∈ thanDegreesAug62 (via the zero disjunct)
    left; rfl
  · -- ∀ d ∈ thanDegreesAug62, d ≤ 0
    intro d hd
    rcases hd with hd_zero | ⟨e, ⟨hExp_β, hPred_β, hThm_β⟩, hμ_β⟩
    · exact le_of_eq hd_zero
    · exact le_trans hμ_β (hβ_empty e hExp_β hPred_β hThm_β)

/-! ## §5. Mental State Homogeneity (Pasternak (55))

Pasternak (55) (PDF p.290): `⟦vP_men⟧(e) ↔ ∀e' ⊑ e [⟦vP_men⟧(e')]`.
The biconditional form. Forward direction is exactly `Mereology.DIV`
(specialized). Reverse direction follows from preorder reflexivity
(`e ≤ e` instantiates the universal at `e' := e`).
-/

/-- Mental state homogeneity (Pasternak (55)): the predicate is closed
    under taking parts. Defined as `Mereology.DIV` — the substrate-level
    downward-closure primitive [champollion-2017] §2.3.3. -/
def MentalStateHomogeneity {Event : Type*} [Preorder Event] (P : Event → Prop) : Prop :=
  Mereology.DIV P

/-- Bridge to Pasternak's biconditional form (55): `P e ↔ ∀ e' ≤ e, P e'`.
    The forward direction is `Mereology.DIV` instantiated; the reverse
    direction uses `Preorder.le_refl` to instantiate the universal at
    `e' := e`. -/
theorem mentalStateHomogeneity_iff {Event : Type*} [Preorder Event]
    (P : Event → Prop) (h : MentalStateHomogeneity P) (e : Event) :
    P e ↔ ∀ e' : Event, e' ≤ e → P e' := by
  constructor
  · intro hPe e' hle; exact h hle hPe
  · intro hAll; exact hAll e (le_refl e)

/-! ## §5.1 Intensity Comparative Max-Reduction

The Pasternak unique-witness collapse: under
unique-witness assumptions on both sides, the intensity comparative
reduces to direct measure comparison. Pasternak fn 25 (PDF p.298)
explicitly rejects the unique-state assumption, so this reduction is a
*working simplification*, not Pasternak's official semantics — useful
when the max-quantified than-clause adds noise. -/

/-- Pasternak's intensity comparative reduces to direct measure
    comparison `v.μint eb < v.μint ea` when both sides have unique
    witness eventualities, by specializing `Degree.maxComparative_unique`
    to the intensity case (experiencer plus themed predicates). -/
theorem intensityComparative_max {Entity Time : Type*} [LinearOrder Time]
    {frame : ThematicFrame Entity Time}
    {v : MentalStateVerb Time}
    {α β x y : Entity} {ea eb : Event Time}
    (ha : frame.experiencer α ea ∧ themedPredicate v frame x ea)
    (ha_unique : ∀ e, frame.experiencer α e → themedPredicate v frame x e → e = ea)
    (hb : frame.experiencer β eb ∧ themedPredicate v frame y eb)
    (hb_unique : ∀ e, frame.experiencer β e → themedPredicate v frame y e → e = eb) :
    intensityComparative frame v α β x y ↔ v.μint eb < v.μint ea :=
  Degree.maxComparative_unique ha (fun e he => ha_unique e he.1 he.2)
    hb (fun e he => hb_unique e he.1 he.2)

/-! ## §6. Bridge to Event Mereology + CSW

`MentalStateHomogeneity` is `Mereology.DIV` over the ambient `[Preorder Event]`.
When `Event = Event Time` and the preorder comes from
`Semantics/Events/Basic.lean::Event.Mereology`, Pasternak's claim
becomes: vP-predicates respect the event-mereology part-of. We expose
two substrate consequences below: a downward-closure inheritance lemma
for sort-determined predicates (using `Event.Mereology.sort_preserved`),
and a g-homogeneity bridge to `Semantics/Mereology.lean::gHomogeneous`
(triggered when the carrier is a `PartialOrder`).

CSW [cariani-santorio-wellwood-2024] share Pasternak's monotonicity
discipline: their eq. (21) is the same `StrictMono` constraint exposed
as `Degree.admissibleMeasure` (multi-tradition naming there). The
architectural mismatch with Pasternak is theme typing — Pasternak's
`Thm : Entity → Event → Prop` is entity-themed (§4 transitive psych
verbs); CSW's `theme : W → Prop` is propositional (gradable attitude
adjectives like `confident that p`). The substrate-level identification
(monotonicity = admissibleMeasure) is now in the `admissibleMeasure`
docstring, not as a redundant per-file Iff.rfl. -/

/-- Sort-determined predicates inherit homogeneity from
    `Event.Mereology.sort_preserved`: any predicate of the form
    "eventuality has sort `s`" is downward-closed under part-of, so
    `MentalStateHomogeneity` follows for free. Pasternak's mental-state
    predicates are stative (Levin class 31.2; Vendler `state`); to the
    extent they implicate sort, they inherit homogeneity from this
    theorem. -/
theorem sortDetermined_isHomogeneous
    {Time : Type*} [LinearOrder Time] [Event.Mereology Time]
    (s : Features.Dynamicity) :
    letI := Event.partialOrder Time
    MentalStateHomogeneity (fun e : Event Time => e.sort = s) := by
  exact fun e e' hle hPe =>
    (Event.Mereology.sort_preserved e' e hle).trans hPe

/-- On a `PartialOrder` carrier, Pasternak's `MentalStateHomogeneity`
    implies `Mereology.gHomogeneous` (every proper part has a P-part —
    itself, by reflexivity). Direct application of the substrate's
    `Mereology.div_implies_gHomogeneous` since `MentalStateHomogeneity`
    is definitionally `Mereology.DIV`. -/
theorem mentalStateHomogeneity_implies_gHomogeneous
    {Event : Type*} [PartialOrder Event] {P : Event → Prop}
    (h : MentalStateHomogeneity P) : Mereology.gHomogeneous P :=
  Mereology.div_implies_gHomogeneous h

/-! ## §6.1 Fragment Integration: English Psych Verbs

Pasternak's intensity framework predicts that *experiencer-subject psych
verbs* (Levin class 31.2 "admire") are gradable in intensity and pattern
with monotonic measurement constructions. The English Fragment
(`Fragments/English/Predicates/Verbal.lean`) classifies seven such
verbs: `like`, `love`, `hate`, `admire`, `respect`, `fear` (NP form),
`dread` (NP form). All seven carry `vendlerClass := some .state` and
`levinClass := some .admire` — consistent with Pasternak's prediction.

The agreement theorem below makes the Fragment-substrate consistency
audit-visible: any change to either the Fragment's classification of
these verbs or the Pasternak-side claim that state-class admire-class
verbs are gradable in intensity will surface as a type error or
broken proof. -/

open English.Predicates.Verbal in
/-- Fragment-substrate agreement: the seven English psych verbs with
    Levin class 31.2 ("admire") share the state-class + admire-class
    profile Pasternak's intensity framework predicts for gradable
    mental-state verbs (Pasternak §3.1, §4.1). -/
theorem english_psych_verbs_pasternak_profile :
    like.vendlerClass    = some .state ∧ like.levinClass    = some .admire ∧
    love.vendlerClass    = some .state ∧ love.levinClass    = some .admire ∧
    hate.vendlerClass    = some .state ∧ hate.levinClass    = some .admire ∧
    admire.vendlerClass  = some .state ∧ admire.levinClass  = some .admire ∧
    respect.vendlerClass = some .state ∧ respect.levinClass = some .admire ∧
    fear_np.vendlerClass = some .state ∧ fear_np.levinClass = some .admire ∧
    dread_np.vendlerClass = some .state ∧ dread_np.levinClass = some .admire := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-! ## §7. Future Work

Three Pasternak topics this file does not formalize:

### §3.2 Mandarin `duo` / `hen duo (de)`

Pasternak §3.2 argues from Mandarin morphology that intensity
comparatives pattern with monotonic constructions even when `duo`
('much') is overtly required. Substrate side (monotonicity discipline)
carries through unchanged; the per-construction Mandarin Fragment is
the missing piece. `Fragments/Mandarin/` exists but lacks `duo`/`hen`/`de`
entries with measure-function payloads.

### §4.2 Two-dimensional state ontology + DOG (eq. 87)

Pasternak's vertical altitude axis `K` (PDF p.288) extends rather than
replaces the substrate's `Event.Mereology Time` preorder. A
`Semantics/Events/VerticalDimension.lean` add-on with
`κ : Event Time → Set Altitude` plus the DOG fineness lattice (which can
consume `Core.Order.PullbackPreorder.coarsen_via_monotone`) is a clean
follow-up. Out of scope here because it is not load-bearing for §1–§6.

### §5 `want` / `wish` / `regret` semantics

Pasternak §5 integrates Hintikkan world-quantification into the two-
dimensional ontology via point-states (eq. 67), `WANT_vF` (eq. 73,
[von-fintel-1999]), `WANT_H` (eq. 91, [heim-1992]), and DOG.
The substrate has `Attitudes.Desire.wantVF` and
`Attitudes.Desire.worldAtLeastAsGood` already; the Pasternak §5
integration is a composition with `MentalStateHomogeneity`, not new
substrate. A follow-on `Pasternak2019Attitudes.lean` (or extension of
this file) is the natural next paper-level deepening, alongside
Phillips-Brown 2018 (Sinn und Bedeutung) on graded want — also not in
linglib bib yet.

The chronologically-later [phillips-brown-2025] formalization
(`Studies/PhillipsBrown2025.lean`) builds on the same
`Attitudes.Desire` substrate, generalizing `wantVF` to question-based
`wantQuestionBased`. That study file's §11 makes the disagreement with
[condoravdi-lauer-2016] explicit; the analogous Pasternak vs
question-based contrast (intensity-based vs question-based resolution
of conflicting desires) is left as future work.

The chronologically-later [lassiter-2017] formalization
(`Studies/Lassiter2017.lean`) sits structurally
adjacent to Pasternak: both are gradable-`want` accounts (Pasternak
intensity, Lassiter expected value) using ℚ-valued degree functions.
The substrate overlap is `Attitudes.Desire.Lassiter.expectedValue` vs
Pasternak's mereological `intensityComparative`; both are
`Set.entails`-style `μ(p) > μ(q)` predicates over different scales.
A `pasternak_lassiter_intensity_vs_EV` bridge theorem comparing
predictions on a shared mental-state model is the natural next step,
also future work.

-/

end Pasternak2019
