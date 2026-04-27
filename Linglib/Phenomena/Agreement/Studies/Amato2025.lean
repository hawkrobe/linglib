import Linglib.Theories.Syntax.Minimalist.NestedAgree
import Linglib.Phenomena.Case.Studies.Marantz1991

/-!
# @cite{amato-2025} — Agreement case studies via Nested Agree
@cite{sigurdsson-holmberg-2008}

@cite{amato-2025} (NLLT) advances *Nested Agree* — formalized at
`Theories/Syntax/Minimalism/NestedAgree.lean` — as a unifying account
across at least six syntactic phenomena. This file collects the
case studies whose primary phenomenon is **agreement**:

- **§4.1.2 — Icelandic DAT-NOM intervention** (`DatNom`): quirky-dative
  subjects with nominative objects exhibit optional agreement with the
  lower nominative across the structurally higher dative. Derived from
  *feature ordering on T* (@cite{sigurdsson-holmberg-2008}).
- **§4.2.1 — Lak perfective person agreement** (`Lak`): in the
  Nakh-Daghestanian language Lak, perfective aspect forces person
  agreement on the lowest argument (the absolutive), even across the
  unmarked ergative subject. Derived from a Nested Agree configuration
  on Asp with cyclic Agree threading the φ-features from the
  absolutive through v.

The Italian auxiliary selection chapter (§3) lives at
`Phenomena/AuxiliaryVerbs/Studies/Amato2025.lean` (different primary
phenomenon). Cross-domain cases beyond agreement — Bulgarian
multiple wh-fronting (§4.2.3), ditransitive case alignments (§4.1.1)
— are deferred to future companion files in their respective
phenomenon directories.

## Cross-domain validation thesis

Every case study here uses *the same* `NestedAgreeConfig` shape with
*zero* API changes — different `SyntacticObject`s, different choices
of `goalHead`, different `validGoal` predicates, but one Theory layer.
This validates `NestedAgree.lean` as a genuine cross-domain primitive
rather than Italian-shaped scaffolding.

## Related infrastructure

`Phenomena/Case/Studies/Marantz1991.lean` contains an independent
treatment of dative intervention via `DativeInterventionContext` and
`dativeIntervenes`. Bridge theorems connecting Marantz's threshold
analysis to Amato's feature-ordering analysis are future work.
-/

namespace Phenomena.Agreement.Studies.Amato2025

open Minimalist
open Minimalist.NestedAgree

-- ════════════════════════════════════════════════════════════════════════════
-- Part A: §4.1.2 — Icelandic DAT-NOM intervention
-- ════════════════════════════════════════════════════════════════════════════

/-! ## Part A: Icelandic DAT-NOM intervention (Amato §4.1.2)

Icelandic *quirky* dative subjects with nominative objects exhibit a
well-known optionality. @cite{amato-2025} §4.1.2 derives this from two
co-existing feature orderings on T (@cite{sigurdsson-holmberg-2008}):

- **Ordering A**: `[*case:nom*] ≻ [*φ:_*]` — case-Agree fires first
  and selects the nominative DP (skipping the case-marked dative
  subject); φ-Agree by Nested Agree must target the same goal,
  yielding agreement with the nominative.
- **Ordering B**: `[*φ:_*] ≻ [*case:nom*]` — φ-Agree fires first and
  hits the dative subject (closest), but the dative is φ-defective
  for valuation purposes; default 3sg agreement surfaces.

The two orderings give two `NestedAgreeConfig`s with the same root
`SyntacticObject` but different `goalHead` choices and `validGoal`
predicates. Optionality follows from which is well-formed.

**Out of scope**: biclausal Icelandic (Amato 29b, requires modeling
clause embedding); the Sigurðsson-Holmberg A/B/C dialect taxonomy
(this section proves optionality holds in Icelandic A; B/C variation
is a follow-up). -/

namespace DatNom

/-- Matrix T (the probing head). -/
private def aT : LIToken := ⟨LexicalItem.simple .T [], 0⟩
/-- The lexical V (irrelevant for Agree but present structurally
    between the dative subject and the nominative object). -/
private def aV : LIToken := ⟨LexicalItem.simple .V [], 1⟩
/-- The quirky-dative subject. -/
private def aDPdat : LIToken := ⟨LexicalItem.simple .D [], 2⟩
/-- The nominative object — the surface agreement target under
    ordering A. -/
private def aDPnom : LIToken := ⟨LexicalItem.simple .D [], 3⟩

/-- T's probe with C horizon. The two orderings use the same probe
    profile twice; the ordering distinction is captured by `goalHead`
    and `validGoal` in the two configs below. -/
private def tProbe : ProbeProfile := ⟨.T, some .C⟩

/-! ### Configuration A — agreement with the nominative -/

/-- Ordering A: `[*case:nom*] ≻ [*φ:_*]`. Case-Agree skips the
    case-marked dative and reaches the nominative; φ-Agree by Nested
    Agree must target the same nominative goal. All heads are
    phi-active under this ordering — the dative is irrelevant since
    it's not the chosen goal. Tree: `T [DPdat [V DPnom]]`, goal = DPnom. -/
def icelandicOrderingA : NestedAgreeConfig :=
  standardConfig tProbe aT aDPdat aV aDPnom aDPnom (fun _ => true)

/-- Ordering A is well-formed: T c-commands DPnom in `icelandicTree`,
    and DPnom is phi-active. -/
theorem orderingA_is_nested : IsNestedAgreeConfig icelandicOrderingA := by decide

theorem orderingA_runStack_0 :
    runStack icelandicOrderingA 0 = some (.leaf aDPnom) := by decide

theorem orderingA_runStack_1 :
    runStack icelandicOrderingA 1 = some (.leaf aDPnom) := by decide

/-- **Apparent dative intervention is not actual.** The dative subject
    is in T's c-command (probe 0's domain) but is *not* in DPnom's
    daughters (DPnom doesn't c-command DPdat — DPdat is structurally
    above DPnom). DPdat is excluded from probe 1's truncated domain
    by Nested Agree. -/
theorem orderingA_excludes_dative :
    SyntacticObject.leaf aDPdat ∈ icelandicOrderingA.searchDomain 0 ∧
    SyntacticObject.leaf aDPdat ∉ icelandicOrderingA.searchDomain 1 :=
  apparent_intervener_excluded icelandicOrderingA 0 (.leaf aDPdat)
    (by decide) (by decide)

/-! ### Configuration B — default agreement -/

/-- Ordering B: `[*φ:_*] ≻ [*case:nom*]`. φ-Agree fires first and hits
    the dative subject (closest), but the dative's φ-features are
    quirky/defective for finite T's valuation purposes. -/
def icelandicOrderingB : NestedAgreeConfig :=
  standardConfig tProbe aT aDPdat aV aDPnom aDPdat
    (fun y => decide (y ≠ .leaf aDPdat))

/-- Ordering B is *not* well-formed: the chosen goal is φ-defective.
    The formal expression of "default agreement surfaces because
    π-Agree on T fails to value." -/
theorem orderingB_not_nested : ¬ IsNestedAgreeConfig icelandicOrderingB := by decide

theorem orderingB_runStack_1_fails :
    runStack icelandicOrderingB 1 = none := by decide

/-! ### Optionality -/

/-- **Monoclausal optionality** (Amato 29a, Sigurðsson-Holmberg 2008
    Icelandic A): the same surface tree admits both feature orderings,
    so both agreement outcomes are predicted. The optionality is a
    property of T's feature ordering, not of the underlying structure. -/
theorem icelandic_optionality :
    IsNestedAgreeConfig icelandicOrderingA ∧
    ¬ IsNestedAgreeConfig icelandicOrderingB :=
  ⟨orderingA_is_nested, orderingB_not_nested⟩

/-- Both orderings operate on the *same* root tree — the optionality
    is in the probe stack's feature ordering, not in the structural
    representation. -/
theorem orderingA_orderingB_same_tree :
    icelandicOrderingA.root = icelandicOrderingB.root := rfl

/-! ### Bridge to @cite{marantz-1991}'s threshold analysis

    @cite{marantz-1991} models dative intervention through a *case
    accessibility threshold*: a dative DP intervenes (blocks the probe)
    when its lexical case is below the probe's accessibility threshold
    (so the probe can't Agree with it) but it still blocks access to
    the intended target by minimality. The Marantz analysis produces
    a Bool `dativeIntervenes`; @cite{amato-2025} §4.1.2 produces a
    Prop `¬ IsNestedAgreeConfig orderingB`. The bridge below shows
    they make the same prediction on the same configuration. -/

/-- A `DativeInterventionContext` corresponding to ordering B's
    structural setup: dative present, standard `unmarked` threshold
    (lexical case is *not* accessible), nominative target. -/
def orderingB_marantzContext : DativeInterventionContext :=
  ⟨true, .unmarked, .unmarked⟩

/-- **Bridge**: under ordering B's parameter setting,
    @cite{marantz-1991}'s `dativeIntervenes` predicts intervention iff
    @cite{amato-2025}'s `IsNestedAgreeConfig` rejects the configuration.
    Both theories agree: dative intervention → agreement failure
    (default 3sg in Amato's surface, agreement-failure in Marantz's
    threshold model). -/
theorem marantz_amato_agree_on_dative_intervention :
    dativeIntervenes orderingB_marantzContext = true ∧
    ¬ IsNestedAgreeConfig icelandicOrderingB :=
  ⟨by decide, orderingB_not_nested⟩

end DatNom

-- ════════════════════════════════════════════════════════════════════════════
-- Part B: §4.2.1 — Lak perfective person agreement
-- ════════════════════════════════════════════════════════════════════════════

/-! ## Part B: Lak perfective person agreement (Amato §4.2.1)

Lak is a Nakh-Daghestanian language with ergative-absolutive case
marking. In the present tense, person agreement is controlled by the
external argument *if* it's not ergative-marked (1st/2nd person under
the differential ergativity pattern of @cite{radkevich-2017}); else
by the absolutive object. **In the perfective aspect, however, person
agreement is always controlled by the lowest argument (the
absolutive), even when the external argument is unmarked**
(@cite{amato-2025} §4.2.1, examples 31a–d).

Amato derives this from Nested Agree on the perfective Asp head:
Asp bears `[*Infl:perf*] ≻ [*π:_*]`. Infl-Agree fires first and
agrees with v (creating the channel); π-Agree by Nested Agree must
target the same v. v has prior π-Agreed with the absolutive object
via cyclic Agree (Legate 2005), so v carries the absolutive's
φ-features. Result: agreement on Asp surfaces as the absolutive's
φ-features, across the unmarked ergative.

Structurally identical to the Italian transitive aux selection
configuration (Italian: `Perf [DPsubj [v DPobj]]` → goal v;
Lak: `Asp [Erg [v Abs]]` → goal v). The same `NestedAgreeConfig`
shape applies — what changes is the linguistic interpretation of
the surface output.

**Out of scope**: non-perfective Lak (no Asp head, no Nested Agree
configuration, standard agreement controlled by case-marking
threshold per @cite{marantz-1991}-style accessibility); the
contrast between (31a/b) and (31c/d) demonstrating the perfective's
distinctive pattern. -/

namespace Lak

/-- The perfective Asp head (the probing head). -/
private def aAsp : LIToken := ⟨LexicalItem.simple .Asp [], 0⟩
/-- The light verb v — shared goal under Nested Agree, carrier of the
    absolutive's φ-features via prior cyclic Agree. -/
private def aV : LIToken := ⟨LexicalItem.simple .V [], 1⟩
/-- The ergative external argument. Apparent intervener. -/
private def aErg : LIToken := ⟨LexicalItem.simple .D [], 2⟩
/-- The absolutive internal argument. Source of the φ-features that
    surface on Asp via cyclic Agree through v. -/
private def aAbs : LIToken := ⟨LexicalItem.simple .D [], 3⟩

/-- Asp's probe with C horizon. Both `[*Infl:perf*]` and `[*π:_*]`
    use the same profile; the Nested Agree ordering is captured by
    list position, the shared goal by `goalHead`. -/
private def aspProbe : ProbeProfile := ⟨.T, some .C⟩

/-- The Lak perfective configuration. Tree: `Asp [Erg [v Abs]]`,
    goal = v. v is reachable (c-commanded by Asp) and phi-active
    (carries Abs's φ via cyclic Agree). -/
def lakPerfective : NestedAgreeConfig :=
  standardConfig aspProbe aAsp aErg aV aAbs aV (fun _ => true)

theorem lakPerfective_is_nested : IsNestedAgreeConfig lakPerfective := by decide

theorem lakPerfective_runStack_0 :
    runStack lakPerfective 0 = some (.leaf aV) := by decide

theorem lakPerfective_runStack_1 :
    runStack lakPerfective 1 = some (.leaf aV) := by decide

/-- **Apparent ergative intervention is not actual.** The ergative
    subject is in Asp's c-command (probe 0's domain) but is *not* in
    v's daughters (v doesn't c-command Erg — Erg is structurally
    above v in Spec,vP). Erg is therefore excluded from probe 1's
    truncated domain.

    This is @cite{amato-2025} §4.2.1's structural resolution of the
    Lak agreement puzzle: the ergative looks like a closer goal but
    Nested Agree restricts probe 1 to v's subtree, where Erg has no
    presence. Surface result: agreement with Abs (transitively
    through v's prior cyclic Agree). -/
theorem lakPerfective_excludes_ergative :
    SyntacticObject.leaf aErg ∈ lakPerfective.searchDomain 0 ∧
    SyntacticObject.leaf aErg ∉ lakPerfective.searchDomain 1 :=
  apparent_intervener_excluded lakPerfective 0 (.leaf aErg)
    (by decide) (by decide)

end Lak

end Phenomena.Agreement.Studies.Amato2025
