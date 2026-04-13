import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Basic
import Linglib.Theories.Syntax.Minimalism.Core.ClauseSpine

/-!
# Probe Profiles (@cite{keine-2019}, @cite{keine-2020})

A probe's locality behavior is determined by two properties: where it sits
in the functional sequence (`probeHead`) and what terminates its search
(`horizon`). @cite{keine-2020} shows that selective opacity — where
the same domain is opaque to some operations but transparent to others —
is a property of probes, not of domains.

## Two Transparency Models

This file provides two transparency models:

1. **Bilateral labeling** (`transparentToLabel`): the proper model from
   @cite{keine-2020} chapter 3. A probe's search terminates when it
   encounters a domain whose *bilateral label* (= projected heads)
   contains the horizon category. This correctly handles partially
   ordered clause types (NmlzP vs CP in Hindi).

2. **F-value approximation** (`transparentTo`): the simplified model
   from @cite{keine-2019}. Uses `fValue clauseHead < fValue probeHead`
   as an approximation. Valid when all clause types are linearly ordered
   within a single extended projection, but fails for NmlzP/CP.

## Language Parameterization

@cite{keine-2020} shows that probe horizons are *language-specific*:
Hindi, English, and German each have different probe–horizon pairings.
`LanguageProbeConfig` bundles per-language settings.

## Architecture

This file imports `ExtendedProjection/Basic.lean` (for `fValue`, `Cat`,
`ComplementSize`) and `ClauseSpine.lean` (for bilateral label checks in
vacuity and BIM theorems). The full Agree operation, tree-based horizons,
and satisfaction conditions remain in `Agree.lean`, which imports this file.
-/

namespace Minimalism

-- ============================================================================
-- § 1: Probe Profiles
-- ============================================================================

/-- A probe's identity: where it sits in the functional sequence and
    what terminates its search.

    @cite{keine-2020} argues that selective opacity arises because
    probes differ in their *horizons* — the category that terminates
    their search. A probe on T⁰ with horizon T cannot search past TP,
    while a probe on C⁰ with no horizon can search into any clause.

    The A/Ā distinction is correlated with probe height but not
    strictly derived from it: probes on the same head can have
    different horizons (@cite{keine-2020} §3.6). -/
structure ProbeProfile where
  /-- The head that hosts this probe (T⁰, C⁰, etc.) -/
  probeHead : Cat
  /-- The category that terminates this probe's search.
      `none` means the probe can search into any domain. -/
  horizon : Option Cat
  deriving DecidableEq, Repr

/-- Is this an A-probe? A-probes sit at or below T (fValue ≤ 2).
    @cite{keine-2020} §3: A-movement lands in Spec,TP (fValue 2). -/
def ProbeProfile.isAProbe (p : ProbeProfile) : Bool :=
  fValue p.probeHead ≤ 2

/-- Is this an Ā-probe? Ā-probes sit at or above C (fValue ≥ 6).
    @cite{keine-2020} §3: Ā-movement lands in Spec,CP (fValue 6). -/
def ProbeProfile.isĀProbe (p : ProbeProfile) : Bool :=
  fValue p.probeHead ≥ 6

-- ============================================================================
-- § 2: Bilateral Labeling Transparency (@cite{keine-2020} ch. 3)
-- ============================================================================

/-- Is a domain with the given bilateral label transparent to this probe?

    @cite{keine-2020} §3.3.2: under bilateral labeling, both head and
    complement project labels. A CP's label is `[C, T, v, V]` — the set
    of all projected heads. A probe's search terminates when it encounters
    a domain whose bilateral label CONTAINS the horizon category.

    A domain is transparent iff:
    - The probe has no horizon (`horizon = none`): always transparent.
    - The probe has a horizon: the horizon does NOT appear in the label.

    This model correctly handles partially ordered clause types:
    NmlzP's label `[V, v, T, Nmlz]` does not contain C (transparent to
    wh with horizon C), while CP's label `[V, v, T, C]` does not contain
    Nmlz (transparent to Ā with horizon Nmlz in Hindi). -/
def ProbeProfile.transparentToLabel (p : ProbeProfile) (label : List Cat) : Bool :=
  match p.horizon with
  | none => true
  | some h => !(label.any (· == h))

-- ============================================================================
-- § 3: F-Value Transparency (Simplified Model, @cite{keine-2019})
-- ============================================================================

/-- Is a clause with highest head `clauseHead` transparent to this probe?

    **Simplified (F-value) model** from @cite{keine-2019}: uses
    `fValue clauseHead < fValue probeHead` as an approximation of
    bilateral labeling. Valid when all clause types are linearly ordered
    within a single EP branch, but produces incorrect results for
    partially ordered clause types (NmlzP vs CP in Hindi).

    For the proper bilateral-labeling model, use `transparentToLabel`.

    A clause is transparent iff:
    - The probe has no horizon (`horizon = none`): always transparent.
    - The probe has a horizon: the clause's highest head is strictly
      below the probe head in the functional sequence
      (`fValue clauseHead < fValue probeHead`). -/
def ProbeProfile.transparentTo (p : ProbeProfile) (clauseHead : Cat) : Bool :=
  if p.horizon.isSome then fValue clauseHead < fValue p.probeHead else true

-- ============================================================================
-- § 4: The Four Article Probes (@cite{keine-2019} Table (58))
-- ============================================================================

/-! These four probes are from the 2019 LI article, which used a simplified
    3-clause-size model (vP, TP, CP). They remain useful for backward
    compatibility and for verifying the article's predictions. For the
    book's language-specific probe settings, see `LanguageProbeConfig`. -/

/-- φ-agreement probe: sits on T⁰, horizon is C.
    Can search into vP but not TP or CP clauses.
    Note: this is the @cite{keine-2019} article setting; the book
    refines Hindi φ to have horizon T (@cite{keine-2020} (219)). -/
def keinePhiProbe : ProbeProfile := ⟨.T, some .C⟩

/-- A-movement probe (EPP on T⁰): sits on T⁰, horizon is C.
    Same locality as φ-agreement — both are on T⁰. -/
def keineAProbe : ProbeProfile := ⟨.T, some .C⟩

/-- Wh-licensing probe: sits on C⁰, horizon is C.
    Can search into vP and TP but not CP clauses. -/
def keineWhLicensing : ProbeProfile := ⟨.C, some .C⟩

/-- Ā-movement probe from @cite{keine-2019}: sits on C⁰, no horizon.
    The 2019 article treated Ā as having no horizon.
    @cite{keine-2020} (219) refines this: Hindi Ā has horizon Nmlz,
    English Ā has horizon C, German topicalization has no horizon. -/
def keineĀProbe : ProbeProfile := ⟨.C, none⟩

-- ────────────────────────────────────────────────────────────────
-- Derived properties of the article probes
-- ────────────────────────────────────────────────────────────────

theorem phi_is_A : keinePhiProbe.isAProbe = true := by decide
theorem a_is_A : keineAProbe.isAProbe = true := by decide
theorem wh_is_Ā : keineWhLicensing.isĀProbe = true := by decide
theorem ābar_is_Ā : keineĀProbe.isĀProbe = true := by decide

-- ============================================================================
-- § 5: Language-Parameterized Probe Configs (@cite{keine-2020})
-- ============================================================================

/-- A language's probe configuration: the set of probes and their horizons.

    @cite{keine-2020} shows that probe horizons vary across languages.
    The same syntactic operation (e.g., Ā-movement) may have different
    horizons in Hindi (⊣ Nmlz), English (⊣ C), and German (⊣ ∅).

    The four fields correspond to the four operations in the transparency
    tables: φ-agreement, A-movement, wh-licensing, and Ā-movement. -/
structure LanguageProbeConfig where
  /-- φ-agreement probe -/
  phi : ProbeProfile
  /-- A-movement probe -/
  aMove : ProbeProfile
  /-- wh-licensing probe -/
  wh : ProbeProfile
  /-- Ā-movement / topicalization probe -/
  ābar : ProbeProfile
  deriving Repr

/-- Hindi probe settings (@cite{keine-2020} (219)).

    | Probe  | Head | Horizon |
    |--------|------|---------|
    | [*φ*]  | T⁰   | ⊣ T    |
    | [*A*]  | T⁰   | ⊣ T    |
    | [*wh*] | C⁰   | ⊣ C    |
    | [*Ā*]  | C⁰   | ⊣ Nmlz | -/
def LanguageProbeConfig.hindi : LanguageProbeConfig :=
  { phi  := ⟨.T, some .T⟩
    aMove := ⟨.T, some .T⟩
    wh   := ⟨.C, some .C⟩
    ābar := ⟨.C, some .Nmlz⟩ }

/-- English probe settings (@cite{keine-2020} (241)).

    | Probe    | Head | Horizon |
    |----------|------|---------|
    | [*A*]    | T⁰   | ⊣ C    |
    | [*wh*]   | C⁰   | ⊣ ∅    |
    | [*extr*] | T⁰   | ⊣ T    |

    English has three probes. The book does not list a separate φ-probe
    for English — we use the same settings as [*A*] (both on T⁰ ⊣ C).
    The wh-probe has no horizon — English wh-movement can cross CP
    boundaries. We map Ā-movement to wh (both on C⁰ with no horizon
    in English). The extraposition probe [*extr*] is stored separately
    (see `english_extr`). -/
def LanguageProbeConfig.english : LanguageProbeConfig :=
  { phi  := ⟨.T, some .C⟩
    aMove := ⟨.T, some .C⟩
    wh   := ⟨.C, none⟩
    ābar := ⟨.C, none⟩ }

/-- English extraposition probe (@cite{keine-2020} (241c)):
    [*extr*] on T⁰ with horizon T.

    Extraposition is more local than A-movement: it cannot cross
    even TP boundaries. This is the default horizon for T⁰. -/
def english_extr : ProbeProfile := ⟨.T, some .T⟩

/-- German probe settings (@cite{keine-2020} (367)).

    | Probe          | Head    | Horizon |
    |----------------|---------|---------|
    | [*scr*]        | T⁰      | ⊣ T    |
    | [*rel*]        | C⁰      | ⊣ C    |
    | [*wh*]         | C⁰      | ⊣ Force|
    | [*top_{(wh)}*] | Force⁰  | ⊣ ∅    |

    German has ForceP as a distinct clause size above CP (V2 clauses
    are ForcePs). The topicalization probe sits on Force⁰ and has no
    horizon — it can search into any domain. -/
def LanguageProbeConfig.german : LanguageProbeConfig :=
  { phi  := ⟨.T, some .T⟩
    aMove := ⟨.T, some .T⟩
    wh   := ⟨.C, some .Force⟩
    ābar := ⟨.Force, none⟩ }

/-- Itelmen probe settings (@cite{keine-2020} §3.4.5, (269), via
    @cite{bobaljik-wurmbrand-2005}).

    Itelmen allows optional LDA (φ-agreement) into nonfinite clauses,
    but A-movement out of them forces obligatory high scope. Crucially,
    there are locality constraints on agreement that do not apply to
    A-movement: A-movement is *more permissive* than φ-agreement.

    @cite{keine-2020} (269):
    - [*φ*] ⊣ T (φ-agreement more local than movement)
    - [*μ*] ⊣ ∅ (movement has no horizon)

    We model the embedded clause as TP-sized. The φ-probe has T as
    its horizon (blocked by TP), while the A-probe has no horizon
    (can cross TP). -/
def LanguageProbeConfig.itelmen : LanguageProbeConfig :=
  { phi  := ⟨.T, some .T⟩
    aMove := ⟨.T, none⟩
    wh   := ⟨.C, some .C⟩
    ābar := ⟨.C, none⟩ }

/-- Tsez probe settings (@cite{keine-2020} §3.4.5, (271), via
    @cite{polinsky-potsdam-2001}).

    Tsez allows LDA (φ-agreement) into an embedded clause, but
    disallows crossclausal movement. This is the *inverse* of Itelmen:
    A-movement is more permissive than φ-agreement in Itelmen, while
    φ-agreement is more permissive than A-movement in Tsez.

    @cite{keine-2020} (271):
    - [*φ*] ⊣ Force (φ-agreement is less local)
    - [*μ*] ⊣ Top (movement more local than φ)

    We simplify: the key point is the *direction* of the mismatch
    (φ more permissive than movement). We model this with φ having no
    horizon and A-movement having T as horizon. The book's specific
    Force/Top horizons require Tsez-specific clause structure that we
    do not model (footnote 23 acknowledges the horizons are
    underdetermined by the sparse evidence). -/
def LanguageProbeConfig.tsez : LanguageProbeConfig :=
  { phi  := ⟨.T, none⟩
    aMove := ⟨.T, some .T⟩
    wh   := ⟨.C, some .C⟩
    ābar := ⟨.C, none⟩ }

/-- Itelmen and Tsez demonstrate movement–agreement mismatches
    in *opposite directions*:

    - **Itelmen** ((269)): A-movement can cross boundaries that
      φ-agreement cannot. Movement is more permissive.
    - **Tsez** ((271)): φ-agreement can cross boundaries that
      A-movement cannot. Agreement is more permissive.

    This shows that movement and agreement can have *different*
    horizons, even when triggered by probes on the same head, and
    that there is no inherent directionality to this difference. -/
theorem itelmen_movement_agreement_mismatch :
    -- Itelmen: A-movement can probe into TP, φ-agreement cannot
    LanguageProbeConfig.itelmen.aMove.transparentTo .T = true ∧
    LanguageProbeConfig.itelmen.phi.transparentTo .T = false ∧
    -- Tsez: φ can probe into TP, A-movement cannot
    LanguageProbeConfig.tsez.phi.transparentTo .T = true ∧
    LanguageProbeConfig.tsez.aMove.transparentTo .T = false := by decide

-- ============================================================================
-- § 5b: Crosslinguistic A-Movement Typology (@cite{keine-2020} (300))
-- ============================================================================

/-! ### Three attested A-movement horizons (@cite{keine-2020} §3.6, (300))

@cite{keine-2020} identifies three crosslinguistically attested settings
for the A-movement probe, forming an entailment chain from most permissive
to most restrictive:

| Language       | A-probe horizon | Hyperraising? |
|----------------|-----------------|---------------|
| Lubukusu       | ⊣ ∅            | Yes (finite)  |
| English        | ⊣ C            | No (blocked by CP) |
| Hindi/Russian  | ⊣ T            | No (blocked by TP) |

These correspond to three points on the locality profile entailment
chain (305). -/

/-- Lubukusu A-probe: no horizon — hyperraising out of finite clauses.
    @cite{keine-2020} (300a). -/
def lubukusuAProbe : ProbeProfile := ⟨.T, none⟩

/-- The three A-movement settings form an entailment chain:
    Lubukusu (⊣ ∅) is strictly more permissive than English (⊣ C),
    which is strictly more permissive than Hindi (⊣ T).

    For any clause type, if Hindi allows A-movement into it, English
    does too; if English allows it, Lubukusu does too. -/
theorem a_movement_typology :
    -- Lubukusu ⊣ ∅: everything transparent
    lubukusuAProbe.transparentToLabel ClauseSpine.cP.projectedHeads = true ∧
    lubukusuAProbe.transparentToLabel ClauseSpine.tP.projectedHeads = true ∧
    -- English ⊣ C: TP transparent, CP opaque
    LanguageProbeConfig.english.aMove.transparentToLabel
      ClauseSpine.tP.projectedHeads = true ∧
    LanguageProbeConfig.english.aMove.transparentToLabel
      ClauseSpine.cP.projectedHeads = false ∧
    -- Hindi ⊣ T: vP transparent, TP and CP opaque
    LanguageProbeConfig.hindi.aMove.transparentToLabel
      ClauseSpine.vP.projectedHeads = true ∧
    LanguageProbeConfig.hindi.aMove.transparentToLabel
      ClauseSpine.tP.projectedHeads = false := by decide

-- ============================================================================
-- § 6: Default Horizon (@cite{keine-2020} (307))
-- ============================================================================

/-- The default horizon for a probe: the probe's own head category.

    @cite{keine-2020} (307): for any probe [*F*] on head X⁰, the default
    horizon is X itself. This is the maximally restrictive setting that
    is not vacuous — the probe can search into domains smaller than its
    own projection but not into domains of the same size or larger. -/
def ProbeProfile.defaultHorizon (probeHead : Cat) : ProbeProfile :=
  ⟨probeHead, some probeHead⟩

/-- A probe with the default horizon can search into domains strictly
    below its own F-level but not at or above it (in the fValue model). -/
theorem default_horizon_restrictive (head c : Cat)
    (h : fValue c ≥ fValue head) :
    (ProbeProfile.defaultHorizon head).transparentTo c = false := by
  simp [ProbeProfile.defaultHorizon, ProbeProfile.transparentTo, Option.isSome]
  omega

-- ============================================================================
-- § 6b: Locality Profile Entailment (@cite{keine-2020} (305))
-- ============================================================================

/-! ### Locality profiles form an entailment chain

@cite{keine-2020} §3.7, (305): different horizon choices yield locality
profiles in a strict entailment relationship. A lower horizon produces a
strictly more restrictive profile:

| Horizon | CP | TP | vP | VP |
|---------|----|----|----|----|
| ⊣ v     | *  | *  | *  | ✓  |
| ⊣ T     | *  | *  | ✓  | ✓  |
| ⊣ C     | *  | ✓  | ✓  | ✓  |
| ⊣ ∅     | ✓  | ✓  | ✓  | ✓  |

Each row is a strict superset of the one above it. -/

/-- Horizon entailment: ⊣ v ⊂ ⊣ T ⊂ ⊣ C ⊂ ⊣ ∅ (for a probe on C⁰).
    Each step adds exactly one more transparent clause type. -/
theorem locality_profile_entailment :
    let onC (hz : Option Cat) := ProbeProfile.mk .C hz
    -- ⊣ v: only VP transparent (but v is vacuous on C⁰, so untestable)
    -- ⊣ T: also vacuous on C⁰
    -- ⊣ C: TP, vP transparent; CP opaque
    (onC (some .C)).transparentToLabel ClauseSpine.tP.projectedHeads = true ∧
    (onC (some .C)).transparentToLabel ClauseSpine.cP.projectedHeads = false ∧
    -- ⊣ ∅: everything transparent
    (onC none).transparentToLabel ClauseSpine.cP.projectedHeads = true := by decide

/-- Horizon entailment for probes on T⁰: ⊣ T ⊂ ⊣ C ⊂ ⊣ ∅.
    This is the empirically relevant case (A-movement, φ-agreement). -/
theorem locality_profile_entailment_T :
    let onT (hz : Option Cat) := ProbeProfile.mk .T hz
    -- ⊣ T (default): only vP transparent
    (onT (some .T)).transparentToLabel ClauseSpine.vP.projectedHeads = true ∧
    (onT (some .T)).transparentToLabel ClauseSpine.tP.projectedHeads = false ∧
    -- ⊣ C: vP and TP transparent
    (onT (some .C)).transparentToLabel ClauseSpine.tP.projectedHeads = true ∧
    (onT (some .C)).transparentToLabel ClauseSpine.cP.projectedHeads = false ∧
    -- ⊣ ∅: everything transparent
    (onT none).transparentToLabel ClauseSpine.cP.projectedHeads = true := by decide

-- ============================================================================
-- § 7: Upward Entailment (@cite{keine-2020} (40))
-- ============================================================================

/-- **Upward Entailment** (@cite{keine-2020} ch. 3):
    If a clause of size Π is opaque to probe π, every larger clause
    (higher `fValue` for its highest head) is also opaque.

    Under bilateral labeling, this is an emergent property: a larger
    clause's label is a superset of a smaller clause's label, so if the
    horizon appears in the smaller label, it appears in the larger one too.

    This theorem proves it for the simplified fValue model. -/
theorem upward_entailment (p : ProbeProfile) (c₁ c₂ : Cat)
    (h_opaque : p.transparentTo c₁ = false)
    (h_larger : fValue c₁ ≤ fValue c₂) :
    p.transparentTo c₂ = false := by
  simp only [ProbeProfile.transparentTo] at *
  cases h_eq : p.horizon <;> simp_all [Option.isSome]
  omega

/-- Upward Entailment for bilateral labeling: if a label L₁ ⊆ L₂
    (every head in L₁ also appears in L₂), then opacity to L₁ implies
    opacity to L₂. -/
theorem upward_entailment_label (p : ProbeProfile)
    (L₁ L₂ : List Cat)
    (h_sub : ∀ c, c ∈ L₁ → c ∈ L₂)
    (h_opaque : p.transparentToLabel L₁ = false) :
    p.transparentToLabel L₂ = false := by
  simp only [ProbeProfile.transparentToLabel] at *
  cases h_hz : p.horizon with
  | none => simp_all
  | some h =>
    simp_all only [Bool.not_eq_false']
    rw [List.any_eq_true] at h_opaque ⊢
    obtain ⟨x, hx_mem, hx_eq⟩ := h_opaque
    exact ⟨x, h_sub x hx_mem, hx_eq⟩

-- ============================================================================
-- § 8: Height-Locality Connection (@cite{keine-2020} (20)/(33))
-- ============================================================================

/-- **Height-Locality Connection (HLC)** (@cite{keine-2020} (20)/(33)):
    The higher the structural position of a probe, the more kinds of
    structures it can search into.

    If probe π₂ is at least as high as π₁ (fValue p₁.probeHead ≤
    fValue p₂.probeHead) and both have horizons, then every clause
    transparent to π₁ is transparent to π₂. The Ā-probe (no horizon)
    trivially subsumes everything.

    This is the *empirical generalization*. The HLT (279) *derives*
    it from bilateral labeling + vacuity (see `height_locality_theorem`).

    Note: the HLC is a "connection" not an isomorphism — probes on the
    same head can differ in locality (@cite{keine-2020} §3.6). -/
theorem height_locality_connection (p₁ p₂ : ProbeProfile) (c : Cat)
    (h_higher : fValue p₁.probeHead ≤ fValue p₂.probeHead)
    (h_horizon : p₁.horizon = none → p₂.horizon = none)
    (h_transparent : p₁.transparentTo c = true) :
    p₂.transparentTo c = true := by
  simp only [ProbeProfile.transparentTo] at *
  cases h₁ : p₁.horizon <;> cases h₂ : p₂.horizon <;>
    simp_all [Option.isSome]
  omega

-- ============================================================================
-- § 9: Horizon Category Irrelevance (fValue model only)
-- ============================================================================

/-- In the simplified fValue model, the specific horizon category does
    not affect transparency — only whether a horizon exists matters.

    **Warning**: this does NOT hold under bilateral labeling. Under
    bilateral labeling, the horizon category matters because it
    determines which labels trigger search termination. This theorem
    is an artifact of the fValue approximation. -/
theorem horizon_category_irrelevant_fvalue (head : Cat) (h₁ h₂ : Cat) (c : Cat) :
    (ProbeProfile.mk head (some h₁)).transparentTo c =
    (ProbeProfile.mk head (some h₂)).transparentTo c := by
  simp [ProbeProfile.transparentTo]

/-- Under bilateral labeling, horizon category DOES matter.
    Example: wh (horizon C) finds NmlzP transparent, but Ā (horizon Nmlz)
    finds NmlzP opaque. Both probes are on C⁰ — only the horizon differs. -/
theorem horizon_category_relevant_label :
    let whProbe := (⟨.C, some .C⟩ : ProbeProfile)
    let āProbe := (⟨.C, some .Nmlz⟩ : ProbeProfile)
    let nmlzLabel := [Cat.V, .v, .T, .Nmlz]
    whProbe.transparentToLabel nmlzLabel = true ∧
    āProbe.transparentToLabel nmlzLabel = false := by decide

-- ============================================================================
-- § 10: Vacuous Probes (@cite{keine-2020} §3.5, (274)–(278))
-- ============================================================================

/-- Is this probe vacuous *relative to a specific sister label*?

    A probe is vacuous for a given bilateral label if the label
    contains the probe's horizon category — the probe's search
    terminates at its sister, leaving no searchable domain.

    @cite{keine-2020} §3.5, (274)–(278): a probe on C⁰ with
    horizon T is vacuous because its sister TP's bilateral label
    `[T, v, V]` contains T.

    This is the general check; `isVacuous` below specializes it
    to the standard verbal spine. -/
def ProbeProfile.isVacuousFor (p : ProbeProfile) (sisterLabel : List Cat) : Bool :=
  match p.horizon with
  | none => false
  | some _ => p.transparentToLabel sisterLabel = false

/-- Is this probe vacuous in the standard verbal spine?

    @cite{keine-2020} §3.5, (274)–(278): a probe is vacuous when
    its sister's bilateral label (in the standard verbal spine)
    contains its horizon category. The sister of a head is
    determined by the standard clause spine:
    - Sister of C⁰: TP (label `[V, Appl, v, Voice, T]`)
    - Sister of T⁰: vP (label `[V, Appl, v, Voice]`)
    - Sister of Force⁰: CP (label `[V, Appl, v, Voice, T, C]`)

    Vacuous probes cannot trigger movement or agreement, and are
    therefore undetectable. The Height-Locality Theorem (279)
    emerges because only nonvacuous probes produce observable
    dependencies. -/
def ProbeProfile.isVacuous (p : ProbeProfile) : Bool :=
  match p.horizon with
  | none => false
  | some _ =>
    let sisterLabel := match p.probeHead with
      | .C     => ClauseSpine.tP.projectedHeads    -- sister of C⁰ is TP
      | .Force => ClauseSpine.cP.projectedHeads    -- sister of Force⁰ is CP
      | .T     => ClauseSpine.vP.projectedHeads    -- sister of T⁰ is vP
      | _      => []                                -- conservative: unknown sister
    p.transparentToLabel sisterLabel = false

/-- A probe with no horizon is never vacuous — it can always
    search into any domain. -/
theorem no_horizon_not_vacuous (head : Cat) :
    (ProbeProfile.mk head none).isVacuous = false := by
  simp [ProbeProfile.isVacuous]

/-- The four article probes are all nonvacuous. -/
theorem keine_probes_nonvacuous :
    keinePhiProbe.isVacuous = false ∧
    keineAProbe.isVacuous = false ∧
    keineWhLicensing.isVacuous = false ∧
    keineĀProbe.isVacuous = false := by decide

/-- All Hindi probes are nonvacuous. -/
theorem hindi_probes_nonvacuous :
    LanguageProbeConfig.hindi.phi.isVacuous = false ∧
    LanguageProbeConfig.hindi.aMove.isVacuous = false ∧
    LanguageProbeConfig.hindi.wh.isVacuous = false ∧
    LanguageProbeConfig.hindi.ābar.isVacuous = false := by decide

/-- All German probes are nonvacuous. -/
theorem german_probes_nonvacuous :
    LanguageProbeConfig.german.phi.isVacuous = false ∧
    LanguageProbeConfig.german.aMove.isVacuous = false ∧
    LanguageProbeConfig.german.wh.isVacuous = false ∧
    LanguageProbeConfig.german.ābar.isVacuous = false := by decide

/-- All English probes are nonvacuous. -/
theorem english_probes_nonvacuous :
    LanguageProbeConfig.english.phi.isVacuous = false ∧
    LanguageProbeConfig.english.aMove.isVacuous = false ∧
    LanguageProbeConfig.english.wh.isVacuous = false ∧
    LanguageProbeConfig.english.ābar.isVacuous = false := by decide

/-- A probe with the default horizon (horizon = own head) is not
    vacuous for T⁰ and C⁰: the sister label does not contain the
    probe's own head. -/
theorem default_horizon_not_vacuous_T :
    (ProbeProfile.defaultHorizon .T).isVacuous = false := by decide
theorem default_horizon_not_vacuous_C :
    (ProbeProfile.defaultHorizon .C).isVacuous = false := by decide

/-- Example vacuous probes from @cite{keine-2020} (278):
    a probe on C⁰ with horizon T, v, or V is vacuous — the sister
    TP's bilateral label contains all three. -/
theorem vacuous_examples :
    (ProbeProfile.mk .C (some .T)).isVacuous = true ∧
    (ProbeProfile.mk .C (some .v)).isVacuous = true ∧
    (ProbeProfile.mk .C (some .V)).isVacuous = true := by decide

/-- Hindi Ā (C⁰ ⊣ Nmlz) is NOT vacuous: TP's bilateral label
    does not contain Nmlz. -/
theorem hindi_ābar_not_vacuous :
    (ProbeProfile.mk .C (some .Nmlz)).isVacuous = false := by decide

/-- A probe vacuous for a given sister label cannot search past
    that sister — the sister itself is opaque. -/
theorem vacuousFor_means_opaque (p : ProbeProfile) (label : List Cat)
    (hv : p.isVacuousFor label = true) :
    p.transparentToLabel label = false := by
  simp only [ProbeProfile.isVacuousFor] at hv
  cases hHz : p.horizon <;> simp_all

-- ============================================================================
-- § 11: Three Distinct Locality Types (@cite{keine-2019} p. 45)
-- ============================================================================

/-- The transparency profile of a probe: which of the three standard
    clause sizes (vP, TP, CP) are transparent to it. -/
def ProbeProfile.profile (p : ProbeProfile) : Bool × Bool × Bool :=
  (p.transparentTo .v, p.transparentTo .T, p.transparentTo .C)

/-- The four article probes produce exactly three distinct transparency
    profiles. This is the paper's central empirical discovery:
    selective opacity is not binary (A vs. Ā) but admits at least
    three locality types.

    | Profile       | vP | TP | CP | Probes                    |
    |---------------|----|----|----| --------------------------|
    | Type 1        | ✓  | *  | *  | φ-agreement, A-movement   |
    | Type 2        | ✓  | ✓  | *  | wh-licensing              |
    | Type 3        | ✓  | ✓  | ✓  | Ā-movement                |
-/
theorem three_locality_types :
    -- φ and A share the same profile (Type 1)
    keinePhiProbe.profile = keineAProbe.profile ∧
    -- wh-licensing has a different profile from φ (Type 2 ≠ Type 1)
    keineWhLicensing.profile ≠ keinePhiProbe.profile ∧
    -- Ā has a different profile from wh (Type 3 ≠ Type 2)
    keineĀProbe.profile ≠ keineWhLicensing.profile ∧
    -- Ā has a different profile from φ (Type 3 ≠ Type 1)
    keineĀProbe.profile ≠ keinePhiProbe.profile := by decide

-- ============================================================================
-- § 12: ComplementSize Bridge
-- ============================================================================

/-- A complement's transparency to a given probe: delegates to
    `ProbeProfile.transparentTo` on the complement's highest head.

    This unifies the phase-based (`transparentToTenseAgree`) and
    horizon-based (@cite{keine-2019}) transparency models into a
    single parameterized function. -/
def ComplementSize.transparentTo (cs : ComplementSize) (p : ProbeProfile) : Bool :=
  p.transparentTo cs.highestHead

/-- Tense-Agree probe: sits on C⁰ with horizon C.
    Same profile as `keineWhLicensing` — both check whether the
    complement's highest head is below C in the fseq.

    This is the probe implicit in @cite{egressy-2026}'s phase-based
    `transparentToTenseAgree`: any complement smaller than CP is
    transparent. -/
def tenseAgreeProbe : ProbeProfile := ⟨.C, some .C⟩

/-- `transparentToTenseAgree` is the special case of `transparentTo`
    parameterized by `tenseAgreeProbe`. -/
theorem transparentToTenseAgree_eq_transparentTo (cs : ComplementSize) :
    cs.transparentToTenseAgree = cs.transparentTo tenseAgreeProbe := by
  simp [ComplementSize.transparentToTenseAgree, ComplementSize.transparentTo,
        ProbeProfile.transparentTo, tenseAgreeProbe, ComplementSize.fLevel]

/-- `tenseAgreeProbe` has the same profile as `keineWhLicensing`. -/
theorem tenseAgreeProbe_eq_whLicensing :
    tenseAgreeProbe = keineWhLicensing := rfl

/-- `ComplementSize.transparentToTenseAgree` matches the transparency
    profile of wh-licensing, NOT the φ-probe on T⁰.

    The two models diverge on TP-sized complements:
    - Phase-based (`transparentToTenseAgree`): TP is transparent ✓
    - Horizon-based (`keinePhiProbe.transparentTo`): TP is opaque ✗

    This is a genuine theoretical difference: phase theory treats CP
    as the only opaque boundary, while Keine's horizon theory derives
    a tighter cutoff from the probe's own structural position. -/
theorem complementSize_matches_wh_not_phi (cs : ComplementSize) :
    cs.transparentToTenseAgree = keineWhLicensing.transparentTo cs.highestHead := by
  simp [ComplementSize.transparentToTenseAgree, ComplementSize.fLevel,
        ProbeProfile.transparentTo, keineWhLicensing]

/-- The divergence: TP complements are transparent under the
    phase-based model but opaque under Keine's φ-probe. -/
theorem phase_horizon_diverge_on_tp :
    ComplementSize.tP.transparentToTenseAgree = true ∧
    keinePhiProbe.transparentTo ComplementSize.tP.highestHead = false := by decide

-- ── Parameterized bridge theorems ──

/-- vP complements are transparent to φ-probes. -/
theorem vP_transparent_to_phi :
    ComplementSize.vP.transparentTo keinePhiProbe = true := by decide

/-- TP complements are opaque to φ-probes. -/
theorem tP_opaque_to_phi :
    ComplementSize.tP.transparentTo keinePhiProbe = false := by decide

/-- CP complements are opaque to a probe iff the probe has a horizon
    and sits at or below C (fValue ≤ 6). A probe on SA⁰ (fValue 7)
    with a horizon would find CP transparent. -/
theorem cP_opaque_to_wh :
    ComplementSize.cP.transparentTo keineWhLicensing = false := by decide

-- ============================================================================
-- § 13: Height-Locality Theorem (@cite{keine-2020} (279))
-- ============================================================================

/-! ### Height-Locality Theorem (HLT) (@cite{keine-2020} (279))

The HLT is an emergent property of horizons + bilateral labeling.
Probes whose (location, horizon) pairing violates (279) are vacuous
and hence undetectable — all *attested* dependencies conform to
the HLT.

We verify the HLT's concrete predictions for the standard spine:

**(279a) Location → Horizon**: A probe on C⁰ cannot have T, v, or V
as its horizon (vacuous). It CAN have C, Nmlz, or Force.

**(279b) Horizon → Location**: A probe with horizon T cannot be on
C⁰ or Force⁰ (vacuous). It can be on T⁰ (default horizon). -/

/-- HLT (279a): Probes on C⁰ with horizons T, v, V are vacuous
    (TP's bilateral label contains all three). Horizons C, Nmlz, Force
    are NOT vacuous (TP's label lacks these). -/
theorem hlt_279a_C :
    -- Vacuous horizons for C⁰
    (ProbeProfile.mk .C (some .T)).isVacuous = true ∧
    (ProbeProfile.mk .C (some .v)).isVacuous = true ∧
    (ProbeProfile.mk .C (some .V)).isVacuous = true ∧
    -- Nonvacuous horizons for C⁰
    (ProbeProfile.mk .C (some .C)).isVacuous = false ∧
    (ProbeProfile.mk .C (some .Nmlz)).isVacuous = false ∧
    (ProbeProfile.mk .C (some .Force)).isVacuous = false := by decide

/-- HLT (279a): Probes on T⁰ with horizons v, V are vacuous
    (vP's bilateral label contains both). Horizon T is NOT vacuous. -/
theorem hlt_279a_T :
    (ProbeProfile.mk .T (some .v)).isVacuous = true ∧
    (ProbeProfile.mk .T (some .V)).isVacuous = true ∧
    (ProbeProfile.mk .T (some .T)).isVacuous = false := by decide

/-- HLT (279b): A probe ⊣ T cannot be nonvacuously located on
    C⁰ or Force⁰ — both have T in their sister label. But ⊣ T
    on T⁰ is the default horizon (nonvacuous). -/
theorem hlt_279b_T :
    (ProbeProfile.mk .C (some .T)).isVacuous = true ∧
    (ProbeProfile.mk .Force (some .T)).isVacuous = true ∧
    (ProbeProfile.mk .T (some .T)).isVacuous = false := by decide

/-- The HLT derives the HLC: for nonvacuous probes, higher probes
    can search into at least as many clause types (fValue model). -/
theorem hlt_derives_hlc (p₁ p₂ : ProbeProfile) (c : Cat)
    (h_higher : fValue p₁.probeHead ≤ fValue p₂.probeHead)
    (h_horizon : p₁.horizon = none → p₂.horizon = none)
    (h_transparent : p₁.transparentTo c = true) :
    p₂.transparentTo c = true :=
  height_locality_connection p₁ p₂ c h_higher h_horizon h_transparent

-- ============================================================================
-- § 14: Ban on Improper Movement (@cite{keine-2020} §3.4.1–3.4.2)
-- ============================================================================

/-- **Ban on Improper Movement** (derived from horizons).

    @cite{keine-2020} §3.4.1–3.4.2: Ā-movement cannot feed A-movement.
    Under the horizon account, this is an emergent property:

    1. Ā-movement out of a clause places the DP in [Spec,CP], creating
       a CP structure that encapsulates it.
    2. The A-probe has a horizon that includes C (in Hindi, ⊣ T; in
       English, ⊣ C) — either way, CP is opaque to the A-probe.
    3. Therefore the A-probe cannot reach an element in [Spec,CP].

    This theorem verifies the key premise: CPs are opaque to A-probes
    in all three formalized languages. -/
theorem ban_on_improper_movement_premise :
    -- Hindi: A-probe (T⁰ ⊣ T) cannot search into CP
    LanguageProbeConfig.hindi.aMove.transparentToLabel
      ClauseSpine.cP.projectedHeads = false ∧
    -- English: A-probe (T⁰ ⊣ C) cannot search into CP
    LanguageProbeConfig.english.aMove.transparentToLabel
      ClauseSpine.cP.projectedHeads = false ∧
    -- German: A-probe (T⁰ ⊣ T) cannot search into CP
    LanguageProbeConfig.german.aMove.transparentToLabel
      ClauseSpine.cP.projectedHeads = false := by decide

/-- Conversely, Ā-probes CAN search into CP in Hindi and English
    (and ForceP in German), so A-movement feeding Ā-movement is
    permitted — as expected. -/
theorem a_can_feed_ābar :
    -- Hindi: Ā-probe (C⁰ ⊣ Nmlz) can search into CP
    LanguageProbeConfig.hindi.ābar.transparentToLabel
      ClauseSpine.cP.projectedHeads = true ∧
    -- English: Ā/wh-probe (C⁰ ⊣ ∅) can search into CP
    LanguageProbeConfig.english.wh.transparentToLabel
      ClauseSpine.cP.projectedHeads = true := by decide

-- ============================================================================
-- § 15: A-movement–Agreement Generalization (@cite{keine-2020} (231))
-- ============================================================================

/-- **A-movement–Agreement Generalization** (@cite{keine-2020} (231)):
    If A-movement of any element out of an embedded clause has taken
    place, that clause is obligatorily transparent for LDA (long-distance
    agreement). Agreement is hence obligatory and default agreement is
    impossible, regardless of whether the agreement controller moves
    or not. Ā-movement has no such effect.

    This is derived from horizons: A-movement requires the embedded
    clause to be a vP (transparent to [*A*] ⊣ T). Since vP is also
    transparent to [*φ*] ⊣ T, φ-agreement is obligatory.

    The theorem verifies the key structural fact: in Hindi, A-probes
    and φ-probes have identical horizons, so anything transparent to
    one is transparent to the other. -/
theorem a_movement_agreement_generalization_hindi :
    -- A and φ probes have the same settings in Hindi
    LanguageProbeConfig.hindi.aMove = LanguageProbeConfig.hindi.phi ∧
    -- If a clause is transparent to A-movement, it's transparent to φ
    (∀ label, LanguageProbeConfig.hindi.aMove.transparentToLabel label = true →
      LanguageProbeConfig.hindi.phi.transparentToLabel label = true) := by
  constructor
  · rfl
  · intro label h; exact h

/-- Ā-movement does NOT force φ-agreement: Ā and φ have different
    horizons in Hindi, so Ā-transparency does not imply φ-transparency. -/
theorem ābar_does_not_force_agreement_hindi :
    -- NmlzP is opaque to Ā but transparent to wh
    -- CP is transparent to Ā but opaque to φ
    LanguageProbeConfig.hindi.ābar.transparentToLabel
      ClauseSpine.cP.projectedHeads = true ∧
    LanguageProbeConfig.hindi.phi.transparentToLabel
      ClauseSpine.cP.projectedHeads = false := by decide

end Minimalism
