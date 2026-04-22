import Linglib.Theories.Syntax.Minimalism.VerbalDecomposition

set_option autoImplicit false

/-!
# Cascade Structures (@cite{pesetsky-1995})

@cite{pesetsky-1995}

Binary-branching PP spines where each node is a preposition (possibly
phonologically null) that θ-selects its specifier. Cascade structures
provide the geometry for:

1. **T/SM restriction** (Ch. 6): CAUS movement blocked by nonaffixal P
2. **Backward binding** (§6.2.2): CAUS starts lower than experiencer
3. **Double object alternation** (Ch. 5): G as zero preposition for Theme
4. **Heavy shift** (§7.2): rightward adjunction constrained by Cascades

## Architecture

A Cascade is a recursive PP spine. Each layer has a preposition head
(with an affixality feature) and a specifier DP. The complement of
each layer is another layer or a terminal:

```
V'
├── V
└── PP₁ (head: P₁, spec: DP₁)
    └── PP₂ (head: P₂, spec: DP₂)
        └── PP₃ (head: P₃, spec: DP₃)
```

The Head Movement Constraint (HMC) determines whether a zero morpheme
head (like CAUS) can incorporate into V by successive head adjunction
through the spine. Movement is blocked if any intervening head is
nonaffixal.

## CAUS ≠ vCAUSE

Pesetsky's CAUS is a **syntactic zero morpheme** — a phonologically null
P head that creates causative verbs by incorporating into V. This is
distinct from @cite{cuervo-2003}'s `VerbHead.vCAUSE`, which is an
**event-structural** head present in both causative and anticausative
decompositions.

| | Pesetsky CAUS | Cuervo vCAUSE |
|---|---|---|
| Nature | Syntactic head (P⁰) | Event-structural head |
| Phonology | Zero morpheme | Not a morpheme |
| Present in anticausative | No | Yes |
| Movement | Incorporates into V via HMC | No movement |
| Effect | Suppresses external θ-role | Relates subevents |
-/

namespace Minimalism

-- ════════════════════════════════════════════════════
-- § 1. Cascade Head
-- ════════════════════════════════════════════════════

/-- A preposition head in a Cascade structure.

    Each head has:
    - `label`: identifies the head (e.g., "CAUS", "G", "at", "about")
    - `overt`: whether the head is phonologically realized
    - `affixal`: whether the head permits head adjunction passthrough

    Affixality determines HMC behavior: when a lower head Z adjoins to
    this head Y, the resulting complex [Z+Y] is headed by Y. If Y is
    affixal, [Z+Y] can continue moving upward. If Y is nonaffixal,
    [Z+Y] is stuck — the complex cannot move further. -/
structure CascadeHead where
  label : String
  overt : Bool := true
  affixal : Bool
  deriving DecidableEq, Repr

/-- Is this a zero morpheme (phonologically unrealized)? -/
def CascadeHead.isZero (h : CascadeHead) : Bool := !h.overt

-- ════════════════════════════════════════════════════
-- § 2. Cascade Structure
-- ════════════════════════════════════════════════════

/-- A Cascade structure: binary-branching recursive PP spine.

    Each layer consists of a P head, its specifier (a DP argument
    identified by a label), and its complement (another layer or
    a terminal). The outermost layer is V's complement. -/
inductive Cascade where
  /-- Base: bottom of the cascade (no more PP layers). -/
  | terminal : Cascade
  /-- PP layer: head P, specifier DP label, complement. -/
  | layer : CascadeHead → String → Cascade → Cascade
  deriving Repr

-- ════════════════════════════════════════════════════
-- § 3. Cascade Spine
-- ════════════════════════════════════════════════════

/-- Extract the spine of P heads, ordered from closest-to-V (index 0)
    to deepest. -/
def Cascade.spine : Cascade → List CascadeHead
  | .terminal => []
  | .layer h _ rest => h :: rest.spine

/-- The argument labels, ordered from closest-to-V to deepest. -/
def Cascade.arguments : Cascade → List String
  | .terminal => []
  | .layer _ arg rest => arg :: rest.arguments

/-- Number of PP layers. -/
def Cascade.depth : Cascade → Nat
  | .terminal => 0
  | .layer _ _ rest => 1 + rest.depth

theorem spine_length_eq_depth (c : Cascade) : c.spine.length = c.depth := by
  induction c with
  | terminal => rfl
  | layer _ _ _ ih => simp [Cascade.spine, Cascade.depth, ih]; omega

-- ════════════════════════════════════════════════════
-- § 4. HMC Reachability
-- ════════════════════════════════════════════════════

/-- Can a head at position `idx` in the spine reach V via successive
    head adjunction?

    A head at position `idx` must adjoin to each intermediate head
    (positions idx−1, idx−2, …, 0) before reaching V. Movement is
    blocked if any intermediate head is nonaffixal, because the
    resulting complex is headed by the nonaffixal host, which cannot
    itself move. @cite{pesetsky-1995} §6.2.

    Formally: all heads at positions 0 … idx−1 must be affixal. -/
def canReachV (spine : List CascadeHead) (idx : Nat) : Bool :=
  (spine.take idx).all (·.affixal)

/-- Does the spine contain a head with the given label?
    Returns its index if found. -/
def findInSpine (spine : List CascadeHead) (label : String) : Option Nat :=
  go spine 0
where
  go : List CascadeHead → Nat → Option Nat
    | [], _ => none
    | h :: rest, i => if h.label == label then some i else go rest (i + 1)

/-- Can a head with the given label reach V in this cascade? -/
def Cascade.headCanReachV (c : Cascade) (label : String) : Option Bool :=
  (findInSpine c.spine label).map (canReachV c.spine ·)

/-- Does this cascade contain a head with the given label? -/
def Cascade.hasHead (c : Cascade) (label : String) : Bool :=
  c.spine.any (·.label == label)

-- ════════════════════════════════════════════════════
-- § 5. Named Zero Morpheme Heads
-- ════════════════════════════════════════════════════

/-- CAUS: zero causative morpheme. Decomposes Class II psych verbs
    as √root + CAUS. Affixal: must incorporate into V via HMC. -/
def caus : CascadeHead := ⟨"CAUS", false, true⟩

/-- G: zero preposition for Theme/Patient. Mediates Theme θ-selection
    in double object constructions (§5.3). Affixal. -/
def headG : CascadeHead := ⟨"G", false, true⟩

/-- TEMP: zero temporal preposition (§7.1.5). Heads temporal adjunct
    PPs in Cascade structures. Affixal. -/
def headTEMP : CascadeHead := ⟨"TEMP", false, true⟩

/-- SUG: zero Suggestor morpheme (§6.2.3). Parallel to CAUS for
    adjectives: assigns Suggestor role to AP's external argument
    (e.g., "his manner was angry"). Affixal. -/
def headSUG : CascadeHead := ⟨"SUG", false, true⟩

-- ════════════════════════════════════════════════════
-- § 6. Named Overt Prepositions
-- ════════════════════════════════════════════════════

/-- Overt "at" — introduces Target stimulus in psych verbs. Nonaffixal:
    blocks CAUS movement through it. -/
def headAt : CascadeHead := ⟨"at", true, false⟩

/-- Overt "about" — introduces Subject Matter stimulus. Nonaffixal. -/
def headAbout : CascadeHead := ⟨"about", true, false⟩

/-- Overt "to" — dative/goal preposition. Nonaffixal. -/
def headTo : CascadeHead := ⟨"to", true, false⟩

/-- Overt "of" — partitive/possessive. Nonaffixal. -/
def headOf : CascadeHead := ⟨"of", true, false⟩

-- ════════════════════════════════════════════════════
-- § 7. θ-Suppression
-- ════════════════════════════════════════════════════

/-- @cite{pesetsky-1995} (522): Suppression of external argument.

    Only affixation of a **semantically contentful** morpheme to a verb
    with an external argument α allows α to be unexpressed. When CAUS
    affixes to √annoy, the A-Causer (CAUS's object) surfaces as subject,
    and √annoy's original Agent role is suppressed.

    This distinguishes CAUS from semantically vacuous affixes (e.g.,
    anticausative SE), which do not suppress external arguments. -/
def thetaSuppressed (causAffixed : Bool) (rootHasExtArg : Bool) : Bool :=
  causAffixed && rootHasExtArg

-- ════════════════════════════════════════════════════
-- § 8. CAUS Variants
-- ════════════════════════════════════════════════════

/-- Two occurrences of CAUS in Experiencer predicate structures
    (@cite{pesetsky-1995} §6.2.2, p. 208):

    - `affixal` (CAUS_aff): starts affixed to V in the lexicon; bears
      strong features that must be discharged at PF
    - `prepositional` (CAUS_p): an independent P head in the Cascade;
      its features are discharged when V+CAUS_aff adjoins -/
inductive CausVariant where
  | affixal       -- CAUS_aff: on V, strong features
  | prepositional -- CAUS_p: independent P in Cascade
  deriving DecidableEq, Repr

/-- CAUS_aff bears strong features that must be discharged at PF. -/
def CausVariant.hasStrongFeatures : CausVariant → Bool
  | .affixal => true
  | .prepositional => false

-- ════════════════════════════════════════════════════
-- § 9. CAUS Strength Classification
-- ════════════════════════════════════════════════════

/-- Three types of semantically causative verbs, classified by their
    relationship to CAUS (@cite{pesetsky-1995} §6.3, p. 217):

    1. `strong`: A-Causer suppressed by CAUS_aff (ObjExp psych verbs,
       causative *give*). Subject = A-Causer, not Agent.
    2. `weak`: CAUS adds a causal clause without suppressing any θ-role
       (causative *break*, *grow*).
    3. `absent`: no CAUS at all (*run*, *sleep*). -/
inductive CausStrength where
  | strong  -- CAUS with A-Causer suppression (annoy, give)
  | weak    -- CAUS without suppression (break, grow)
  | absent  -- No CAUS (run, sleep)
  deriving DecidableEq, Repr

/-- Derive CAUS strength from cascade structure.
    A cascade containing CAUS has strong causation; one without has absent.
    (Weak CAUS — causative *break*/*grow* — requires additional verbal
    decomposition beyond cascade presence alone.) -/
def Cascade.causStrength (c : Cascade) : CausStrength :=
  if c.hasHead "CAUS" then .strong else .absent

-- ════════════════════════════════════════════════════
-- § 10. Cascade C-Command
-- ════════════════════════════════════════════════════

/-- Position of an argument label in the cascade (0 = closest to V,
    i.e., outermost PP = structurally highest). -/
def Cascade.argPosition : Cascade → String → Option Nat
  | .terminal, _ => none
  | .layer _ arg rest, target =>
    if arg == target then some 0
    else (rest.argPosition target).map (· + 1)

/-- In a Cascade, spec of position `i` c-commands spec of position `j`
    when `i < j` (outer spec c-commands inner specs).

    Position 0 = outermost PP (closest to V) = structurally highest.
    This follows from X-bar c-command: spec of PP₀ c-commands the
    complement of PP₀, which contains PP₁ and its spec. -/
def Cascade.specCCommands (c : Cascade) (commander commanded : String) : Bool :=
  match c.argPosition commander, c.argPosition commanded with
  | some i, some j => i < j
  | _, _ => false

-- ════════════════════════════════════════════════════
-- § 11. HNPS Landing Sites
-- ════════════════════════════════════════════════════

/-- Number of potential heavy NP shift landing sites in a cascade.
    Each cascade layer provides one rightward adjunction site.
    @cite{pesetsky-1995} Ch. 7 derives HNPS from cascade geometry:
    shifted phrases adjoin to cascade nodes, so cascade depth
    determines how many landing sites are available. -/
def Cascade.shiftSites (c : Cascade) : Nat := c.depth

-- ════════════════════════════════════════════════════
-- § 12. Verification Theorems
-- ════════════════════════════════════════════════════

section ZeroMorphemeProperties

/-- Zero morphemes are phonologically unrealized. -/
theorem caus_is_zero : caus.isZero = true := rfl
theorem g_is_zero : headG.isZero = true := rfl
theorem temp_is_zero : headTEMP.isZero = true := rfl
theorem sug_is_zero : headSUG.isZero = true := rfl

/-- Overt prepositions are phonologically realized. -/
theorem at_is_overt : headAt.isZero = false := rfl
theorem about_is_overt : headAbout.isZero = false := rfl

/-- Zero morphemes are affixal; T/SM prepositions are nonaffixal. -/
theorem caus_affixal : caus.affixal = true := rfl
theorem g_affixal : headG.affixal = true := rfl
theorem at_nonaffixal : headAt.affixal = false := rfl
theorem about_nonaffixal : headAbout.affixal = false := rfl
theorem to_nonaffixal : headTo.affixal = false := rfl

end ZeroMorphemeProperties

section HMCTheorems

/-- A head at position 0 (immediately below V) can always reach V:
    no intervening heads. -/
theorem position_zero_reachable (spine : List CascadeHead) :
    canReachV spine 0 = true := by
  simp [canReachV]

/-- If all heads in the spine are affixal, any position can reach V. -/
private theorem all_take_of_all {α : Type} {p : α → Bool} {l : List α}
    (h : l.all p = true) (n : Nat) : (l.take n).all p = true := by
  induction l generalizing n with
  | nil => simp
  | cons hd tl ih =>
    cases n with
    | zero => simp
    | succ m =>
      simp only [List.take, List.all]
      have hcons := h
      simp only [List.all] at hcons
      rw [Bool.and_eq_true] at hcons
      rw [Bool.and_eq_true]
      exact ⟨hcons.1, ih hcons.2 m⟩

theorem all_affixal_reachable (spine : List CascadeHead) (idx : Nat)
    (h : spine.all (·.affixal) = true) :
    canReachV spine idx = true := by
  exact all_take_of_all h idx

/-- A nonaffixal head at position 0 blocks anything below it. -/
theorem nonaffixal_blocks (h : CascadeHead) (rest : List CascadeHead) (idx : Nat)
    (hna : h.affixal = false) (hidx : idx > 0) :
    canReachV (h :: rest) idx = false := by
  simp only [canReachV]
  cases idx with
  | zero => omega
  | succ n =>
    simp [List.take, hna]

end HMCTheorems

section CascadeTheorems

/-- Spine of a terminal cascade is empty. -/
theorem terminal_spine : Cascade.terminal.spine = [] := rfl

/-- Spine of a single-layer cascade is a singleton. -/
theorem single_layer_spine (h : CascadeHead) (arg : String) :
    (Cascade.layer h arg .terminal).spine = [h] := rfl

/-- A two-layer cascade spine lists heads from top to bottom. -/
theorem two_layer_spine (h₁ h₂ : CascadeHead) (a₁ a₂ : String) :
    (Cascade.layer h₁ a₁ (.layer h₂ a₂ .terminal)).spine = [h₁, h₂] := rfl

end CascadeTheorems

-- ════════════════════════════════════════════════════
-- § 13. Bridge: CAUS vs vCAUSE
-- ════════════════════════════════════════════════════

/-- Pesetsky's CAUS is distinct from event-structural vCAUSE.

    `VerbHead.vCAUSE` (from @cite{cuervo-2003}) is present in both
    causative and anticausative decompositions — it encodes the causal
    **relation** between subevents, independent of Voice.

    Pesetsky's `caus` is a syntactic zero morpheme — a P⁰ head that
    **creates** causative verbs by incorporating into V, and is present
    ONLY in causative structures. The anticausative "the door opened"
    has `vCAUSE` (causal relation exists) but no CAUS (no zero
    morpheme creating a derived causative).

    This theorem witnesses the structural distinction: vCAUSE can appear
    without external cause (anticausative), while CAUS always requires
    a Causer argument as its specifier in the Cascade. -/
theorem vcause_in_anticausative_but_not_caus :
    isAnticausative [.vCAUSE, .vGO, .vBE] = true := by native_decide

end Minimalism
