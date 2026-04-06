/-!
# Theory Space for the Morphology/Syntax Interface
@cite{kalin-bjorkman-etal-2026}

@cite{kalin-bjorkman-etal-2026} identify four binary dimensions along which
theories of the morphology/syntax interface vary. These dimensions are
partially independent: some combinations are structurally impossible
(a process-based theory cannot be non-lexicalist, since generative syntax
is piece-based). The constrained space defines the positions of the major
contemporary theories: DM, PFM, Nanosyntax, and MaS.

## The four dimensions

1. **Lexicalism** (§2.1.1): whether the Morphology is a dedicated component
   separate from the Syntax (lexicalist) or whether morphological and
   syntactic computation use the same principles (non-lexicalist).

2. **Architecture** (§2.1.2): the relative ordering of the Morphology and
   the Syntax. Lexicalist theories use pre-syntactic or parallel
   architectures; non-lexicalist theories use syntactic (morphology = syntax)
   or post-syntactic architectures.

3. **Pieces vs processes** (§2.1.3): whether complex morphological forms
   result from combining discrete stored pieces (Item-and-Arrangement) or
   from applying (morpho)phonological rules/transformations to stems
   (Item-and-Process). Non-lexicalist theories are necessarily piece-based,
   since syntax is piece-based.

4. **Realizational vs incremental** (§2.1.4): whether phonological exponents
   are separated from meanings/functions and matched later (realizational)
   or built up in lockstep with meaning (incremental).

## Structural constraints

Not all 2⁴ = 16 combinations are possible:
- Process-based → lexicalist (syntax is piece-based, so non-lexicalist
  morphology must also be piece-based)
- Syntactic architecture → non-lexicalist (by definition: morphology
  *is* syntax)
- Post-syntactic architecture → non-lexicalist (morphology operates on
  syntactic output)
- Pre-syntactic architecture → lexicalist (morphology feeds syntax,
  implying separation)
- Parallel architecture → lexicalist (morphology and syntax are
  co-present but independent)
-/

namespace Theories.Morphology.TheorySpace

-- ============================================================================
-- §1: Dimensions
-- ============================================================================

/-- Whether the Morphology is a dedicated component separate from the
    Syntax (lexicalist) or uses the same computational system
    (non-lexicalist). @cite{kalin-bjorkman-etal-2026} §2.1.1. -/
inductive Lexicalism where
  /-- Morphology is a separate component; the Lexical Integrity Hypothesis
      holds (syntax cannot manipulate sub-word pieces). -/
  | lexicalist
  /-- Morphological and syntactic computation operate with the same
      kinds of principles and processes. -/
  | nonLexicalist
  deriving DecidableEq, Repr

/-- The relative ordering of morphological and syntactic computation.
    @cite{kalin-bjorkman-etal-2026} §2.1.2.

    Lexicalist theories use `preSyntactic` or `parallel` architectures.
    Non-lexicalist theories use `syntactic` or `postSyntactic`. -/
inductive Architecture where
  /-- Morphology feeds the Syntax (input to syntactic computation).
      Lexicalist. -/
  | preSyntactic
  /-- Morphology and Syntax run independently, mapping to each other.
      Lexicalist. -/
  | parallel
  /-- Morphology *is* the Syntax (no separate morphological component).
      Non-lexicalist. -/
  | syntactic
  /-- Syntax feeds the Morphology (morphology operates on syntactic
      output). Non-lexicalist. -/
  | postSyntactic
  deriving DecidableEq, Repr

/-- Whether complex morphological forms result from combining discrete
    stored pieces (Item-and-Arrangement) or from applying rules to stems
    (Item-and-Process). @cite{kalin-bjorkman-etal-2026} §2.1.3. -/
inductive Exponence where
  /-- Complex words = combination of discrete, independently-stored
      morphemes. Traditional morphemes are primitive. -/
  | pieceBased
  /-- Complex words = result of applying (morpho)phonological
      modifications (processes) to a stem. Morphemes are not primitive;
      affixation is one possible output of a rule. -/
  | processBased
  deriving DecidableEq, Repr

/-- Whether phonological exponents are independent of or unified with
    the meanings/functions they realize.
    @cite{kalin-bjorkman-etal-2026} §2.1.4. -/
inductive Mapping where
  /-- Features/meanings precede or are independent of phonological
      exponents. Exponents *realize* already-present features. Late
      Insertion is the prototypical realizational mechanism. -/
  | realizational
  /-- Form and meaning are built up in lockstep. A morpheme is a
      pairing of form and meaning; adding it adds both simultaneously. -/
  | incremental
  deriving DecidableEq, Repr

-- ============================================================================
-- §2: Theory Classification
-- ============================================================================

/-- A position in the four-dimensional theory space.
    @cite{kalin-bjorkman-etal-2026} Table 2. -/
structure TheoryPosition where
  lexicalism   : Lexicalism
  architecture : Architecture
  exponence    : Exponence
  mapping      : Mapping
  deriving DecidableEq, Repr

/-- Distributed Morphology (@cite{halle-marantz-1993}).
    Non-lexicalist, post-syntactic, piece-based, realizational. -/
def dm : TheoryPosition :=
  { lexicalism   := .nonLexicalist
    architecture := .postSyntactic
    exponence    := .pieceBased
    mapping      := .realizational }

/-- Paradigm Function Morphology (@cite{stump-2001}).
    Lexicalist, parallel, process-based, realizational. -/
def pfm : TheoryPosition :=
  { lexicalism   := .lexicalist
    architecture := .parallel
    exponence    := .processBased
    mapping      := .realizational }

/-- Nanosyntax (@cite{starke-2009}).
    Non-lexicalist, post-syntactic, piece-based, realizational.
    Shares DM's position on all four dimensions; differs in the
    *size* of spellout (phrasal, not terminal). -/
def nanosyntax : TheoryPosition :=
  { lexicalism   := .nonLexicalist
    architecture := .postSyntactic
    exponence    := .pieceBased
    mapping      := .realizational }

/-- Morphology as Syntax (@cite{collins-kayne-2023}).
    Non-lexicalist, syntactic (integrated), piece-based, incremental. -/
def mas : TheoryPosition :=
  { lexicalism   := .nonLexicalist
    architecture := .syntactic
    exponence    := .pieceBased
    mapping      := .incremental }

-- ============================================================================
-- §3: Structural constraints between dimensions
-- ============================================================================

/-- A theory position is **well-formed** if its dimension values respect
    the structural dependencies identified by
    @cite{kalin-bjorkman-etal-2026}:
    - Process-based → lexicalist (syntax is piece-based)
    - Syntactic/post-syntactic architecture → non-lexicalist
    - Pre-syntactic/parallel architecture → lexicalist -/
def TheoryPosition.wellFormed (t : TheoryPosition) : Bool :=
  -- process-based requires lexicalism
  (t.exponence != .processBased || t.lexicalism == .lexicalist) &&
  -- syntactic/postSyntactic architecture requires non-lexicalism
  (t.architecture != .syntactic     || t.lexicalism == .nonLexicalist) &&
  (t.architecture != .postSyntactic || t.lexicalism == .nonLexicalist) &&
  -- preSyntactic/parallel architecture requires lexicalism
  (t.architecture != .preSyntactic  || t.lexicalism == .lexicalist) &&
  (t.architecture != .parallel      || t.lexicalism == .lexicalist)

theorem dm_wellFormed : dm.wellFormed = true := rfl
theorem pfm_wellFormed : pfm.wellFormed = true := rfl
theorem nanosyntax_wellFormed : nanosyntax.wellFormed = true := rfl
theorem mas_wellFormed : mas.wellFormed = true := rfl

-- ============================================================================
-- §4: Distinguishing properties
-- ============================================================================

/-- DM and Nanosyntax agree on all four dimensions. -/
theorem dm_eq_nanosyntax : dm = nanosyntax := rfl

/-- DM and PFM agree only on mapping (both realizational). -/
theorem dm_pfm_share_mapping :
    dm.mapping = pfm.mapping := rfl

theorem dm_pfm_differ_lexicalism :
    dm.lexicalism ≠ pfm.lexicalism := by decide

theorem dm_pfm_differ_exponence :
    dm.exponence ≠ pfm.exponence := by decide

/-- DM and MaS agree only on lexicalism and exponence. -/
theorem dm_mas_share_lexicalism :
    dm.lexicalism = mas.lexicalism := rfl

theorem dm_mas_share_exponence :
    dm.exponence = mas.exponence := rfl

theorem dm_mas_differ_architecture :
    dm.architecture ≠ mas.architecture := by decide

theorem dm_mas_differ_mapping :
    dm.mapping ≠ mas.mapping := by decide

/-- PFM is the only major theory that is process-based. -/
theorem pfm_unique_processBased :
    pfm.exponence = .processBased ∧
    dm.exponence = .pieceBased ∧
    nanosyntax.exponence = .pieceBased ∧
    mas.exponence = .pieceBased := ⟨rfl, rfl, rfl, rfl⟩

/-- MaS is the only major theory that is incremental. -/
theorem mas_unique_incremental :
    mas.mapping = .incremental ∧
    dm.mapping = .realizational ∧
    nanosyntax.mapping = .realizational ∧
    pfm.mapping = .realizational := ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §5: Structural impossibility
-- ============================================================================

/-- A non-lexicalist, process-based theory is ill-formed: syntax is
    piece-based, so non-lexicalist morphology (which shares the syntactic
    computation) must also be piece-based. -/
theorem nonLexicalist_processBased_illFormed :
    ∀ (a : Architecture) (m : Mapping),
    (TheoryPosition.mk .nonLexicalist a .processBased m).wellFormed = false := by
  intro a m; cases a <;> cases m <;> rfl

/-- A lexicalist theory cannot have syntactic architecture (morphology
    *is* syntax contradicts morphology being separate). -/
theorem lexicalist_syntactic_illFormed :
    ∀ (e : Exponence) (m : Mapping),
    (TheoryPosition.mk .lexicalist .syntactic e m).wellFormed = false := by
  intro e m; cases e <;> cases m <;> rfl

end Theories.Morphology.TheorySpace
