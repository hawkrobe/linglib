import Linglib.Fragments.Dutch.Adpositions
import Linglib.Theories.Syntax.Minimalism.Formal.ExtendedProjection.Properties
import Linglib.Core.WALS.Features.F85A
import Linglib.Phenomena.Constructions.ParticleVerbs.Studies.Dendikken1995
import Linglib.Phenomena.AuxiliaryVerbs.Selection
import Linglib.Theories.Semantics.Events.SpatialTrace

/-!
# Broekhuis & Corver (2026): Adpositions in Dutch
@cite{broekhuis-corver-2026} @cite{dendikken-2010} @cite{svenonius-2010}

The four-way surface classification of Dutch adpositions (preP, postP,
circumP, intransitive particle) is argued to be epiphenomenal: all derive
from underlying prePs via movement within a PP-internal functional
projection.

## Core empirical generalizations

1. PostPs ⊆ PrePs — every postP can also be a preP (§6)
2. PreP = locational; PostP = directional (§2.2, ex. 21–23)
3. Morphologically complex PrePs block R-pronominalization (§2.1, ex. 20)
4. PostPs/circumPs cannot take adjectival or clausal complements (§2.2)
5. Dutch resists P-stranding; R-pronouns can be extracted (§5.2)

## Theoretical analysis (§6, ex. 62/64)

All four surface orders derive from `[FP _ F [PP P DP/PP]]`:
- **PreP** (default): complement stays in situ
- **PostP**: DP moves to Spec,FP (semantically conditioned — directional)
- **CircumP**: PP/R-pronoun moves to Spec,FP (default for PP complements)
- **Intransitive**: no complement projected

The key distinction is WHAT moves (DP → postP; PP/R-pronoun → circumP),
not whether F is overt. See `MovedConstituent`.

## Cross-references

- `Fragments.Dutch.Adpositions`: lexical inventory
- `Minimalism.Formal.ExtendedProjection`: Place/Path in EP
- `Core.Path.PathShape`: bounded/unbounded/source classification
- `Theories.Semantics.Events.SpatialTrace`: PathShape → telicity
- `Phenomena.AuxiliaryVerbs.Selection`: Dutch *zijn*/*hebben* split
- `Dendikken1995`: particles as P heads
- `Core.WALS.Features.F85A`: cross-linguistic adposition order
-/

namespace BroekhuisCorver2026

open Fragments.Dutch.Adpositions
open Minimalism
open Core.Path (PathShape)

-- ════════════════════════════════════════════════════
-- § 1. PP-internal structure and surface orders
-- ════════════════════════════════════════════════════

/-- Surface order of P and its complement.
    @cite{broekhuis-corver-2026} §6, ex. 62/64: all four derive from the
    same underlying structure `[FP _ F [PP P DP/PP]]`. -/
inductive PPSurfaceOrder where
  | preP        -- P DP: complement stays in situ
  | postP       -- DP P: DP complement moves to Spec,FP
  | circumP     -- P₁ DP P₂: PP/R-pronoun complement moves to Spec,FP
  | intransP    -- P (no complement): verbal particle / intransitive
  deriving DecidableEq, Repr

/-- What constituent moves to Spec,FP to produce a non-canonical order.
    @cite{broekhuis-corver-2026} §6 ex. 64: the crucial distinction is
    WHAT moves — DP yields postP, PP/R-pronoun yields circumP. -/
inductive MovedConstituent where
  | noMovement      -- preP: complement in situ (default)
  | dpToSpecFP      -- postP: DP moves (semantically conditioned — directional)
  | ppToSpecFP      -- circumP: PP or R-pronoun moves (default for PP complements)
  | noComplement    -- intransitive: nothing to move
  deriving DecidableEq, Repr

/-- Derive surface order from what moved.
    @cite{broekhuis-corver-2026} §6, ex. 64:
    - a. PrePP (default): `[FP _ F [P DP]]`
    - b. PostP (semantically conditioned): `[FP DPᵢ F [P tᵢ]]`
    - c. CircumP (default for PP compl): `[FP PPᵢ/R-pronᵢ F [P tᵢ]]` -/
def deriveSurfaceOrder : MovedConstituent → PPSurfaceOrder
  | .noMovement   => .preP
  | .dpToSpecFP   => .postP
  | .ppToSpecFP   => .circumP
  | .noComplement => .intransP

/-- PreP = no movement (default). -/
theorem preP_no_movement :
    deriveSurfaceOrder .noMovement = .preP := rfl

/-- PostP = DP to Spec,FP (semantically conditioned — directional). -/
theorem postP_dp_movement :
    deriveSurfaceOrder .dpToSpecFP = .postP := rfl

/-- CircumP = PP/R-pronoun to Spec,FP (default for PP complements). -/
theorem circumP_pp_movement :
    deriveSurfaceOrder .ppToSpecFP = .circumP := rfl

/-- Intransitive = no complement projected. -/
theorem intransP_no_complement :
    deriveSurfaceOrder .noComplement = .intransP := rfl

-- ════════════════════════════════════════════════════
-- § 2. Surface order inventory
-- ════════════════════════════════════════════════════

/-- Derive available surface orders from an adposition's distributional
    properties. -/
def availableOrders (a : DutchAdposition) : List PPSurfaceOrder :=
  (if a.prePOk then [.preP] else []) ++
  (if a.postPOk then [.postP] else []) ++
  (if a.circumPart.isSome then [.circumP] else []) ++
  (if a.intransOk then [.intransP] else [])

/-- *op* has three surface orders: preP, postP, intransitive. -/
example : availableOrders op = [.preP, .postP, .intransP] := by native_decide

/-- *van* has preP and circumP (*van...af*). -/
example : availableOrders van = [.preP, .circumP] := by native_decide

/-- *onder* has preP, circumP (*onder...door*), locational + directional. -/
example : availableOrders onder = [.preP, .circumP] := by native_decide

/-- *af* is only intransitive (circumP second element, not standalone). -/
example : availableOrders af = [.intransP] := by native_decide

-- ════════════════════════════════════════════════════
-- § 3. Complement-type restrictions
-- ════════════════════════════════════════════════════

/-! @cite{broekhuis-corver-2026} §2.2 (p.9): "it seems that postPs and
    circumPs differ from prePs in that they are incapable of selecting
    adjectival or clausal complements." -/

/-- No postP-capable adposition takes adjectival complements. -/
theorem postP_no_adjectival :
    ∀ a ∈ dutchAdpositions, a.postPOk →
    a.complTypes.all (· != .adjectival) := by native_decide

/-- No postP-capable adposition takes clausal complements. -/
theorem postP_no_clausal :
    ∀ a ∈ dutchAdpositions, a.postPOk →
    a.complTypes.all (· != .clausal) := by native_decide

/-- No circumP-capable adposition takes adjectival complements. -/
theorem circumP_no_adjectival :
    ∀ a ∈ dutchAdpositions, a.circumPart.isSome →
    a.complTypes.all (· != .adjectival) := by native_decide

/-- No circumP-capable adposition takes clausal complements. -/
theorem circumP_no_clausal :
    ∀ a ∈ dutchAdpositions, a.circumPart.isSome →
    a.complTypes.all (· != .clausal) := by native_decide

-- ════════════════════════════════════════════════════
-- § 4. Bridge to Extended Projection framework
-- ════════════════════════════════════════════════════

/-! The locational/directional distinction maps onto the Place/Path
    cartographic heads in the Extended Projection framework. Locational PPs
    are `[PlaceP Place [PP P DP]]` (truncated EP); directional PPs add
    PathP: `[PathP Path [PlaceP Place [PP P DP]]]` (full adpositional EP). -/

/-- Locational PPs correspond to truncated adpositional EPs. -/
theorem locational_is_truncated_ep :
    isTruncated locationalPP = true := locational_pp_truncated

/-- Directional PPs correspond to full adpositional EPs. -/
theorem directional_is_full_ep :
    allCategoryConsistent directionalPP = true ∧
    allFMonotone directionalPP = true := directional_pp_ep_wellformed

/-- Place and Path inherit [-V, -N] from P. -/
theorem place_path_inherit_cat_features :
    catFeatures .Place = catFeatures .P ∧
    catFeatures .Path = catFeatures .P := by decide

/-- Place and Path are in the adpositional family. -/
theorem place_path_family :
    catFamily .Place = .adpositional ∧
    catFamily .Path = .adpositional := place_path_adpositional

-- ════════════════════════════════════════════════════
-- § 5. End-to-end: PathShape → telicity → auxiliary
-- ════════════════════════════════════════════════════

/-! @cite{broekhuis-corver-2026} §2.2 ex. 22: directional *de heuvel op*
    takes *zijn* (be), locational *op de heuvel* takes *hebben* (have).
    This connects through `PathShape → telicity → unaccusativity →
    auxiliary selection`. -/

open Semantics.Events.SpatialTrace (pathShapeToTelicity)
open Core.Verbs
open Phenomena.AuxiliaryVerbs.Selection

/-- All directional adpositions in the inventory carry a PathShape. -/
theorem directional_adpositions_have_pathShape :
    ∀ a ∈ dutchAdpositions, a.directional → a.pathShape.isSome :=
  directional_has_pathShape

/-- PostP-capable adpositions are directional (and locational). -/
theorem postP_implies_directional :
    ∀ a ∈ dutchAdpositions, a.postPOk → a.directional :=
  fun a ha hpost => (postP_has_both_readings a ha hpost).2

/-- PostP-capable adpositions have a PathShape. -/
theorem postP_has_pathShape :
    ∀ a ∈ dutchAdpositions, a.postPOk → a.pathShape.isSome := by
  intro a ha hpost
  exact directional_has_pathShape a ha (postP_implies_directional a ha hpost)

/-- End-to-end chain for *op*: directional → bounded path → telic.
    @cite{broekhuis-corver-2026} §2.2 ex. 22: *De fietser is de heuvel
    op gereden* "The cyclist rode onto the hill" — *zijn* (be) because
    directional postP *op* denotes a bounded path, which is telic. -/
theorem op_bounded_telic :
    op.pathShape = some .bounded ∧
    pathShapeToTelicity .bounded = .telic :=
  ⟨rfl, rfl⟩

/-- End-to-end: telic → unaccusative → *zijn* (be) in Dutch.
    Dutch has a split auxiliary system; unaccusative (telic change-of-state)
    verbs select *zijn*, matching @cite{broekhuis-corver-2026}'s ex. 22. -/
theorem telic_unaccusative_zijn :
    canonicalSelection .unaccusative = .be ∧
    dutchAankomen.selectionRule = .split :=
  ⟨rfl, rfl⟩

/-- *op* (bounded) vs *van* (source): distinct PathShapes but both telic.
    Goal-oriented and origin-oriented directionality both yield telic VPs. -/
theorem op_van_both_telic :
    pathShapeToTelicity .bounded = .telic ∧
    pathShapeToTelicity .source = .telic :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 6. P-stranding and extraction (§5.2)
-- ════════════════════════════════════════════════════

/-! @cite{broekhuis-corver-2026} §5.2: Dutch resists P-stranding for DP
    complements (ex. 53: *✱Janᵢ heeft Els niet [PP op tᵢ] gewacht*), but
    allows R-pronoun extraction (ex. 54: *Daar <op> heeft Els niet <op>
    gewacht*) and postPP complement extraction (ex. 58b-c).

    This three-way extraction asymmetry follows from the movement analysis:
    - PrePPs: DP is in base position (complement of P) → extraction blocked
    - R-pronouns: already PP-internally moved → can be further extracted
    - PostPPs: DP is in Spec,FP → higher position → extraction possible -/

/-- Extraction possibility from different PP types. -/
inductive PPExtractionType where
  | dpFromPrePP       -- ex. 53: *Jan heeft Els niet [op t] gewacht* — blocked
  | rPronFromPrePP    -- ex. 54: Daar <op> heeft Els niet <op> gewacht — OK
  | dpFromPostPP      -- ex. 58: Marie gaat het bosᵢ [t_i in] — OK
  deriving DecidableEq, Repr

/-- Whether extraction is possible for each PP type. -/
def extractionOk : PPExtractionType → Bool
  | .dpFromPrePP    => false  -- P-stranding blocked (ex. 53)
  | .rPronFromPrePP => true   -- R-pronoun extraction OK (ex. 54)
  | .dpFromPostPP   => true   -- PostPP complement extraction OK (ex. 58)

/-- P-stranding is blocked for DP complements of prePPs. -/
theorem no_p_stranding : extractionOk .dpFromPrePP = false := rfl

/-- R-pronouns can be extracted from prePPs. -/
theorem r_pronoun_extraction_ok : extractionOk .rPronFromPrePP = true := rfl

/-- Complement extraction from postPPs is possible. -/
theorem postPP_extraction_ok : extractionOk .dpFromPostPP = true := rfl

/-- The extraction asymmetry: prePP blocks DP extraction but postPP allows it.
    This follows from the movement analysis — in postPPs the DP is already
    in Spec,FP (a higher, extraction-friendly position). -/
theorem extraction_asymmetry :
    extractionOk .dpFromPrePP = false ∧
    extractionOk .dpFromPostPP = true := ⟨rfl, rfl⟩

/-- R-pronominalization-blocking Ps cannot be postPs.
    Complex Ps lack the internal functional structure needed for
    complement movement. -/
theorem no_rPron_not_postP :
    ∀ a ∈ dutchAdpositions, a.rPronOk = false → a.postPOk = false := by
  native_decide

-- ════════════════════════════════════════════════════
-- § 7. Bridge to WALS F85A
-- ════════════════════════════════════════════════════

/-! Dutch is classified as a preposition language in WALS (F85A). This is
    consistent with @cite{broekhuis-corver-2026}'s analysis: the base order
    is always P-DP (preP); postP/circumP are derived by movement, not by
    a different head-direction parameter. -/

/-- Dutch is listed as "prepositions" in WALS F85A (code "dut"). -/
theorem dutch_wals_prepositions :
    (Core.WALS.F85A.allData.find?
      (fun d => d.walsCode == "dut")).map (·.value)
    = some .prepositions := by native_decide

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Den Dikken (1995): particles as P heads
-- ════════════════════════════════════════════════════

/-! @cite{dendikken-1995} analyzes verbal particles as P heads of small
    clauses. @cite{broekhuis-corver-2026}'s intransitive adpositions include
    the same elements: *op*, *in*, *uit*, *af*, etc. -/

/-- The intransitive adpositions from the fragment. -/
def intransitivePs : List DutchAdposition :=
  dutchAdpositions.filter (·.intransOk)

/-- *af* is exclusively intransitive (circumP second element / particle). -/
theorem af_only_intransitive :
    af.prePOk = false ∧ af.postPOk = false ∧ af.intransOk = true :=
  ⟨rfl, rfl, rfl⟩

/-- @cite{dendikken-1995} PVC predicate category is P — matching
    the category of intransitive adpositions in the fragment. -/
theorem pvc_predCat_is_P :
    Dendikken1995.pvc_pred_is_P
      Phenomena.Constructions.ParticleVerbs.pick_up 0 1 = rfl := rfl

-- ════════════════════════════════════════════════════
-- § 9. R-pronominalization and morphological complexity
-- ════════════════════════════════════════════════════

/-! @cite{broekhuis-corver-2026} §2.1 ex. 19–20: simplex prePs allow
    R-pronominalization (*er op*, *daar in*), but morphologically complex
    prePs (*tijdens*, *ondanks*, *zonder*) resist it. -/

/-- Simplex spatial Ps allow R-pronominalization. -/
theorem simplex_spatial_rPron :
    op.rPronOk = true ∧ in_.rPronOk = true ∧ naar.rPronOk = true ∧
    van.rPronOk = true ∧ uit.rPronOk = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Complex Ps block R-pronominalization. -/
theorem complex_no_rPron :
    tijdens.rPronOk = false ∧ ondanks.rPronOk = false ∧
    zonder.rPronOk = false := complex_Ps_no_rPron

end BroekhuisCorver2026
