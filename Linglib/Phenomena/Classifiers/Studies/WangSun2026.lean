import Linglib.Theories.Syntax.MereologicalSyntax.Interpretation
import Linglib.Fragments.Mandarin.Classifiers
import Linglib.Theories.Interfaces.SyntaxSemantics.Borer2005
import Linglib.Phenomena.Classifiers.Studies.Chierchia1998

/-!
# Wang & Sun (2026): Detaching Mandarin Classifiers from Nouns
@cite{wang-sun-2026} @cite{adger-2025}

Applies @cite{adger-2025}'s mereological syntax to three problems in
Mandarin classifier phrases:

1. **Modification**: Degree-modified adjectives cannot appear between Num
   and Cl — predicted by dimensionality (Q is full).
2. **Dislocation**: [Cl-N] cannot be topicalized independently of Num —
   predicted by collective spell-out at Q.
3. **Interpretation**: 的 *de* changes classifier from sortal (concrete
   object) to mensural (abstract unit) — predicted by cross-dimensional
   visibility.

## Key Structural Insight

Classifiers are NOT projections of nouns. They are independent syntactic
objects that subjoin to Q as its 1-part. The classifier word spells out
at Q (collective spell-out of the Q-Cl complementation line). This
detachment from N explains all three problems.

-/

namespace WangSun2026

open MereologicalSyntax

-- ════════════════════════════════════════════════════
-- § 1. Grammaticality Data
-- ════════════════════════════════════════════════════

/-- Grammaticality status for Mandarin classifier examples. -/
inductive GramStatus where
  | ok       -- grammatical
  | marginal -- marginally acceptable (?)
  | bad      -- ungrammatical (*)
  | hashBad  -- semantically anomalous (#)
  deriving DecidableEq, Repr

structure ClDatum where
  mandarin : String
  gloss : String
  translation : String
  status : GramStatus
  deriving Repr

/-! ### Problem 1: Modification restrictions -/

/-- (4c) *yī hěn cōngmíng de gè xuéshēng — degree adj before Cl: bad. -/
def ex4c : ClDatum :=
  { mandarin := "yī hěn cōngmíng de gè xuéshēng"
  , gloss := "one very clever DE CL student"
  , translation := "a very clever student"
  , status := .bad }

/-- (8a) yī gè cōngmíng (de) xuéshēng — adj after Cl: ok. -/
def ex8a : ClDatum :=
  { mandarin := "yī gè cōngmíng (de) xuéshēng"
  , gloss := "one CL clever (DE) student"
  , translation := "a clever student"
  , status := .ok }

/-- (29a) *yī hěn dà (de) zhāng zhuōzi — degree adj between Num and Cl: bad. -/
def ex29a : ClDatum :=
  { mandarin := "yī hěn dà (de) zhāng zhuōzi"
  , gloss := "one very big (DE) CL table"
  , translation := "a very big table"
  , status := .bad }

/-- (29b) yī dà zhāng zhuōzi — bare size adj before Cl: ok (included in Q spell-out). -/
def ex29b : ClDatum :=
  { mandarin := "yī dà zhāng zhuōzi"
  , gloss := "one big CL table"
  , translation := "a big table"
  , status := .ok }

/-! ### Problem 1b: Modification IS possible after Cl -/

/-- (28a) yī zhāng hěn dà de zhuōzi — degree adj after Cl: ok. -/
def ex28a : ClDatum :=
  { mandarin := "yī zhāng hěn dà de zhuōzi"
  , gloss := "one CL very big DE table"
  , translation := "a very big table"
  , status := .ok }

/-! ### Problem 2: Dislocation restrictions -/

/-- (5c) *Gè píngguǒ, Zhāngsān chī-le sān — [Cl-N] topicalized, Num stranded: bad. -/
def ex5c : ClDatum :=
  { mandarin := "Gè píngguǒ, Zhāngsān chī-le sān"
  , gloss := "CL apple Zhangsan eat-PFV three"
  , translation := "(intended) As to apples, Zhangsan ate three."
  , status := .bad }

/-- (13b) Píngguǒ, Zhāngsān chī-le sān gè — N topicalized alone: ok. -/
def ex13b : ClDatum :=
  { mandarin := "Píngguǒ, Zhāngsān chī-le sān gè"
  , gloss := "Apple Zhangsan eat-PFV three CL"
  , translation := "(As to) apples, Zhangsan ate three."
  , status := .ok }

/-- (14a) *Sān gè, Zhāngsān chī-le píngguǒ — [Num-Cl] without N: bad. -/
def ex14a : ClDatum :=
  { mandarin := "Sān gè, Zhāngsān chī-le píngguǒ"
  , gloss := "Three CL Zhangsan eat-PFV apple"
  , translation := "(intended) Zhangsan ate three apples."
  , status := .bad }

/-! ### Wh-island effects (§5) -/

/-- (39a) Zhāngsān mǎi-le jǐ zhāng hěn dà de zhuōzi? — wh-numeral before Cl: ok. -/
def ex39a : ClDatum :=
  { mandarin := "Zhāngsān mǎi-le jǐ zhāng hěn dà de zhuōzi?"
  , gloss := "Zhangssan buy-PFV how-many CL very big DE table"
  , translation := "How many very big tables did Zhangssan buy?"
  , status := .ok }

/-- (39b) *Zhāngsān mǎi-le hěn dà de jǐ zhāng zhuōzi? — wh-numeral after Mod: bad. -/
def ex39b : ClDatum :=
  { mandarin := "Zhāngsān mǎi-le hěn dà de jǐ zhāng zhuōzi?"
  , gloss := "Zhangssan buy-PFV very big DE how-many CL table"
  , translation := "(intended) same as (39a)"
  , status := .bad }

/-! ### Problem 3: Interpretation change with 的 *de* -/

/-- (33a) sān bēi jiǔ — no *de*: "three glasses of liquor" (real glasses). -/
def ex33a : ClDatum :=
  { mandarin := "sān bēi jiǔ"
  , gloss := "three glass liquor"
  , translation := "three glasses of liquor"
  , status := .ok }

/-- (33b) sān bēi de jiǔ — with *de*: "three glassfuls of liquor" (abstract). -/
def ex33b : ClDatum :=
  { mandarin := "sān bēi de jiǔ"
  , gloss := "three glass DE liquor"
  , translation := "three glassfuls of liquor"
  , status := .ok }

-- ════════════════════════════════════════════════════
-- § 2. Mereological Structures
-- ════════════════════════════════════════════════════

/-! ### (26b): yī zhāng zhuōzi "a table"

    ```
    D
      @Q: zhāng        ← Q and Cl collectively spell out
        Num: yī    Cl
                     N: zhuōzi
    ```
    Parthood: N <₁ Cl <₁ Q, Num <₂ Q, Q <₁ D. -/

def basic_N : SynObj := .leaf .N
def basic_Cl : SynObj := .sub₁ .Cl basic_N
def basic_Num : SynObj := .leaf .Num
def basic_Q : SynObj := .sub₁₂ .Q basic_Cl basic_Num
def basic_D : SynObj := .sub₁ .D basic_Q

/-! ### (34a): sān bēi jiǔ "three glasses of liquor" — without 的

    Same topology as (26b). Cl is in D's 1-part chain → visible → sortal. -/

def noDe_N : SynObj := .leaf .N
def noDe_Cl : SynObj := .sub₁ .Cl noDe_N
def noDe_Num : SynObj := .leaf .Num
def noDe_Q : SynObj := .sub₁₂ .Q noDe_Cl noDe_Num
def noDe_D : SynObj := .sub₁ .D noDe_Q

/-! ### (34b): sān bēi de jiǔ "three glassfuls of liquor" — with 的

    的 *de* is the spell-out of Mod. Q subjoins to Mod as 1-part;
    Mod then subjoins to D as 2-part. N subjoins directly to D
    as 1-part — NOT to Cl (contrast with noDe where N <₁ Cl).
    ```
    D
      N: jiǔ         Mod: de
                        @Q: bēi
                          Cl    Num: sān
    ```
    Parthood: Cl <₁ Q, Num <₂ Q, Q <₁ Mod, N <₁ D, Mod <₂ D.
    Cl is NOT in D's 1-part chain → invisible → mensural. -/

def de_Cl : SynObj := .leaf .Cl
def de_Num : SynObj := .leaf .Num
def de_Q : SynObj := .sub₁₂ .Q de_Cl de_Num
def de_Mod : SynObj := .sub₁ .Mod de_Q
def de_N : SynObj := .leaf .N
def de_D : SynObj := .sub₁₂ .D de_N de_Mod

/-! ### (27b): hěn dà de "very big"

    ```
    Mod
      @Deg: dà-de
        A          Adv: hěn
    ```
    A <₁ Deg, Adv <₂ Deg, Deg <₁ Mod. Mod spells out *de* at its node;
    Deg spells out the adjective *dà* collectively with A. -/

def modPhrase_A : SynObj := .leaf .A
def modPhrase_Adv : SynObj := .leaf .Adv
def modPhrase_Deg : SynObj := .sub₁₂ .Deg modPhrase_A modPhrase_Adv
def modPhrase : SynObj := .sub₁ .Mod modPhrase_Deg

/-! ### (28c): yī zhāng hěn dà de zhuōzi "a very big table"

    Mod adjoins as 2-part of Cl (Cl has only N as 1-part, so it has room).
    ```
    D
      @Q: zhāng
        Num: yī    Cl
                     N: zhuōzi    Mod
                                    @Deg: dà-de
                                      A    Adv: hěn
    ```
    Parthood: A <₁ Deg, Adv <₂ Deg, Deg <₁ Mod, N <₁ Cl, Mod <₂ Cl,
              Cl <₁ Q, Num <₂ Q, Q <₁ D. -/

def postCl_N : SynObj := .leaf .N
def postCl_Cl : SynObj := .sub₁₂ .Cl postCl_N modPhrase
def postCl_Num : SynObj := .leaf .Num
def postCl_Q : SynObj := .sub₁₂ .Q postCl_Cl postCl_Num
def postCl_D : SynObj := .sub₁ .D postCl_Q

/-! ### (32b): hěn dà de yī zhāng zhuōzi "a very big table" — pre-DP modifier

    Mod adjoins as 2-part of D (D has only Q as 1-part, so it has room).
    Contrast with (28c) where Mod is 2-part of Cl. Same structure
    blocks wh-extraction in (39b): D is full, Num cannot subjoin.
    ```
    D
      @Q: zhāng      Mod: de
        Num: yī  Cl     @Deg: dà-de
                   N      A    Adv: hěn
    ```
    Parthood: N <₁ Cl <₁ Q, Num <₂ Q, Q <₁ D, Mod <₂ D. -/

def preDp_D : SynObj := .sub₁₂ .D basic_Q modPhrase

/-! ### (45b): sān kē "three (CL)" — measure phrase without N

    Classifier independent of noun: Cl has no N subjoined.
    ```
    @PRED: duō
      Deg
        Q          A
        Num: sān   Cl: kē
    ```
    Cl <₁ Q, Num <₂ Q, Q <₁ Deg, A <₂ Deg, Deg <₁ Pred. -/

def meas_Cl : SynObj := .leaf .Cl
def meas_Num : SynObj := .leaf .Num
def meas_Q : SynObj := .sub₁₂ .Q meas_Cl meas_Num
def meas_A : SynObj := .leaf .A
def meas_Deg : SynObj := .sub₁₂ .Deg meas_Q meas_A
def meas_Pred : SynObj := .sub₁ .Pred meas_Deg

-- ════════════════════════════════════════════════════
-- § 3. Structural Predictions
-- ════════════════════════════════════════════════════

/-! ### Prediction 1: Q is full — no modifier can intervene

    Q has both a 1-part (Cl) and a 2-part (Num). By Dimensionality,
    no further subjunction to Q is possible. This derives the ban on
    degree-modified adjectives between Num and Cl (examples 4c, 29a). -/

theorem q_is_full : basic_Q.isFull = true := rfl

theorem cannot_subjoin_to_q :
    subjoin (.leaf .Mod) basic_Q = none := rfl

/-- Cl has only N as 1-part — it has room for Mod as 2-part. -/
theorem cl_has_room : basic_Cl.isFull = false := rfl

/-- The modification contrast: Mod CAN be 2-part of Cl (has room)
    but CANNOT be part of Q (full). This derives (28a) vs (29a). -/
theorem modification_contrast :
    basic_Cl.isFull = false ∧ basic_Q.isFull = true := ⟨rfl, rfl⟩

/-- (28c): post-Cl modification preserves Cl visibility from D.
    Adding Mod as Cl's 2-part does not disrupt the 1-part chain
    D → Q → Cl, so the classifier retains its sortal reading. -/
theorem postCl_cl_still_visible :
    labelInOnePartChain .Cl postCl_D = true := by native_decide

/-! ### Prediction 1b: Classifier independence from nouns

    (45b) shows a classifier with no N subjoined — the classifier
    functions as a measure phrase in a degree construction. -/

/-- Cl has no N as subpart in (45b): classifier is structurally
    independent of nouns. -/
theorem meas_cl_has_no_noun :
    meas_Cl.containsLabel .N = false := by native_decide

/-- Cl is still in Pred's 1-part chain despite having no N. -/
theorem meas_cl_visible :
    labelInOnePartChain .Cl meas_Pred = true := by native_decide

/-! ### Prediction 2: Cl spells out at Q

    Q's complementation line (1-part chain) includes both Q and Cl.
    The classifier word is realized at Q via collective spell-out.
    Extracting the classifier therefore means extracting Q, which also
    contains Num as 2-part — [Cl-N] cannot topicalize without Num
    (examples 5c, 14a). -/

theorem q_compline : basic_Q.compLine = [.Q, .Cl, .N] := rfl

theorem cl_in_q_spellout :
    basic_Q.compLine.contains .Cl = true := by native_decide

/-- Q contains both Cl and Num: extracting Q extracts both. -/
theorem q_contains_both :
    basic_Q.containsLabel .Cl = true ∧
    basic_Q.containsLabel .Num = true := ⟨rfl, rfl⟩

/-! ### Prediction 3: 的 *de* changes Cl visibility from D

    **Without 的**: Cl <₁ Q <₁ D — within-dimension transitivity applies.
    Cl is in D's 1-part chain, so Cl's semantic content (sortal meaning,
    e.g., "real glass") contributes to D's referential interpretation.

    **With 的**: Cl <₁ Q <₁ Mod ∧₂ D — cross-dimension path. Cl is NOT
    in D's 1-part chain (D's 1-part chain goes through N only). Cl's
    content is invisible to D → abstract measure reading ("glassful"). -/

theorem cl_visible_without_de :
    labelInOnePartChain .Cl noDe_D = true := by native_decide

theorem cl_invisible_with_de :
    labelInOnePartChain .Cl de_D = false := by native_decide

/-- The *de* contrast: same classifier, different visibility. -/
theorem de_changes_visibility :
    labelInOnePartChain .Cl noDe_D = true ∧
    labelInOnePartChain .Cl de_D = false :=
  ⟨by native_decide, by native_decide⟩

/-! ### Prediction 3b: 的 detaches N from Cl

    The key structural difference: without 的, N is 1-part of Cl
    (N <₁ Cl); with 的, Cl is bare (no N) and N is directly 1-part
    of D (N <₁ D). This is NOT movement — it is a different
    derivation path (different subjunction targets). -/

/-- Without 的: N is inside Cl (N <₁ Cl). -/
theorem noDe_n_inside_cl : noDe_Cl.onePart = some noDe_N := rfl

/-- With 的: Cl is bare — no N subjoined to it. -/
theorem de_cl_is_bare : de_Cl.onePart = none := rfl

/-! ### Prediction 3c: Two modifier positions

    Post-Cl (28c): Mod <₂ Cl. D has only Q as 1-part (not full).
    Pre-DP (32b): Mod <₂ D. D is full (Q + Mod).
    Both are grammatical, but the pre-DP structure blocks
    wh-movement because D is full (see Prediction 5). -/

/-- Pre-DP modifier: D is full. -/
theorem preDp_D_is_full : preDp_D.isFull = true := rfl

/-- Post-Cl modifier: D is NOT full (only Q as 1-part). -/
theorem postCl_D_not_full : postCl_D.isFull = false := rfl

/-! ### Prediction 4: N is always visible from D

    Regardless of 的, N is always directly in D's 1-part chain:
    without 的, N <₁ Cl <₁ Q <₁ D; with 的, N <₁ D.
    The noun's denotation always contributes to the referent. -/

theorem n_visible_without_de :
    labelInOnePartChain .N noDe_D = true := by native_decide

theorem n_visible_with_de :
    labelInOnePartChain .N de_D = true := by native_decide

/-! ### Prediction 5: Wh-island via dimensionality (§5)

    In (39a), D has only Q as 1-part (no Mod). D is not full, so
    Num (the wh-phrase jǐ) can subjoin to D as its 2-part — the
    intermediate step needed for wh-movement to C.

    In (39b), Mod is 2-part of D (pre-nominal modifier). D is full.
    Num cannot subjoin to D → wh-movement is blocked. -/

/-- (39a): D without Mod has room — Num can subjoin. -/
theorem wh_ok_without_mod :
    (subjoin (.leaf .Num) (SynObj.sub₁ .D basic_Q)).isSome = true := rfl

/-- (39b): D with Mod is full — Num blocked. -/
theorem wh_blocked_with_mod :
    (subjoin (.leaf .Num) (SynObj.sub₁₂ .D basic_Q modPhrase)).isSome = false := rfl

/-- The wh-island contrast: same Q, different D dimensionality. -/
theorem wh_dimensionality_contrast :
    (subjoin (.leaf .Num) (SynObj.sub₁ .D basic_Q)).isSome = true ∧
    (subjoin (.leaf .Num) (SynObj.sub₁₂ .D basic_Q modPhrase)).isSome = false :=
  ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 4. Classifier Reading
-- ════════════════════════════════════════════════════

/-- Reading of a classifier determined by its structural visibility from D.
    When Cl is in D's 1-part chain, the classifier denotes a concrete
    object (sortal). When invisible, it denotes an abstract unit (mensural). -/
inductive ClReading where
  | sortal   -- Cl visible from D: concrete referent (e.g., real glass)
  | mensural -- Cl invisible from D: abstract measure (e.g., glassful)
  deriving DecidableEq, Repr

def classifierReading (d : SynObj) : ClReading :=
  if individuates d then .sortal else .mensural

theorem noDe_is_sortal : classifierReading noDe_D = .sortal := by native_decide

theorem de_is_mensural : classifierReading de_D = .mensural := by native_decide

/-- Both modifier positions (post-Cl and pre-DP) preserve Cl visibility
    from D, so the classifier retains its sortal reading regardless of
    where Mod attaches. -/
theorem both_positions_sortal :
    classifierReading postCl_D = .sortal ∧
    classifierReading preDp_D = .sortal :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 5. Fragment Bridge
-- ════════════════════════════════════════════════════

/-- 杯 bēi (glass) is the classifier in examples (33)–(34). It has
    `isMensural = true`, indicating it CAN function as a measure phrase.
    Whether it DOES have a mensural reading is determined by the structure
    (§4 above), not by the lexical entry alone. -/
theorem bei_can_be_mensural :
    Fragments.Mandarin.Classifiers.bei.isMensural = true := rfl

/-- 张 zhāng (flat surface) is the classifier in the basic structure
    (26b) and modification examples (28)–(29). It is a pure sortal
    classifier — not lexically mensural. -/
theorem zhang_is_sortal :
    Fragments.Mandarin.Classifiers.zhang.isMensural = false := rfl

/-- 个 gè (general) is the default classifier in the dislocation
    examples (5c), (13b), (14a). -/
theorem ge_is_default :
    Fragments.Mandarin.Classifiers.ge.isDefault = true := rfl

-- ════════════════════════════════════════════════════
-- § 6. Bridge to Borer 2005
-- ════════════════════════════════════════════════════

/-! Both @cite{borer-2005} and @cite{wang-sun-2026} place Q below D
    and above N in the nominal spine, and both treat classifiers as
    independent of nouns. The mereological analysis adds a structural
    explanation for the 的-contrast that Borer's theory does not directly
    address: without 的, the classifier is visible to D (sortal);
    with 的, it is invisible (mensural). -/

/-- The 1-part chain from D (without 的) follows the ordering
    D → Q → Cl → N. Two differences from @cite{borer-2005}'s EP
    (D → Num → Q → n → N): (1) n (categorizer) is absent in the
    mereological analysis; (2) Num is Q's 2-part here (outside
    the 1-part chain), whereas Borer places Num above Q in the
    spine. Both frameworks agree on D > Q > N ordering and on Q
    as the individuation locus. -/
theorem noDe_matches_borer_spine :
    noDe_D.compLine = [.D, .Q, .Cl, .N] := rfl

/-- Q is the individuation locus in both frameworks.
    Borer: Q hosts CL#/Div, converting CUM → QUA.
    Wang & Sun: Cl subjoins to Q as 1-part; Q spells out the classifier. -/
theorem q_is_individuation_locus :
    noDe_D.compLine.contains .Q = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 7. End-to-End Chain
-- ════════════════════════════════════════════════════

/-- End-to-end argumentation for 杯 bēi:
    1. Fragment: bēi has mensural affordance (`isMensural = true`)
    2. Without 的: Cl visible from D → sortal reading (real glass)
    3. With 的: Cl invisible from D → mensural reading (glassful)
    4. Without-的 spine matches @cite{borer-2005}'s nominal EP -/
theorem bei_end_to_end :
    Fragments.Mandarin.Classifiers.bei.isMensural = true ∧
    classifierReading noDe_D = .sortal ∧
    classifierReading de_D = .mensural ∧
    noDe_D.compLine = [.D, .Q, .Cl, .N] :=
  ⟨rfl, by native_decide, by native_decide, rfl⟩

/-- End-to-end for modification: Cl has room for Mod (derives 28c),
    Q is full (blocks 29a), and post-Cl modification preserves
    Cl visibility from D (sortal reading maintained). -/
theorem modification_end_to_end :
    basic_Cl.isFull = false ∧
    basic_Q.isFull = true ∧
    classifierReading postCl_D = .sortal :=
  ⟨rfl, rfl, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 8. Semantic Grounding
-- ════════════════════════════════════════════════════

/-! The structural predictions in §§ 3–5 determine syntactic visibility.
    This section connects visibility to @cite{borer-2005}'s mereological
    semantics via the bridge in `Interpretation.lean`: visible Cl → QUA
    (count/sortal); invisible Cl → root preserved (mass/mensural). -/

section SemanticGrounding

open Mereology (CUM QUA)

variable {α : Type*} [SemilatticeSup α]

/-- Without 的: Cl visible → denotation is individuated → QUA. -/
theorem noDe_is_qua (P : α → Prop) :
    QUA (nominalDenotation noDe_D P) :=
  visible_cl_gives_qua noDe_D P (by native_decide)

/-- With 的: Cl invisible → denotation equals the root predicate. -/
theorem de_preserves_root (P : α → Prop) :
    nominalDenotation de_D P = P :=
  invisible_cl_preserves_root de_D P (by native_decide)

/-- With 的 and a cumulative root: denotation is CUM (mass/mensural). -/
theorem de_is_cum (P : α → Prop) (hc : CUM P) :
    CUM (nominalDenotation de_D P) :=
  invisible_cl_cum de_D P (by native_decide) hc

/-- End-to-end 的-contrast: same root, different structure, opposite
    mereological properties. -/
theorem bei_semantic_contrast (P : α → Prop) (hc : CUM P) :
    QUA (nominalDenotation noDe_D P) ∧
    CUM (nominalDenotation de_D P) :=
  de_semantic_contrast noDe_D de_D P
    (by native_decide) (by native_decide) hc

end SemanticGrounding

-- ════════════════════════════════════════════════════
-- § 9. Cross-Theory Chain
-- ════════════════════════════════════════════════════

/-! End-to-end argumentation connecting three independent theories:

    1. **@cite{chierchia-1998}**: Mandarin is [+arg, -pred] → nouns are
       kind-denoting → bare nouns are arguments → classifiers required.
    2. **@cite{borer-2005}**: Roots denote cumulative (CUM) predicates.
       The Q head hosts individuation (Div), converting CUM → QUA.
       Classifiers spell out at Q.
    3. **@cite{wang-sun-2026}**: Mereological syntax determines whether
       Cl is visible from D via 1-part chain transitivity. Visible Cl → QUA
       (sortal); invisible Cl → CUM (mensural). The particle 的 changes
       dimensional attachment, toggling visibility.

    The CUM P hypothesis in `bei_semantic_contrast` IS Borer's thesis
    instantiated for Chierchia's [+arg, -pred] languages: root predicates
    are cumulative because they denote kind-level extensions (closed under
    join). -/

section CrossTheoryChain

open Mereology (CUM QUA)

variable {α : Type*} [SemilatticeSup α]

/-- Mandarin's NMP is [+arg, -pred]: nouns denote kinds, requiring
    classifiers for counting. This is the typological precondition
    for the entire mereological analysis. -/
theorem mandarin_needs_classifiers :
    Fragments.Mandarin.Nouns.mandarinMapping =
      Semantics.Noun.Kind.Chierchia1998.NominalMapping.argOnly :=
  Chierchia1998.mandarin_mapping

/-- The Chierchia–Borer–Wang&Sun chain for 杯 bēi:
    1. Mandarin NMP = argOnly → classifiers required (Chierchia)
    2. bēi has mensural affordance (Fragment)
    3. Without 的: Cl visible → QUA (Borer + Wang&Sun)
    4. With 的: Cl invisible → CUM under Borer's thesis
    5. Same root, opposite mereological properties (Interpretation) -/
theorem full_chain (P : α → Prop) (hc : CUM P) :
    -- Chierchia: Mandarin needs classifiers
    Fragments.Mandarin.Nouns.mandarinMapping =
      Semantics.Noun.Kind.Chierchia1998.NominalMapping.argOnly ∧
    -- Fragment: bēi can be mensural
    Fragments.Mandarin.Classifiers.bei.isMensural = true ∧
    -- Structural: opposite visibility
    individuates noDe_D = true ∧
    individuates de_D = false ∧
    -- Semantic: opposite mereological properties
    QUA (nominalDenotation noDe_D P) ∧
    CUM (nominalDenotation de_D P) :=
  ⟨Chierchia1998.mandarin_mapping,
   rfl,
   by native_decide,
   by native_decide,
   visible_cl_gives_qua noDe_D P (by native_decide),
   invisible_cl_cum de_D P (by native_decide) hc⟩

end CrossTheoryChain

end WangSun2026
