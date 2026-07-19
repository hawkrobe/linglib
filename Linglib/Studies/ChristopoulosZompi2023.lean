import Linglib.Morphology.Exponence.Select
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sigma

/-!
# Christopoulos & Zompì 2023: Weak Case Containment
[christopoulos-zompi-2023]

Three rival featural decompositions of NOM ≺ ACC ≺ DAT, run against two
discriminating predictions under Subset-Principle competition. **Strong Case
Containment** (Table 1; [caha-2009], [smith-moskal-xu-kang-bobaljik-2019])
nests the three cases in a chain; **No Case Containment** (Table 2) makes them
pairwise incomparable; the paper's **Weak Case Containment** (Table 24) keeps
ACC ⊂ DAT but gives NOM its own feature, incomparable to ACC. The predictions:

* ***ABA** ([bobaljik-2012]'s coinage): SCC and WCC exclude it structurally
  (`noABA`, discharged for both by their shared order-theoretic profile:
  ACC-appliers persist to DAT, and NOM∩DAT-appliers reach ACC); NCC derives it
  (`ncc_aba_generable`, via a rule referencing its ACC-only feature k₃).
* **Non-Elsewhere Nominative Stems**: SCC forces any NOM-applying rule to be
  the featureless elsewhere (`scc_nom_forces_empty`) — Doric Greek h-stems,
  Latvian *pat-*, and English 3sg *h-* stems refute this; WCC's k₀ writes them
  directly (Table 25 rows 2–3; the Latvian rules (7) below). [mcfadden-2018]'s
  markedness rescue of SCC is refuted on Latvian/Tocharian Gender in the
  paper's §3.3 (not formalized here).

Table 25's eight derivation rows are reproduced by `decide`; the Latvian
emphatic pronoun (Table 20, rules (7)) and the Yiddish 1st person (fn. 25) are
run as full stem-distribution checks, including the paper's two minimality
points: *pat-* needs the singular feature alongside k₀ (fn. 26), and *undz*
needs k₁ (fn. 25).

## Main results

* `noABA` — under any decomposition with `D acc ⊆ D dat` and
  `D nom ∩ D dat ⊆ D acc`, one rule winning NOM and DAT forces it to win ACC;
  `noABA_scc` / `noABA_wcc` discharge the hypotheses by `decide`
* `ncc_aba_generable` — the two-rule NCC vocabulary generating A B A
* `scc_nom_forces_empty` — SCC has no non-elsewhere nominative rules
* `table25_row1` … `table25_row8` — the WCC derivation table
* `latvian_stems` / `latvian_gender_blind` / `latvian_pat_needs_singular` —
  Table 20 under rules (7)
* `yiddish_stems` / `undz_needs_k1` — the fn. 25 paradigm and its k₁ argument
-/

namespace ChristopoulosZompi2023

open Morphology Morphology.Exponence

/-- The privative features: k₀–k₃ across the three Case decompositions
(Tables 1, 2, 24), plus number (s₀ singular, p₀ plural) and gender features
for the empirical paradigms — no property contained in its category-mates
(fn. 26). -/
inductive K | k0 | k1 | k2 | k3 | s0 | p0 | m0 | f0
  deriving DecidableEq, Fintype, Repr

/-- The case triplet, in the *ABA order NOM ≺ ACC ≺ DAT. -/
inductive Case3 | nom | acc | dat
  deriving DecidableEq, Fintype, Repr

/-- **Strong Case Containment** (Table 1): a chain ∅ ⊂ {k₁} ⊂ {k₁,k₂}. -/
def scc : Case3 → Finset K
  | .nom => ∅ | .acc => {.k1} | .dat => {.k1, .k2}

/-- **No Case Containment** (Table 2): pairwise incomparable feature sets;
k₃ is the NOM/ACC feature absent from DAT. -/
def ncc : Case3 → Finset K
  | .nom => {.k0, .k3} | .acc => {.k1, .k3} | .dat => {.k1, .k2}

/-- **Weak Case Containment** (Table 24): ACC ⊂ DAT as in SCC, but NOM carries
its own k₀, incomparable to ACC — no k₃. -/
def wcc : Case3 → Finset K
  | .nom => {.k0} | .acc => {.k1} | .dat => {.k1, .k2}

/-- A rule of exponence over a decomposition `D`: a feature specification and
an exponent. Applicability is the **Subset Principle** — the rule's features
are a subset of the cell's. -/
structure Rule (Cell : Type*) (D : Cell → Finset K) (F : Type*) where
  /-- The rule's Case (and φ) feature specification. -/
  feats : Finset K
  /-- The exponent inserted. -/
  exponent : F
  deriving DecidableEq

variable {Cell F : Type*} {D : Cell → Finset K}

instance : Exponence (Rule Cell D F) Cell F :=
  ⟨Rule.exponent, fun r c => r.feats ⊆ D c⟩

@[simp] theorem applies_iff {r : Rule Cell D F} {c : Cell} :
    Exponence.Applies (F := F) r c ↔ r.feats ⊆ D c := Iff.rfl

instance (c : Cell) :
    DecidablePred (fun r : Rule Cell D F => Exponence.Applies (F := F) r c) :=
  fun r => inferInstanceAs (Decidable (r.feats ⊆ D c))

/-- The surface pattern of a vocabulary: at each cell, the exponent of the
most highly specified applicable rule — the paper's DM implementation of the
Elsewhere Principle, as the shared core's `selectBy` on feature cardinality. -/
def pattern (v : List (Rule Cell D F)) (c : Cell) : Option F :=
  (selectBy (fun r : Rule Cell D F => r.feats.card) v c).map Rule.exponent

/-- Strict competition: `r` beats every other applicable rule on feature
cardinality. -/
def IsWinner (v : List (Rule Cell D F)) (c : Cell) (r : Rule Cell D F) : Prop :=
  r ∈ v ∧ r.feats ⊆ D c ∧
    ∀ s ∈ v, s.feats ⊆ D c → s ≠ r → s.feats.card < r.feats.card

/-! ### *ABA -/

/-- ***ABA, order-theoretically**: whenever ACC-appliers persist to DAT
(`D acc ⊆ D dat`) and NOM∩DAT-appliers reach ACC (`D nom ∩ D dat ⊆ D acc`), a
rule winning both NOM and DAT also wins ACC. The two hypotheses are the shared
profile of SCC and WCC; NCC violates the first via k₃. -/
theorem noABA {D : Case3 → Finset K} {v : List (Rule Case3 D F)}
    {A B : Rule Case3 D F}
    (h1 : D .acc ⊆ D .dat) (h2 : D .nom ∩ D .dat ⊆ D .acc)
    (hnom : IsWinner v .nom A) (hdat : IsWinner v .dat A)
    (hacc : IsWinner v .acc B) : B = A := by
  by_contra hne
  have hAacc : A.feats ⊆ D .acc := fun k hk =>
    h2 (Finset.mem_inter.mpr ⟨hnom.2.1 hk, hdat.2.1 hk⟩)
  have hAB : A.feats.card < B.feats.card :=
    hacc.2.2 A hnom.1 hAacc (fun h => hne h.symm)
  have hBdat : B.feats ⊆ D .dat := fun k hk => h1 (hacc.2.1 hk)
  exact absurd (hdat.2.2 B hacc.1 hBdat hne) (Nat.lt_asymm hAB)

/-- *ABA under Strong Case Containment ([caha-2009],
[smith-moskal-xu-kang-bobaljik-2019]). -/
theorem noABA_scc {v : List (Rule Case3 scc F)} {A B : Rule Case3 scc F}
    (hnom : IsWinner v .nom A) (hdat : IsWinner v .dat A)
    (hacc : IsWinner v .acc B) : B = A :=
  noABA (by decide) (by decide) hnom hdat hacc

/-- *ABA under Weak Case Containment: the paper's Table 24 decomposition keeps
SCC's exclusion. -/
theorem noABA_wcc {v : List (Rule Case3 wcc F)} {A B : Rule Case3 wcc F}
    (hnom : IsWinner v .nom A) (hdat : IsWinner v .dat A)
    (hacc : IsWinner v .acc B) : B = A :=
  noABA (by decide) (by decide) hnom hdat hacc

/-- Exponent labels for the derivation tables. -/
inductive Ex | A | B | C
  deriving DecidableEq, Repr

/-- **ABA is generable under NCC**: an elsewhere rule plus a rule referencing
{k₁, k₃} — features jointly present only in ACC — yields A B A (the
overgeneration of the paper's §2). -/
theorem ncc_aba_generable :
    pattern (D := ncc) [⟨∅, Ex.A⟩, ⟨{.k1, .k3}, Ex.B⟩] .nom = some .A ∧
      pattern (D := ncc) [⟨∅, Ex.A⟩, ⟨{.k1, .k3}, Ex.B⟩] .acc = some .B ∧
      pattern (D := ncc) [⟨∅, Ex.A⟩, ⟨{.k1, .k3}, Ex.B⟩] .dat = some .A := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Non-Elsewhere Nominative Stems -/

/-- Under SCC, a rule applicable in the nominative is featureless — the
elsewhere rule. SCC therefore cannot write a Non-Elsewhere Nominative Stem
(the paper's §3 problem: Doric h-stems, Latvian *pat-*, English *h-*). -/
theorem scc_nom_forces_empty {r : Rule Case3 scc F}
    (h : Exponence.Applies (F := F) r .nom) : r.feats = ∅ :=
  Finset.subset_empty.mp h

/-! ### Table 25: derivations of AAA, ABB, AAB, ABC under WCC

Each row's rule inventory, its generated pattern by `decide`. Rows 5 and 7
use the minimal `{k₂}` variant of the table's `{(k₁,)k₂}`. Rows 2–3 are the
NENS derivations — rule A strictly or weakly outranks the elsewhere B. -/

theorem table25_row1 :
    ∀ c, pattern (D := wcc) [⟨∅, Ex.A⟩] c = some .A := by decide

theorem table25_row2 :
    pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨{.k1}, Ex.B⟩] .nom = some .A ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨{.k1}, Ex.B⟩] .acc = some .B ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨{.k1}, Ex.B⟩] .dat = some .B := by
  refine ⟨by decide, by decide, by decide⟩

theorem table25_row3 :
    pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨∅, Ex.B⟩] .nom = some .A ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨∅, Ex.B⟩] .acc = some .B ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨∅, Ex.B⟩] .dat = some .B := by
  refine ⟨by decide, by decide, by decide⟩

theorem table25_row4 :
    pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k1}, Ex.B⟩] .nom = some .A ∧
      pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k1}, Ex.B⟩] .acc = some .B ∧
      pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k1}, Ex.B⟩] .dat = some .B := by
  refine ⟨by decide, by decide, by decide⟩

theorem table25_row5 :
    pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k2}, Ex.B⟩] .nom = some .A ∧
      pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k2}, Ex.B⟩] .acc = some .A ∧
      pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k2}, Ex.B⟩] .dat = some .B := by
  refine ⟨by decide, by decide, by decide⟩

theorem table25_row6 :
    pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k1}, Ex.B⟩, ⟨{.k1, .k2}, Ex.C⟩] .nom
        = some .A ∧
      pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k1}, Ex.B⟩, ⟨{.k1, .k2}, Ex.C⟩] .acc
        = some .B ∧
      pattern (D := wcc) [⟨∅, Ex.A⟩, ⟨{.k1}, Ex.B⟩, ⟨{.k1, .k2}, Ex.C⟩] .dat
        = some .C := by
  refine ⟨by decide, by decide, by decide⟩

theorem table25_row7 :
    pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨∅, Ex.B⟩, ⟨{.k2}, Ex.C⟩] .nom
        = some .A ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨∅, Ex.B⟩, ⟨{.k2}, Ex.C⟩] .acc
        = some .B ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨∅, Ex.B⟩, ⟨{.k2}, Ex.C⟩] .dat
        = some .C := by
  refine ⟨by decide, by decide, by decide⟩

theorem table25_row8 :
    pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨{.k1}, Ex.B⟩, ⟨{.k1, .k2}, Ex.C⟩] .nom
        = some .A ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨{.k1}, Ex.B⟩, ⟨{.k1, .k2}, Ex.C⟩] .acc
        = some .B ∧
      pattern (D := wcc) [⟨{.k0}, Ex.A⟩, ⟨{.k1}, Ex.B⟩, ⟨{.k1, .k2}, Ex.C⟩] .dat
        = some .C := by
  refine ⟨by decide, by decide, by decide⟩

/-! ### Latvian *pat-* ~ *paš-* (Table 20, rules (7))

The emphatic pronoun singles out nominative singular across both genders:
*pat-s* / *pat-i* against *paš-* everywhere else. Rules (7): *pat-* in k₀
singular contexts, *paš-* elsewhere. Number decomposes with neither value
contained in the other (fn. 26); gender features are carried by the cells but
referenced by no rule. -/

/-- Number. -/
inductive LNum | sg | pl
  deriving DecidableEq, Fintype, Repr

/-- Gender. -/
inductive LGen | masc | fem
  deriving DecidableEq, Fintype, Repr

/-- A Latvian cell: case, number, gender. -/
structure LCell where
  case : Case3
  num : LNum
  gen : LGen
  deriving DecidableEq, Fintype, Repr

/-- The Latvian decomposition: WCC for case, s₀/p₀ for number, m₀/f₀ for
gender. -/
def latvian (c : LCell) : Finset K :=
  wcc c.case ∪ (match c.num with | .sg => {.s0} | .pl => {.p0})
    ∪ (match c.gen with | .masc => {.m0} | .fem => {.f0})

/-- Rules (7): *pat-* in k₀ singular contexts; *paš-* elsewhere. -/
def latvianRules : List (Rule LCell latvian String) :=
  [⟨{.k0, .s0}, "pat"⟩, ⟨∅, "paš"⟩]

/-- The stem distribution of Table 20: *pat-* exactly in the nominative
singulars, *paš-* elsewhere (stems read off *pat-s, pat-i, paš-u, paš-am,
paš-ai, paš-i, paš-as, paš-us, paš-iem, paš-ām*). -/
def table20stem (c : LCell) : String :=
  if c.case = .nom ∧ c.num = .sg then "pat" else "paš"

/-- Rules (7) generate Table 20's stem distribution. -/
theorem latvian_stems : ∀ c, pattern latvianRules c = some (table20stem c) := by
  decide

/-- The pattern "cuts across genders": neither rule references gender, so the
distribution is gender-blind. -/
theorem latvian_gender_blind (c n) :
    pattern latvianRules ⟨c, n, .masc⟩ = pattern latvianRules ⟨c, n, .fem⟩ := by
  revert c n; decide

/-- *pat-* must be specified for the singular alongside k₀ (fn. 26): dropping
s₀ overgenerates *pat-* into the nominative plural. -/
theorem latvian_pat_needs_singular :
    pattern [(⟨{.k0}, "pat"⟩ : Rule LCell latvian String), ⟨∅, "paš"⟩]
        ⟨.nom, .pl, .masc⟩ = some "pat" := by
  decide

/-! ### Yiddish 1st person (fn. 25): why k₁ exists

*ix* (NOM.SG), *m-* (elsewhere: *m-ir, m-ix*), *undz* (ACC.PL and DAT.PL).
The *undz* rule must reference k₁: specified for plural alone it would also
capture the nominative plural *m-ir*. This ABB row with B more specific than
the elsewhere is the evidence that WCC's k₁ is not eliminable. -/

/-- A Yiddish cell: case and number. -/
structure YCell where
  case : Case3
  num : LNum
  deriving DecidableEq, Fintype, Repr

/-- The Yiddish decomposition: WCC for case, s₀/p₀ for number. -/
def yiddish (c : YCell) : Finset K :=
  wcc c.case ∪ (match c.num with | .sg => {.s0} | .pl => {.p0})

/-- The three stem rules: *ix* a non-elsewhere nominative-singular stem,
*undz* the k₁-plural stem, *m-* the elsewhere. -/
def yiddishRules : List (Rule YCell yiddish String) :=
  [⟨{.k0, .s0}, "ix"⟩, ⟨{.k1, .p0}, "undz"⟩, ⟨∅, "m"⟩]

/-- The fn. 25 paradigm's stem distribution: *ix* / *m-ix* / *m-ir* in the
singular, *m-ir* / *undz* / *undz* in the plural. -/
def yiddishStem (c : YCell) : String :=
  if c.case = .nom ∧ c.num = .sg then "ix"
  else if c.case ≠ .nom ∧ c.num = .pl then "undz"
  else "m"

/-- The three rules generate the paradigm. -/
theorem yiddish_stems : ∀ c, pattern yiddishRules c = some (yiddishStem c) := by
  decide

/-- *undz* needs k₁ (fn. 25): specified for plural alone, it wrongly beats
*m-* in the nominative plural. -/
theorem undz_needs_k1 :
    pattern [(⟨{.k0, .s0}, "ix"⟩ : Rule YCell yiddish String),
        ⟨{.p0}, "undz"⟩, ⟨∅, "m"⟩] ⟨.nom, .pl⟩ = some "undz" := by
  decide

end ChristopoulosZompi2023
