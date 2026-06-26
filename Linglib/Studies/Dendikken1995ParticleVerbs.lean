import Linglib.Syntax.Minimalist.SmallClause

/-!
# Particle verb constructions — small-clause analysis

[dendikken-1995] [baker-1988]

[dendikken-1995] analyses verbal particles as **ergative** small-clause
heads. The book's primary focus is *complex* particle constructions
(`make John out a liar`, ch. 2), with applications to triadic constructions
and Dative Shift (ch. 3-4) and to applicatives and transitive causatives
(ch. 5). All four phenomena instantiate a SC-in-SC structural template
`[VP V [SC1 Spec [XP Prt [SC2 NP {AP/NP/PP/VP}]]]]` (book p. 269).

This file formalises only the simplex case (`John looked up the
information`) of ch. 2.4, and only the surface SC after NP-movement
to SpecSC. It does **not** capture:

- The SC-in-SC structure for complex PVCs (the book's main contribution).
  Encoding nested small clauses cleanly is pending substrate work on
  `SmallClause` itself; current `structure SmallClause` has no
  recursion-friendly shape.

- Overt P-to-V head incorporation. [dendikken-1995] (§2.4.3) argues
  that English does **not** feature overt particle incorporation. Two
  arguments (book p. 89, citing Emonds 1993:243, fn. 27): (i) V+Prt
  sequences like `brush off` lack the English compound stress pattern
  found on N `'brush off` and V `'baby sit`; (ii) inflection attaches to
  V alone, e.g. `Are your friends pushin' the car?` (V `push` + `-in'`
  participle), not to a putative [V+Prt] complex. Right-Hand Head Rule
  also forbids right-adjoining the particle to V. What den Dikken calls
  "verb-particle reanalysis" is an LF operation (cosuperscripting /
  Government Transparency Corollary, [baker-1988]), not formation
  of an overt complex head. Encoding LF reanalysis requires substrate
  distinct from `formComplexLI`.

- A weight-based derivation rule (`pronoun → split` / `heavy → continuous`).
  This is [kayne-1985]'s account, which [dendikken-1995] (§2.4.5)
  explicitly refutes (citing Diesing & Jelinek 1993). den Dikken's own
  account of the pronoun ban derives from LF reanalysis interacting with
  pronominal cliticization, again pending the LF reanalysis substrate.

## Main declarations

- `ParticleVerb`, `inventory`: English verb-particle lexical entries
- `pvToSmallClause`: the simplex PVC as a P-headed small clause
- `pvToSmallClause_isSmallClause`: the SC satisfies the companion
  `IsSmallClause` predicate
-/

namespace Dendikken1995ParticleVerbs

open Minimalist

/-! ## Particle verb inventory -/

/-- A particle verb entry: verb + particle + gloss. -/
structure ParticleVerb where
  verb     : String
  particle : String
  meaning  : String
  deriving Repr, DecidableEq

def pick_up   : ParticleVerb := ⟨"pick",  "up",  "lift / collect"⟩
def lift_up   : ParticleVerb := ⟨"lift",  "up",  "raise"⟩
def throw_out : ParticleVerb := ⟨"throw", "out", "discard"⟩
def put_down  : ParticleVerb := ⟨"put",   "down", "set down"⟩
def call_off  : ParticleVerb := ⟨"call",  "off", "cancel"⟩

def inventory : List ParticleVerb :=
  [pick_up, lift_up, throw_out, put_down, call_off]

/-! ## Simplex PVC: surface SC after NP-movement

For a simplex PVC `John looked the information up` (the V-NP-Prt order),
the surface structure has the DP raised to SpecSC and the particle as
the SC head. Note this is the *output* of NP-movement — den Dikken's
D-structure has the DP as the *complement* of the (ergative) particle,
with SpecSC empty. The current `SmallClause` shape forces a subject
field, so we record the post-movement form. -/

def pvToSmallClause (pv : ParticleVerb) (dpId prtId : Nat) : SmallClause :=
  { subject := SO.mkLeafPhon .D [] "DP" dpId
    predicate := SO.mkLeafPhon .P [] pv.particle prtId
    predCat := .P }

/-- All PVC small clauses have predicate category P. -/
theorem pvc_pred_is_P (pv : ParticleVerb) (dpId prtId : Nat) :
    (pvToSmallClause pv dpId prtId).predCat = .P := rfl

/-! ## Connection to canonical SC shape

The two trivial unfolding theorems above are convenience aliases. The
load-bearing structural fact about `pvToSmallClause` is its tree shape
once converted to a `SyntacticObject` via `SmallClause.toSO` — a 2-leaf
binary tree (subject + predicate). This is the shape consumed by any
file that wants to compose PVC SCs into larger structures (e.g.
`embedUnderV` for the full `[VP V [SC DP Prt]]` analysis, as used by
`HaddicanEtAl2026.pvc_sc`). Stated as a leaf count over the noncomputable
Merge node (`SO.leafCount_merge`) so downstream files can rewrite without
unfolding `pvToSmallClause`. -/

/-- Any PVC small clause is a 2-leaf binary tree (subject + predicate). -/
theorem pvToSmallClause_toSO_shape (pv : ParticleVerb) (dpId prtId : Nat) :
    (pvToSmallClause pv dpId prtId).toSO.leafCount = 2 := by
  simp only [pvToSmallClause, SmallClause.toSO, SO.leafCount_merge,
    SO.mkLeafPhon, SO.leafCount_lexLeaf]

/-- The `predCat` field of `pvToSmallClause` agrees with the
    `predicate.headCat` reading — the well-formedness invariant
    consumed by `SmallClause.toSO_isSmallClause`. The `mkLeafPhon`-built
    predicate is a leaf, so the computable `outerCatC` head category
    reduces definitionally to its stored `predCat`. -/
theorem pvToSmallClause_consistent (pv : ParticleVerb) (dpId prtId : Nat) :
    (pvToSmallClause pv dpId prtId).predicate.headCat =
      some (pvToSmallClause pv dpId prtId).predCat.toCat := rfl

/-- The PVC small clause satisfies `IsSmallClause` — the companion
    predicate over raw `SyntacticObject`s. Discharges via the
    well-formedness invariant + the SC-side round-trip lemma. -/
theorem pvToSmallClause_isSmallClause (pv : ParticleVerb) (dpId prtId : Nat) :
    IsSmallClause (pvToSmallClause pv dpId prtId).toSO :=
  SmallClause.toSO_isSmallClause _ (pvToSmallClause_consistent pv dpId prtId)

end Dendikken1995ParticleVerbs
