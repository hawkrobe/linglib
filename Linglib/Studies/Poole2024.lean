import Linglib.Syntax.Case.Assigner

/-!
# Poole (2024) — Dependent-case assignment could be Agree
[poole-2024] [marantz-1991] [baker-vinokurova-2010]

There are three models of case assignment: **m1** = case via Agree
(functional-head valuation), **m2** = configurational/dependent case
([marantz-1991]), **m3** = m1 + m2. Preminger argues m1 *undergenerates* —
it has no analogue of dependent case, so m1 < m2. [poole-2024] pushes back:
dependent case *can* be implemented in m1, via an ordered Agree **probe
stack** ⟨[∗φ∗]ᵁᴺᴹ < [∗φ∗]ᵁᴺᴹ_DEP⟩ — the first probe values on a caseless DP
("unlocking" the second), and the second then assigns dependent case to the
next caseless DP (the dependency requirement: a second caseless DP must
exist). So m1 ≥ m2: the two models are **extensionally equivalent**, and the
choice between them is *theoretical* (parsimony, baroqueness), not empirical.

This is the **convergence dual of `Studies/Kalin2018.lean`**: where Kalin's
licensing diverges from a no-licensing account (`¬ AgreesOnCase`), Poole's
Agree-based dependent case *converges* with configurational dependent case.
Both are stated through the same `Assigner` harness (`Syntax/Case/Assigner.lean`).

`agreeAssigner` below is the m1 mechanism for the *low-dependent* (accusative)
pattern: probe stack on a head above both arguments, so the higher caseless DP
unlocks (and stays unmarked) and the lower gets dependent case. We prove it
yields **identical verdicts** to the configurational `dependentAssigner` on
the two-argument configurations [poole-2024] illustrates from Sakha
([baker-vinokurova-2010]'s "accusative" as low dependent case). The harness
compares *outcomes*, so it can only confirm the *extensional* equivalence —
which is exactly Poole's point: the m1/m2 distinction is not adjudicable on
empirical reach. The Sakha ditransitive (UNM–DAT–ACC) needs *two* probe
stacks (high DAT on V + low ACC on T); the single-stack model here covers the
transitive, leaving multi-stack ditransitives as the natural extension.
-/

namespace Poole2024

open Syntax.Case
open Syntax.Case.Licensing (LicensedNP)

/-- The m1 Agree-based dependent-case assigner for the low-dependent
    (accusative) pattern, as a probe stack on a head above both arguments.
    A DP with lexical case keeps it (`inherent`). Among the caseless DPs in
    c-command order: the first **unlocks** the stack and stays unmarked
    (`default`), the second is assigned dependent case (`structural`,
    accusative). A single stack discharges once — so a lone caseless DP, or
    DPs beyond the second, stay unmarked (the ditransitive needs a second
    stack; see the module docstring). -/
def agreeAssigner : Assigner := fun nps label =>
  match nps.find? (·.label == label) with
  | none => none
  | some np =>
    match np.lexicalCase with
    | some c => some ⟨.inherent, some c⟩
    | none =>
      let caseless := (nps.filter (·.lexicalCase.isNone)).map (·.label)
      match caseless.findIdx (· == np.label) with
      | 1 => some ⟨.structural, some .acc⟩   -- second probe: dependent ACC
      | _ => some ⟨.default, some .nom⟩      -- unlocker / lone DP: unmarked
  /- (`findIdx` is total — `np` is caseless and present, so its label is in
     `caseless`; index 0 is the unlocker, ≥2 are post-discharge.) -/

/-! ### m1 = m2 on the whole transitive paradigm

The two mechanisms — a per-DP "is there a caseless c-commander?" check
(`dependentAssigner`, m2) versus an ordered unlock-then-assign probe stack
(`agreeAssigner`, m1) — are not merely equal on sample clauses: they compute
the **same function** on the entire two-argument paradigm, for arbitrary case
content. And their *exact point of divergence* is itself structural. -/

/-- The two-argument clause schema, parameterized by the case content and
    licensing status of the subject and object. -/
private def stim2 (sc oc : Option Case) (sn on : Bool) : List LicensedNP :=
  [ { label := "subj", lexicalCase := sc, needsLicensing := sn }
  , { label := "obj",  lexicalCase := oc, needsLicensing := on } ]

/-- **m1 = m2 on every transitive clause.** For *any* case content (`sc`, `oc`)
    and licensing status of the two arguments, the Agree probe stack and
    configurational dependent case assign the identical verdict — case *and*
    provenance — to each argument. This is [poole-2024]'s extensional
    equivalence as a statement about the two *functions*, not a finite sample:
    on the configurations a single low-dependent stack covers, m2 ≤ m1. -/
theorem agree_eq_dependent_two_args (sc oc : Option Case) (sn on : Bool) :
    ∀ np ∈ stim2 sc oc sn on,
      agreeAssigner (stim2 sc oc sn on) np.label
        = dependentAssigner .accusative (stim2 sc oc sn on) np.label := by
  rintro np hnp
  simp only [stim2, List.mem_cons, List.not_mem_nil, or_false] at hnp
  rcases hnp with rfl | rfl <;> cases sc <;> cases oc <;> rfl

/-- **m1 ≈ m2 through the harness, over the whole paradigm.** A corollary of
    the verdict identity: the two accounts `AgreesOnCase` *and* `AgreesOnSource`
    on every transitive — the convergence dual of `Kalin2018`'s
    `dependentCase_vs_licensing_diverge_on_perfective_object` (`¬ AgreesOnCase`).
    The harness compares outcomes, so this is exactly the extensional
    equivalence [poole-2024] argues for; the residual m1-vs-m2 distinction is
    theoretical (probe-stack baroqueness vs. a primitive dependent-case rule),
    which an outcome comparison cannot — and should not — adjudicate. -/
theorem m1_agrees_m2_two_args (sc oc : Option Case) (sn on : Bool) :
    AgreesOnCase agreeAssigner (dependentAssigner .accusative) (stim2 sc oc sn on) ∧
    AgreesOnSource agreeAssigner (dependentAssigner .accusative) (stim2 sc oc sn on) := by
  refine ⟨fun np hnp => ?_, fun np hnp => ?_⟩ <;>
    rw [agree_eq_dependent_two_args sc oc sn on np hnp]

/-! ### The boundary: one stack, one dependent case

The equivalence is *exact*: it holds for two arguments and fails for three.
Configurational case marks every non-initial caseless DP accusative, whereas a
single probe stack discharges only once. This divergence is the formal
signature of "one stack = one dependent case" — and precisely why [poole-2024]
models the Sakha ditransitive (UNM–DAT–ACC) with a *second* probe stack rather
than one. -/

private def threeCaseless : List LicensedNP :=
  [ { label := "a", lexicalCase := none, needsLicensing := true }
  , { label := "b", lexicalCase := none, needsLicensing := true }
  , { label := "c", lexicalCase := none, needsLicensing := true } ]

/-- On three caseless arguments the two accounts diverge on the **third**: the
    single probe stack leaves it unmarked (`nom`), whereas configurational case
    marks it accusative (it is c-commanded by a caseless DP). -/
theorem agree_diverges_dependent_three_caseless :
    agreeAssigner threeCaseless "c" = some ⟨.default, some .nom⟩ ∧
    dependentAssigner .accusative threeCaseless "c" = some ⟨.structural, some .acc⟩ := by
  exact ⟨by decide, by decide⟩

end Poole2024
