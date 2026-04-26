import Linglib.Theories.Syntax.Minimalism.Basic
import Linglib.Theories.Syntax.Minimalism.SmallClause
import Linglib.Theories.Syntax.Minimalism.Formal.HeadMovement.Basic

/-!
# Triadic constructions and Dative Shift — den Dikken's SC-in-SC analysis
@cite{dendikken-1995} @cite{baker-1988} @cite{larson-1988}

@cite{dendikken-1995} chapters 3-4 extend the SC analysis from particle
verb constructions (book ch. 2) to **triadic** constructions and
Dative Shift. The central thesis: ditransitives instantiate a SC-in-SC
template with an *abstract* copular verb BE between the matrix V and
a lower SC, and an empty preposition that either remains in situ
(prepositional dative frame) or undergoes Predicate Inversion + LF
incorporation into BE (double object frame). Possessive HAVE is the
suppletive surface result of this BE+TO incorporation (book §3.8).

## D-structure template (book p. 132 ex. 52a; p. 271 ex. 4)

    [VP V [SC1 Spec_θ' [VP "BE" [SC2 Spec_θ' [XP X [SC3 NP_Th [PP P NP_Go]]]]]]]

- `V` = matrix triadic verb (e.g. *send*, *give*)
- `X` = lexical particle if any (e.g. *off* in *send a package off to Bob*),
  empty otherwise (book §3.11 covers the particle-less case as a
  special case of the same template)
- `SC3`'s predicate is the dative PP `[PP P NP_Go]`
- Both `Spec_θ'` positions are empty θ'-positions

## DOC S-structure (book p. 132 ex. 52b)

    [VP V [SC1 Spec_θ' [VP "BE"+[P ∅]j [SC2 [PP_i tj NP_Go] [XP X [SC3 NP_Th t_i]]]]]]

Two operations relate (52a) → (52b):

1. **Predicate Inversion** (A-movement): the dative PP raises from the
   predicate position of SC3 to SpecSC2 (and onward to SpecSC1 per
   book fn. 20, omitted from the diagram). This is the same Predicate
   Inversion mechanism applied to applicatives + transitive causatives
   in book ch. 5.

2. **P-incorporation**: the empty head P_∅ incorporates into BE,
   producing the complex BE+P_∅. Per book §3.10.1, the incorporation
   appeals to @cite{baker-1988}'s Government Transparency Corollary
   for Case licensing of the embedded NP — consistent with the
   broader treatment of incorporation as LF reanalysis throughout the
   book (cf. ch. 2.4.3 on V-Prt reanalysis as LF, not overt). Same
   convention as the PVC analysis. UNVERIFIED: specific footnote
   number not pinned to text.

## §3.8: HAVE = BE + incorporated dative P

Cross-linguistic evidence (Russian *U Ivana krasivye glaza* "by Ivan
pretty eyes" ≈ English *Ivan has pretty eyes*; French *à*-construction
↔ *avoir* construction; Latin *mihi est* ↔ *habeo*) supports treating
possessive HAVE as the surface result of P-incorporation into an
abstract copula. The DOC analysis applies this decomposition: the
abstract BE in (52a) becomes BE+P_∅ at S-structure (52b), the
syntactic source of HAVE.

## §3.10: Motivation for movement

In the prepositional dative the Theme NP undergoes Case-driven
movement to receive Case from V. In the DOC, by contrast, the
*predicate* moves: the empty-headed dative PP raises to SpecSC2,
allowing the Theme NP to receive Case in situ via BE+P_∅ (which
inherits Case-assigning capability from the incorporated P, per
@cite{baker-1988}'s GTC). The Goal NP receives Case via further
movement of the empty-headed PP to SpecSC1.

## Cross-references

- Book §3.2 contrasts with @cite{larson-1988}'s VP-shell analysis,
  which derives the DOC from the prepositional dative via a
  PASSIVE-style operation. den Dikken argues Larson's analysis fails
  for triadic VPCs (book §3.2 ex. 4-6) because the particle's
  position cannot be accommodated in Larson's flat VP shell.
  See `Phenomena/ArgumentStructure/Studies/Larson1988.lean` for the
  predecessor formalization.
- @cite{baker-1988} is the source of the Government Transparency
  Corollary used to license Case assignment after P-incorporation.

## Scope

This file formalises the structural template (52a)/(52b) for triadic
constructions with and without a lexical particle, plus the BE+P
decomposition of HAVE (§3.8). The book's full chapter 3-4 treatment
also covers: empty dative P licensing across languages (§3.10.2),
binding asymmetries from Predicate Inversion (ch. 4.6), Kichaga / German
double-object peculiarities (ch. 4.5-4.6), and Romance causativised
verbs (ch. 5.3.7). Those remain TODO; encoding them faithfully needs
LF-reanalysis substrate that is not yet in linglib (see the SC/particles
architectural target memo).

-/

namespace Phenomena.ArgumentStructure.Studies.Dendikken1995

open Minimalism

/-! ## §1. Lexical items -/

def V_send : SyntacticObject := mkLeafPhon .V [.D, .D, .P] "send" 400
def V_give : SyntacticObject := mkLeafPhon .V [.D, .D, .P] "give" 401

/-- The abstract copular verb BE. Per book §3.7 / §3.8: an empty verbal
    head between matrix V and the lower SC, providing the incorporation
    site for the dative P. Not overtly realised in DOC (because the
    incorporated complex BE+P_∅ surfaces as the suppletive HAVE / as a
    null head in DOCs without an overt possessor). -/
def BE_abstract : SyntacticObject := mkLeafPhon .V [] "BE" 402

/-- Empty (zero-headed) dative preposition. Per book §3.10.2: licensed
    in English DOCs by incorporation into BE; in German/Icelandic by
    overt dative Case morphology (book §3.10.2 ex. 54). -/
def P_empty : SyntacticObject := mkLeafPhon .P [.D] "∅_to" 403

/-- The overt dative preposition *to*. -/
def P_to : SyntacticObject := mkLeafPhon .P [.D] "to" 404

/-- The lexical particle position X. Filled by an overt particle in
    triadic VPCs (e.g. *off* in *send a package off to Bob*); empty in
    plain triadic verbs like *give*. -/
def Prt_off : SyntacticObject := mkLeafPhon .P [] "off" 405
def X_empty : SyntacticObject := mkLeafPhon .V [] "∅_X" 406

/-- The empty θ'-Spec position used in SC1 and SC2 of the template. -/
def Spec_theta_prime : SyntacticObject := mkLeafPhon .D [] "θ'" 407

/-! ## §2. Theme and Goal arguments

Two example pairs: a particle case (*send a package off to Bob*) and
a particle-less case (*give the book to Mary*). -/

def DP_package : SyntacticObject := mkLeafPhon .D [] "a package" 410
def DP_bob     : SyntacticObject := mkLeafPhon .D [] "Bob" 411
def DP_book    : SyntacticObject := mkLeafPhon .D [] "the book" 412
def DP_mary    : SyntacticObject := mkLeafPhon .D [] "Mary" 413

/-! ## §3. The triadic D-structure (book ex. 52a)

For "send a package off to Bob": -/

/-- The PP predicate of SC3: `[PP to Bob]`. -/
def pp_to_bob : SyntacticObject := merge P_to DP_bob

/-- SC3 in (52a): `[SC3 a-package [PP to Bob]]` — Theme NP + dative PP. -/
def sc3_send : SyntacticObject := merge DP_package pp_to_bob

/-- XP in (52a): `[XP off SC3]` — particle X with SC3 as complement. -/
def xp_send : SyntacticObject := merge Prt_off sc3_send

/-- SC2 in (52a): `[SC2 Spec_θ' XP]`. -/
def sc2_send : SyntacticObject := merge Spec_theta_prime xp_send

/-- The lower VP of (52a): `[VP BE SC2]`. -/
def vp_BE_send : SyntacticObject := merge BE_abstract sc2_send

/-- SC1 in (52a): `[SC1 Spec_θ' VP_BE]`. -/
def sc1_send : SyntacticObject := merge Spec_theta_prime vp_BE_send

/-- The triadic D-structure for *send a package off to Bob*. -/
def triadicDStructure_send : SyntacticObject := merge V_send sc1_send

/-! ## §4. The triadic D-structure for plain ditransitives (no particle)

Per book §3.11, particle-less triadic verbs share the same template
with `X = ∅`. For "give the book to Mary": -/

def pp_to_mary : SyntacticObject := merge P_to DP_mary
def sc3_give   : SyntacticObject := merge DP_book pp_to_mary
def xp_give    : SyntacticObject := merge X_empty sc3_give
def sc2_give   : SyntacticObject := merge Spec_theta_prime xp_give
def vp_BE_give : SyntacticObject := merge BE_abstract sc2_give
def sc1_give   : SyntacticObject := merge Spec_theta_prime vp_BE_give

/-- The triadic D-structure for *give the book to Mary*. -/
def triadicDStructure_give : SyntacticObject := merge V_give sc1_give

/-! ## §5. The DOC S-structure (book ex. 52b)

After Predicate Inversion (PP raises to SpecSC2) + LF P-incorporation
(empty P incorporates into BE forming BE+P_∅, the source of HAVE).

For *send Bob a package off* (the DOC counterpart): -/

/-- The PP `[P_∅ Bob]` after Predicate Inversion (now at SpecSC2). -/
def pp_empty_bob : SyntacticObject := merge P_empty DP_bob

/-- BE+P_∅ — the abstract complex head after LF P-incorporation;
    the syntactic source of HAVE per book §3.8. Built via
    `formAbstractIncorporation`, the LF-cosuperscripting variant of
    head incorporation (consistent with den Dikken's general treatment
    of incorporation as LF, see ch. 2.4.3 on V-Prt reanalysis). The
    named alias makes the analytical commitment (LF, not PF) explicit
    at the use site. -/
def BE_plus_P : LIToken :=
  formAbstractIncorporation
    ⟨LexicalItem.simple .V [] "BE", 402⟩
    ⟨LexicalItem.simple .P [.D] "∅_to", 403⟩

/-- The complex BE+P head as a SyntacticObject (the surface HAVE). -/
def HAVE_so : SyntacticObject := .leaf BE_plus_P

/-- SC3 in (52b): the Theme NP and the trace `t_i` of the moved PP.
    We represent the trace by P_empty alone (head, no complement),
    since linglib has no first-class trace primitive. -/
def sc3_send_post : SyntacticObject := merge DP_package P_empty

/-- SC2 in (52b): `[SC2 PP_i [XP off SC3]]` — PP raised to Spec. -/
def sc2_send_post : SyntacticObject :=
  merge pp_empty_bob (merge Prt_off sc3_send_post)

/-- The lower VP in (52b): `[VP BE+P_∅ SC2]`. -/
def vp_HAVE_send : SyntacticObject := merge HAVE_so sc2_send_post

/-- SC1 in (52b): `[SC1 Spec_θ' VP_HAVE]`. -/
def sc1_send_post : SyntacticObject := merge Spec_theta_prime vp_HAVE_send

/-- The triadic DOC S-structure for *send Bob a package off*. -/
def triadicSStructure_DOC_send : SyntacticObject :=
  merge V_send sc1_send_post

/-! ## §6. The PD S-structure (no movement, no incorporation)

The prepositional dative S-structure differs from D-structure only
by Case-driven movement of the Theme NP (which we abstract over here);
the SC-in-SC skeleton is unchanged. -/

/-- The triadic PD S-structure for *send a package off to Bob*. -/
def triadicSStructure_PD_send : SyntacticObject := triadicDStructure_send

/-! ## §7. Structural facts -/

/-- D-structure for *send a package off to Bob* has the deep
    SC-in-SC-in-SC shape predicted by (52a). -/
theorem triadicDStructure_send_shape :
    triadicDStructure_send.shape =
      .node .leaf
        (.node .leaf
          (.node .leaf
            (.node .leaf
              (.node .leaf
                (.node .leaf
                  (.node .leaf .leaf)))))) := rfl

/-- The DOC S-structure has a *different* shape from D-structure —
    Predicate Inversion is structure-changing. -/
theorem inversion_changes_shape :
    structurallyIsomorphic triadicDStructure_send triadicSStructure_DOC_send
      = false := by decide

/-- The plain *give the book to Mary* triadic D-structure is
    structurally isomorphic to the *send-off* D-structure modulo
    lexical content (same template). -/
theorem give_send_d_structure_isomorphic :
    structurallyIsomorphic triadicDStructure_give triadicDStructure_send
      = true := by decide

/-! ## §7b. IsSmallClause witnesses for the SC-in-SC backbone

Each of the three SCs (SC1, SC2, SC3) in the triadic D-structure
satisfies the `IsSmallClause` companion predicate (`SmallClause.lean`).
This is the unifying structural claim — the SC-in-SC architecture is
literally three nested instantiations of the same predicate. -/

/-- SC3: theme NP + dative PP-predicate (head category P). -/
theorem sc3_send_isSmallClause : IsSmallClause sc3_send := by decide
theorem sc3_give_isSmallClause : IsSmallClause sc3_give := by decide

/-- SC2: empty θ'-Spec + XP-predicate (head category P, since particle
    or empty X-head defaults to P/V). -/
theorem sc2_send_isSmallClause : IsSmallClause sc2_send := by decide
theorem sc2_give_isSmallClause : IsSmallClause sc2_give := by decide

/-- SC1: empty θ'-Spec + VP-predicate headed by abstract BE
    (head category V). -/
theorem sc1_send_isSmallClause : IsSmallClause sc1_send := by decide
theorem sc1_give_isSmallClause : IsSmallClause sc1_give := by decide

/-- The post-Predicate-Inversion SC2 (with the raised PP at Spec
    and the empty-P trace inside SC3) still satisfies `IsSmallClause`
    — Predicate Inversion is structure-preserving in the SC sense. -/
theorem sc2_send_post_isSmallClause : IsSmallClause sc2_send_post := by decide

/-! ## §8. HAVE = BE + TO_∅ decomposition (book §3.8) -/

/-- The post-incorporation complex is genuinely complex (length > 1). -/
theorem HAVE_is_complex : BE_plus_P.item.isComplex = true := by decide

/-- HAVE retains V as its outer category — the matrix projection is
    verbal, with the incorporated P providing the inner feature.
    Proved structurally via `complex_li_outer_projects` rather than
    `decide`, which gets stuck on the proof obligation inside
    `LexicalItem.combine`. The lemma applies regardless of overt-vs-LF
    interpretation since both `formAbstractIncorporation` and
    `formOvertIncorporation` reduce to `formComplexLI`. -/
theorem HAVE_outer_is_V : BE_plus_P.item.outerCat = .V := by
  unfold BE_plus_P formAbstractIncorporation
  rw [complex_li_outer_projects]
  rfl

/-! ## §9. Connection to predecessor analysis (book §3.2)

Book §3.2 argues that @cite{larson-1988}'s VP-shell analysis fails
for triadic verb-particle constructions of the form *send a package
off to Bob*: Larson's flat VP shell cannot accommodate the particle
in a position consistent with both the binding asymmetries he
derives and the constituency of the post-particle PP. den Dikken's
SC-in-SC structure has X as a syntactic head taking SC3 as
complement, naturally hosting the particle in this position.

The contrast is *between paper analyses*; the formalisation of
Larson's predictions lives in `Studies/Larson1988.lean`. The
contrast is anchored to den Dikken (the chronologically-later,
critiquing paper); per CLAUDE.md the comparison is hosted here.
The structural shape claim is captured by `triadicDStructure_send_shape`
above (the deep right-branching SC-in-SC pattern with XP as a
distinct constituent layer is what Larson's flat shell lacks). -/

/-! ## §10. Predicate Inversion as a tree-rewriting operation

Up to this point, the D-structure (`sc1_send`) and DOC S-structure
(`sc1_send_post`) have been *independently stipulated*. Book §3.10
crucially relies on Predicate Inversion as the *operation* that
relates them: the empty-headed dative PP raises from SC3-pred to
SpecSC2, and the empty P incorporates into BE forming HAVE.

Here we make the operation explicit. The DOC derivation starts from
a D-structure variant in which the dative PP already has the empty P
(book §3.10.2 ex. 54: in English, lacking dative Case morphology,
the empty P is licensed only by incorporation, which forces the DOC
derivation; the PD frame has overt `to` instead). -/

/-- DOC D-structure variant of `sc1_send` with the empty dative P
    (rather than overt `to`). This is the input to Predicate Inversion. -/
def sc3_send_doc_dstr : SyntacticObject :=
  merge DP_package (merge P_empty DP_bob)
def xp_send_doc_dstr : SyntacticObject :=
  merge Prt_off sc3_send_doc_dstr
def sc2_send_doc_dstr : SyntacticObject :=
  merge Spec_theta_prime xp_send_doc_dstr
def vp_BE_send_doc_dstr : SyntacticObject :=
  merge BE_abstract sc2_send_doc_dstr
/-- The DOC D-structure (with empty P, before Predicate Inversion). -/
def sc1_send_doc_dstr : SyntacticObject :=
  merge Spec_theta_prime vp_BE_send_doc_dstr

/-- **Predicate Inversion** as a partial tree-rewriting operation on
    the SC1-shape used by triadic D-structures.

    Pattern (D-structure):
        `[SC1 Spec₁ [VP V [SC2 Spec₂ [XP X [SC3 NP [PP P NP_obj]]]]]]`

    Result (S-structure after PI + P-incorporation):
        `[SC1 Spec₁ [VP V+P [SC2 [PP P NP_obj] [XP X [SC3 NP P]]]]]`

    The empty-P trace inside SC3 is represented as `P` reused in the
    SC3 right-child slot — same encoding as `sc3_send_post`. The
    incorporation step (V → V+P) uses `formAbstractIncorporation`
    to honour book §3.10.1's LF-reanalysis attribution.

    On non-matching shapes, returns the input unchanged (identity). -/
def predicateInversion : SyntacticObject → SyntacticObject
  | .node spec1 (.node (.leaf v_tok)
      (.node _spec2 (.node x (.node np (.node (.leaf p_tok) np_obj))))) =>
        let v_plus_p := formAbstractIncorporation v_tok p_tok
        let pp_moved : SyntacticObject := merge (.leaf p_tok) np_obj
        let new_sc3 : SyntacticObject := merge np (.leaf p_tok)
        let new_xp : SyntacticObject := merge x new_sc3
        let new_sc2 : SyntacticObject := merge pp_moved new_xp
        let new_vp : SyntacticObject := merge (.leaf v_plus_p) new_sc2
        merge spec1 new_vp
  | so => so

/-- **The derivation theorem**: applying `predicateInversion` to the
    DOC D-structure yields exactly the (previously stipulated) DOC
    S-structure `sc1_send_post`. The S-structure is now *derived*,
    not just asserted. -/
theorem predicateInversion_sc1_send_doc_dstr_eq_sc1_send_post :
    predicateInversion sc1_send_doc_dstr = sc1_send_post := rfl

/-- Predicate Inversion changes the tree shape (it raises an embedded
    PP to the specifier of the SC two levels up). The PI-derived
    output is *not* structurally isomorphic to its input. -/
theorem predicateInversion_changes_shape :
    structurallyIsomorphic (predicateInversion sc1_send_doc_dstr) sc1_send_doc_dstr
      = false := by decide

/-- **Structure preservation**: Predicate Inversion preserves
    `IsSmallClause` of the input SC1. The post-inversion SC1 still
    has the SC structure `[Spec_θ' [VP_HAVE …]]` — V at the head of
    its predicate, hence head category `.V`, hence `IsSmallClause`. -/
theorem predicateInversion_preserves_IsSmallClause_sc1 :
    IsSmallClause (predicateInversion sc1_send_doc_dstr) := by decide

/-- The pre-PI DOC D-structure also satisfies `IsSmallClause` —
    the SC analysis is invariant under whether overt `to` or empty
    `P_∅` heads the SC3-predicate PP. -/
theorem sc1_send_doc_dstr_isSmallClause :
    IsSmallClause sc1_send_doc_dstr := by decide

end Phenomena.ArgumentStructure.Studies.Dendikken1995
