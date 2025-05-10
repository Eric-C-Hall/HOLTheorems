open HolKernel Parse boolLib bossLib;

open useful_tacticsLib;
open dep_rewrite;
open fsgraphTheory;
open finite_mapTheory;
open pred_setTheory;

val _ = new_theory "partite_ea";

(* -------------------------------------------------------------------------- *)
(* Gen partite: provides a specific partition which shows that a given graph  *)
(* is r-partite.                                                              *)
(*                                                                            *)
(* We represent a partition by a function which colours the nodes on the      *)
(* graph into at most r colours such that no two nodes of the same colour     *)
(* have an edge between them.                                                 *)
(*                                                                            *)
(* The previous verison of this definition required that every component of   *)
(* the partition was nonempty. This version doesn't have this requirement.    *)
(* It is easier to use the new version to prove things becauase you can avoid *)
(* performing additional work in the special case where there are empty sets  *)
(* in the partition.                                                          *)
(*                                                                            *)
(* It is no longer sensible to use a "set of sets" definition for the         *)
(* partition when empty components are allowed, because there may be multiple *)
(* empty components in the partition, and a set doesn't allow for duplicate   *)
(* components. Therefore, we changed the representation of a partition: we    *)
(* decided to represent it by a colouring function, rather than one of the    *)
(* other options.                                                             *)
(*                                                                            *)
(* See https://github.com/HOL-Theorem-Prover/HOL/issues/1465 for a detailed   *)
(* discussion of this change (this page has been archived on archive.org,     *)
(* although archive.org did not successfully archive the entire page).        *)
(* -------------------------------------------------------------------------- *)
Definition gen_partite_ea_def :
  gen_partite_ea r (g : fsgraph) (f : unit + num |-> num) <=>
  (FDOM f = nodes g) ∧
  (∀m. m ∈ nodes g ⇒ f ' m < r) ∧
  (∀e. e ∈ fsgedges g ⇒ CARD (IMAGE ($' f) e) = 2)
End

(* -------------------------------------------------------------------------- *)
(* Gen bipartite: the special case of partite for r = 2                       *)
(*                                                                            *)
(* Using an overload instead of a definition minimizes the number of          *)
(* additional symbols defined and simplifies the process of proof: we only    *)
(* need to prove a theorem for gen_partite, and it will automatically also be *)
(* proven for gen_bipartite.                                                  *)
(* -------------------------------------------------------------------------- *)
Overload gen_bipartite_ea = “gen_partite_ea 2”;

(* ------------------------------------------------------------------------
   Messy workaround: using “2” instead of (mk_numeral ...) would cause the
   following comment to be automatically indented incorrectly.

   When this issue is fixed, remove the "open numSyntax" and replace
   (mk_numeral $ Arbnum.fromString "2") with “2”
   ------------------------------------------------------------------------ *)
open numSyntax;
Theorem gen_bipartite_ea_def = SPEC (mk_numeral $ Arbnum.fromString "2") gen_partite_ea_def;

(* -------------------------------------------------------------------------- *)
(* Partite: when we only care that a partition exists, but we don't care what *)
(* the specific partition is                                                  *)
(* -------------------------------------------------------------------------- *)
Overload partite_ea = “λr g. ∃f. gen_partite_ea r g f”;

(* -------------------------------------------------------------------------- *)
(* Bipartite: when we don't care what specific partition we use, and we are   *)
(* working with a graph that can be split into two components                 *)
(* -------------------------------------------------------------------------- *)
Overload bipartite_ea = “λg. ∃f. gen_partite_ea 2 g f”;*)

(* -------------------------------------------------------------------------- *)
(* Any function shows that the empty graph is r-partite for any r             *)
(* -------------------------------------------------------------------------- *)
Theorem gen_partite_ea_empty[simp]:
  ∀r f.
    gen_partite_ea r emptyG f ⇔ f = FEMPTY
Proof
  rpt strip_tac
  >> gvs[gen_partite_ea_def, FDOM_EQ_EMPTY]
QED

(* -------------------------------------------------------------------------- *)
(* Adding a node to a graph, without adding any corresponding edges, and      *)
(* updating the partite function to include this node maintains partiteness   *)
(* -------------------------------------------------------------------------- *)
Theorem gen_partite_fsgAddNode:
  ∀r g f x z.
    gen_partite_ea r g f ∧
    x ∉ nodes g ∧
    z < r ⇒
    gen_partite_ea r (fsgAddNode x g) (f |+ (x, z))
Proof
  rw[]
  >> gvs[gen_partite_ea_def]
  >> rw[]
  >- gvs[]
  >- (DEP_PURE_ONCE_REWRITE_TAC[NOT_EQ_FAPPLY]
      >> gvs[]
      >> CCONTR_TAC
      >> gvs[]
     )
  >- (first_x_assum drule
      >> rw[]
      >> ‘FINITE e’ by gvs[fsgedges_def]
      >> sg ‘CARD e = 2’
      >- (‘2 ≤ CARD e’ by metis_tac[CARD_IMAGE_LE]
          >> sg ‘CARD e ≤ 2’ >- (gvs[fsgedges_def] >> Cases_on ‘m = n’ >> gvs[])
          >> gvs[])
      >> Cases_on ‘e’ >> gvs[]
      >> Cases_on ‘t’ >> gvs[]
      >> qmatch_goalsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
      >> qmatch_asmsub_abbrev_tac ‘if b then _ else _’
      >> Cases_on ‘b’ >> gvs[]
      (* Doing Case_on ‘x = x'’ and Cases_on ‘x = x''’ and then applying
         gvs[NOT_EQ_FAPPLY, FAPPLY_FUPDATE] automatically solves for the
         cases where we don't have x = x' or x = x''.
.
         We then use "without loss of generality" to show that x = x' is
         an equivalent proof state to x = x'', as they are symmetric*)
      >> Q.SUBGOAL_THEN ‘x = x' \/ x = x''’ assume_tac
      >- (Cases_on ‘x = x'’ >> Cases_on ‘x = x''’
          >> gvs[NOT_EQ_FAPPLY, FAPPLY_FUPDATE])
      >> wlog_tac ‘x = x'’ [‘x'’, ‘x''’]
      >- (gvs[]
            >> pop_assum $ qspec_then ‘x'’ assume_tac
            >> gvs[]
          >> ‘{x;x'} = {x';x}’ by (gvs[EXTENSION] >> rpt strip_tac
                                   >> EQ_TAC >> rw[])
          >> metis_tac[])
      >> gvs[]
      >- (drule alledges_valid
          >> rw[]
          >> gvs[]
          >> Cases_on ‘x = a’ >> gvs[]
          >> Cases_on ‘x = b’ >> gvs[]
          >> ‘x ∈ {x; x''} ∧ x ∉ {a; b}’ by gvs[]
          >> metis_tac[])
     )
QED


(* -------------------------------------------------------------------------- *)
(* If the edges being added aren't between nodes of the same type, then       *)
(* adding edges to a graph doesn't affect partiteness.                        *)
(* -------------------------------------------------------------------------- *)
(*Theorem gen_partite_ea_fg_add_edges_for_function_node0:
  ∀r (vs : (unit + num) list) g f.
    f ' (INR (CARD (nodes g) - 1)) = 1 ∧
    (∀x. MEM x vs ⇒ x ∈ nodes g ∧ f ' x = 0) ⇒
    (gen_partite_ea r (fg_add_edges_for_function_node0 vs g) f ⇔
       gen_partite_ea r g f)
Proof
  rpt strip_tac
  >> EQ_TAC >> rw[]
  >- (gvs[fg_add_edges_for_function_node0_def]
      >> simp[gen_partite_ea_def]
      >> rw[]
      >- gvs[gen_partite_ea_def]
      >> gvs[gen_partite_ea_def]
      >> first_x_assum irule
      >> gvs[fsgedges_fsgAddEdges]
     )
  >- (gvs[gen_partite_ea_def]
      >> rw[]
      >> Cases_on ‘e ∈ fsgedges g’ >> gvs[]
      >> Cases_on ‘e ⊆ nodes g ∧ CARD e = 2’
      >- (gvs[fsgedges_fg_add_edges_for_function_node0]
          >> qmatch_asmsub_abbrev_tac ‘if b then 1 else 2’
          >> Cases_on ‘b’ >> gvs[]
          >> qmatch_goalsub_abbrev_tac ‘if b then 1 else 2’
          >> Cases_on ‘b’ >> gvs[]
          >> first_assum drule >> rpt strip_tac
         )
      >- (gvs[] (* Perhaps this could be proven more efficiently by moving
                   this working upwards *)
          >> gvs[fg_add_edges_for_function_node0_def]
          >> gvs[fsgedges_fsgAddEdges]
         )
     )
QED*)

val _ = export_theory();
