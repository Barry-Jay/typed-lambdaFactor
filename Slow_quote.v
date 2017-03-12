(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*               Typed LambdaFactor Calculus                          *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus  from Project Coq                                  *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                    Slow_quote .v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import List.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import LamSF_Terms.
Require Import LamSF_Substitution_term.
Require Import LamSF_Tactics.
Require Import Compounds. 
Require Import Components. 
Require Import LamSF_reduction.
Require Import LamSF_Normal.
Require Import LamSF_Closed.
Require Import LamSF_Eval.
Require Import type_derivation. 
Require Import type_derivation_rwf. 
Require Import operator_types. 
Require Import subject_reduction.
Require Import Equal.
Require Import Combinators.
Require Import Unstar. 

(* slow quotation separates all applications by introducing a wait. *) 
(* the rank is required to keep track of commuting lambda *) 

Fixpoint slow_quote_rank p M := 
match p with 
| 0 => M 
| S q => 
match M with 
| Ref n => Ref n 
| Op o => Op o 
| Abs M1 => App (App a_op (slow_quote_rank q abs_left)) (slow_quote_rank q (star M1))
| App M1 M2 => App (App a_op (slow_quote_rank q M1)) (slow_quote_rank q M2)
end
end. 

Definition slow_quote M := slow_quote_rank (rank M) M. 



Lemma slow_quote_rank_stable: 
forall p q M, p>= q -> q >= rank M -> slow_quote_rank p M = slow_quote_rank q M. 
Proof. 
induction p; split_all. 
assert(rank M >0) by eapply2 rank_positive. noway. 
gen_case H0 M. 
(* 4 *) 
assert(q = S(pred q)) by omega. 
rewrite H1. auto. 
(* 3 *) 
assert(q = S(pred q)) by omega. 
rewrite H1. auto. 
(* 2 *) 
assert(rank l > 0) by eapply2 rank_positive. 
assert(q = S(pred q)) by omega. 
rewrite H2. simpl.
rewrite (IHp (pred q)). 
rewrite (IHp (pred q)). 
auto.
omega. 
assert(rank(star l) < rank (Abs l)) by eapply2 rank_star. 
simpl in *. 
omega. omega. unfold_op; simpl; omega. 
(* 1 *) 
rewrite (IHp (pred q)). 
rewrite (IHp (pred q)). 
assert(q = S(pred q)) by omega. 
rewrite H1. auto. 
omega.
omega. 
omega. 
omega. 
Qed. 


Lemma slow_quote_abs: 
forall M, slow_quote (Abs M) = App (App a_op (slow_quote abs_left)) (slow_quote (star M)). 
Proof. 
split_all. 
unfold slow_quote, rank, slow_quote_rank; fold slow_quote_rank; fold rank. 
assert(rank M >0) by eapply2 rank_positive. 
assert(abs_rank * rank M = S (pred (abs_rank * rank M))).  
unfold abs_rank.  omega. 
rewrite H0. 
simpl. 
rewrite (slow_quote_rank_stable (pred
              (rank M +
               (rank M +
                (rank M +
                 (rank M +
                  (rank M +
                   (rank M +
                    (rank M +
                     (rank M +
                      (rank M +
                       (rank M +
                        (rank M +
                         (rank M +
                          (rank M +
                           (rank M +
                            (rank M + (rank M + (rank M + (rank M + 0)))))))))))))))))))
 (rank (star M)) (star M)). 
rewrite (slow_quote_rank_stable (pred
              (rank M +
               (rank M +
                (rank M +
                 (rank M +
                  (rank M +
                   (rank M +
                    (rank M +
                     (rank M +
                      (rank M +
                       (rank M +
                        (rank M +
                         (rank M +
                          (rank M +
                           (rank M +
                            (rank M + (rank M + (rank M + (rank M + 0)))))))))))))))))))
 (rank (abs_left)) abs_left). 
auto. 
assert(rank(star M) < rank (Abs M)) by eapply2 rank_star.
simpl in *. omega. 
auto.
assert(rank(star M) < rank (Abs M)) by eapply2 rank_star.
simpl in *. omega. 
auto.
Qed.


Lemma slow_quote_app: 
forall M N, slow_quote (App M N) = App (App a_op (slow_quote M)) (slow_quote N).
Proof. 
split_all. 
unfold slow_quote, rank, slow_quote_rank; fold slow_quote_rank; fold rank. 
assert(rank M >0) by eapply2 rank_positive. 
assert(rank M + rank N = S (pred (rank M + rank N))) by omega. rewrite H0.
rewrite (slow_quote_rank_stable (S (pred (rank M + rank N))) (rank M)); try omega. 
rewrite (slow_quote_rank_stable (S (pred (rank M + rank N))) (rank N)); try omega. 
auto. 
Qed. 



Lemma slow_quote_rank_normal_closed: 
forall p M, p > rank M -> normal M -> maxvar M = 0 -> normal (slow_quote_rank p M).
Proof.
induction p; split_all. 
gen3_case H H0 H1 M. 
unfold_op.  repeat eapply2 nf_app; try (simpl; discriminate). 
eapply2 IHp. 
assert(rank(star l) < rank (Abs l)) by eapply2 rank_star. 
simpl in *. omega. 
repeat eapply2 nf_app; try (simpl; discriminate).
eapply2 IHp. 
assert(rank(star l) < rank (Abs l)) by eapply2 rank_star. 
simpl in *. 
assert(rank(star l) < rank (Abs l)) by eapply2 rank_star. 
simpl in *.  omega. 
inversion H0; eapply2 normal_star. 
rewrite maxvar_star. auto. 
repeat eapply2 nf_app; try (simpl; discriminate).
unfold_op; auto. 
eapply2 IHp. omega. 
inversion H0; auto. max_out. 
eapply2 IHp. omega. 
inversion H0; auto. max_out. 
Qed. 




(* quote *) 

Definition quote_fn := 
Abs (Abs (App (App (App (App (Op Eop) (Ref 0)) (Ref 0)) (Ref 0)) 
              (App (App (Op Gop) (Abs (Abs (App (App a_op (App (Ref 3) (Ref 1))) 
                                                (App (Ref 3) (Ref 0)))))) 
                   (Ref 0))))
.

Definition quote := App (App a_op y_op) quote_fn. 


Theorem quote_type: 
derivation nil quote (Abs (funty (varty 0) (varty 0))).
Proof. 
unfold quote.
eapply derive_app.
instantiate(1:= funty (Abs (funty (varty 0) (varty 0))) (Abs (funty (varty 0) (varty 0)))). 
eapply derive_app.
2: eapply derive_Y.   2: auto. 
instantiate(1:= Abs (funty (varty 0) (varty 0))).  2: wfcs_tac. 
eapply derive_A. auto. wfcs_tac. wfcs_tac. 

unfold quote_fn. 
eapply derive_abs. 
eapply derive_gen1.  simpl. unfold lift; simpl. relocate_lt. 
eapply derive_abs. 
eapply derive_app. 
eapply derive_app. 2: derive_tac. 
eapply derive_app. 2: derive_tac. 
eapply derive_app. 2: derive_tac. 
derive_tac. 
eapply derive_app. 2: derive_tac.
eapply derive_app. 
derive_tac. 
eapply derive_gen1. 
unfold lift; simpl. relocate_lt. simpl. 
eapply derive_abs. 
eapply derive_abs. 
eapply derive_app. 
eapply derive_app. 
(* 3 *) 
derive_tac.
eapply derive_app.
2: derive_tac. 
eapply derive_instance. 
derive_tac. 
red; one_step. instantiate(1:= 0).
replace (funty (funty (varty 0) (Ref 1)) (funty (varty 0) (Ref 1)))
with (subst (funty (Ref 0) (varty 1)) (funty (Ref 0) (Ref 0))) by auto. 
eapply2 instance_rule.  
eapply derive_app. 
eapply derive_instance. 
derive_tac. 
instantiate(1:= Ref 0). 
red; one_step. 
replace(funty (Ref 0) (varty 0)) with (subst(Ref 0) (funty (Ref 0) (Ref 0))) by auto. 
eapply2 instance_rule. 
derive_tac. 
Qed. 


Lemma quote_op : forall o, lamSF_red (App quote (Op o)) (Op o). 
Proof. split_all; unfold quote. eval_lamSF. unfold quote_fn. 
 unfold y_op. eapply2 succ_red. eval_lamSF. unfold lift; simpl. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eval_lamSF. auto. eapply succ_red. eapply2 g_lamSF_red. 
unfold factorable; case o; split_all; auto 10.  eval_lamSF. 
insert_Ref_tac. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 succ_red. auto. auto. 
eval_lamSF. 
 Qed. 




Lemma quote_abs_0: forall M, normal M -> maxvar (Abs M) = 0 -> 
lamSF_red (App (App y_op quote_fn) (Abs M)) (App (App a_op (App (App y_op quote_fn) abs_left))
                                                   (App (App y_op quote_fn) (star M)))
.
Proof. 
split_all. 
unfold y_op, quote_fn; eapply2 succ_red. eval_lamSF.   
unfold lift; rewrite lift_rec_null. 
assert(factorable (Abs M)). eapply2 programs_are_factorable. split_all. 
inversion H1; split_all; subst;split_all. 
simpl in *. gen_case H2 (status M); gen_case H2 n. 
eapply transitive_red. eapply preserves_app_lamSF_red.  eapply preserves_app_lamSF_red. 
 eapply preserves_app_lamSF_red. eapply succ_red. eapply2 e_compound_lamSF_red. 
eapply2 factorable_abstractions_are_compounds. auto. auto. auto. 
eapply succ_red. eapply2 g_lamSF_red. eval_lamSF. simpl. insert_Ref_tac. 
eval_lamSF. eval_lamSF. auto. 
eapply2 preserves_app_lamSF_red. eapply2 preserves_app_lamSF_red.  eval_lamSF.   eval_lamSF. 
Qed. 



Lemma quote_compound_0: 
forall M N, program (App M N) -> 
lamSF_red (App (App y_op quote_fn) (App M N))  (App (App a_op (App (App y_op quote_fn) M)) (App (App y_op quote_fn)  N)).
Proof. 
split_all. unfold y_op, quote_fn; eapply2 succ_red. eval_lamSF. eval_lamSF. 
unfold lift; rewrite lift_rec_null. 
assert(factorable (App M N)). eapply2 programs_are_factorable. 
eapply transitive_red. eapply preserves_app_lamSF_red.  eapply preserves_app_lamSF_red. 
 eapply preserves_app_lamSF_red. eapply succ_red. eapply2 e_compound_lamSF_red. 
eapply2 factorable_applications_are_compounds. auto. auto. auto. 
eapply succ_red. eapply2 g_lamSF_red. eval_lamSF. simpl. insert_Ref_tac. 
rewrite subst_rec_closed; try(split_all; omega). 
rewrite lift_rec_closed; try(split_all; omega). 
eval_lamSF. eval_lamSF.  
eapply2 preserves_app_lamSF_red.  eapply2 preserves_app_lamSF_red. eval_lamSF. eval_lamSF.  
inversion H. simpl in *. max_out. inversion H. simpl in *. max_out. 
rewrite lift_rec_closed; try(split_all; omega).  
Qed. 




Lemma quote_slow_quote_0:  
forall M, program M -> lamSF_red (App (App y_op quote_fn) M) (slow_quote M). 
Proof.
rank_tac. 
unfold program; intros rnk prog; split_all.  assert(program M) by split_all. 
induction H; split_all. 
(* 4 *)
simpl in *; noway. 
(* 3 *) 
unfold slow_quote; split_all. 
unfold y_op, quote_fn. eapply2 succ_red. eval_lamSF. 
unfold lift; rewrite lift_rec_null. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 succ_red. auto. 
eapply succ_red. eapply2 g_lamSF_red. 
unfold factorable; case o; split_all; auto 10. 
eval_lamSF. eval_lamSF. 
(* 2 *) 
eapply transitive_red. eapply2 quote_abs_0. 
rewrite slow_quote_abs. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHp. 
unfold abs_left; simpl in *.  assert(rank M > 0) by eapply2 rank_positive. omega. 
unfold_op; unfold program; auto. 
eapply2 IHp. assert (rank (star M) < rank (Abs M)) by eapply2 rank_star. omega. 
unfold program; split_all. eapply2 normal_star. rewrite maxvar_star. simpl in *; omega. 
(* 1 *) 
eapply transitive_red. eapply2 quote_compound_0. 
rewrite slow_quote_app. 
simpl in *. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHnormal1.  
omega.  unfold program; split_all. max_out. 
unfold program; split_all. max_out.
eapply2 IHnormal2.  
omega.  unfold program; split_all. max_out. 
unfold program; split_all. max_out.
Qed. 


Theorem quote_is_definable : 
forall M, program M -> lamSF_red (App quote M) (slow_quote M). 
Proof. 
split_all. unfold quote. eapply transitive_red. eval_lamSF. eapply2 quote_slow_quote_0.
Qed. 



Lemma quote_op0 : forall o, lamSF_red (App (App (App a_op y_op) quote_fn) (Op o)) (Op o). 
Proof. 
split_all. eval_lamSF. unfold quote_fn, y_op. eapply2 succ_red. repeat eval_lamSF. 
unfold lift; rewrite lift_rec_null. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 succ_red. auto. eapply succ_red. eapply2 g_lamSF_red. 
unfold factorable; case o; split_all; auto 10.  eval_lamSF. eval_lamSF. 
 Qed. 


