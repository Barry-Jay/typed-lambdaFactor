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
(*                      Unstar.v                                      *)
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
Require Import Components.
Require Import Compounds.
Require Import LamSF_reduction.
Require Import LamSF_Normal.
Require Import LamSF_Closed.
Require Import LamSF_Eval.
Require Import type_derivation.
Require Import type_derivation_resi.
Require Import operator_types. 
Require Import subject_reduction. 
Require Import Equal.


Definition id_type := Abs (funty (Ref 0) (Ref 0)). 

Definition ref := Ref. 
Definition ap := App . 
Definition abs := Abs. 
Definition abs_S := (abs (abs (abs (ap (ap (ref 2) (ref 0)) (ap (ref 1) (ref 0)))))) . 
Definition abs_K := (abs (abs (ref 1))).
Definition abs_I := (abs (ref 0)).
Definition abs_KI := (abs (abs (ref 0))).



Lemma abs_S_type : derivation nil abs_S (opty Sop).
Proof. 
unfold abs_S; unfold_opty; unfold abs, ap. 
repeat eapply derive_gen1.  simpl. 
repeat eapply derive_abs. 
repeat eapply derive_app; var_tac. 
Qed. 

Lemma abs_K_type : derivation nil abs_K (opty Kop).
Proof. 
unfold abs_K; unfold_opty; unfold abs, ap. 
repeat eapply derive_gen1.  simpl. 
repeat eapply derive_abs. 
repeat eapply derive_app; var_tac. 
Qed. 





Definition abs_A u := Abs (Abs (App u (App (Ref 1) (Ref 0)))).

Lemma abs_A_type : derivation (cons id_type nil) (abs_A (Ref 2)) (opty Aop). 
Proof. 
unfold abs_A; unfold_opty. 
repeat eapply derive_gen1. 
unfold lift; simpl; repeat rewrite lift_rec_closed; try (split_all; omega). 
unfold relocate; simpl. 
repeat eapply derive_abs. 
repeat eapply derive_app. 
eapply derive_instance. 
derive_tac. 
eapply succ_red. eapply instance_rule. 
2: wfcs_tac. instantiate(1:= varty 1). 
wfcs_tac. 
unfold subst; simpl. insert_Ref_out. 
repeat rewrite lift_rec_null. eapply2 zero_red. derive_tac. derive_tac. 
Qed. 


(* unstar *) 

Definition unstar_fn := 
Abs (App g_op 
(App (App (Op DAop) (abs_A (Ref 2)))
(App (App (Op DKop) abs_K) 
(App g_op (App (App (Op DSop) abs_S) i_op)))))
.

Definition unstar := App (App a_op y_op) unstar_fn. 



(* 
Definition unstar_fn := 
Abs (Abs (App (App (App is_abs (Ref 0)) 
                   (App (Abs (Abs (App (Ref 3) (App (Ref 1) (Ref 0))))) (Ref 0)))
              (App (App (App f_op (Ref 0)) (Ref 0)) 
                   (Abs (Abs (App (App (App f_op (Ref 1))
                                       (App (App d_op (Ref 1)) (Ref 0)))
                                   (Abs (Abs (App (App (App d_op (Ref 1)) 
                                                       (App (Ref 5) (Ref 0)))
                                                  (App (Ref 5) (Ref 2)))))))))))
.

Definition unstar := App (App a_op y_op) unstar_fn. 
*) 

Proposition unstar_type: derivation nil unstar (Abs (funty (varty 0) (varty 0))).
Proof. 
unfold unstar. 
eapply derive_app. 
eapply derive_app. 
eapply derive_A. 
wfcs_tac. 
2: wfcs_tac. 
2: eapply derive_Y. 
wfcs_tac. 
wfcs_tac. 
wfcs_tac. 
unfold unstar_fn.
eapply derive_abs. 
eapply derive_gen1. 
unfold lift; simpl. relocate_lt. 
eapply derive_app.
eapply derive_G. 
wfcs_tac. 
wfcs_tac. 
wfcs_tac. 
eapply derive_gen1. 
unfold lift; simpl. relocate_lt. simpl.  
eapply derive_app.
eapply derive_app.
eapply derive_DA. 
wfcs_tac. 
wfcs_tac. 
eapply abs_A_type. 
eapply derive_app.
eapply derive_app.
eapply derive_DK. 
wfcs_tac. 
wfcs_tac.
eapply derive_nil.  
eapply abs_K_type. 
wfcs_tac. 
eapply derive_app.
eapply derive_G. 
wfcs_tac. wfcs_tac. wfcs_tac. 
eapply derive_gen1. 
unfold lift; simpl. relocate_lt; simpl. 
eapply derive_app.
eapply derive_app. 
eapply derive_DS. 
wfcs_tac. 
wfcs_tac.
eapply derive_nil.  
eapply abs_S_type. 
wfcs_tac. 
eapply2 derive_I; wfcs_tac. 
Qed. 






Theorem unstar_star : forall M, normal M -> lamSF_red (App unstar (star M)) (Abs M). 
Proof. 
rank_tac. 
induction M; split_all. 
(* 4 *) 
case n; split_all. 
(* 5 *) 
unfold unstar. eval_lamSF. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
red; one_step. 
eauto. 
unfold unstar_fn at 1. 
eval_lamSF.
g_tac. 
unfold factorable; simpl in *; auto 20. 
simpl. 
insert_Ref_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. 
eapply da_oth_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
discriminate. 
eapply succ_red. 
eapply dk_oth_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
discriminate. 
g_tac. 
unfold factorable; simpl in *; auto 20. 
simpl. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. 
eapply ds_s_lamSF_red. 
eauto. 
eauto.
eval_lamSF. 
eauto. 
eauto.
eval_lamSF. 
eapply preserves_abs_lamSF_red. 
eval_lamSF.
(* 4 *) 
unfold unstar. eval_lamSF. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
red; one_step. 
eauto. 
unfold unstar_fn at 1. 
eval_lamSF.
g_tac. 
unfold factorable; simpl in *; auto 20. 
simpl. 
insert_Ref_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. 
eapply da_oth_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
discriminate. 
eapply succ_red. 
eapply dk_k_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
eauto. 
eval_lamSF. 
eapply preserves_abs_lamSF_red. 
relocate_lt. simpl; auto. 
unfold lift; split_all. relocate_lt. auto. 
(* 3 *) 
unfold unstar. eval_lamSF. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
red; one_step. 
eauto. 
unfold unstar_fn at 1. 
eval_lamSF.
g_tac. 
unfold factorable; simpl in *; auto 20. 
simpl. 
insert_Ref_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. 
eapply da_oth_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
discriminate. 
eapply succ_red. 
eapply dk_k_lamSF_red. 
eauto.
eauto.
eval_lamSF. 
auto.
(* 2 *) 
unfold unstar. eval_lamSF. eval_lamSF. 
unfold unstar_fn at 1. 
eval_lamSF.
g_tac. 
unfold factorable; simpl in *; auto 20. 
simpl. 
insert_Ref_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply2 succ_red. 
auto. 
eval_lamSF. 
eapply preserves_abs_lamSF_red. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
instantiate(1:= unstar). auto. 
unfold lift; simpl. eval_lamSF. 
rewrite subst_rec_lift_rec2. 
eapply2 IHp. 
omega. 
inversion H0; auto. 
(* 1 *) 
unfold unstar. eval_lamSF. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
red; one_step. 
eauto. 
unfold unstar_fn at 1. 
eval_lamSF.
g_tac. 
unfold factorable; simpl in *; auto 20. 
simpl. 
insert_Ref_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. 
eapply da_oth_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
discriminate. 
eapply succ_red. 
eapply dk_oth_lamSF_red. 
unfold factorable; simpl in *; auto 20. 
discriminate. 
g_tac. 
unfold factorable; simpl in *; auto 20. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
simpl. eapply succ_red. 
eapply ds_s_lamSF_red. 
eauto. 
simpl. eauto. eval_lamSF. 
eauto. eauto. eval_lamSF. 
eapply preserves_abs_lamSF_red. 
rewrite subst_rec_lift_rec; try omega. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eval_lamSF. 
unfold lift; simpl. eval_lamSF. 
repeat rewrite subst_rec_lift_rec2. 
auto. 
Qed. 
