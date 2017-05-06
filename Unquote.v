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
(*                      Unquote.v                                     *)
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
Require Import Slow_quote. 



(* unquote *) 

Lemma instance_id : forall ty, wfs ty -> instance (Abs (funty (Ref 0) (Ref 0))) (funty ty ty).
Proof. 
split_all. red; one_step. 
replace (funty ty ty) with (subst ty (funty (Ref 0) (Ref 0))).
eapply2 instance_rule. 
unfold subst.  simpl. insert_Ref_tac. auto.
Qed. 




Definition to_lambda0 := 
  App (App (Op DKop) abs_K) 
      (App (App (Op DSop) abs_S) i_op)
.

Definition to_lambda_fn := 
Abs (Abs (App (App (App (App e_op (Ref 0)) (Ref 0)) (App to_lambda0 (Ref 0))) 
         (App (App g_op (Abs (Abs (App (App (Ref 3) (Ref 1)) (App (Ref 3) (Ref 0)))))) 
              (Ref 0)))).

Definition to_lambda := App (App a_op y_op) to_lambda_fn. 

Lemma abs_K_type : forall gamma, wfc gamma -> derivation gamma abs_K (opty Kop). 
Proof. 
intros. unfold abs_K, opty.  unfold abs, ref, op_abs, quant, opty_core, opty_core0. 
repeat eapply2 derive_gen1. repeat eapply2 derive_abs. derive_tac. 
Qed. 

Lemma abs_S_type : forall gamma, wfc gamma -> derivation gamma abs_S (opty Sop). 
Proof. 
intros; unfold abs_S, opty.  unfold abs, ref, op_abs, quant, opty_core, opty_core0. 
repeat eapply2 derive_gen1. simpl. repeat eapply2 derive_abs. 
repeat eapply2 derive_app; derive_tac. 
Qed. 


Lemma to_lambda0_type : 
forall gamma, wfc gamma -> derivation gamma to_lambda0 (Abs (funty (Ref 0) (Ref 0))).
Proof. 
intros; unfold to_lambda0.
eapply2 derive_gen1. unfold lift; simpl. 
eapply2 derive_app.
eapply derive_app.
2: eapply2 abs_K_type.
eapply derive_instance. eapply2 derive_op. red; one_step.
instantiate(1:= (funty (Ref 0) (Ref 0))). 
replace (funty (opty Kop)
        (funty (funty (Ref 0) (Ref 0)) (funty (Ref 0) (Ref 0))))
with (subst (Ref 0) (funty (opty Kop)
        (funty (funty (Ref 0) (Ref 0)) (funty (Ref 0) (Ref 0))))) by auto. 
unfold opty, opty_core, case_op_type, op_abs, opty_core0, quant. 
eapply2 instance_rule. wfcs_tac. 
eapply derive_app.
eapply derive_app.
2: eapply2 abs_S_type.
instantiate(1:= (funty (Ref 0) (Ref 0))). 
eapply derive_instance. eapply2 derive_op. 
replace (funty (opty Sop)
        (funty (funty (Ref 0) (Ref 0)) (funty (Ref 0) (Ref 0))))
with (subst (Ref 0) (funty (opty Sop)
        (funty (funty (Ref 0) (Ref 0)) (funty (Ref 0) (Ref 0))))) by auto. 
unfold opty, opty_core, case_op_type, op_abs, opty_core0, quant. 
red; one_step. eapply2 instance_rule. wfcs_tac. 
eapply2 derive_instance. 
eapply2 zero_red. 
Qed. 

Lemma to_lambda_type : derivation nil to_lambda (Abs (funty (Ref 0) (Ref 0))).
Proof. 
unfold to_lambda.
eapply derive_app.
eapply derive_app.
eapply derive_A. 
wfcs_tac. 
2:wfcs_tac. 
2: derive_tac. 
wfcs_tac. 
unfold to_lambda_fn. 
eapply2 derive_abs. 
eapply2 derive_gen1. unfold lift; simpl. relocate_lt. simpl. 
eapply2 derive_abs. 
eapply derive_app. 
eapply derive_app. 
eapply derive_app. 
2: derive_tac. 
eapply derive_app. 
2: derive_tac. 
derive_tac. 
(* 2 *) 
eapply derive_app. eapply derive_instance. eapply2 to_lambda0_type. wfcs_tac. 
instantiate (1:= Ref 0). red; one_step. 
replace (funty (Ref 0) (Ref 0)) with (subst (Ref 0) (funty (Ref 0) (Ref 0))) by auto. 
eapply2 instance_rule. 
derive_tac. 
eapply derive_app. eapply derive_app.
3: derive_tac. 
derive_tac. 
(* 1 *) 
eapply2 derive_gen1.  unfold lift; simpl. relocate_lt. simpl. 
eapply2 derive_abs. 
eapply2 derive_abs. 
eapply derive_app. 
eapply derive_app.
2: derive_tac.  
2: eapply derive_app. 3: derive_tac.
instantiate(1:= (varty 0)).  
eapply2 derive_instance. derive_tac. 
replace(funty (funty (varty 0) (Ref 1)) (funty (varty 0) (Ref 1)))
with (subst  (funty (varty 0) (varty 1)) (funty (Ref 0) (Ref 0))) by auto. 
red; one_step. 
eapply2 derive_instance. 
derive_tac. 
replace(funty (varty 0) (varty 0))
with (subst  (varty 0) (funty (varty 0) (varty 0))) by auto. 
red; one_step. 
Qed. 



Definition unstar_S := 
  Abs (Abs (Abs (App (App (App to_lambda (Ref 2)) (App unstar (Ref 0))) (App (App to_lambda (Ref 1)) (Ref 0))))).

Lemma unstar_S_type : 
forall gamma, wfc gamma -> derivation gamma  unstar_S (opty Sop). 
Proof. 
intros; unfold unstar_S; unfold opty, opty_core, op_abs, quant. 
repeat eapply derive_gen1; simpl. repeat eapply derive_abs. 
eapply derive_app. eapply derive_app. eapply derive_app.
2: derive_tac. 
2: eapply derive_app. 3: derive_tac. 
eapply derive_instance. 
eapply derive_nil. 
eapply to_lambda_type. 
wfcs_tac. 
instantiate(1:= (varty 1)).
instantiate(1:= (varty 2)).
eapply instance_id. 
wfcs_tac. 
eapply derive_instance. 
eapply derive_nil. 
eapply unstar_type. 
wfcs_tac. 
eapply instance_id. auto. 
eapply derive_app. 2: derive_tac. 
eapply derive_app. 2: derive_tac. 
eapply derive_instance.
eapply derive_nil. 
2: wfcs_tac. 
eapply to_lambda_type. 
eapply2 instance_id. 
Qed. 



Definition unstar_abs_left := 
Abs (App (App (App (App e_op (Ref 0)) (Ref 0))  (Ref 0)) 
    (App (App g_op (Abs (Abs (App (App (App (App e_op (Ref 1)) (Ref 1)) 
                        (App (Ref 1) (Ref 0)))
                   (App (App (App g_op (Abs (Abs (App (App (App (App (Op DSop) unstar_S) 
                                            i_op) (Ref 1)) 
                                                 (Ref 0)))))
                        (Ref 1)) (Ref 0)))))) (Ref 0)))
.


Lemma unstar_abs_left_type :
derivation nil unstar_abs_left (Abs (funty (Ref 0) (Ref 0))).
Proof. 
unfold unstar_abs_left; eapply derive_gen1; simpl. eapply derive_abs.
eapply derive_app. 
eapply derive_app.  2: derive_tac.  
eapply derive_app.  2: derive_tac.  
eapply derive_app.  2: derive_tac.  
derive_tac. 
eapply derive_app.  2: derive_tac.  
eapply derive_app.  derive_tac. 
eapply derive_gen1; simpl. unfold lift; simpl. relocate_lt. simpl. 
eapply derive_abs. eapply derive_abs.
eapply derive_app. 
eapply derive_app.  
eapply derive_app. eapply derive_app. 2: derive_tac. 2: derive_tac.  derive_tac. 
eapply derive_app. derive_tac. derive_tac.  
eapply derive_app.  2:derive_tac.  
eapply derive_app.  2: derive_tac. 
eapply derive_app.  derive_tac.  
eapply derive_gen1; simpl. unfold lift; simpl. relocate_lt. simpl. 
eapply derive_abs. eapply derive_abs.
eapply derive_app.  2: derive_tac.
eapply derive_app.  2: derive_tac.  
eapply derive_app. eapply derive_app. derive_tac.   
2: eapply2 unstar_S_type. 2: wfcs_tac. 
derive_tac. 
instantiate(1:= (funty (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))
              (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2))))). 
eapply2 derive_instance. eapply2 derive_op. wfcs_tac. 
unfold opty, opty_core, case_op_type, op_abs, opty_core0, quant. 
eapply succ_red.  eapply instance_rule. 2: wfcs_tac. 
instantiate(1:= (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))). 
wfcs_tac. 
unfold subst; simpl.  insert_Ref_tac.  eapply2 zero_red. 
unfold_op.  
repeat eapply derive_app. 
instantiate(1:= funty (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))
                      (funty (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))
                      (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2))))). 
derive_tac. derive_tac. derive_tac. 
Qed. 


Definition unquote_fn :=   (* duplicates some computations *) 
Abs(Abs(App(App(App(App (Op Eop) (Ref 0))(Ref 0))(Ref 0)) 
 (App (App (Op Gop) (Abs(Abs(App(App(Op Gop) (Abs(Abs
      (App(App(App(App(App(Op DAop) i_op) i_op) (Ref 1))
              (App (Ref 5) (Ref 0)))
          (App(App(App(App equal i_op)  
                      (App (Ref 5) (Ref 0)))
                  (App unstar (App (Ref 5) (Ref 2))))
              (App (Ref 5) (Ref 2)))))))
                                (Ref 1)))))
      (Ref 0))))
.

Definition unquote := App (App a_op y_op) unquote_fn. 

Theorem unquote_type : derivation nil unquote (Abs (funty (varty 0) (varty 0))).
Proof. 
unfold unquote.
eapply derive_app.
eapply derive_app.
eapply derive_A. 
wfcs_tac. 
2: wfcs_tac.
2: derive_tac. 
wfcs_tac. 
(* unquote_fn *) 
unfold unquote_fn. 
eapply2 derive_abs. 
eapply2 derive_gen1. unfold lift; simpl. relocate_lt. simpl. 
eapply2 derive_abs. 
repeat eapply derive_app. 
2: derive_tac. 
2: derive_tac. 
derive_tac. 
derive_tac. 
3: derive_tac. 
derive_tac. 
eapply2 derive_gen1. unfold lift; simpl. relocate_lt. simpl. 
repeat eapply2 derive_abs. repeat eapply derive_app. 
3: derive_tac. 
derive_tac. 
eapply2 derive_gen1. unfold lift; simpl. relocate_lt. simpl. 
repeat eapply derive_abs. 
eapply derive_app. 
eapply derive_app. 
2: eapply derive_app. 
3: derive_tac. 
2: eapply derive_instance; [ derive_tac |  eapply2 instance_id]. 
eapply derive_app. 2: derive_tac. 
eapply derive_app. eapply derive_app.
eapply derive_instance. eapply derive_op. wfcs_tac. 
instantiate(1:= Ref 1). 
instantiate(1:= (funty (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))
              (funty (varty 0) (funty (Ref 1) (Ref 2))))). 
instantiate(1:= opty Aop).
unfold opty, opty_core, case_op_type, op_abs, opty_core0, quant. 
replace(funty
        (Abs
           (Abs
              (funty (funty (varty 0) (varty 1)) (funty (varty 0) (varty 1)))))
        (funty
           (funty (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))
              (funty (varty 0) (funty (Ref 1) (Ref 2))))
           (funty (funty (varty 0) (App (App (Op Sop) (Ref 1)) (Ref 2)))
              (funty (varty 0) (funty (Ref 1) (Ref 2))))))
with (subst  (funty (varty 0) (funty (Ref 1) (Ref 2))) (funty
           (Abs
              (Abs
                 (funty (funty (varty 0) (varty 1))
                    (funty (varty 0) (varty 1)))))
           (funty (funty (varty 0) (varty 0)) (funty (varty 0) (varty 0)))))
by auto. 
red; one_step. eapply2 instance_rule. wfcs_tac. 
unfold opty, opty_core, case_op_type, op_abs, opty_core0, quant. 
eapply2 derive_gen1. unfold lift; simpl. relocate_lt. simpl. 
eapply2 derive_gen1. unfold lift; simpl. relocate_lt. simpl. 
eapply2 derive_I. wfcs_tac. eapply2 derive_I. wfcs_tac. 
(* 1 *) 
eapply derive_app. 
2: eapply derive_app. 3:derive_tac. 
2: eapply2 derive_instance; derive_tac; eapply2 instance_id. 
eapply derive_app. eapply derive_app. 
2: eapply derive_app. 3: derive_tac. 
2: eapply2 derive_instance. 2: derive_tac. 
2: eapply2 instance_id. 
2: eapply derive_app. 
3: eapply derive_app. 4: derive_tac. 
3: eapply2 derive_instance. 3: derive_tac. 3: eapply2 instance_id. 
2: eapply2 derive_instance. 2: eapply2 derive_nil. 2: eapply2 unstar_type. 
2: wfcs_tac. 2: eapply2 instance_id. 
(* 1 *) 
eapply derive_app. 
2: eapply derive_I. 2: wfcs_tac. 2: auto. 
eapply derive_instance.   eapply2 derive_nil. eapply2 equal_type. wfcs_tac. 
unfold_opty.
instantiate(1:= 0).  
eapply succ_red. eapply instance_rule. 2: wfcs_tac.
instantiate(1:=  (funty (varty 0) (varty 0))). 
wfcs_tac. unfold subst; simpl. insert_Ref_out.  simpl. relocate_lt. simpl. 
eapply succ_red. eapply instance_rule. 2: wfcs_tac.
instantiate(1:=  varty 0). 
wfcs_tac. unfold subst; simpl. insert_Ref_out.  simpl. relocate_lt. simpl. 
eapply succ_red. eapply instance_rule. 2: wfcs_tac.
instantiate(1:=  varty 1). 
wfcs_tac. unfold subst; simpl. insert_Ref_out.  simpl. relocate_lt. simpl. 
auto. 
Qed. 


Lemma unquote_op : 
forall o,  lamSF_red (App (App (Op Yop) unquote_fn) (Op o)) (Op o).
Proof. 
intros.  eapply2 succ_red. unfold unquote_fn at 1. eval_lamSF. 
simpl. insert_Ref_tac. relocate_lt. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. eapply2 e_o_K_lamSF_red. auto.  auto. auto. eval_lamSF. 
Qed. 


Lemma unquote_A : 
forall M N, lamSF_red (App (App (Op Yop) unquote_fn)  (App (App a_op M) N))
                      (App (App (App (Op Yop) unquote_fn) M)
                           (App(App(App(App equal i_op)  
                                       (App (App (Op Yop) unquote_fn) M))
                                   (App unstar (App (App (Op Yop) unquote_fn) N)))
                               (App (App (Op Yop) unquote_fn) N)))
.

Proof.
split_all. eapply2 succ_red. unfold unquote_fn at 1. eval_lamSF. 
unfold lift; rewrite lift_rec_null.  
simpl. insert_Ref_tac. relocate_lt. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. 
eapply succ_red. eapply2 e_compound_lamSF_red. 
unfold compound; split_all. auto. auto. auto. auto. eval_lamSF. eval_lamSF. 
eapply succ_red. eapply2 g_lamSF_red. 
unfold factorable; split_all. auto 10. eval_lamSF. 
eapply succ_red. eapply2 g_lamSF_red. 
unfold factorable; split_all. auto 10. eval_lamSF. 
simpl. insert_Ref_tac. relocate_lt. repeat rewrite subst_rec_lift_rec; try omega. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. 
eapply2 succ_red. auto. auto. eval_lamSF. eval_lamSF. eval_lamSF. 
repeat rewrite lift_rec_null. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eapply2 preserves_app_lamSF_red. 
eval_lamSF; auto. 
eapply2 preserves_app_lamSF_red. 
eval_lamSF; auto. 
eval_lamSF; auto. 
Qed. 


Lemma unquote_quote_abs_left: 
 lamSF_red (App (App (Op Yop) unquote_fn) (slow_quote abs_left)) abs_left.
Proof. 
unfold_op; unfold slow_quote; split_all. 
eapply transitive_red. eapply2 unquote_A. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply2 unquote_A. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. auto. eapply2 unquote_A. auto. 
eapply2 unquote_op.  
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. auto. 
eapply preserves_app_lamSF_red. eapply2 unquote_op. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. auto. eapply2 unquote_op. auto. 
eapply2 unquote_op. auto. auto. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 equal_compounds. unfold_op; unfold compound; split_all. 
unfold compound; split_all. auto. auto. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 unquote_op. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. auto. 
eapply2 unquote_op. auto. 
eapply2 unquote_op. 
unfold_op; simpl. auto. 
eapply2 preserves_app_lamSF_red. eapply2 preserves_app_lamSF_red. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 unequal_programs. 
unfold_op; unfold program; split_all.  unfold program; split_all. 
discriminate. 
auto. auto. eval_lamSF. eval_lamSF. auto. 
replace (App (App (Op Aop) (Op Yop)) equal_fn) with equal by auto. 
eapply transitive_red. eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. eapply2 unequal_programs. 
unfold_op; unfold program; split_all.  repeat eapply2 nf_app. split_all. 
unfold program; split_all. 
discriminate. 
eapply preserves_app_lamSF_red. auto. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red.  auto. 
eapply preserves_app_lamSF_red. auto. eapply2 unquote_op. auto. auto. 
eapply preserves_app_lamSF_red. auto. eapply2 unquote_op. auto. 
eval_lamSF. eval_lamSF. eval_lamSF. 
Qed. 


Theorem unquote_quote : 
forall M, program M -> lamSF_red  (App (App (Op Yop) unquote_fn) (slow_quote M)) M. 
Proof. 
rank_tac. 
induction M; split_all. 
(* 4 *) 
inversion H0; split_all. simpl in *. noway. 
(* 3 *) 
unfold unquote, unquote_fn, slow_quote. 
eval_lamSF. eval_lamSF. simpl. insert_Ref_tac. relocate_lt; simpl. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. 
red; one_step. auto. 
eapply2 succ_red. eapply2 g_lamSF_red. eapply2 programs_are_factorable. 
eval_lamSF. auto. 
(* 2 *) 
rewrite slow_quote_abs. 
eapply transitive_red. eapply2 unquote_A. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. 
eapply2 unquote_quote_abs_left. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. auto. 
eapply2 unquote_quote_abs_left. 
eapply preserves_app_lamSF_red. auto. 
eapply2 IHp. 
assert(rank(star M)< rank(Abs M)) by eapply2 rank_star. 
assert(rank M >0) by eapply2 rank_positive. simpl in *. omega. 
unfold program; split_all. eapply2 normal_star. inversion H0. inversion H1. auto. 
inversion H0. simpl in *. rewrite maxvar_star. auto. 
eapply2 IHp. 
assert(rank(star M)< rank(Abs M)) by eapply2 rank_star. 
assert(rank M >0) by eapply2 rank_positive. simpl in *. omega. 
unfold program; split_all. eapply2 normal_star. inversion H0. inversion H1. auto. 
inversion H0. simpl in *. rewrite maxvar_star. auto. 
unfold_op. eval_lamSF. eval_lamSF. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 equal_programs. 
unfold program; split_all. 
eapply2 unstar_star. 
inversion H0. inversion H1; auto. auto. eval_lamSF. auto. 
(* 1 *) 
rewrite slow_quote_app. 
eapply transitive_red. eapply2 unquote_A. 
eapply2 preserves_app_lamSF_red. 
eapply2 IHM1. omega. inversion H0. simpl in *. unfold program; split_all. 
inversion H1; auto. max_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply preserves_app_lamSF_red. auto. 
eapply2 IHM1. omega. inversion H0. simpl in *. unfold program; split_all. 
inversion H1; auto. max_out. 
eapply preserves_app_lamSF_red. auto. 
eapply2 IHM2. omega. inversion H0. simpl in *. unfold program; split_all. 
inversion H1; auto. max_out. 
eapply2 IHM2. omega. inversion H0. simpl in *. unfold program; split_all. 
inversion H1; auto. max_out. 
eapply transitive_red. 
eapply preserves_app_lamSF_red. eapply preserves_app_lamSF_red. 
eapply2 unequal_programs. 
unfold_op; unfold program; split_all. 
inversion H0; split_all. inversion H1.  auto. simpl in *; max_out.  
intro; subst. inversion H0. inversion H1. eapply2 H7. auto. auto. 
eval_lamSF. eval_lamSF.
Qed. 
