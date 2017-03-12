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
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus from Project Coq                                *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   LamSF_Eval.v                                     *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import Components.
Require Import Compounds.
Require Import LamSF_reduction.
Require Import LamSF_Closed.

Ltac insert_Ref_tac := unfold subst_rec; fold subst_rec; insert_Ref_out; repeat(rewrite lift_rec_null).




Ltac g_tac := 
match goal with 
| |- multi_step lamSF_red1 (App (App (Op Gop) ?M) ?N) _ => 
apply succ_red with (App (App M (left_component N)) (right_component N));
[eapply2 g_lamSF_red|]
end. 


Ltac app_lamSF := unfold_op; 
match goal with 
| |- lamSF_red _ _ => red; app_lamSF
| |- multi_step lamSF_red1 (Ref _) (Ref _) => red; one_step
| |- multi_step lamSF_red1 (App _ _) (App _ _) => eapply2 preserves_app_lamSF_red ; app_lamSF
| |- multi_step lamSF_red1 (Abs _) (Abs _) => eapply2 preserves_abs_lamSF_red ;app_lamSF
| |- lamSF_red1 (Abs _) (Abs _) => eapply2 abs_lamSF_red ; app_lamSF
| _ => try red; split_all
end.

Definition eval_app M N := 
match M with 
| App (App (Op Sop) M1) M2  => App (App M1 N) (App M2 N)
| App (App (Op Aop) M1) M2  => App (App M1 M2) N
| App (Op Kop) M1  => M1
| Op Yop  => App N (App (App (Op Aop) (Op Yop)) N)
| Abs M2 => subst N M2
| x => App x N
end.


Lemma eval_app_from_lamSF : forall M N, lamSF_red (App M N) (eval_app M N).
Proof. 
induction M; split_all.
try (red; one_step; fail).  
case o; split_all; try eapply2 zero_red. red; one_step. 
red; one_step.
gen_case IHM1 M1. 
gen_case IHM1 o. 
red; one_step.
gen_case IHM1 l. 
gen_case IHM1 o. 
red; one_step. 
red; one_step. 
Qed. 


Fixpoint eval0 (M: lamSF) :=
match M with 
| Ref i => Ref i 
| Op o => Op o
| Abs M0 => Abs M0
| App M1 M11 => eval_app (eval0 M1) M11
end. 

Lemma eval0_from_lamSF : forall M, lamSF_red M (eval0 M).
Proof. 
induction M; split_all.
apply transitive_red with (App (eval0 M1) M2). eapply2 preserves_app_lamSF_red. 
eapply2 eval_app_from_lamSF. 
Qed. 


Ltac eval_lamSF0 := unfold_op; 
match goal with 
| |-  lamSF_red ?M _ => red; eval_lamSF0
| |-  multi_step lamSF_red1 ?M _ =>
  (apply transitive_red with (eval0 M); 
[eapply2 eval0_from_lamSF |  
  unfold eval0, eval_app;  unfold subst; split_all])
| _ => auto
end.


(* Boolean operations *) 

Definition not M := App (App M (App k_op i_op)) k_op.

Lemma not_true : lamSF_red (not k_op) (App k_op i_op).
Proof. unfold not; eval_lamSF0. Qed. 

Lemma not_false : lamSF_red (not (App k_op i_op)) k_op.
Proof. eval_lamSF0. one_step.   Qed. 

Definition  iff M N := App (App M N) (not N). 

Lemma true_true : lamSF_red (iff k_op k_op) k_op. 
Proof. unfold iff; unfold not; eval_lamSF0; split_all. Qed. 
Lemma true_false : lamSF_red (iff k_op (App k_op i_op)) (App k_op i_op). 
Proof. unfold iff; unfold not; eval_lamSF0; split_all. Qed. 
Lemma false_true : lamSF_red (iff (App k_op i_op) k_op) (App k_op i_op). 
Proof. unfold iff; unfold not; eval_lamSF0; eval_lamSF0; eval_lamSF0; eval_lamSF0; split_all. Qed. 
Lemma false_false : lamSF_red (iff (App k_op i_op) (App k_op i_op)) k_op.
Proof. 
unfold iff, not. unfold_op. repeat eval_lamSF0. Qed. 


Ltac eval_lamSF1 := 
eval_lamSF0; relocate_lt; unfold insert_Ref; unfold lift; try (rewrite lift_rec_closed); split_all. 

Ltac eval_lamSF := eval_lamSF0;  relocate_lt; unfold insert_Ref; split_all.
