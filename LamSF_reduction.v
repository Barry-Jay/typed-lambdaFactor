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
(*                Typed LambdaFactor Calculus                         *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   LamSF_reduction.v                                *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)


Require Import Arith.
Require Import Max. 
Require Import Test.
Require Import General. 
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import Components.
Require Import Compounds.

(* lamSF-reduction *) 


Inductive lamSF_red1 : lamSF -> lamSF -> Prop := 
  | appl_lamSF_red :  forall M M' N, lamSF_red1 M M' -> 
                                      lamSF_red1 (App M N) (App M' N)  
  | appr_lamSF_red :  forall M N N', lamSF_red1 N N' -> 
                                      lamSF_red1 (App M N) (App M N')  
  | abs_lamSF_red : forall M M', lamSF_red1 M M' -> lamSF_red1 (Abs M) (Abs M')
  | beta_lamSF_red : forall (M N: lamSF),
                     lamSF_red1 (App (Abs M) N) (subst N M)
  | s_lamSF_red: forall (M N P : lamSF),
             lamSF_red1 
                   (App (App (App (Op Sop) M) N) P) 
                  (App (App M P) (App N P))
  | a_lamSF_red: forall (M N P: lamSF), lamSF_red1 (App (App (App a_op M) N) P) (App (App M N) P)
  | k_lamSF_red : forall M N,  
               lamSF_red1 (App (App (Op Kop) M) N) M 
  | e_o_K_lamSF_red : forall o,  lamSF_red1 (App (App e_op (Op o)) (Op o)) k_op 
  | e_o_KI_lamSF_red : forall o N, factorable N -> Op o <> N -> 
                             lamSF_red1 (App (App e_op (Op o)) N) (App k_op i_op) 
  | e_compound_lamSF_red : forall M, compound M -> 
                                       lamSF_red1 (App e_op M) (App k_op (App k_op i_op)) 
  | g_lamSF_red : forall (M P: lamSF), factorable P -> 
             lamSF_red1 (App (App g_op M) P) 
                     (App (App M (left_component P)) (right_component P))
  | q_o_lamSF_red : forall M N o, lamSF_red1 (App (App (App (Op Qop) M) N) (Op o)) (App M (Op o))
  | q_compound_lamSF_red : forall M N P, compound P -> 
            lamSF_red1 (App (App (App (Op Qop) M) N) P) 
                       (App (App N (App (App (App (Op Qop) M) N) (left_component P)))
                            (App (App (App (Op Qop) M) N) (right_component P)))
  | u_o_lamSF_red : forall M o, lamSF_red1 (App (App (Op Uop) M) (Op o)) (Op o)
  | u_compound_lamSF_red : forall M P, compound P -> 
            lamSF_red1 (App (App (Op Uop) M) P)
                       (App (App (App M P) (App (App (Op Uop) M) (left_component P)))
                            (App (App (Op Uop) M) (right_component P)))
  | y_lamSF_red: forall (M: lamSF), lamSF_red1 (App (Op Yop) M) 
                                                   (App M (App (App (Op Aop) (Op Yop)) M))
  | ds_s_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DSop) M) N) (Op Sop)) M
  | ds_oth_lamSF_red : forall M N P, factorable P -> Op Sop <>P -> 
                                   lamSF_red1 (App (App (App (Op DSop) M) N) P) (App N P)
  | da_a_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DAop) M) N) (Op Aop)) M
  | da_oth_lamSF_red : forall M N P, factorable P -> Op Aop <>P -> 
                                   lamSF_red1 (App (App (App (Op DAop) M) N) P) (App N P)
  | dk_k_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DKop) M) N) (Op Kop)) M
  | dk_oth_lamSF_red : forall M N P, factorable P -> Op Kop <>P -> 
                                   lamSF_red1 (App (App (App (Op DKop) M) N) P) (App N P)
  | de_e_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DEop) M) N) (Op Eop)) M
  | de_oth_lamSF_red : forall M N P, factorable P -> Op Eop <>P -> 
                                   lamSF_red1 (App (App (App (Op DEop) M) N) P) (App N P)
  | dg_g_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DGop) M) N) (Op Gop)) M
  | dg_oth_lamSF_red : forall M N P, factorable P -> Op Gop <>P -> 
                                   lamSF_red1 (App (App (App (Op DGop) M) N) P) (App N P)
  | dq_q_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DQop) M) N) (Op Qop)) M
  | dq_oth_lamSF_red : forall M N P, factorable P -> Op Qop <>P -> 
                                   lamSF_red1 (App (App (App (Op DQop) M) N) P) (App N P)
  | du_u_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DUop) M) N) (Op Uop)) M
  | du_oth_lamSF_red : forall M N P, factorable P -> Op Uop <>P -> 
                                   lamSF_red1 (App (App (App (Op DUop) M) N) P) (App N P)
  | dy_y_lamSF_red : forall M N, lamSF_red1 (App (App (App (Op DYop) M) N) (Op Yop)) M
  | dy_oth_lamSF_red : forall M N P, factorable P -> Op Yop <>P -> 
                                   lamSF_red1 (App (App (App (Op DYop) M) N) P) (App N P)
 .

Hint Constructors lamSF_red1. 

Definition lamSF_red := multi_step lamSF_red1. 

Lemma reflective_lamSF_red: reflective lamSF_red. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_lamSF_red.

Lemma preserves_apl_lamSF_red: preserves_apl lamSF_red. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_lamSF_red.

Lemma preserves_apr_lamSF_red: preserves_apr lamSF_red. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_lamSF_red.



Lemma preserves_app_lamSF_red: preserves_app lamSF_red. 
Proof. 
red; split_all. 
apply transitive_red with (App M' N); split_all. 
eapply2 preserves_apl_lamSF_red. 
eapply2 preserves_apr_lamSF_red. 
Qed. 
Hint Resolve preserves_app_lamSF_red.

Lemma preserves_abs_lamSF_red: preserves_abs lamSF_red. 
Proof. red; split_all. eapply2 preserves_abs_multi_step. red; split_all. Qed.
Hint Resolve preserves_abs_lamSF_red.
