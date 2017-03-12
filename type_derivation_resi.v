(* This Program is free software; you can redistribute it and/or      *)
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
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                 type_derivation_resi.v                             *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Bool.
Require Import List.
Require Import General.
Require Import Max. 
Require Import Test.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import Components.
Require Import Compounds.
Require Import LamSF_reduction.
Require Import LamSF_Closed.
Require Import type_derivation.


(* Now restrict instantiation to operators and variables.  *)


Inductive derivation_resi : context -> lamSF -> lamSF -> Prop := 
| resi_op : forall gamma o ty,  instance (opty o) ty -> wfc gamma -> 
                                   derivation_resi gamma (Op o) ty 
| resi_var : forall gamma ty1 ty2,  instance ty1 ty2 -> wfc gamma -> wfs ty1 -> 
                                       derivation_resi (cons ty1 gamma) (Ref 0) ty2
| resi_weak : forall gamma i ty1 ty,  derivation_resi gamma (Ref i) ty -> wfs ty1 -> 
                                 derivation_resi (cons ty1 gamma) (Ref (S i)) ty
| resi_abs : forall gamma ty1 ty2 t,   
                 derivation_resi (cons ty1 gamma) t ty2 ->
                 derivation_resi gamma (Abs t) (funty ty1 ty2)
| resi_app: forall gamma t ty1 ty2 u,  
                derivation_resi gamma t (funty ty1 ty2) -> 
                derivation gamma u ty1 -> (* note use of derivation here *) 
                derivation_resi gamma (App t u) ty2
| resi_gen1: forall gamma t ty, derivation_resi (map (lift 1) gamma) t ty ->
                                  derivation_resi gamma t (Abs ty)
| resi_push1 : forall gamma t ty, derivation_resi gamma t ty ->
                forall ty2, push1 ty ty2 -> derivation_resi gamma t ty2
 .


Hint Resolve 
resi_op resi_var resi_weak resi_abs resi_app resi_gen1 resi_push1
. 

Lemma lift_rec_ty_preserves_resi : forall gamma t ty, derivation_resi gamma t ty -> forall n k , 
derivation_resi (map (fun ty0 => lift_rec ty0 n k) gamma) t (lift_rec ty n k). 
Proof. 
intros gamma t ty d; induction d; split_all. 
(* 6 *)
eapply2 resi_op. 
replace (opty o) with (lift_rec (opty o) n k) by (case o; split_all); auto. 
eapply2 lift_rec_preserves_instance. 
(* 5 *) 
eapply2 resi_var.  eapply2 lift_rec_preserves_instance. 
(* 4 *) 
eapply2 resi_abs; eapply2 IHd. 
(* 3 *) 
apply resi_app with (lift_rec ty1 n k); auto. 
replace (funty (lift_rec ty1 n k) (lift_rec ty2 n k)) 
with (lift_rec (funty ty1 ty2) n k) by auto.
eapply2 IHd. 
eapply2 lift_rec_ty_preserves_derive.  
(* 2 *) 
eapply2 resi_gen1. 
replace(map (lift 1) (map (fun ty0 : lamSF => lift_rec ty0 n k) gamma)) 
with (map (fun ty0 : lamSF => lift_rec ty0 (S n) k) (map (lift 1) gamma)).
eapply2 IHd. 
clear; induction gamma; subst; split_all. 
rewrite IHgamma. 
unfold lift; rewrite lift_lift_rec; try omega. auto. 
(* 1 *) 
eapply2 resi_push1. eapply2 lift_rec_preserves_push1. 
Qed. 


Lemma subst_rec_ty_preserves_derive_resi : 
forall gamma t ty, derivation_resi gamma t ty -> 
forall ty1 k, wfs ty1 -> 
derivation_resi (map (fun ty0 => subst_rec ty0 ty1 k) gamma) t 
           (subst_rec ty ty1 k). 
Proof. 
intros gamma t ty d; induction d; split_all. 
(* 7 *) 
eapply2 resi_op. 
replace(opty o) with (subst_rec (opty o) ty1 k) by (case o; split_all). 
eapply2 subst_rec_preserves_instance. 
(* 6 *) 
eapply2 resi_var. eapply2 subst_rec_preserves_instance.  eapply2 subst_rec_preserves_wfs. 
(* 5 *) 
eapply2 resi_weak. eapply2 subst_rec_preserves_wfs. 
(* 4 *) 
eapply2 resi_abs. eapply2 IHd. 
(* 3 *) 
eapply2 resi_app. 
2: eapply subst_rec_ty_preserves_derive. 3: eexact H. 3: auto. 
simpl in *. eapply2 IHd. eapply2 derive_implies_wfcs. 
(* 2 *) 
assert(derivation_resi
          (map (fun ty0 : lamSF => subst_rec ty0 ty1 (S k)) (map (lift 1) gamma))
          t (subst_rec ty ty1 (S k))) by eapply2 IHd. 
replace (map (fun ty0 : lamSF => subst_rec ty0 ty1 (S k)) (map (lift 1) gamma))
with (map (lift 1) (map (fun ty0 : lamSF => subst_rec ty0 ty1 k) gamma)) in H0. 
auto.
clear; induction gamma; split_all; rewrite IHgamma. 
unfold lift; rewrite subst_rec_lift_rec1; auto; omega.
(* 1 *) 
eapply2 resi_push1. eapply2 subst_rec_preserves_push1.
Qed. 



Definition preserves_resi (red: termred) := 
forall ty1 ty2, red ty1 ty2 -> 
forall gamma t, derivation_resi gamma t ty1 -> derivation_resi gamma t ty2. 

Lemma preserves_resi_multi_step: 
forall red, preserves_resi red -> preserves_resi (multi_step red).
Proof. red; intros red p ty1 ty2 m; induction m; split_all; eapply2 IHm. Qed.

Lemma preserves_resi_push : preserves_resi push. 
Proof. eapply2 preserves_resi_multi_step. red; split_all. eapply2 resi_push1. Qed. 


Lemma derivation_resi_implies_derivation : 
forall gamma t ty, derivation_resi gamma t ty -> derivation gamma t ty.
Proof. 
intros gamma t ty d; induction d; split_all; eauto.
(* 2 *) 
eapply2 derive_instance. 
(* 1 *) 
eapply derive_instance. 
eapply2 derive_var.  auto. 
Qed. 

Lemma derive_resi_instance_context : 
forall gamma1 t ty, derivation_resi gamma1 t ty -> 
forall gamma2, instance_context gamma2 gamma1 -> derivation_resi gamma2 t ty.
Proof. 
intros gamma1 t ty d; induction d; intros gamma2 inst; subst; split_all. 
(* 7 *) 
eapply2 resi_op. eapply2 instance_context_reflects_wfc. 
(* 6 *) 
inversion inst; subst. eapply2 resi_var. eapply2 transitive_red. 
eapply2 instance_context_reflects_wfc.
eapply2 instance_implies_wfs. 
(* 5 *) 
inversion inst; split_all; subst. eapply2 resi_weak. eapply2 instance_implies_wfs. 
(* 4 *) 
eapply2 resi_abs. eapply2 IHd. eapply2 instance_context_cons. eapply2 zero_red. 
(* 3 *) 
eapply2 resi_app. eapply2 derive_instance_context. 
(* 2 *) 
eapply2 resi_gen1. eapply2 IHd. eapply2 lift_rec_preserves_instance_context. 
(* 1 *) 
eapply2 resi_push1. 
Qed. 


Lemma resi_inst1 : 
forall gamma t ty1, derivation_resi gamma t ty1 -> 
forall ty2, instance1 ty1 ty2 -> derivation_resi gamma t ty2. 
Proof. 
intros gamma t ty1 d; induction d; intros; subst; split_all. 
(* 6 *) 
eapply2 resi_op. eapply transitive_red. eexact H. one_step.
(* 5 *) 
eapply2 resi_var. eapply transitive_red. eexact H. one_step. 
(* 4 *)
inversion H; subst; eapply2 resi_abs. 
eapply2 derive_resi_instance_context. eapply2 instance_context_cons. red; one_step. 
clear; induction gamma; split_all. eapply2 instance_context_cons. eapply2 zero_red. 
(* 3 *) 
eapply2 resi_app. eapply2 IHd. eapply2 instance_funty. eapply2 derive_implies_wfcs. 
(* 2 *) 
inversion H; subst. 
(* 3 *) 
assert(derivation_resi (map (fun M => subst_rec M ty0 0) (map (lift 1) gamma)) t (subst_rec ty ty0 0)) by eapply2 subst_rec_ty_preserves_derive_resi. 
assert(map (fun M : lamSF => subst_rec M ty0 0) (map (lift 1) gamma) = gamma). 
clear; induction gamma; split_all. rewrite IHgamma. 
unfold lift; rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null; auto. 
rewrite H3 in H0. auto. 
(* 2 *) 
eapply2 resi_gen1. 
(* 1 *) 
assert(exists ty5, instance1 ty ty5 /\ push ty5 ty0) by eapply2 push1_instance1. 
split_all. 
assert(derivation_resi gamma t x) by eapply2 IHd. 
eapply2 preserves_resi_push.
Qed. 



Lemma derivation_implies_derivation_resi: 
forall gamma t ty, derivation gamma t ty -> 
derivation_resi gamma t ty.
Proof.
intros gamma t ty d; induction d; split_all; eauto.
(* 3 *) 
eapply2 resi_op. eapply2 zero_red.  
(* 2 *) 
eapply2 resi_var. eapply2 zero_red. 
(* 1 *)
eapply2 resi_inst1.
Qed. 
