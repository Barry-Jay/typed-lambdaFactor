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
(*                    operator_types.v                                *)
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
Require Import type_derivation_resi.
Require Import type_derivation_rwf.


Ltac one_instance ty := 
match goal with 
| |- multi_step instance1 (Abs ?ty1) _ =>
     apply succ_red with (subst ty ty1); 
    [eapply2 instance_rule; wfcs_tac  | subst_out]
end. 

Ltac instances tys := 
match tys with 
| cons ?ty ?tys1 => one_instance ty; instances tys1
| nil => idtac
end. 


Ltac wfcs_tac ::= unfold lift; simpl; relocate_lt; repeat eapply2 wfc_cons;  
repeat (repeat eapply2 wfs_abs; repeat eapply2 wfs_funty); simpl; repeat eapply2 wf_funty; 
match goal with 
| H : wf (Abs _) |- _ => inversion H
| _ => auto
end. 




Lemma instance_abs_to_wf: 
forall ty1 ty2, instance ty1 ty2 -> wf ty2 -> 
forall ty0, ty1 = Abs ty0 -> exists ty, wfs ty /\ instance(subst ty ty0) ty2. 
Proof.
cut(forall red ty1 ty2, multi_step red ty1 ty2 -> red = instance1 -> wf ty2 -> 
forall ty0, ty1 = Abs ty0 -> exists ty, wfs ty /\ instance(subst ty ty0) ty2). 
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 m; induction m; split_all; subst; inv1 wf. 
inversion H; subst. 
exist ty.
assert(exists ty : lamSF, wfs ty /\ instance (subst ty ty2) P) by eapply2 IHm. 
split_all. 
exist x. 
eapply transitive_red.  2: eexact H4. 
unfold subst; eapply2 subst_rec_preserves_instance. red; one_step. 
Qed. 

Lemma instance_preserves_funty: 
forall ty1 ty2, instance ty1 ty2 -> 
forall ty11 ty12, ty1 = funty ty11 ty12 -> 
exists ty21 ty22, ty2 = funty ty21 ty22 /\ instance ty21 ty11 /\ instance ty12 ty22.
Proof.
cut(forall red ty1 ty2, multi_step red ty1 ty2 -> red = instance1 -> 
forall ty11 ty12, ty1 = funty ty11 ty12 -> 
exists ty21 ty22, ty2 = funty ty21 ty22 /\ instance ty21 ty11 /\ instance ty12 ty22). 
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 m; induction m; split_all; subst; inv1 wf; eauto. 
(* 2 *) 
exist ty11; exist ty12; eapply2 zero_red. 
(* 1 *)
inversion H; subst. 
assert(exists ty21 ty22 : lamSF, P = funty ty21 ty22 /\ instance ty21 ty11 /\ instance ty3 ty22) by eapply2 IHm. 
split_all; subst.  
exist x; exist x0. 
eapply2 succ_red.  
assert(exists ty21 ty22 : lamSF, P = funty ty21 ty22 /\ instance ty21 ty0 /\ instance ty12 ty22)
 by eapply2 IHm. 
split_all; subst.  
exist x; exist x0. 
eapply transitive_red.  eexact H0. one_step. 
Qed. 


Ltac inst_tac := unfold funty, s_op in *; 
match goal with 
| H : instance (Abs ?ty1) ?ty2 |- _ => 
assert(exists ty, wfs ty /\ instance (subst ty ty1) ty2) by eapply2 instance_abs_to_wf; 
clear H; split_all; unfold subst in *; simpl in * ; inst_tac
| H : instance (App (App (Op Sop) ?ty0) ?ty1) ?ty2 |- _ => 
generalize H; clear H; subst_out; intro target; 
assert(exists ty21 ty22, ty2 = funty ty21 ty22 /\ instance ty21 ty0 /\ instance  ty1 ty22)
by eapply2 instance_preserves_funty; 
clear target; split_all; subst; inv1 wf; unfold subst in *; simpl in * ; inst_tac
| _ => subst
end.


Lemma instance_S : 
forall ty1 ty2 ty3, wfs ty1 -> wfs ty2 -> wfs ty3 -> instance (opty Sop) 
  (funty (funty ty1 (funty ty2 ty3)) (funty (funty ty1 ty2) (funty ty1 ty3))). 
Proof. 
unfold instance; unfold_opty; split_all. instances (cons ty1 (cons ty2 (cons ty3 nil))).
Qed.

Lemma derive_S : 
forall gamma ty1 ty2 ty3, wfc gamma -> wfs ty1 -> wfs ty2 -> wfs ty3 -> 
derivation gamma s_op 
  (funty (funty ty1 (funty ty2 ty3)) (funty (funty ty1 ty2) (funty ty1 ty3))). 
Proof. intros. eapply2 derive_instance. eapply2 derive_op. eapply2 instance_S. Qed. 


Lemma instance_S2 : 
forall ty, instance(opty Sop) ty -> wf ty -> 
exists (ty0 ty1 ty2 x0 x1 x7 x8: lamSF), 
ty = funty ty1 (funty ty0 (funty ty2 x8)) /\ 
instance ty2 x7 /\ 
instance ty0 (funty x7 x0) /\ 
instance ty1 (funty x7 (funty x0 x1)) /\ 
instance x1 x8. 
Proof. 
unfold opty, quant, funty; split_all. unfold funty in *.  inst_tac.
generalize H4; clear H4; subst_out; intro.
inst_tac. 
exist x4; exist x2; exist x3. 
exist x0; exist x1; exist x; exist x6. 
Qed. 

Lemma derive_rwf_S : 
forall gamma ty, derivation_rwf gamma s_op ty -> 
exists (ty0 ty1 ty2 x0 x1 x7 x8: lamSF), 
ty = funty ty1 (funty ty0 (funty ty2 x8)) /\ 
instance ty2 x7 /\ 
instance ty0 (funty x7 x0) /\ 
instance ty1 (funty x7 (funty x0 x1)) /\ 
instance x1 x8. 
Proof. split_all.  inversion H; subst. eapply2 instance_S2. Qed. 


Lemma instance_A : 
forall ty1 ty2, wfs ty1 -> wfs ty2 -> 
instance (opty Aop) (funty (funty ty1 ty2)  (funty ty1 ty2)).
Proof.
unfold instance; unfold_opty; split_all.  
instances (cons ty2 (cons ty1 nil)).
Qed.

Lemma derive_A : forall gamma ty1 ty2, wfc gamma -> wfs ty1 -> wfs ty2 -> 
derivation gamma a_op  (funty (funty ty1 ty2)  (funty ty1 ty2)).
Proof. intros. eapply2 derive_instance. eapply2 derive_op. eapply2 instance_A. Qed. 

Lemma instance_A2 : 
forall ty, instance(opty Aop) ty -> wf ty -> 
exists ty1 ty2 ty3, ty = funty ty1 (funty ty2 ty3) /\ instance ty1 (funty ty2 ty3).
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H; clear H; subst_out; intro.
generalize H3; clear H3; insert_Ref_out. rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
intro. inst_tac.
exist x1; exist x3; exist x4.
eapply2 transitive_red. 
eapply2 preserves_funty_instance. 
Qed. 


Lemma instance_K : 
forall ty1 ty2, wfs ty1 -> wfs ty2 -> instance (opty Kop) (funty ty1 (funty ty2 ty1)).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty1 (cons ty2 nil)). Qed.

Lemma derive_K : forall gamma ty1 ty2, wfc gamma -> wfs ty1 -> wfs ty2 ->  
derivation gamma k_op (funty ty1 (funty ty2 ty1)). 
Proof. intros. eapply2 derive_instance. eapply2 derive_op. eapply2 instance_K. Qed. 

Lemma instance_K2 : 
forall ty, instance(opty Kop) ty -> wf ty -> 
exists ty1 ty2 ty3, ty = funty ty1 (funty ty2 ty3) /\ instance ty1 ty3.
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H; clear H; subst_out; intro.
generalize H3; clear H3; insert_Ref_out. rewrite lift_rec_null. rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null. 
intro. inst_tac.
exist x1; exist x3; exist x4.
eapply2 transitive_red.
Qed. 


Lemma instance_E : 
forall ty1 ty2 ty3,  wfs ty1 -> wfs ty2 ->  wfs ty3 -> instance (opty Eop) (funty ty1 (funty ty2 (funty ty3 (funty ty3 ty3)))).
Proof.
unfold instance; unfold_opty; split_all; instances (cons ty1 (cons ty2 (cons ty3 nil))).
Qed.

Lemma derive_E : forall gamma ty0 ty1 ty2, wfc gamma ->  wfs ty0 -> wfs ty1 -> wfs ty2 ->   
derivation gamma e_op (funty ty0 (funty ty1 (funty ty2 (funty ty2 ty2)))).
Proof. intros. eapply2 derive_instance. eapply2 derive_op. eapply2 instance_E. Qed. 


Lemma instance_E2 : 
forall ty, instance(opty Eop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, 
wfs ty1 /\ wfs ty2 /\ wfs ty3 /\ wfs ty4 /\ wfs ty5 /\ 
ty = funty ty1 (funty ty2 (funty ty3 (funty ty4 ty5))) /\
instance ty3 ty5 /\ instance ty4 ty5.
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H4; clear H4; subst_out; intro.
inst_tac. 
exist x2; exist x4; exist x3; exist x5; exist x7;
try (eapply2 instance_implies_wfs; fail). 
inversion H12. eapply2 wf_implies_wfs. 
eapply2 transitive_red. eapply2 transitive_red. 
Qed. 

Lemma derive_rwf_E : 
forall gamma ty, derivation_rwf gamma e_op ty -> 
exists ty1 ty2 ty3 ty4 ty5, 
wfs ty1 /\ wfs ty2 /\ wfs ty3 /\ wfs ty4 /\ wfs ty5 /\ 
ty = funty ty1 (funty ty2 (funty ty3 (funty ty4 ty5))) /\
instance ty3 ty5 /\ instance ty4 ty5.
Proof. split_all. inversion H; subst. eapply2 instance_E2. Qed. 

Lemma instance_G : 
forall ty1 ty2, wfs ty1 -> wfs ty2 ->  instance (opty Gop) 
                  (funty (Abs (funty (funty (varty 0) (lift 1 ty1)) (funty (varty 0) (lift 1 ty2))))(funty ty1  ty2)).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty1 (cons ty2 nil)). Qed.

Lemma derive_G : forall gamma ty1 ty2,  wfc gamma -> wfs ty1 -> wfs ty2 ->  
derivation gamma g_op (funty (Abs (funty (funty (varty 0) (lift 1 ty1)) (funty (varty 0) (lift 1 ty2)))) (funty ty1 ty2)). 
Proof. intros.  eapply2 derive_instance. eapply2 derive_op. eapply2 instance_G. Qed.

Lemma instance_G2 : 
forall ty, instance(opty Gop) ty -> wf ty -> 
exists ty1 ty2 ty3, ty = funty ty1 (funty ty2 ty3) /\ 
instance ty1 (Abs (funty (funty (varty 0) (lift 1 ty2)) (funty (varty 0) (lift 1 ty3)))). 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H3; clear H3; subst_out; intro.
match goal with 
| H : instance (App (App (Op Sop) ?ty11) ?ty12) ?ty2 |- _ => 
generalize H; clear H; subst_out; intro target; 
assert(exists ty21 ty22, ty2 = funty ty21 ty22 /\ instance ty21 ty11 /\ instance  ty12 ty22)
end. 
eapply2 instance_preserves_funty. split_all; subst.  
clear target. 
inst_tac.
exist x1; exist x3; exist x4.
eapply transitive_red. eexact H2. 
eapply2 preserves_abs_multi_step. red; split_all.
eapply preserves_funty_instance.  eapply2 wfs_funty.  eapply2 wfs_funty. 
eapply preserves_funty_r_instance.  eapply2 wfs_var. eapply2 lift_rec_preserves_instance. 
eapply preserves_funty_r_instance.  eapply2 wfs_var. eapply2 lift_rec_preserves_instance. 
Qed. 

Lemma derive_rwf_G : 
forall gamma ty, derivation_rwf gamma g_op ty -> 
exists ty1 ty2 ty3, ty = funty ty1 (funty ty2 ty3) /\ 
instance ty1 (Abs (funty (funty (varty 0) (lift 1 ty2)) (funty (varty 0) (lift 1 ty3)))). 
Proof. split_all. inversion H; subst. eapply2 instance_G2. Qed. 



Lemma instance_Q : 
forall ty1 ty2, wfs ty1 -> wfs ty2 ->  instance (opty Qop) 
                 (funty (Abs (funty (varty 0) (lift 1 ty2)))
                          (funty      (funty ty2 (funty ty2 ty2))                        
                  (funty ty1 ty2))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty1 (cons ty2 nil)). Qed.

Lemma derive_Q : forall gamma ty1 ty2,  wfc gamma -> wfs ty1 -> wfs ty2 ->  
derivation gamma q_op (funty (Abs (funty (varty 0) (lift 1 ty2))) 
                 (funty (funty ty2 (funty ty2 ty2)) 
                        (funty ty1 ty2))).
Proof. intros.  eapply2 derive_instance. eapply2 derive_op. eapply2 instance_Q. Qed.

Lemma instance_Q2 : 
forall ty, instance(opty Qop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty5)) /\ 
instance ty4 ty5 /\
instance ty2 (funty ty4 (funty ty4 ty4)) /\ 
instance ty1 (Abs (funty (varty 0) (lift 1 ty4))). 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H3; clear H3; subst_out; intro.
inst_tac. 
exist x1; exist x3; exist x2; exist x0; exist x5.
Qed. 

Lemma instance_U : 
forall ty1, wfs ty1 ->  instance (opty Uop) 
                 (funty (Abs (Abs (funty (varty 1) 
                                         (funty (funty (varty 0) (varty 1))
                                                (funty (varty 0) (varty 1))))))
                         (funty ty1 ty1)). 
Proof. unfold instance; unfold_opty; split_all; instances (cons ty1 nil). Qed.

Lemma derive_U : forall gamma ty1,  wfc gamma -> wfs ty1 ->  
derivation gamma u_op 
                 (funty (Abs (Abs (funty (varty 1) 
                                         (funty (funty (varty 0) (varty 1))
                                                (funty (varty 0) (varty 1))))))
                        (funty ty1 ty1)). 
Proof. intros.  eapply2 derive_instance. eapply2 derive_op. eapply2 instance_U. Qed.

Lemma instance_U2 : 
forall ty, instance(opty Uop) ty -> wf ty -> 
exists ty1 ty2 ty3, ty = funty ty1 (funty ty2 ty3) /\ 
instance ty2 ty3 /\
instance ty1 (Abs (Abs (funty (varty 1) 
                                         (funty (funty (varty 0) (varty 1))
                                                (funty (varty 0) (varty 1)))))). 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac. 
exist x0; exist x2; exist x3. eapply2 transitive_red. 
Qed. 


Lemma instance_Y : 
forall ty, wfs ty -> 
instance (opty Yop) (funty (funty ty ty)  ty).
Proof.
unfold instance; unfold_opty; split_all.  
instances (cons ty nil).
Qed.

Lemma derive_Y : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma y_op  (funty (funty ty ty)  ty).
Proof. intros. eapply2 derive_instance. eapply2 derive_op. eapply2 instance_Y. Qed. 

Lemma instance_Y2 : 
forall ty, instance(opty Yop) ty -> wf ty -> 
exists ty1 ty2 ty3, ty = funty ty1 ty2 /\ 
instance ty1 (funty ty3 ty3) /\ 
instance ty3 ty2. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x1; exist x.
Qed. 


Lemma instance_DS : 
forall ty, wfs ty -> instance (opty DSop) (funty (opty Sop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DS : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DSop) (funty (opty Sop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DS. Qed.

Lemma instance_DS2 : 
forall ty, instance(opty DSop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Sop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DA : 
forall ty, wfs ty -> instance (opty DAop) (funty (opty Aop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DA : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DAop) (funty (opty Aop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DA. Qed.

Lemma instance_DA2 : 
forall ty, instance(opty DAop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Aop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DK : 
forall ty, wfs ty -> instance (opty DKop) (funty (opty Kop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DK : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DKop) (funty (opty Kop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DK. Qed.

Lemma instance_DK2 : 
forall ty, instance(opty DKop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Kop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DE : 
forall ty, wfs ty -> instance (opty DEop) (funty (opty Eop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DE : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DEop) (funty (opty Eop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DE. Qed.

Lemma instance_DE2 : 
forall ty, instance(opty DEop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Eop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DG : 
forall ty, wfs ty -> instance (opty DGop) (funty (opty Gop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DG : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DGop) (funty (opty Gop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DG. Qed.

Lemma instance_DG2 : 
forall ty, instance(opty DGop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Gop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DQ : 
forall ty, wfs ty -> instance (opty DQop) (funty (opty Qop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DQ : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DQop) (funty (opty Qop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DQ. Qed.

Lemma instance_DQ2 : 
forall ty, instance(opty DQop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Qop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DU : 
forall ty, wfs ty -> instance (opty DUop) (funty (opty Uop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DU : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DUop) (funty (opty Uop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DU. Qed.

Lemma instance_DU2 : 
forall ty, instance(opty DUop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Uop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 


Lemma instance_DY : 
forall ty, wfs ty -> instance (opty DYop) (funty (opty Yop) (funty (funty ty ty) (funty ty ty))).
Proof. unfold instance; unfold_opty; split_all; instances (cons ty nil). Qed. 

Lemma derive_DY : forall gamma ty, wfc gamma -> wfs ty -> 
derivation gamma (Op DYop) (funty (opty Yop) (funty (funty ty ty) (funty ty ty))).
Proof. intros.  eapply2 derive_instance. eapply2 instance_DY. Qed.

Lemma instance_DY2 : 
forall ty, instance(opty DYop) ty -> wf ty -> 
exists ty1 ty2 ty3 ty4 ty5, ty = funty ty1 (funty ty2 (funty ty3 ty4)) /\ 
instance ty3 ty5 /\ 
instance ty2 (funty ty5 ty5) /\ 
instance ty1 (opty Yop) /\ 
instance ty5 ty4. 
Proof. 
unfold opty, quant; split_all. inst_tac.
generalize H2; clear H2; subst_out; intro.
inst_tac.
exist x0; exist x2; exist x1; exist x4; exist x.
Qed. 



Hint Resolve derive_S derive_A derive_K. 

Lemma derive_SKX : 
forall gamma t ty ty2, wfs ty -> derivation gamma t (funty ty ty2) -> 
derivation gamma (App (App s_op k_op) t) (funty ty ty).
Proof. 
split_all; unfold_op. 
assert(wfs (funty ty ty2)) by eapply2 derive_implies_wfcs. inversion H1; auto. subst. 
eapply2 derive_app.  
eapply2 derive_app. 
eapply2 derive_S. 
eapply2 derive_implies_wfcs. 
eapply2 derive_K. eapply2 derive_implies_wfcs.
Qed. 


Lemma derive_I : 
forall gamma ty, wfc gamma -> wfs ty -> derivation gamma i_op (funty ty ty).
Proof. split_all; unfold_op. eapply2 derive_SKX.  Qed. 


Hint Resolve derive_I. 

Lemma derive_KI : 
forall gamma ty, wfc gamma -> wfs ty -> derivation gamma (App k_op i_op) (funty ty (funty ty ty)).
Proof. split_all; unfold_op. repeat eapply2 derive_app; simpl; repeat rewrite pull_wf2; simpl;
unfold lift; repeat rewrite lift0_context; repeat rewrite lift_rec_null. 
Qed. 

 

Lemma derive_abs_left : 
forall gamma ty1 ty2,  wfc gamma -> wfs ty1 -> wfs ty2 -> derivation gamma abs_left (funty (funty ty1 ty2) (funty ty1 ty2)).
Proof. unfold_op; split_all.  Qed. 

Lemma derive_star : 
forall gamma M ty, derivation gamma M ty -> 
forall ty0 gamma0, gamma = ty0 :: gamma0 -> 
derivation gamma0 (star M) (funty ty0 ty). 
Proof. 
intros gamma M ty d; induction d; split_all; subst.
(* 8 *) 
inversion H; subst. eapply2 derive_app. eapply2 derive_K. 
case o; unfold opty, funty; wfcs_tac. 
(* 7 *) 
inversion H1; subst; auto. 
(* 6 *) 
inversion H0; subst; auto.  eapply2 derive_app. 
eapply2 derive_K; eapply2 derive_implies_wfcs. 
(* 5 *) 
eapply derive_app. 
eapply derive_A. 
assert(wfc  (ty1 :: ty0 :: gamma0)) by eapply2 derive_implies_wfcs.
inversion H. inversion H3; auto. 
assert(wfc  (ty1 :: ty0 :: gamma0)) by eapply2 derive_implies_wfcs.
inversion H. inversion H3; auto. 
assert(wfc (ty1 :: ty0 :: gamma0) /\ wfs ty2) by eapply2 derive_implies_wfcs. 
split_all. inversion H0. wfcs_tac. 
 eapply2 derive_abs. 
(* 4 *) 
eapply2 derive_app. eapply2 derive_app. eapply2 derive_S.
assert(wfc (ty0 :: gamma0)) by eapply2 derive_implies_wfcs. inversion H; auto. 
assert(wfc (ty0 :: gamma0)) by eapply2 derive_implies_wfcs. inversion H; auto. 
assert(wfs (funty ty1 ty2)) by eapply2 derive_implies_wfcs. inversion H; auto. 
assert(wfs (funty ty1 ty2)) by eapply2 derive_implies_wfcs. inversion H; auto. 
(* 3 *)
apply derive_inst with (funty ty0 ty1); auto.  unfold funty; auto. 
eapply2 instance_funty. 
assert(wfc (ty0 :: gamma0)) by eapply2 derive_implies_wfcs. inversion H0; auto. 
(* 2 *) 
apply derive_push1  with (Abs (funty (lift 1 ty0) ty)); auto. 
replace (funty (lift 1 ty0) ty) with (App (lift 1 (App s_op ty0)) ty) by auto.
eapply2 push_lift.
assert(wfc (ty0 :: gamma0)) by eapply2 derive_implies_wfcs. inversion H; auto. 
 eapply2 derive_implies_wfcs. 
(* 1 *) 
eapply2 derive_push1. unfold funty; auto. eapply2 push_funty. 
assert(wfc (ty0 :: gamma0)) by eapply2 derive_implies_wfcs. inversion H0; auto. 
Qed. 



Lemma instance_opty : forall o, instance (opty o) (snd (pull (opty o))).
Proof.
induction o; unfold opty at 2; unfold op_abs, quant, opty_core, opty_core0.
eapply2 instance_S. 
eapply2 instance_A. 
eapply2 instance_K; unfold varty, lift; split_all. 
eapply2 instance_E; unfold varty, lift; split_all. 
(* G *) 
simpl. unfold lift; repeat rewrite lift_rec_null. 
replace (varty 1) with (lift 1(varty 0)) by auto. 
replace (varty 2) with (lift 1(varty 1)) by auto. 
eapply2 instance_G. 
unfold lift; auto. 
(* Q *) 
simpl. unfold lift; repeat rewrite lift_rec_null. 
replace (varty 1) with (lift 1(varty 0)) by auto. 
eapply2 instance_Q. 
unfold lift; auto. 
(* U *) 
simpl. unfold lift; repeat rewrite lift_rec_null. 
replace (varty 1) with (lift 1(varty 0)) by auto. 
replace (varty 2) with (lift 1(varty 1)) by auto. 
eapply2 instance_U. 
unfold lift; auto. 
(* Y *) 
simpl. unfold lift; repeat rewrite lift_rec_null. 
eapply2 instance_Y. 
unfold lift; auto. 
(* DS *) 
eapply2 instance_DS. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DA. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DK. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DE. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DG. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DQ. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DU. unfold funty, varty; unfold_op. simpl. unfold lift; auto. 
eapply2 instance_DY.
Qed. 


Lemma derive_other_left : 
forall gamma ty, wfc gamma -> wfs ty -> derivation gamma other_left (funty ty ty).
Proof. split_all; unfold other_left. eapply derive_SKX. auto. eapply2 derive_I.  Qed.

Lemma derive_compounds0 : 
forall gamma P ty, derivation gamma P ty -> 
                   derivation gamma (App (left_component P) (right_component P)) ty.
Proof. 
intros gamma P ty d; induction d; split_all; eauto.
(* 4 *) 
eapply derive_app. eapply derive_app. eapply derive_K. auto. case o; unfold_opty; wfcs_tac. 
2: auto.  2: eapply2 derive_K. wfcs_tac. 
(* 3 *) 
eapply derive_app. 2: auto. eapply derive_other_left.  wfcs_tac. auto. 
(* 2 *) 
eapply derive_app. 2: eapply derive_weak. 2: eexact d. 2: auto. eapply2 derive_other_left.  
wfcs_tac. eapply2 derive_implies_wfcs. eapply2 derive_implies_wfcs. 
(* 1 *) 
assert(wfc (ty1 :: gamma) /\ wfs ty2) by eapply2 derive_implies_wfcs. 
split_all. inversion H0; subst.  
eapply derive_app.  eapply2 derive_abs_left.  eapply2 derive_star. 
Grab Existential Variables. apply 0. apply 0. 
Qed. 


Lemma derive_compounds : 
forall gamma P ty, derivation gamma P ty -> wf ty -> 
exists ty0, derivation gamma (right_component P) ty0 /\ 
            derivation gamma (left_component P) (funty ty0 ty).
Proof. 
split_all. 
assert( derivation gamma (App (left_component P) (right_component P)) ty) 
by eapply2 derive_compounds0. 
assert(derivation_rwf gamma (App (left_component P) (right_component P)) ty) 
by eapply2 derivation_implies_derivation_rwf_wf. 
inversion H2; subst. 
exist ty1.
eapply2 rwf_implies_derive. 
Qed. 
