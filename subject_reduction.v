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
(*                   subject_reduction.v                              *)
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
Require Import operator_types.


Ltac var_tac := repeat eapply2 derive_weak; try eapply2 derive_var; wfcs_tac.  

Ltac derive_tac := unfold_op; wfcs_tac; match goal with 
| |- derivation _ _  (Abs _) => eapply derive_gen1; derive_tac
| |- derivation _ (Ref _) _ => var_tac; derive_tac 
| |- derivation _ (Op Sop) _ => eapply2 derive_S; derive_tac 
| |- derivation _ (Op Aop) _ => eapply2 derive_A; derive_tac 
| |- derivation _ (Op Kop) _ => eapply2 derive_K; derive_tac 
| |- derivation _ (Op Eop) _ => eapply2 derive_E; derive_tac 
| |- derivation _ (Op Gop) _ => eapply2 derive_G; derive_tac 
| |- derivation _ (Op Yop) _ => eapply2 derive_Y; derive_tac 
| |- derivation _ i_op _ => eapply2 derive_I; derive_tac 
| |- derivation _ (App k_op i_op) _ => eapply2 derive_KI; derive_tac 
| |- derivation _ (App _ _) _ => eapply derive_app; var_tac; derive_tac 
| |- derivation _ (Abs _) _ => eapply derive_abs; derive_tac 
| _ => idtac
end. 



Lemma derive_ops : 
forall gamma t ty, derivation gamma t ty -> 
forall o t2, t = Op o -> derivation gamma t2 (opty o) -> 
derivation gamma t2 ty. 
Proof. 
intros gamma t ty d; induction d; split_all; subst. 
(* 3 *) 
eapply derive_inst.  2: eexact H. eapply2 IHd. 
(* 2 *) 
eapply2 derive_gen1 . eapply2 IHd. 
replace (opty o) with (lift 1 (opty o)) by (case o; auto). 
eapply2 lift_rec_ty_preserves_derive. 
(* 1 *) 
eapply derive_push1. 2: eauto. eapply2 IHd. 
Qed. 


Lemma derive_append: 
forall gamma t ty, derivation gamma t ty -> forall gamma2, wfc gamma2 -> derivation (gamma ++ gamma2) t ty. 
Proof. 
intros gamma t ty d; induction d; split_all; subst.
(* 7 *)
eapply2 derive_op.  eapply2 append_preserves_wfc. 
(* 6 *) 
derive_tac.  eapply2 append_preserves_wfc. 
(* 5 *) 
eapply2 derive_abs. 
(* 4 *) 
eapply2 derive_app. 
(* 3 *) 
eapply2 derive_inst. 
(* 2 *) 
eapply2 derive_gen1. 
rewrite map_app. eapply2 IHd. 
unfold lift. eapply2 lift_rec_preserves_wfc.  
(* 1 *) 
eapply2 derive_push1. 
Qed. 

Lemma derive_nil: 
forall t ty, derivation nil t ty -> forall gamma, wfc gamma -> derivation gamma t ty. 
Proof. split_all. replace gamma with (nil ++ gamma) by auto. eapply2 derive_append.  Qed. 



Theorem reduction_preserves_derivation : 
forall t gamma ty, derivation gamma t ty -> forall t1, lamSF_red1 t t1 -> derivation gamma t1 ty.
Proof. 
cut(forall t,  
((forall gamma ty, derivation_rwf gamma t ty -> 
                   forall t1, lamSF_red1 t t1 -> derivation_rwf gamma t1 ty) -> 
 (forall gamma ty, derivation gamma t ty -> 
                   forall t1, lamSF_red1 t t1 -> derivation gamma t1 ty)) 
/\
(forall gamma ty, derivation_rwf gamma t ty -> 
                  forall t1, lamSF_red1 t t1 -> derivation_rwf gamma t1 ty)).
intro aux; split_all; eapply2 aux; eapply2 aux. 

rank_tac. 
intro rk; split.
(* 2 *) 
split_all. 
assert(derivation_rwf (map (lift(fst (pull ty))) gamma) t (snd (pull ty))). 
eapply2 resi_implies_rwf. 
eapply2 derivation_implies_derivation_resi. 
eapply2 derive_implies_wfcs. 
eapply2  derive_pull. 
eapply2 rwf_implies_derive. eapply2 derive_implies_wfcs. 
(* 1 *) 
intros gamma ty d; induction d; intros t1 r; split_all; try (inversion r; fail).
(* 2 *)
inversion r; subst. eapply2 rwf_abs. eapply2 IHd. simpl in *; omega. 
(* 1 *) 
inversion r; subst. 
(* 31 *) 
eapply2 rwf_app. eapply2 IHd. simpl in *; omega. 
(* 30 *) 
eapply2 rwf_app. eapply2 IHp. simpl in *; omega. eapply2 IHp. simpl in *; omega. 
(* 29 beta *)
inversion d; subst. 
eapply2 derivation_implies_derivation_rwf_wf.
unfold subst. replace gamma with (removen 0 (ty1 :: gamma)) by auto. 
eapply2 subst_rec_preserves_derive.
eapply2 rwf_implies_derive. 
split_all; omega. 
eapply2 rwf_implies_wf. 
(* 28 Sop *)
inversion d; subst. 
inversion H3; subst.
inversion H4; subst. 
elim(instance_S2  (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all.
inversion H6; subst. 
repeat(eapply2 rwf_app). 
unfold funty in *; inv1 wf; subst. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H7. 
eapply transitive_red. eexact H10. 
eapply transitive_red. 
eapply preserves_contra_instance. eapply2 wfs_funty. 
assert(wfs  (App (App s_op x4) x2)). eapply2 (instance_implies_wfs x). 
inversion H8; auto.  
 eapply2 (instance_implies_wfs x3 x5).
eapply2 wf_implies_wfs. 
eexact H0. 
eapply preserves_funty_r_instance. auto. 
eapply preserves_funty_r_instance. 
assert(wfs  (App (App s_op x4) x2)). eapply2 (instance_implies_wfs x). 
inversion H8; auto.  
auto.  
eapply2 wf_funty. 
eapply2 wf_funty. 
assert(wfs  (App (App s_op x4) x2)). eapply2 (instance_implies_wfs x). 
inversion H8; auto.  
eapply2 derive_app.
eapply derive_instance. eexact H5. 
eapply transitive_red. 
eexact H9. 
eapply2 preserves_contra_instance. 
assert(wfs  (App (App s_op x4) x2)). eapply2 (instance_implies_wfs x). 
inversion H8; auto; subst.  inversion H15; subst. auto. 
inversion H11. auto. 
(* 27 A *) 
inversion d; subst. 
inversion H3; subst.
inversion H4; subst. 
elim(instance_A2  (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all.
inversion H6; subst. 
repeat(eapply2 rwf_app). 
unfold funty in *; inv1 wf; subst. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H7. 
eapply transitive_red. eexact H9.  auto. 
eapply2 wf_funty. 
eapply2 wf_funty. 
(* 26  K *)
inversion d; subst. 
inversion H3; subst.
elim(instance_K2 (funty ty0 (funty ty1 ty2))); split_all.
inversion H4; subst. 
unfold funty in *; inv1 wf; subst. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H5. auto. 
(* 25 E op *) 
inversion d; subst. 
inversion H3; subst.
elim(instance_E2 (funty ty0 (funty ty1 ty2))); split_all; subst. 
inversion H10; subst. 
eapply2 rwf_op. 
eapply transitive_red. 
eapply instance_K. 
3: eapply preserves_funty_instance. 
6: eapply zero_red. 
auto. auto. auto. auto. auto. eapply2 wf_funty. eapply2 wf_funty. 
inversion H6. inversion H16. inversion H20. inversion H24. auto. 
(* 24 op unequal *) 
inversion d; subst. 
inversion H5; subst.
simpl in *.
elim(instance_E2 (funty ty0 (funty ty1 ty2))); split_all; subst. 
inversion H12; subst. 
eapply rwf_app.
2: eapply2 (derive_I gamma x3). 
eapply2 rwf_op. 
eapply transitive_red. 
2:eapply2 preserves_contra_instance. 
2:eapply2 preserves_contra_instance. 
eapply2 instance_K. 
eapply2 wf_funty. eapply2 wf_funty. eapply2 wf_funty.
inversion H8; subst.   inversion H18; subst. inversion H20; subst. inversion H22; subst. auto. 
(* 23 equal compound *) 
inversion d; subst.
elim(instance_E2 (funty ty1 ty2)); split_all; subst. 
inversion H9; subst. 
eapply rwf_app.
2: eapply (derive_KI gamma). 
eapply rwf_op.
instantiate(1:= x3).  
eapply transitive_red. eapply instance_K. 
instantiate(1:= funty x3 (funty x3 x3)). wfcs_tac. 
2: eapply preserves_funty_r_instance. 
2: wfcs_tac. 
2: eapply2 preserves_funty_r_instance. 
auto. 
eapply2 preserves_funty_instance. 
eapply2 preserves_contra_instance. 
wfcs_tac. 
wfcs_tac. 
inversion H5. inversion H15. inversion H19. inversion H23; auto. 
wfcs_tac. auto. 
(* 22 G *) 
inversion d; subst. 
inversion H4; subst. 
elim(instance_G2 (funty ty0 (funty ty1 ty2))); split_all.
inversion H5; subst. 
assert(wfs x0) by eapply2 derive_implies_wfcs. 
assert(derivation (map (lift (fst (pull x0))) gamma) u (lift(fst (pull x0)) x0)).
unfold lift; eapply2 lift_rec_ty_preserves_derive. 
assert(derivation (map (lift (fst (pull x0))) gamma) u (snd (pull x0))).
eapply2 derive_instance. eapply2 instance_pull. 
assert(exists ty0, derivation (map (lift (fst (pull x0))) gamma) (right_component u) ty0 /\ 
            derivation (map (lift (fst (pull x0))) gamma) (left_component u) (funty ty0 (snd(pull x0)))). eapply2 derive_compounds. 
eapply2 pull_wf. 
split_all. 

assert(derivation  (map (lift (fst (pull x0))) gamma) 
          (left_component u) (funty (lift(fst (pull x0)) (quant (fst (pull x0)) x2)) (snd (pull x0)))). 
eapply2 derive_instance. 
eapply2 preserves_contra_instance.
eapply2 pull_preserves_wfs. 
eapply2 instance_quant_lift2. 
eapply2 derive_implies_wfcs. 
assert(derivation gamma (left_component u) (quant (fst (pull x0)) (funty (lift (fst (pull x0)) (quant (fst (pull x0)) x2))
             (snd (pull x0)))))
 by eapply2 derive_gen. 
assert(derivation gamma (left_component u) (funty (quant (fst (pull x0)) x2) (quant (fst (pull x0)) 
             (snd (pull x0)))))
 . eapply2 derive_push. eapply2 push_quant. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 pull_preserves_wfs. 
assert(derivation gamma (left_component u) (funty (quant (fst (pull x0)) x2) x0)). 
eapply2 derive_push. 
eapply2 preserves_funty_r_push.  
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 quant_pull.

eapply2 rwf_app. 
eapply2 rwf_app. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H6. 
eapply transitive_red. eexact H8. 
eapply succ_red. 
eapply instance_rule. 
2: repeat(eapply2 wfs_funty); unfold lift; eapply2 lift_rec_preserves_wfs.  
3: unfold subst; simpl; insert_Ref_out; rewrite lift_rec_null; 
rewrite subst_rec_lift_rec; try omega; rewrite lift_rec_null;
repeat (eapply2 preserves_funty_r_instance). 
eapply2 quant_preserves_wfs. 
eapply2 derive_implies_wfcs. 
inversion H7. inversion H20. eapply2 wf_implies_wfs. 
eapply2 wfs_funty. 
eapply2 quant_preserves_wfs. 
eapply2 derive_implies_wfcs. 
eapply2 quant_preserves_wfs. 
eapply2 derive_implies_wfcs. 
rewrite subst_rec_lift_rec; try omega.  rewrite lift_rec_null. eapply2 zero_red. 
repeat (eapply2 wf_funty). 
repeat (eapply2 wfs_funty). 
eapply2 quant_preserves_wfs. 
eapply2 derive_implies_wfcs. 
eapply2 quant_preserves_wfs. 
eapply2 derive_implies_wfcs. 
inversion H7. inversion H20. auto. 
eapply2 derive_gen. 
(* 21 Q op *) 
inversion d; subst. 
inversion H3; subst. 
elim(instance_Q2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all.
inversion H1; subst. 
repeat(eapply2 rwf_app). 
unfold funty in *; inv1 wf; subst. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H7. 
eapply transitive_red. eexact H8.
eapply succ_red.  eapply instance_rule. 
instantiate(1:= x1). eapply2 derive_implies_wfcs. 
wfcs_tac. 
eapply lift_rec_preserves_wfs. 
assert(wfs (App (App s_op x2) (App (App s_op x2) x2))). 
eapply2 (instance_implies_wfs x0).  eapply2 derive_implies_wfcs. 
inversion H6. inversion H12; auto. 
unfold subst. simpl. insert_Ref_out. 
repeat rewrite subst_rec_lift_rec; try omega.  repeat rewrite lift_rec_null. 
eapply2 preserves_funty_instance. eapply2 derive_implies_wfcs. 
assert(wfs (App (App s_op x2) (App (App s_op x2) x2))). 
eapply2 (instance_implies_wfs x0).  eapply2 derive_implies_wfcs. 
inversion H6. auto. 
eapply2 zero_red. eapply2 wf_funty. eapply2 derive_implies_wfcs. 
assert(wf (App (App s_op x1) x3)) .  eapply2 rwf_implies_wf.  inversion H6. auto. 
inversion H4. auto. eapply2 rwf_implies_wf. 
(* 20 Q compound *) 
inversion d; subst. 
inversion H4; subst. 
inversion H5; subst. 
elim(instance_Q2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all.
inversion H7; subst. 
assert(wfs  (funty x2 (funty x2 x2))). 
eapply2 (instance_implies_wfs x0). eapply2 derive_implies_wfcs.  
inversion H11; auto; subst. 
assert(wfs x1) by eapply2 derive_implies_wfcs. 
assert(derivation (map (lift (fst (pull x1))) gamma) u (lift(fst (pull x1)) x1)).
unfold lift; eapply2 lift_rec_ty_preserves_derive. 
assert(derivation (map (lift (fst (pull x1))) gamma) u (snd (pull x1))).
eapply2 derive_instance. eapply2 instance_pull. 
assert(exists ty0, derivation (map (lift (fst (pull x1))) gamma) (right_component u) ty0 /\ 
            derivation (map (lift (fst (pull x1))) gamma) (left_component u) (funty ty0 (snd(pull x1)))). eapply2 derive_compounds. 
eapply2 pull_wf. 
split_all. 

assert(derivation  (map (lift (fst (pull x1))) gamma) 
          (left_component u) (funty (lift(fst (pull x1)) (quant (fst (pull x1)) x4)) (snd (pull x1)))). 
eapply2 derive_instance. 
eapply2 preserves_contra_instance.
eapply2 pull_preserves_wfs. 
eapply2 instance_quant_lift2. 
eapply2 derive_implies_wfcs. 
assert(derivation gamma (left_component u) (quant (fst (pull x1)) (funty (lift (fst (pull x1)) (quant (fst (pull x1)) x4))
             (snd (pull x1)))))
 by eapply2 derive_gen. 
assert(derivation gamma (left_component u) (funty (quant (fst (pull x1)) x4) (quant (fst (pull x1)) 
             (snd (pull x1)))))
 . eapply2 derive_push. eapply2 push_quant. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 pull_preserves_wfs. 
assert(derivation gamma (left_component u) (funty (quant (fst (pull x1)) x4) x1)). 
eapply2 derive_push. 
eapply2 preserves_funty_r_push.  
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 quant_pull.

eapply2 rwf_app. 
eapply2 rwf_app. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H6. 
eapply transitive_red. eexact H10. 
eapply preserves_funty_r_instance. 
assert(wfs  (funty x2 (funty x2 x2))).
wfcs_tac. auto. 
eapply2 preserves_funty_r_instance. 
wfcs_tac. 
assert(wf(funty x1 x3)).
eapply2 rwf_implies_wf. inversion H24; auto. 

eapply derive_app. instantiate(1:=   (funty (quant (fst (pull x1)) x4) x1)). 
eapply derive_app. instantiate(1:=  (funty x2 (funty x2 x2))). 
eapply derive_app. instantiate(1:=  (Abs (funty (varty 0) (lift 1 x2)))). 
eapply2 derive_instance.  eapply2 instance_Q. 
wfcs_tac. eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs.  
eapply2 derive_instance.  
eapply2 derive_instance.  
auto. 

eapply derive_app. instantiate(1:=   (quant (fst (pull x1)) x4)). 
eapply derive_app. instantiate(1:=  (funty x2 (funty x2 x2))). 
eapply derive_app. instantiate(1:=  (Abs (funty (varty 0) (lift 1 x2)))). 
eapply2 derive_instance.  eapply2 instance_Q. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs.  
eapply2 derive_instance.  
eapply2 derive_instance.  
eapply2 derive_gen. 

(* 19 U op *) 
inversion d; subst. 
inversion H3; subst. 
elim(instance_U2 (funty ty0 (funty ty1 ty2))); split_all.
inversion H4; subst. inversion H6; subst. inversion H11; subst. 
eapply2 derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H. auto. 
(* 18 U compound *) 
inversion d; subst. 
inversion H4; subst. 
elim(instance_U2 (funty ty0 (funty ty1 ty2))); split_all.
inversion H5; subst. 
inversion H7; subst. inversion H12; subst. 

assert(derivation (map (lift (fst (pull x0))) gamma) u (lift(fst (pull x0)) x0)).
unfold lift; eapply2 lift_rec_ty_preserves_derive. 
assert(derivation (map (lift (fst (pull x0))) gamma) u (snd (pull x0))).
eapply2 derive_instance. eapply2 instance_pull. 
assert(exists ty0, derivation (map (lift (fst (pull x0))) gamma) (right_component u) ty0 /\ 
            derivation (map (lift (fst (pull x0))) gamma) (left_component u) (funty ty0 (snd(pull x0)))). eapply2 derive_compounds. 
eapply2 pull_wf. 
split_all. 

assert(derivation  (map (lift (fst (pull x0))) gamma) 
          (left_component u) (funty (lift(fst (pull x0)) (quant (fst (pull x0)) x2)) (snd (pull x0)))). 
eapply2 derive_instance. 
eapply2 preserves_contra_instance.
eapply2 pull_preserves_wfs. 
eapply2 instance_quant_lift2. 
eapply2 derive_implies_wfcs. 
assert(derivation gamma (left_component u) (quant (fst (pull x0)) (funty (lift (fst (pull x0)) (quant (fst (pull x0)) x2))
             (snd (pull x0)))))
 by eapply2 derive_gen. 
assert(derivation gamma (left_component u) (funty (quant (fst (pull x0)) x2) (quant (fst (pull x0)) 
             (snd (pull x0)))))
 . eapply2 derive_push. eapply2 push_quant. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 pull_preserves_wfs. 
assert(derivation gamma (left_component u) (funty (quant (fst (pull x0)) x2) x0)). 
eapply2 derive_push. 
eapply2 preserves_funty_r_push.  
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 quant_pull.
assert(derivation gamma (right_component u) (quant (fst (pull x0)) x2)). eapply2 derive_gen.


eapply rwf_app. instantiate (1:= (quant (fst (pull x0)) x2)).
eapply rwf_app. instantiate (1:= (funty (quant (fst (pull x0)) x2) x1)).
eapply rwf_app. 
eapply derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H6. 
eapply transitive_red. eexact H9. 
assert(wfs x1) by eapply2 wf_implies_wfs. 
assert(wfs  (quant (fst (pull x0)) x2)). eapply2 quant_preserves_wfs. 
eapply2 derive_implies_wfcs. 
instances (cons x1 (cons (quant (fst (pull x0)) x2) nil)). 
eapply2 preserves_funty_r_instance. 
eapply2 preserves_contra_instance. 
eapply2 preserves_funty_r_instance. 
eapply2 zero_red.
wfcs_tac. 
eapply2 wf_implies_wfs. 
wfcs_tac. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
inversion H12; eapply2 wf_implies_wfs.  
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 derive_instance. 

eapply derive_app. 
eapply derive_app. 
eapply2 derive_instance. 
eapply2 instance_U. 
wfcs_tac. eapply2 quant_preserves_wfs.  eapply2 derive_implies_wfcs. 
auto.  eapply2 wf_implies_wfs.  eapply2 derive_instance. 
eapply2 derive_instance. eapply2 preserves_funty_r_instance. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 

eapply derive_app. 
eapply derive_app. 
eapply2 derive_instance. 
eapply2 instance_U. 
wfcs_tac. eapply2 quant_preserves_wfs.  eapply2 derive_implies_wfcs. 
eapply2 derive_instance. auto. 
(* 17 Yop *)
inversion d; subst. 
inversion H4; subst.
elim(instance_Y2 (funty ty1 ty2)); split_all.
invsub.
assert(wfs x1). 
eapply2 (instance_implies_wfs x1 x0). 
eapply2 wf_implies_wfs. 
eapply rwf_app.
eapply derivation_implies_derivation_rwf_wf. 
eapply derive_instance. 
eexact H.
eapply transitive_red. 
eexact H0. 
eapply2 preserves_funty_r_instance.
eapply2 wf_funty. 
eapply derive_app. 
2: eexact H. 
eapply derive_app. 
eapply derive_A. 
wfcs_tac. auto. 
eapply2 (instance_implies_wfs x1 x0). 
eapply2 wf_implies_wfs. 
eapply derive_instance. 
eapply derive_op. 
auto.
eapply transitive_red. 
eapply instance_Y. 
2: eapply preserves_contra_instance. 
auto. auto. auto. 
(* 16 DS *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DS2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Sop)). eapply2 derive_instance. 
assert(derivation gamma (Op Sop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 15  DS-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DS2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DA *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DA2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Aop)). eapply2 derive_instance. 
assert(derivation gamma (Op Aop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DA-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DA2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DK *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DK2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Kop)). eapply2 derive_instance. 
assert(derivation gamma (Op Kop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DK-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DK2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DE *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DE2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Eop)). eapply2 derive_instance. 
assert(derivation gamma (Op Eop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DE-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DE2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DG *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DG2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Gop)). eapply2 derive_instance. 
assert(derivation gamma (Op Gop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DG-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DG2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DQ *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DQ2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Qop)). eapply2 derive_instance. 
assert(derivation gamma (Op Qop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DQ-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DQ2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DU *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DU2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Uop)). eapply2 derive_instance. 
assert(derivation gamma (Op Uop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DU-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DU2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto. 
(* 14 DY *) 
inversion d; subst. inversion H3; subst. inversion H4; subst. 
elim(instance_DY2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H6; subst. 
inversion H8; auto. 
assert(wf (funty x1 x2)) by eapply2 rwf_implies_wf. inversion H13.  subst. 
assert(derivation gamma t1 (opty Yop)). eapply2 derive_instance. 
assert(derivation gamma (Op Yop) x2). eapply2 derive_instance. 
eapply2 transitive_red. 
assert(derivation gamma t1 x2) by eapply2 derive_via_op. 
assert(derivation_rwf (map (lift (fst (pull x2))) gamma) t1 (snd(pull x2))).
eapply2 derivation_implies_derivation_rwf. eapply2 derive_implies_wfcs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. 
inversion H16. auto. 
(* 13  DY-oth *) 
inversion d; subst. inversion H5; subst. inversion H6; subst. 
elim(instance_DY2 (funty ty3 (funty ty0 (funty ty1 ty2)))); split_all. 
inversion H8; subst. inversion H10. inversion H17. inversion H21; subst. 
assert(derivation gamma (App N u) x2). 
eapply derive_app. 
eapply derive_instance. eexact H7. 
eapply transitive_red. eexact H11. eapply preserves_funty_r_instance. 
eapply2 (instance_implies_wfs x1). auto. 
eapply derive_instance. eexact H. auto. 
assert(derivation_rwf  (map (lift (fst (pull x2))) gamma) (App N u) (snd(pull x2))). 
eapply2 derivation_implies_derivation_rwf. 
eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *. simpl in *. rewrite lift0_context in *. auto. auto.
Qed. 
