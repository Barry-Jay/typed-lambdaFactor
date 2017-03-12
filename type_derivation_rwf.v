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
(*                  type_derivation_rwf.v                             *)
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
(* 
Require Import LamSF_Compound_decidable. 
*) 
Require Import LamSF_Closed.
Require Import type_derivation.
Require Import type_derivation_resi.

(* To reverse instantiation, define pull. *) 

Inductive derivation_rwf : context -> lamSF -> lamSF -> Prop := 
| rwf_op : forall gamma o ty,  instance (opty o) ty -> wfc gamma -> wf ty -> 
                                   derivation_rwf gamma (Op o) ty 
| rwf_var : forall gamma ty1 ty2,  instance ty1 ty2 -> wf ty2 -> wfc gamma -> 
                                       derivation_rwf (cons ty1 gamma) (Ref 0) ty2
| rwf_weak : forall gamma i ty1 ty,  derivation_rwf gamma (Ref i) ty -> wfs ty1 -> 
                                 derivation_rwf (cons ty1 gamma) (Ref (S i)) ty
| rwf_abs : forall gamma ty1 ty2 t,   
                 derivation_rwf (cons ty1 gamma) t ty2 ->
                 derivation_rwf gamma (Abs t) (funty ty1 ty2)
| rwf_app: forall gamma t ty1 ty2 u,  
                derivation_rwf gamma t (funty ty1 ty2) -> 
                derivation gamma u ty1 -> (* note use of derivation here *) 
                derivation_rwf gamma (App t u) ty2
 .


Hint Resolve 
rwf_op rwf_var rwf_weak rwf_abs rwf_app (* rwf_gen1 rwf_push1 *) 
. 

Lemma rwf_implies_resi : 
forall gamma t ty, derivation_rwf gamma t ty -> derivation_resi gamma t ty.
Proof. 
intros gamma t ty d; induction d; split_all.
eapply2 resi_var.  eapply2 instance_implies_wfs. eapply2 wf_implies_wfs. 
eapply2 resi_app.
Qed. 

Definition succ_left (p: nat * lamSF) := (S (fst p), snd p).
 
Fixpoint pull ty := 
match ty with 
| Abs ty0 => succ_left (pull ty0)
| App (App (Op Sop) ty1) ty2 => (fst(pull ty2), 
                  funty (lift (fst(pull ty2)) ty1) (snd (pull ty2)))
| _ => (0,ty)
end.

Lemma lift_rec_preserves_pull: 
forall ty n k, pull(lift_rec ty n k) = 
               (fst (pull ty), lift_rec (snd (pull ty)) (fst(pull ty)+n) k). 
Proof.
induction ty; intros; try (split_all; fail).
(* 2 *)
unfold lift_rec; fold lift_rec. unfold pull; fold pull. 
rewrite IHty; split_all. unfold succ_left. simpl.
replace(fst (pull ty) + S n) with (S (fst (pull ty) + n)) by omega. auto.
(* 1 *)
induction ty1; try (split_all; fail).  
induction ty1_1; try (split_all; fail).  
induction o; try (split_all; fail).  
unfold lift; simpl. rewrite IHty2; split_all. 
unfold lift. rewrite lift_lift_rec; try omega. auto. 
Qed.

Lemma pull_preserves_wfs: forall ty, wfs ty -> wfs (snd (pull ty)).
Proof. 
intros ty w; induction w; split_all. 
eapply2 wfs_funty. unfold lift; eapply2 lift_rec_preserves_wfs. 
Qed. 

Lemma pull_reflects_wfs: forall ty, wfs (snd (pull ty)) -> wfs ty.
Proof. 
induction ty; try (split_all; fail). 
induction ty1; try (split_all; fail). 
induction ty1_1; try (split_all; fail). 
induction o; try (split_all; fail). 
split_all. inversion H; subst. eapply2 wfs_funty.
unfold lift in *; eapply2 lift_rec_reflects_wfs. 
Qed. 
 
Lemma quant_pull : 
forall ty, wfs ty -> push (quant (fst(pull ty)) (snd(pull ty))) ty.
Proof. 
induction ty; intros; try (split_all; try (eapply2 zero_red); fail).  
(* 2 *) 
 inversion H; auto. eapply2 preserves_abs_multi_step. red; split_all. eapply2 IHty.
(* 1 *) 
inversion H; subst; simpl. 
eapply transitive_red. 
eapply2 push_quant. eapply2 pull_preserves_wfs. 
eapply2 preserves_funty_r_push. 
Qed.

Lemma pull_wf : forall ty, wfs ty -> wf (snd (pull ty)).
Proof. 
induction ty; try(split_all; fail). 
simpl. intro. inversion H. 
intro; inversion H; auto. 
intro. inversion H; subst. split_all. eapply2 wf_funty.
unfold lift. eapply2 lift_rec_preserves_wfs. 
Qed.

Lemma pull_wf2: forall ty, wf ty -> pull ty = (0,ty). 
Proof.
induction ty; split_all; inv1 wf; subst; simpl.
rewrite IHty2; auto.
simpl. unfold lift; rewrite lift_rec_null; auto.
Qed.


Lemma pull_quant : 
forall j ty, pull(quant j ty) = (j + fst (pull ty), snd (pull ty)).
Proof.
induction j; split_all.
(* 2 *) 
case (pull ty); auto. 
(* 1 *) 
rewrite IHj; unfold succ_left; auto. 
Qed.


Lemma pull_rank: forall ty, wfs ty -> rank(snd(pull ty)) <= rank ty. 
Proof. 
intros ty w; induction w; try (split_all; fail). 
(* 2 *) 
unfold funty, s_op, pull; fold pull. unfold rank; fold rank. simpl. 
unfold lift; rewrite lift_rec_preserves_rank. omega. 
(* 1 *)
unfold funty, s_op, pull; fold pull. gen_case IHw (pull ty). omega. 
Qed. 




Lemma pull_opty : forall o, pull (opty o) = (op_abs o, opty_core o).
Proof. induction o; split_all. Qed. 


Lemma instance_quant_lift: 
forall n ty, wfs ty -> instance(quant n (lift n ty)) ty. 
Proof. 
induction n; split_all. 
(* 2 *) 
unfold lift; rewrite lift_rec_null; eapply2 zero_red. 
(* 1 *) 
apply succ_red with (subst (Ref 0) (quant n (lift (S n) ty))); auto.
eapply2 instance_rule.  eapply2 quant_preserves_wfs. 
unfold lift; eapply2 lift_rec_preserves_wfs. 
unfold subst, lift; rewrite subst_rec_preserves_quant. 
rewrite subst_rec_lift_rec; try omega. 
eapply2 IHn. 
Qed. 


Lemma instance_quant_lift2: 
forall n ty, wfs ty -> instance(lift n (quant n ty)) ty. 
Proof. 

split_all. 
unfold lift; simpl. 
rewrite lift_rec_preserves_quant. 
replace(n+0) with n by omega. 

induction n; split_all. 
(* 2 *) 
rewrite lift_rec_null; eapply2 zero_red. 
(* 1 *) 
eapply succ_red. 
eapply instance_rule. 
2: eapply2 quant_preserves_wfs. 
2: unfold subst. 2: rewrite subst_rec_preserves_quant. 
2: cut(n = n+0); [| omega]; intro aux; rewrite aux at 2. 
2: rewrite subst_rec_lift_rec3; try omega. 
auto. 
replace(n+0) with n by omega. 
auto. 
Qed. 


Lemma instance_any: 
forall j n ty, j>n -> wfs ty -> instance(quant j (Ref n)) ty. 
Proof. 
induction j; split_all; try noway. 
(* 1 *) 
cut(j=n \/ j>n); [| omega]. 
intro ch; inversion ch; subst; split_all. 
clear - H0; induction n; split_all. 
(* 3 *) 
red; one_step.
replace ty with (subst ty (Ref 0)). 
eapply2 instance_rule.  subst_out. 
(* 2 *) 
apply succ_red with (subst ty (Abs (quant n (Ref (S n))))); auto. 
eapply2 instance_rule. eapply2 wfs_abs. eapply2 quant_preserves_wfs. 
unfold subst; simpl; rewrite subst_rec_preserves_quant. simpl. 
insert_Ref_out. replace(n+1) with (S n) by omega. 
replace (multi_step instance1 (Abs (quant n (lift_rec ty 0 (S n)))) ty) 
with (instance(quant (S n) (lift (S n) ty)) ty) by auto. 
eapply2 instance_quant_lift. 
(* 1 *) 
apply succ_red with (subst (Ref 0) (quant j (Ref n))); auto. 
eapply2 instance_rule. eapply2 quant_preserves_wfs. 
unfold subst; simpl. rewrite subst_rec_preserves_quant. simpl. 
replace(j+0) with j by omega. 
insert_Ref_out.  eapply2 IHj. 
Qed. 






Lemma instance_pull: 
forall ty, wfs ty -> instance (lift (fst (pull ty)) ty) (snd (pull ty)). 
Proof. 
intros ty w; induction w; split_all. 
(* 3 *)
unfold lift; rewrite lift_rec_null; eapply2 zero_red. 
(* 2 *) 
unfold lift; simpl.
eapply2 preserves_funty_r_instance.
(* 1 *) 
unfold lift; split_all.
eapply succ_red. 
eapply instance_rule. 
2: eapply2 lift_rec_preserves_wfs. 
2: unfold subst; rewrite subst_rec_lift_rec5; eapply2 IHw. 
auto.
Qed. 

Lemma pull_preserves_push1: forall ty1 ty2, wfs ty1 -> push1 ty1 ty2 -> pull ty1 = pull ty2. 
Proof. 
intros ty1 ty2 w p; induction p; try (inv1 wfs; fail).
(* 3 *) 
simpl. 
unfold lift; rewrite lift_rec_lift_rec; try omega. 
replace(fst(pull ty2) +1) with (S(fst (pull ty2))) by omega. auto. 
(* 2 *) 
split_all. rewrite IHp. auto. inversion w; auto. 
(* 1 *) 
simpl. rewrite IHp; split_all. inversion w; auto. 
Qed. 


Lemma resi_implies_rwf: 
forall gamma t ty, derivation_resi gamma t ty -> wfs ty -> 
derivation_rwf (map (lift (fst (pull ty))) gamma) t (snd(pull ty)).
Proof. 
intros gamma t ty d; induction d; inv1 wfs. 
(* 7 *)
eapply2 rwf_op. 
eapply transitive_red.
replace (opty o) with (lift(fst (pull ty)) (opty o)) by (unfold lift; case o; split_all). 
unfold lift; eapply lift_rec_preserves_instance. 
eexact H. 
eapply2 instance_pull. 
unfold lift; eapply2 lift_rec_preserves_wfc. 
eapply2 pull_wf. 
(* 6 *) 
eapply2 rwf_var. 
eapply transitive_red; [| eapply instance_pull; auto]. 
unfold lift; eapply2 lift_rec_preserves_instance. 
eapply2 pull_wf. 
unfold lift; eapply2 lift_rec_preserves_wfc. 
(* 5 *) 
eapply2 rwf_weak. 
unfold lift; eapply2 lift_rec_preserves_wfs. 
(* 4 *) 
eapply2 rwf_abs. inversion H; subst. simpl in *. eapply2 IHd. 
(* 3 *) 
eapply2 rwf_app. simpl in *. 
assert(derivation_rwf (map (lift (fst (pull ty2))) gamma) t
          (funty (lift (fst (pull ty2)) ty1) (snd (pull ty2)))). 
eapply2 IHd. eapply2 wfs_funty. 
eapply2 derive_implies_wfcs. 
eexact H1. 
unfold lift; eapply2 lift_rec_ty_preserves_derive. 
(* 2 *) 
inversion H; subst. 
replace (map (lift (S (fst (pull ty)))) gamma) with (map (lift (fst (pull ty))) (map (lift 1) gamma)). 
eapply2 IHd. 
clear; induction gamma; split_all.  rewrite IHgamma. 
unfold lift; rewrite lift_rec_lift_rec; try omega. 
replace(fst(pull ty) +1) with (S(fst(pull ty))) by omega; auto. 
(* 1 *) 
rewrite <- (pull_preserves_push1 ty); auto. 
eapply2 IHd. 
assert(wfs ty /\ wfs ty2) by eapply2 push_implies_wfs. split_all. 
assert(wfs ty /\ wfs ty2) by eapply2 push_implies_wfs. split_all. 
Qed. 



Lemma rwf_implies_derive : 
forall ty gamma t, derivation_rwf gamma t ty -> derivation gamma t ty.
Proof. 
intros ty gamma t d; induction d; split_all. 
(* 3 *) 
eapply2 derive_instance. 
eapply2 derive_instance. eapply2 derive_var. eapply2 instance_implies_wfs. 
eapply2 wf_implies_wfs. 
eapply2 derive_app. 
Qed. 



Lemma derive_pull : 
forall gamma t ty, derivation (map (lift (fst (pull ty))) gamma) t (snd (pull ty)) -> 
wfs ty -> derivation gamma t ty.
Proof. 
cut(forall ty0 gamma0 t, derivation gamma0 t ty0 -> 
forall gamma ty, gamma0 = map (lift (fst (pull ty))) gamma -> ty0 = snd (pull ty) -> 
wfs ty -> derivation gamma t ty).
intro aux; split_all; eapply2 aux. 
intros ty0 gamma0 t d; induction d; split_all; subst.
(* 8 *) 
assert(wf (snd (pull ty))). eapply2 pull_wf. 
rewrite <- H1 in H0. 
gen2_case H0 H1 o; unfold opty, op_abs, quant in *; inv1 wf. 
simpl in *. 
(* 7 *)
gen_case H1 gamma0. inversion H1; subst. 
eapply derive_push. 2: eapply2 quant_pull. eapply derive_gen.
unfold map; fold map.  rewrite <- H4 . eapply2 derive_var. 
(* 6 *) 
gen_case H0 gamma0. inversion H0; subst. eapply2 derive_weak. 
unfold lift in H; eapply2 lift_rec_reflects_wfs. 
(* 5 *) 
eapply derive_push. 2: eapply2 quant_pull. rewrite <- H0. 
eapply derive_gen. eapply2 derive_abs. 
(* 4 *) 
eapply derive_push. 2: eapply2 quant_pull. eapply2 derive_gen. 
(* 3 *) 
eapply derive_push. 2: eapply2 quant_pull. eapply2 derive_gen. 
(* 2 *) 
assert(wf (snd (pull ty0))). eapply2 pull_wf. 
rewrite <- H0 in H. inv1 wf. 
(* 1 *) 
eapply derive_push. 2: eapply2 quant_pull. eapply2 derive_gen. 
Qed. 


Lemma derivation_implies_derivation_rwf:
forall gamma t ty, derivation gamma t ty -> wfs ty -> 
derivation_rwf (map (lift (fst (pull ty))) gamma) t (snd(pull ty)).
Proof. split_all. eapply2 resi_implies_rwf. eapply2 derivation_implies_derivation_resi. Qed. 

Lemma derivation_implies_derivation_rwf_wf:
forall gamma t ty, derivation gamma t ty -> wf ty -> 
derivation_rwf gamma t ty. 
Proof. 
split_all. 
assert(derivation_rwf (map (lift (fst (pull ty))) gamma) t (snd(pull ty))).
eapply2 derivation_implies_derivation_rwf. eapply2 wf_implies_wfs. 
rewrite pull_wf2 in *; simpl in *; split_all. rewrite lift0_context in H1; auto. 
Qed. 


Lemma rwf_implies_wfcs: forall gamma t ty, derivation_rwf gamma t ty -> wfc gamma /\  wfs ty. 
Proof. 
intros gamma t ty d; induction d; split_all.
(* 6 *)  
case o; split_all; unfold opty, funty; split_all; unfold funty;  
repeat (eapply2 wfs_abs); repeat (eapply2 wfs_funty); repeat (eapply2 wf_implies_wfs). 
(* 5 *) 
eapply2 wfc_cons. eapply2 instance_implies_wfs; eapply2 wf_implies_wfs. 
(* 4 *)
assert((wfs ty1 -> wfs ty2) /\ (wfs ty2 -> wfs ty1)). 
eapply2 instance_implies_wfs; split_all. eapply2 wf_implies_wfs. 
(* 3 *) 
inversion H; subst. auto. 
(* 2 *)
inversion H; subst. eapply2 wfs_funty.  
(* 1 *) 
inversion H1; auto. 
Qed. 


Lemma rwf_implies_wf: forall gamma t ty, derivation_rwf gamma t ty -> wf ty. 
Proof. 
intros gamma t ty d; induction d; split_all. 
eapply2 wf_funty. assert(wfc(ty1:: gamma)) by eapply2 rwf_implies_wfcs. 
inversion H; auto. 
inversion IHd; auto. 
Qed. 


Lemma derive_app_invert : 
forall gamma t ty, derivation gamma t ty -> 
forall t1 t2, t = App t1 t2 -> exists ty2, derivation gamma t2 ty2 /\ derivation gamma t1 (funty ty2 ty). 
Proof. 
split_all; subst. 
assert(derivation (map (lift(fst (pull ty))) gamma) (App t1 t2) (lift (fst (pull ty)) ty)) 
by (unfold lift; eapply2 lift_rec_ty_preserves_derive). 
assert(derivation (map (lift(fst (pull ty))) gamma) (App t1 t2) (snd (pull ty))).
eapply2 derive_instance. eapply2 instance_pull.
eapply2 derive_implies_wfcs.
assert(derivation_rwf  (map (lift (fst (pull ty))) gamma) (App t1 t2) (snd (pull ty))).
eapply2 derivation_implies_derivation_rwf_wf. 
eapply2 pull_wf. 
eapply2 derive_implies_wfcs. 
inversion H2; subst. 
assert(derivation gamma t2 (quant (fst (pull ty)) ty1)) by eapply2 derive_gen. 
exist (quant (fst (pull ty)) ty1). 

assert(derivation (map (lift (fst (pull ty))) gamma) t1
         (funty (lift (fst(pull ty)) (quant (fst (pull ty)) ty1)) (snd (pull ty)))). 
eapply2 derive_instance. 
eapply2 rwf_implies_derive. 
eapply2 preserves_contra_instance.
eapply2 pull_preserves_wfs. 
eapply2 derive_implies_wfcs. 
eapply2 instance_quant_lift2. 
eapply2 derive_implies_wfcs. 

assert(derivation gamma t1 (quant (fst (pull ty)) (funty (lift (fst (pull ty)) (quant (fst (pull ty)) ty1))
            (snd (pull ty))))). 
eapply2 derive_gen. 
assert(derivation gamma t1 (funty (quant (fst (pull ty)) ty1)
            (quant (fst (pull ty)) (snd (pull ty))))). 
eapply2 derive_push. eapply2 push_quant. 
eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 pull_preserves_wfs.  eapply2 derive_implies_wfcs. 
eapply derive_push. 
eexact H7. 
eapply preserves_funty_r_push. eapply2 quant_preserves_wfs. eapply2 derive_implies_wfcs. 
eapply2 quant_pull. eapply2 derive_implies_wfcs. 
Qed. 
