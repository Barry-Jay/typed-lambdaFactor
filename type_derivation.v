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
(*                   type_derivation.v                                *)
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


(* Types of System F *) 

(* Typing will be implicit, with rules for instantiating and
generalising type variables that do not change the term.  Further, the
presence of the operators requires that there be rules for pushing type
variables to the right of arrows after generalising when the bound
variable does not appear in the argument type. 

The main goal is to prove subject reduction. This is challenging since
there may be many derivations of the same typing. The strategy will be
to define derivation in a natural manner, and then reduce the variety
of derivation strategies allowed, without losing any typings. This is
done by first limiting instantiation to variables and operators, and
then requiring instantiation to produce a well-formed type,
i.e. without abstractions to the right of an arrow.

*)  

(* the terms are also used to represent types *) 

Definition varty := Ref .
Definition funty ty1 ty2 := App (App s_op ty1) ty2.

Fixpoint quant (k:nat) ty := 
match k with 
| 0 => ty 
| S k1 => Abs (quant k1 ty)
end.

Lemma quant_quant: forall j n ty, quant j (quant n ty) = quant (j+n) ty. 
Proof. induction j; split_all. Qed. 


Lemma lift_rec_preserves_quant : 
forall n ty n0 k, 
lift_rec (quant n ty) n0 k = quant n (lift_rec ty (n+n0) k). 
Proof. 
induction n; split_all. unfold quant; fold quant; simpl. rewrite IHn. 
replace(n + S n0) with (S (n+n0)) by omega. auto. 
Qed. 

Lemma subst_rec_preserves_quant : 
forall n ty1 ty2 k, 
subst_rec (quant n ty1) ty2 k = 
quant n (subst_rec ty1 ty2 (n+k)) . 
Proof. 
induction n; unfold lift; split_all. 
(* 2 *) 
repeat (rewrite lift_rec_null). auto.  
(* 1 *) 
rewrite IHn; unfold lift. 
replace (n + S k) with (S (n+k)) by omega; auto. 
Qed. 

Lemma quant_monotonic : 
forall n ty1 ty2, 
 quant n ty1 = quant n ty2 -> ty1 = ty2. 
Proof. induction n; split_all.  inversion H. auto. Qed. 

(* the well-formed type schemes are characterised as follows *) 

Inductive wfs : lamSF -> Prop := 
| wfs_var : forall i, wfs (varty i)
| wfs_funty : forall ty1 ty2, wfs ty1 -> wfs ty2 -> wfs (funty ty1 ty2)
| wfs_abs : forall ty, wfs ty -> wfs (Abs ty)
.

Hint Constructors wfs.

(* the well-formed types are a sub-set of the well-formed schemes *) 
 
Inductive wf : lamSF -> Prop := 
| wf_var : forall i, wf (varty i)
| wf_funty : forall ty1 ty2, wfs ty1 -> wf ty2 -> wf (funty ty1 ty2)
.

Hint Constructors wf.
 
Lemma lift_rec_preserves_wfs: forall ty, wfs ty -> forall n k, wfs(lift_rec ty n k).
Proof. 
rank_tac. induction ty; split_all; inv1 wfs; subst; simpl in *. 
eapply2 wfs_abs. 
eapply2 IHty. omega. 
eapply2 wfs_funty.  eapply2 IHp; omega. eapply2 IHty2; omega. 
Qed.

Lemma lift_rec_reflects_wfs : forall ty n k, wfs (lift_rec ty n k) -> wfs ty. 
Proof. 
rank_tac. 
induction ty; split_all. 
inversion H0; subst. eapply2 wfs_abs. eapply2 IHp. omega. 
inversion H0; subst. 
gen3_case H H0 H1 ty1. 
inversion H1; subst. 
gen3_case H H0 H5 l; try discriminate. 
rewrite <- H5. 
eapply2 wfs_funty. 
eapply2 IHp. omega.  
eapply2 IHp. omega.  
Qed. 



Lemma subst_rec_preserves_wfs: forall ty1 ty k, wfs ty1 -> wfs ty -> wfs (subst_rec ty1 ty k).
Proof. 
rank_tac. 
induction ty1; split_all. 
unfold insert_Ref. elim(compare k n); split_all. elim a; split_all. 
unfold lift; eapply2 lift_rec_preserves_wfs. 
eapply2 wfs_abs. eapply2 IHty1. simpl in *; omega. inversion H0; auto. 
inversion H0; subst. 
simpl. eapply2 wfs_funty. 
eapply2 IHp. simpl in *; omega. 
eapply2 IHp. simpl in *; omega. 
Qed. 

Lemma lift_rec_preserves_wf: forall ty, wf ty -> forall n k, wf(lift_rec ty n k).
Proof. induction ty; split_all; inv1 wf. eapply2 wf_funty.  eapply2 lift_rec_preserves_wfs. Qed.

Hint Resolve lift_rec_preserves_wfs lift_rec_preserves_wf. 

Lemma wf_implies_wfs : forall ty, wf ty -> wfs ty. 
Proof. induction ty; split_all; inv1 wf; subst. eapply2 wfs_funty. Qed. 

Lemma quant_preserves_wfs: forall j ty, wfs ty -> wfs (quant j ty).
Proof. induction j; split_all. Qed.  

(* operator types *) 


Definition op_abs o := 
match o with 
| Sop => 3
| Aop => 2 
| Kop => 2
| Eop => 3
| Gop => 2
| Qop => 2
| Uop => 1
| _ => 1
end.


Definition  opty_core0 (o: operator) := 
match o with 
  | Sop => funty (funty (varty 2) (funty (varty 1) (varty 0)))
                 (funty (funty (varty 2) (varty 1))
                        (funty (varty 2) (varty 0))
                 )
  | Aop => funty (funty (varty 0) (varty 1)) (funty (varty 0) (varty 1)) 
  | Kop => funty (varty 1) (funty (varty 0) (varty 1))
  | Eop => funty (varty 2) (funty (varty 1) (funty (varty 0) (funty (varty 0) (varty 0)))) 
  | Gop => funty (Abs (funty (funty (varty 0) (varty 2)) (funty (varty 0) (varty 1))))
                        (funty (varty 1) (varty 0))
  | Qop => funty (Abs (funty (varty 0) (varty 1)))
                 (funty (funty (varty 0) (funty (varty 0) (varty 0)))
                        (funty (varty 1) (varty 0)))
  | Uop => funty (Abs (Abs (funty (varty 1) 
                                         (funty (funty (varty 0) (varty 1))
                                                (funty (varty 0) (varty 1))))))
                        (funty (varty 0) (varty 0))
  | Yop => funty (funty (varty 0) (varty 0)) (varty 0)
| _ => Op o (* dummy value *) 
end. 

Definition  case_op_type o := 
  funty (quant (op_abs o) (opty_core0 o)) 
        (funty (funty (varty 0) (varty 0)) 
               (funty (varty 0) (varty 0))) .

Definition opty_core o := 
match o with 
| DSop => case_op_type Sop 
| DAop => case_op_type Aop 
| DKop => case_op_type Kop 
| DEop => case_op_type Eop 
| DGop => case_op_type Gop 
| DQop => case_op_type Qop 
| DUop => case_op_type Uop 
| DYop => case_op_type Yop 
| _ => opty_core0 o
end. 


Definition opty (o: operator) := quant (op_abs o) (opty_core o). 

Ltac unfold_opty := unfold opty, opty_core, opty_core0, case_op_type, op_abs, quant. 


(* instance *) 


Inductive instance1 : lamSF -> lamSF -> Prop :=
| instance_rule : forall ty ty1, wfs ty -> wfs ty1 -> instance1 (Abs ty1) (subst ty ty1)
| instance_abs : forall ty1 ty2, instance1 ty1 ty2 -> instance1 (Abs ty1) (Abs ty2)
| instance_funty : forall ty1 ty2 ty3, wfs ty1 -> instance1 ty2 ty3 -> 
                                     instance1 (funty ty1 ty2) (funty ty1 ty3)
| instance_contra : forall ty0 ty1 ty2, instance1 ty0 ty1 -> wfs ty2 -> 
                                     instance1 (funty ty1 ty2) (funty ty0 ty2)
. 

Hint Constructors instance1. 

Definition instance := multi_step instance1.

Lemma lift_rec_preserves_instance1 : lift_rec_preserves instance1.  
Proof. 
intros ty1 ty2 p; induction p; split_all. 
unfold subst; replace n with (0+n) by omega; 
rewrite lift_rec_subst_rec; try omega. 
eapply2 instance_rule.
eapply2 instance_funty.
eapply2 instance_contra.
Qed. 

Lemma lift_rec_preserves_instance : 
forall ty1 ty2, instance ty1 ty2 -> 
forall n k, instance (lift_rec ty1 n k) (lift_rec ty2 n k). 
Proof. 
eapply2 lift_rec_preserves_multi_step. 
red; split_all. eapply2 lift_rec_preserves_instance1.
Qed. 

Lemma subst_rec_preserves_instance1 : 
forall ty1 ty2, instance1 ty1 ty2 -> 
forall ty k, wfs ty -> instance1(subst_rec ty1 ty k) (subst_rec ty2 ty k). 
Proof. 
intros ty1 ty2 p; induction p; split_all. 
(* 3 *) 
unfold subst. replace k with (0+k) by auto. 
rewrite subst_rec_subst_rec. simpl. 
replace(subst_rec (subst_rec ty1 ty0 (S k)) (subst_rec ty ty0 k) 0)
with (subst (subst_rec ty ty0 k) (subst_rec ty1 ty0 (S k))) by auto.
eapply2 instance_rule; eapply2 subst_rec_preserves_wfs. 
(* 2 *) 
eapply2 instance_funty.  eapply2 subst_rec_preserves_wfs. 
eapply2 instance_contra. eapply2 subst_rec_preserves_wfs.
Qed.

Lemma subst_rec_preserves_instance : 
forall ty1 ty2, instance ty1 ty2 -> 
forall ty k, wfs ty -> instance(subst_rec ty1 ty k) (subst_rec ty2 ty k). 
Proof. 
cut(forall red ty1 ty2, multi_step red ty1 ty2 -> red = instance1 -> 
forall ty k, wfs ty -> instance(subst_rec ty1 ty k) (subst_rec ty2 ty k)).
intro c; split_all; eapply2 c. 
intros red ty1 ty2 m; induction m; split_all; subst.
eapply2 zero_red. 
apply transitive_red with (subst_rec N ty k); auto.
one_step. eapply2 subst_rec_preserves_instance1.
eapply2 IHm.
Qed.


Lemma preserves_abs_instance : forall ty1 ty2, instance ty1 ty2 -> instance (Abs ty1) (Abs ty2).
Proof. 
cut(forall red ty1 ty2, multi_step red ty1 ty2 -> red = instance1 -> 
instance (Abs ty1) (Abs ty2)).
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 m; induction m; split_all; subst. eapply2 zero_red. 
eapply succ_red. 2: eapply2 IHm. auto. 
Qed. 

Lemma preserves_funty_r_instance : 
forall ty1 ty2 ty3, wfs ty1 -> instance ty2 ty3 -> instance(funty ty1 ty2) (funty ty1 ty3).
Proof. 
cut(forall red ty1 ty2 ty3, wfs ty1 -> multi_step red ty2 ty3 -> red = instance1 -> 
instance(funty ty1 ty2) (funty ty1 ty3)).
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 ty3 w m; induction m; split_all; subst. 
eapply2 zero_red. 
eapply transitive_red. one_step. eapply instance_funty; auto. 
eexact H. eapply2 IHm. 
Qed. 

Lemma preserves_contra_instance : 
forall ty1 ty2 ty3, wfs ty1 -> instance ty2 ty3 -> instance(funty ty3 ty1) (funty ty2 ty1).
Proof. 
cut(forall red ty1 ty2 ty3, wfs ty1 -> multi_step red ty2 ty3 -> red = instance1 -> 
instance(funty ty3 ty1) (funty ty2 ty1)).
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 ty3 w m; induction m; split_all; subst. 
eapply2 zero_red. 
eapply transitive_red. eapply2 IHm. one_step. 
Qed. 

Lemma instance1_implies_wfs: forall ty1 ty2, instance1 ty1 ty2 -> wfs ty1 /\ wfs ty2. 
Proof. 
intros ty1 ty2 inst; induction inst; split_all. 
unfold subst; eapply2 subst_rec_preserves_wfs.
Qed. 

Lemma instance_implies_wfs: 
forall ty1 ty2, instance ty1 ty2 -> (wfs ty1 -> wfs ty2) /\ (wfs ty2 -> wfs ty1). 
Proof. 
cut(forall red ty1 ty2, multi_step red ty1 ty2 -> red = instance1 -> 
 (wfs ty1 -> wfs ty2) /\ (wfs ty2 -> wfs ty1)).
intro aux; intros; 
assert((wfs ty1 -> wfs ty2) /\ (wfs ty2 -> wfs ty1)) by eapply2 aux; split_all.  

intros red ty1 ty2 m; induction m; split_all; subst. 
eapply2 IHm; eapply2 instance1_implies_wfs.  
assert(wfs M /\ wfs N) by eapply2 instance1_implies_wfs. split_all. 
Qed. 


Lemma preserves_funty_instance : 
forall ty0 ty1 ty2 ty3, wfs ty1 -> wfs ty2 -> instance ty0 ty1 -> instance ty2 ty3 -> 
instance(funty ty1 ty2) (funty ty0 ty3).
Proof. 
split_all. eapply transitive_red. eapply2 preserves_funty_r_instance. 
eapply2 preserves_contra_instance. 
assert((wfs ty2 -> wfs ty3) /\ (wfs ty3 -> wfs ty2)) by eapply2 instance_implies_wfs. 
split_all. 
Qed. 

Lemma preserves_varty_instance : 
forall red ty1 ty2, multi_step red ty1 ty2 -> red = instance1 -> forall i, ty1 = varty i -> ty2 = ty1. 
Proof. intros red ty1 y2 m; induction m; split_all; subst. inversion H. Qed. 

(* push *) 

Inductive push1 : lamSF -> lamSF -> Prop := 
| push_lift : forall ty1 ty2, wfs ty1 -> wfs ty2 -> 
                push1 (Abs (funty (lift 1 ty1) ty2)) (funty ty1 (Abs ty2))
| push_abs : forall ty1 ty2, push1 ty1 ty2 -> push1 (Abs ty1) (Abs ty2)
                                    (* for pushing after generalizing *)
| push_funty : forall ty1 ty2 ty3, 
                push1 ty2 ty3 -> wfs ty1 -> 
                push1 (funty ty1 ty2) (funty ty1 ty3)  
. 

Definition push := multi_step push1. 

Hint Resolve push_lift push_abs push_funty. 


Lemma lift_rec_preserves_push1 : 
forall ty1 ty2, push1 ty1 ty2 -> 
forall n k, push1 (lift_rec ty1 n k) (lift_rec ty2 n k). 
Proof. 
intros ty1 ty2 p; induction p; split_all.
unfold lift, funty; rewrite lift_lift_rec; try omega. eapply2 push_lift.
eapply2 push_funty. 
Qed. 

Lemma subst_rec_preserves_push1 : 
forall ty1 ty2, push1 ty1 ty2 -> 
forall ty k, wfs ty ->  push1 (subst_rec ty1 ty k) (subst_rec ty2 ty k). 
Proof. 
intros ty1 ty2 p; induction p; split_all. 
unfold lift; rewrite subst_rec_lift_rec1; try omega.
eapply2 push_lift; eapply2 subst_rec_preserves_wfs. 
eapply2 push_funty; eapply2 subst_rec_preserves_wfs. 

Qed. 

Lemma subst_rec_preserves_push : 
forall red ty1 ty2, multi_step red ty1 ty2 -> red = push1 -> 
forall ty k, wfs ty -> push (subst_rec ty1 ty k) (subst_rec ty2 ty k). 
Proof. 
intros red ty1 ty2 p; induction p; split_all; subst. 
eapply2 zero_red. 
apply succ_red with (subst_rec N ty k); auto. 
eapply2 subst_rec_preserves_push1. 
eapply2 IHp. 
Qed. 



Lemma preserves_funty_r_push : 
forall ty1 ty2 ty3, wfs ty1 -> push ty2 ty3 -> push(funty ty1 ty2) (funty ty1 ty3).
Proof. 
cut(forall red ty1 ty2 ty3, wfs ty1 -> multi_step red ty2 ty3 -> red = push1 -> 
push(funty ty1 ty2) (funty ty1 ty3)).
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 ty3 w m; induction m; split_all; subst. 
eapply2 zero_red. 
eapply transitive_red. one_step. eapply push_funty; auto. 
eexact H. eapply2 IHm. 
Qed. 



Lemma push1_quant : 
forall j ty1 ty2, push1 ty1 ty2 -> push1 (quant j ty1) (quant j ty2).
Proof. induction j; split_all; rewrite IHj; auto. Qed. 

Lemma push_quant : 
forall j ty1 ty2, wfs ty1 -> wfs ty2 -> push (quant j (funty (lift j ty1) ty2)) 
                       (funty ty1 (quant j ty2)).
Proof.
induction j; split_all. 
(* 2 *) 
unfold lift; rewrite lift_rec_null. eapply2 zero_red. 
(* 1 *) 
apply transitive_red  with (Abs (funty (lift 1 ty1) (quant j ty2))); auto. 
eapply2 preserves_abs_multi_step. red; split_all.
replace(lift (S j) ty1) with (lift j (lift 1 ty1)).
eapply2 IHj.
unfold lift; eapply2 lift_rec_preserves_wfs. 
unfold lift; rewrite lift_rec_lift_rec; try omega.  
replace (j+1) with (S j) by omega; auto.
one_step.
eapply2 push_lift. 
clear - H0. 
induction j; split_all. 
Qed. 

Lemma push_preserves_abs : 
forall ty1 ty2, push ty1 ty2 -> push (Abs ty1) (Abs ty2). 
Proof.
cut(forall red ty1 ty2, multi_step red ty1 ty2 -> red = push1 -> 
                        push (Abs ty1) (Abs ty2)).
intro aux; split_all; eapply2 aux. 
intros red ty1 ty2 m; induction m; split_all; subst.
eapply2 zero_red. 
eapply succ_red.
eapply2 push_abs. 
eapply2 IHm.
Qed.


Lemma push_preserves_funty : 
forall ty0 ty1 ty2, push ty1 ty2 -> wfs ty0 -> push (funty ty0 ty1) (funty ty0 ty2). 
Proof.
cut(forall red ty0 ty1 ty2, multi_step red ty1 ty2 -> red = push1 -> wfs ty0 -> 
                        push (funty ty0 ty1) (funty ty0 ty2)).
intro aux; split_all; eapply2 aux. 
intros red ty0 ty1 ty2 m; induction m; split_all; subst.
eapply2 zero_red. 
eapply succ_red.
eapply2 push_funty. 
eapply2 IHm.
Qed.


Lemma preserves_abs_push : preserves_abs push. 
Proof.  eapply2 preserves_abs_multi_step. red; split_all. Qed. 

Lemma push_implies_wfs: forall ty1 ty2, push1 ty1 ty2 -> wfs ty1 /\ wfs ty2. 
Proof. 
intros ty1 ty2 p; induction p; split_all. 
eapply2 wfs_abs. eapply2 wfs_funty. unfold lift; eapply2 lift_rec_preserves_wfs. 
Qed. 


Lemma push1_instance1: 
forall ty1 ty2, push1 ty1 ty2 -> forall ty3, instance1 ty2 ty3 -> 
exists ty4, instance1 ty1 ty4 /\ push ty4 ty3. 
Proof. 
intros ty1 ty2 p; induction p; split_all. 
(* 3 *) 
inversion H1; subst. inversion H6; subst.
(* 5 *) 
exist (subst ty (funty (lift 1 ty1) ty2)).
eapply2 instance_rule.  unfold lift; simpl. eapply2 wfs_funty. 
unfold subst, lift; simpl. 
rewrite subst_rec_lift_rec; try omega. rewrite lift_rec_null. 
eapply2 zero_red. 
(* 4 *) 
exist (Abs (funty (lift 1 ty1) ty3)) . 
unfold lift; simpl. eapply2 instance_abs. 
red; one_step. eapply2 push_lift.  eapply2 instance1_implies_wfs. 
(* 3 *) 
unfold lift; simpl. 
exist  (Abs (App (App (Op Sop) (lift_rec ty0 0 1)) ty2)) .
eapply2 instance_abs. eapply2 instance_contra. eapply2 lift_rec_preserves_instance1. 
red; one_step. 
replace  (App (Op Sop) (lift_rec ty0 0 1)) with (lift 1 (App s_op ty0)) by auto. 
eapply2 push_lift.  
assert(wfs ty0 /\ wfs ty1) by eapply2 instance1_implies_wfs. split_all. 
(* 2 *) 
inversion H; subst.
(* 3 *)   
exist(subst ty ty1). eapply2 instance_rule.
assert(wfs ty1 /\ wfs ty2) by eapply2 push_implies_wfs. split_all. 
unfold subst; simpl. red; one_step. eapply2 subst_rec_preserves_push1. 
(* 2 *) 
assert(exists ty5 : lamSF, instance1 ty1 ty5 /\ push ty5 ty4) by eapply2 IHp.
split_all. 
exist(Abs x). 
eapply2 preserves_abs_push. 
(* 1 *) 
inversion H0; subst.  
assert(exists ty5 : lamSF, instance1 ty2 ty5 /\ push ty5 ty6) by eapply2 IHp.
split_all. 
exist(funty ty1 x). 
eapply2 preserves_funty_r_push.
(* 1 *) 
exist(funty ty4 ty2). eapply2 instance_contra. 
assert(wfs ty2 /\ wfs ty3) by eapply2 push_implies_wfs. split_all. 
red; one_step. 
eapply2 push_funty. 
assert(wfs ty4 /\ wfs ty1) by eapply2 instance1_implies_wfs. split_all. 
Qed. 


(* contexts *)


Definition context := list lamSF. 

Inductive wfc : context -> Prop := 
| wfc_nil : wfc nil
| wfc_cons : forall ty gamma, wfs ty -> wfc gamma -> wfc (cons ty gamma).

Hint Resolve wfc_nil wfc_cons. 

Lemma lift_rec_preserves_wfc : 
forall gamma, wfc gamma -> forall n k, wfc (map (fun M => lift_rec M n k) gamma). 
Proof. induction gamma; split_all. inversion H; subst. eapply2 wfc_cons. Qed. 

Lemma subst_rec_preserves_wfc : 
forall gamma, wfc gamma -> forall sch k, wfs sch -> wfc (map (fun M => subst_rec M sch k) gamma). 
Proof. 
induction gamma; split_all. 
inversion H; subst. eapply2 wfc_cons. eapply2 subst_rec_preserves_wfs. 
Qed. 

Hint Resolve lift_rec_preserves_wfc subst_rec_preserves_wfc. 

Lemma lift0_context : forall gamma : context, List.map (lift 0) gamma = gamma. 
Proof. induction gamma; split_all. rewrite IHgamma. unfold lift; rewrite lift_rec_null. auto. Qed.

Definition insertn k (gamma: context) sch := app (firstn k gamma) (cons sch (skipn k gamma)). 
Definition removen k (gamma: context) := app (firstn k gamma) (tl (skipn k gamma)). 


Lemma append_preserves_wfc : 
forall gamma1 gamma2, wfc gamma1 -> wfc gamma2 -> wfc (gamma1 ++ gamma2).
Proof. induction gamma1; split_all. inversion H. eapply2 wfc_cons. Qed. 

Lemma tl_preserves_wfc : 
forall gamma, wfc gamma -> wfc (tl gamma).
Proof. induction gamma; split_all. inversion H; auto. Qed. 

Lemma firstn_preserves_wfc: forall k gamma, wfc gamma -> wfc (firstn k gamma).
Proof. 
induction k; split_all. induction gamma; split_all. inversion H; subst. eapply2 wfc_cons. 
Qed. 

Lemma skipn_preserves_wfc: forall k gamma, wfc gamma -> wfc (skipn k gamma).
Proof. 
induction k; split_all. induction gamma; split_all. inversion H; subst. eapply2 IHk. 
Qed. 

Lemma insertn_preserves_wfc: 
forall k gamma sch, wfc gamma -> wfs sch -> wfc (insertn k gamma sch). 
Proof. 
split_all. unfold insertn. eapply2 append_preserves_wfc.
eapply2 firstn_preserves_wfc. 
eapply2 wfc_cons. eapply2 skipn_preserves_wfc. 
Qed. 

Lemma removen_preserves_wfc: forall k gamma, wfc gamma -> wfc (removen k gamma). 
Proof. 
split_all. unfold removen. eapply2 append_preserves_wfc.
eapply2 firstn_preserves_wfc. 
assert (wfc (skipn k gamma)) by eapply2 skipn_preserves_wfc. 
gen_case H0 (skipn k gamma). 
inversion H0; auto. 
Qed. 

Hint Resolve insertn_preserves_wfc removen_preserves_wfc. 


Ltac wfcs_tac := unfold lift; simpl; relocate_lt; repeat eapply2 wfc_cons;  
repeat (repeat eapply2 wfs_abs; repeat eapply2 wfs_funty); simpl; auto.  

Lemma insertn_cons : 
forall k sch gamma sch0, insertn (S k) (cons sch gamma) sch0 = cons sch (insertn k gamma sch0). 
Proof. auto. Qed. 

Lemma removen_cons : 
forall k sch gamma , removen (S k) (cons sch gamma) = cons sch (removen k gamma). 
Proof. auto. Qed. 

Lemma map_skipn: 
forall gamma k (f:lamSF -> lamSF), map f (skipn k gamma) = skipn k (map f gamma).
Proof. induction gamma; split_all; induction k; split_all. Qed. 

Lemma map_insertn : forall k sch gamma f, map f (insertn k gamma sch) = insertn k (map f gamma) (f sch). 
Proof. 
induction k; split_all.
case gamma. 
split_all. 
intros. 
replace (map f (l :: l0)) with (f l :: map f l0) by auto. 
replace (insertn (S k) (l :: l0) sch) with (l :: insertn k l0 sch) by auto. 
replace (insertn (S k) (f l :: map f l0) (f sch)) 
with (f l :: insertn k (map f l0) (f sch)) by auto. 
replace (map f (l :: insertn k l0 sch)) with (f l :: map f (insertn k l0 sch)) 
by auto. 
rewrite IHk. auto. 
Qed. 

Lemma map_removen : forall k gamma f, map f (removen k gamma) = removen k (map f gamma). 
Proof. 
induction k; split_all.
unfold removen, firstn; simpl.  case gamma; split_all. 
case gamma; intros. 
split_all. 
replace (map f (l::l0)) with (f l :: map f l0) by auto. 
rewrite removen_cons. 
rewrite removen_cons. 
replace (map f (l::removen k l0)) with (f l :: map f (removen k l0)) by auto. 
rewrite IHk.  auto. 
Qed. 


Lemma lift_rec_reflects_wfc : 
forall gamma n k, wfc (map (fun ty => lift_rec ty n k) gamma) -> wfc gamma.
Proof. 
induction gamma; split_all. inversion H. eapply2 wfc_cons. 
eapply2 lift_rec_reflects_wfs. 
Qed. 


(* type derivation *) 

Inductive derivation : context -> lamSF -> lamSF -> Prop := 
| derive_op : forall gamma o,  wfc gamma -> derivation gamma (Op o) (opty o) 
| derive_var : forall gamma ty,  wfc gamma -> wfs ty -> derivation (cons ty gamma) (Ref 0) ty
| derive_weak : forall gamma i ty1 ty,  derivation gamma (Ref i) ty -> wfs ty1 -> 
                                       derivation (cons ty1 gamma) (Ref (S i)) ty
| derive_abs : forall gamma ty1 ty2 t,   
                 derivation (cons ty1 gamma) t ty2 ->
                 derivation gamma (Abs t) (funty ty1 ty2)
| derive_app: forall gamma t ty1 ty2 u,  
                derivation gamma t (funty ty1 ty2) -> 
                derivation gamma u ty1 ->
                derivation gamma (App t u) ty2
| derive_inst : forall gamma t ty1 ty2, derivation gamma t ty1 -> 
                                         instance1 ty1 ty2 -> 
                                   derivation gamma t ty2
| derive_gen1: forall gamma t ty, derivation (map (lift 1) gamma) t ty ->
                                  derivation gamma t (Abs ty)
| derive_push1 : forall gamma t ty, derivation gamma t ty ->
                forall ty2, push1 ty ty2 -> derivation gamma t ty2
 .

Hint Constructors derivation.

Lemma lift_rec_ty_preserves_derive : forall gamma t ty, derivation gamma t ty -> forall n k , 
derivation (map (fun ty0 => lift_rec ty0 n k) gamma) t (lift_rec ty n k). 
Proof. 
intros gamma t ty d; induction d; split_all. 
(* 6 *)
replace (lift_rec (opty o) n k) with (opty o) by (case o; split_all); auto. 
(* 5 *) 
eapply2 derive_abs; eapply2 IHd. 
(* 4 *) 
simpl in *; eapply2 derive_app.  
(* 3 *) 
eapply2 derive_inst. eapply2 lift_rec_preserves_instance1. 
(* 2 *)
eapply2 derive_gen1.
replace(map (lift 1)  (map (fun ty0 : lamSF => lift_rec ty0 n k) gamma)) 
with (map (fun ty0 : lamSF => lift_rec ty0 (S n) k) (map (lift 1) gamma)).
auto.
clear; induction gamma; split_all. 
rewrite IHgamma; unfold lift; rewrite lift_lift_rec; try omega; auto. 
(* 1 *) 
eapply2 derive_push1. eapply2 lift_rec_preserves_push1.
Qed. 

Lemma derive_implies_wfcs: forall gamma t ty, derivation gamma t ty -> wfc gamma /\  wfs ty. 
Proof. 
intros gamma t ty d; induction d; split_all.
(* 7 *)  
case o; split_all; unfold opty, funty; split_all; unfold funty; wfcs_tac.  
(* 6 *) 
inversion H; auto. 
(* 5 *) 
inversion H; subst. wfcs_tac. 
(* 4 *) 
inversion H2; subst. auto. 
(* 3 *) 
eapply2 instance1_implies_wfs. 
assert(wfc(map (subst ty) (map (lift 1) gamma))) 
by eapply2 subst_rec_preserves_wfc. 
replace gamma with (map (subst ty) (map (lift 1) gamma)); auto. 
clear; induction gamma; split_all. rewrite IHgamma. 
unfold lift, subst; rewrite subst_rec_lift_rec; try omega. 
rewrite lift_rec_null; auto. 
eapply2 push_implies_wfs. 
Qed. 


(* general form of derive_weak *)

Lemma derive_weak_general_k: 
forall gamma t ty, derivation gamma t ty -> 
forall k sch, wfs sch -> derivation (insertn k gamma sch) (lift_rec t k 1) ty. 
Proof. 
intros gamma t ty d; induction d; split_all.
(* 7 *) 
unfold relocate. elim(test k 0); split_all; try noway. 
assert(k=0) by omega; subst k. unfold insertn; simpl. eapply2 derive_weak. 
replace k with (S (pred k)) by omega.
rewrite insertn_cons. eapply2 derive_var. 
(* 6 *)
unfold relocate. elim(test k (S i)); split_all. 
gen_case a k. unfold insertn; simpl. eapply2 derive_weak. 
rewrite insertn_cons. eapply2 derive_weak. 
replace (Ref (S i)) with (lift_rec (Ref i) n 1) by (simpl; relocate_lt; auto). 
eapply2 IHd. 
replace k with (S (pred k)) by omega.
rewrite insertn_cons. eapply2 derive_weak.
replace (Ref i) with (lift_rec (Ref i) (pred k) 1) by (simpl; relocate_lt; auto). 
eapply2 IHd. 
(* 5 *) 
eapply2 derive_abs. rewrite <- insertn_cons. eapply2 IHd. 
(* 4 *) 
eapply2 derive_app.
(* 3 *)
eapply2 derive_inst. 
(* 2 *) 
assert(derivation (insertn k (map (lift 1) gamma) (lift 1 sch)) (lift_rec t k 1) ty).
eapply2 IHd. unfold lift; auto. 
rewrite <- map_insertn in H0. 
auto.
(* 1 *) 
eapply2 derive_push1. 
Qed. 

Proposition derive_weak_general : 
forall gamma t ty, derivation gamma t ty -> 
forall sch, wfs sch -> derivation (sch :: gamma) (lift 1 t) ty. 
Proof. 
split_all. 
replace (sch :: gamma) with (insertn 0 gamma sch) by auto. 
replace (lift 1 t) with (lift_rec t 0 1) by auto. 
eapply2 derive_weak_general_k.
Qed. 

(* subst_rec_ty_preserves_derive *) 


Lemma weak_aux : forall gamma t sch, derivation gamma t sch -> forall i, t = Ref i -> gamma <> nil. 
Proof. intros gamma t sch d; induction d; split_all; 
intro; subst; split_all; unfold map in *; auto; eapply2 IHd.
Qed. 

Lemma weak_aux1:
forall gamma t ty, derivation gamma t ty -> forall i, t = Ref (S i) -> 
forall k, k < S i -> derivation (removen k gamma) (Ref i) ty. 
Proof. 
intros gamma t ty d; induction d; split_all.
(* 4 *) 
inversion H0; subst. 
gen_case H1 k. 
rewrite removen_cons. 
replace i0 with (S (pred i0)) by omega. 
eapply2 derive_weak. 
eapply2 IHd. 
assert(i0 = S (pred i0)) by omega; congruence. 
omega. 
(* 3 *) 
subst. eapply2 derive_inst. 
(* 2 *) 
subst. 
assert(derivation (removen k (map (lift 1) gamma)) (Ref i) ty) by eapply2 IHd. 
rewrite <- map_removen in H. auto. 
(* 1 *) 
eapply2 derive_push1.  
Qed. 

Lemma weak_aux2:
forall gamma t ty, derivation gamma t ty -> forall i, t = Ref i -> 
forall k, k > i -> derivation (removen k gamma) (Ref i) ty. 
Proof. 
intros gamma t ty d; induction d; split_all.
(* 5 *) 
inversion H1; subst. 
gen_case H2 k; try noway.  
rewrite removen_cons. 
eapply2 derive_var. 
(* 4 *) 
inversion H0; subst. 
replace k with (S (pred k)) by omega. 
rewrite removen_cons. 
eapply2 derive_weak. 
eapply2 IHd. omega. 
(* 3 *) 
eapply2 derive_inst. 
(* 2 *) 
assert(derivation (removen k (map (lift 1) gamma)) (Ref i) ty) by eapply2 IHd. 
rewrite <- map_removen in H1; auto. 
(* 1 *) 
eapply2 derive_push1.  
Qed. 



Lemma derive_push0: 
forall red gamma t ty, derivation gamma t ty ->
forall ty2, multi_step red ty ty2 -> red = push1 -> derivation gamma t ty2.
Proof.
intros red gamma t ty d ty2 m; induction m; split_all; subst; eapply2 IHm.
Qed.
Lemma derive_push: 
forall gamma t ty, derivation gamma t ty ->
forall ty2, push ty ty2 -> derivation gamma t ty2.
Proof. split_all; eapply2 derive_push0. Qed. 


Lemma derive_instance: 
forall gamma t ty, derivation gamma t ty ->
forall ty2,  instance ty ty2 -> derivation gamma t ty2.
Proof.
cut(forall gamma t ty, derivation gamma t ty ->
forall red ty2,  multi_step red ty ty2 -> red = instance1 -> 
derivation gamma t ty2); [ intro c; split_all; eapply2 c |]. 
intros gamma t ty d red ty2 m; induction m; split_all; subst. eapply2 IHm.
Qed. 


Lemma derive_gen: 
forall j gamma t ty, derivation (map (lift j) gamma) t ty ->
                                  derivation gamma t (quant j ty).
Proof. 
induction j; split_all. 
(* 2 *) 
rewrite lift0_context in *; auto.
(* 1 *)
replace(map (lift (S j)) gamma) 
with (map (lift j) (map (lift 1) gamma)) in H.
assert(derivation (map (lift 1) gamma) t (quant j ty)) by eapply2 IHj.
eapply2 derive_gen1. 
clear; induction gamma; split_all; rewrite IHgamma. 
unfold lift; rewrite lift_rec_lift_rec; try omega. 
replace(j+1) with (S j) by omega; auto.
Qed.


Lemma subst_rec_ty_preserves_derive : 
forall gamma t ty, wfs ty -> derivation gamma t ty -> 
forall ty1 k, wfs ty1 -> 
derivation (map (fun ty0 => subst_rec ty0 ty1 k) gamma) t 
           (subst_rec ty ty1 k). 
Proof. 
intros gamma t ty w d; induction d; split_all. 
(* 8 *) 
replace(subst_rec (opty o) ty1 k) with (opty o) by (case o; split_all). 
eapply2 derive_op.
(* 7 *) 
eapply2 derive_var.  eapply2 subst_rec_preserves_wfs. 
(* 6 *) 
eapply2 derive_weak.  eapply2 subst_rec_preserves_wfs.
(* 5 *) 
eapply2 derive_abs. eapply2 IHd. inversion w. auto. 
(* 4 *) 
eapply2 derive_app. eapply2 IHd1. eapply2 derive_implies_wfcs. 
eapply2 IHd2. assert(wfs (funty ty1 ty2)) by eapply2 derive_implies_wfcs. 
inversion H0. auto. 
(* 3 *) 
eapply2 derive_inst. eapply2 IHd.  eapply2 derive_implies_wfcs. 
eapply2 subst_rec_preserves_instance1. 
(* 2 *) 
assert(derivation
          (map (fun ty0 : lamSF => subst_rec ty0 ty1 (S k)) (map (lift 1) gamma))
          t (subst_rec ty ty1 (S k))).  eapply2 IHd. 
inversion w; auto. 
replace (map (fun ty0 : lamSF => subst_rec ty0 ty1 (S k)) (map (lift 1) gamma))
with (map (lift 1) (map (fun ty0 : lamSF => subst_rec ty0 ty1 k) gamma)) in H0. 
auto.
clear; induction gamma; split_all; rewrite IHgamma. 
unfold lift; rewrite subst_rec_lift_rec1; auto; omega.
(* 1 *) 
eapply2 derive_push1. eapply2 IHd. eapply2 derive_implies_wfcs. 
eapply2 subst_rec_preserves_push1.
Qed. 

Ltac subst_out := 
unfold subst; simpl; insert_Ref_out;
repeat (rewrite subst_rec_lift_rec; [| omega| omega]); 
repeat (rewrite lift_rec_null); auto.


(* subst_rec_preserves_derive *) 

Proposition subst_rec_preserves_derive : 
forall gamma M ty, derivation gamma M ty -> 
forall k u, k < length gamma -> 
derivation (skipn (S k) gamma) u (nth k gamma s_op) -> 
derivation (removen k gamma) (subst_rec M u k) ty.
Proof. 
intros gamma M ty d; induction d; intros. 
(* 8 *) 
split_all.  
(* 7 *) 
generalize H0; clear H0; induction k; split_all; simpl. 
(* 6 *) 
unfold removen; simpl. insert_Ref_out. rewrite lift_rec_null. auto.
(* 5 *) 
rewrite removen_cons. insert_Ref_out. auto. 
(* 4 *) 
 simpl in *. 
unfold insert_Ref. elim(compare k (S i)); split_all. elim a; split_all.
(* 8 *)
apply weak_aux1 with (Ref (S i)); auto. 
(* 7 *) 
subst. rewrite removen_cons. 
replace (lift (S i) u) with (lift 1 (lift i u)). 
eapply2 derive_weak_general. 
cut(derivation (removen i gamma) (subst_rec (Ref i) u i) ty).
simpl; insert_Ref_out. auto. 
 eapply2 IHd. omega. 
unfold lift. rewrite lift_rec_lift_rec; try omega. auto. 
(* 6 *)
apply weak_aux2 with (Ref (S i)); auto. 
(* 5 *) 
simpl. eapply2 derive_abs. 
assert(derivation (removen (S k) (ty1 :: gamma)) (subst_rec t u (S k)) ty2) by (eapply2 IHd; simpl; omega).
replace(removen (S k) (ty1 :: gamma)) with (ty1::removen k gamma) in H1 by auto. 
auto. 
(* 4 *) 
simpl.  eapply2 derive_app. simpl in *; auto. 
(* 3 *) 
eapply2 derive_inst. 
(* 2 *) 
assert( derivation (map (lift 1) (skipn (S k) gamma)) u (lift 1 (nth k gamma s_op))). 
unfold lift; eapply2 lift_rec_ty_preserves_derive. 
rewrite map_skipn in H1.
assert(derivation (removen k (map (lift 1) gamma))
          (subst_rec t u k) ty).
 eapply2 IHd. rewrite map_length; omega. 
replace s_op with (lift 1 s_op) by auto. 
replace(nth k (map (lift 1) gamma) (lift 1 s_op))
with (lift 1 (nth k gamma s_op)).  
auto.
rewrite map_nth. auto. 
rewrite <- map_removen in H2. 
auto.
(* 1 *) 
eapply2 derive_push1. 
Qed. 


Definition preserves_derive (red: termred) := 
forall ty1 ty2, red ty1 ty2 -> 
forall gamma t, derivation gamma t ty1 -> derivation gamma t ty2. 

Lemma preserves_derive_multi_step: 
forall red, preserves_derive red -> preserves_derive (multi_step red).
Proof. red; intros red p ty1 ty2 m; induction m; split_all; eapply2 IHm. Qed.


Inductive instance_context : context -> context -> Prop := 
| instance_context_nil : instance_context nil nil 
| instance_context_cons : forall ty1 ty2 gamma1 gamma2, instance ty1 ty2 -> 
  instance_context gamma1 gamma2 -> instance_context (cons ty1 gamma1) (cons ty2 gamma2) 
.

Hint Resolve instance_context_nil instance_context_cons. 

Lemma lift_rec_preserves_instance_context: 
forall gamma1 gamma2, instance_context gamma1 gamma2 -> 
forall n k, instance_context (map (fun M => lift_rec M n k) gamma1) 
                             (map (fun M => lift_rec M n k) gamma2).
Proof. 
induction gamma1; split_all; inversion H; subst; split_all. 
eapply2 instance_context_cons. eapply2 lift_rec_preserves_instance. 
Qed. 

Lemma instance_context_preserves_wfc: 
forall gamma1, wfc gamma1 -> forall gamma2, instance_context gamma1 gamma2 -> wfc gamma2. 
Proof. 
intros gamma w; induction w; split_all. 
inversion H; split_all. 
inversion H0; split_all. eapply2 wfc_cons. subst.  
assert((wfs ty -> wfs ty2) /\ (wfs ty2 -> wfs ty)). eapply2 instance_implies_wfs. 
split_all. 
Qed. 

Lemma instance_context_reflects_wfc: 
forall gamma1, wfc gamma1 -> forall gamma2, instance_context gamma2 gamma1 -> wfc gamma2. 
Proof. 
intros gamma1 w; induction w; split_all. 
inversion H; split_all. 
inversion H0; split_all. eapply2 wfc_cons. subst.  eapply2 instance_implies_wfs. 
Qed. 

Lemma derive_instance_context : 
forall gamma1 t ty, derivation gamma1 t ty -> 
forall gamma2, instance_context gamma2 gamma1 -> derivation gamma2 t ty.
Proof. 
intros gamma1 t ty d; induction d; intros gamma2 inst; subst; split_all. 
(* 8 *) 
eapply2 derive_op. eapply2 instance_context_reflects_wfc.
(* 7 *) 
inversion inst; subst. eapply2 derive_instance.  eapply2 derive_var.  
eapply2 instance_context_reflects_wfc. eapply2 instance_implies_wfs. 
(* 6 *) 
inversion inst; subst. eapply2 derive_weak. eapply2 instance_implies_wfs. 
(* 5 *) 
eapply2 derive_abs. eapply2 IHd. eapply2 instance_context_cons.  eapply2 zero_red. 
(* 4 *) 
eapply2 derive_app. 
eapply2 derive_inst. 
eapply2 derive_gen1. eapply2 IHd. unfold lift. eapply2 lift_rec_preserves_instance_context. 
eapply2 derive_push1. 
Qed. 



Lemma append_preserves_derive: 
forall gamma t ty, derivation gamma t ty -> 
forall gamma2, wfc gamma2 -> derivation (gamma ++ gamma2) t ty. 
Proof. 
intros gamma t ty d; induction d; split_all; 
assert(wfc(gamma++gamma2)) by (eapply2 append_preserves_wfc; eapply2 derive_implies_wfcs). 
eapply2 derive_op. 
eapply2 derive_var. 
eapply2 derive_abs. 
eapply2 derive_app. 
eapply2 derive_inst. 
eapply2 derive_gen1. 
rewrite map_app. eapply2 IHd. 
unfold lift; eapply2 lift_rec_preserves_wfc. 
eapply2 derive_push1. 
Qed. 

Lemma derive_nil : 
forall t ty, derivation nil t ty -> forall gamma, wfc gamma -> derivation gamma t ty. 
Proof. intros. replace gamma with (app nil gamma) by auto. eapply2 append_preserves_derive. Qed. 


Lemma derive_strong_general_k: 
forall gamma t ty, derivation gamma t ty -> 
forall k, k > maxvar t -> derivation (removen k gamma) t ty. 
Proof. 
intros gamma t ty d;  induction d; split_all;
assert(wfc (removen k gamma)) by (eapply2 removen_preserves_wfc; eapply2 derive_implies_wfcs).
(* 7 *) 
induction k; split_all; try noway. unfold removen, firstn. eapply2 derive_var. 
eapply2 append_preserves_wfc. 
eapply2 firstn_preserves_wfc. 
simpl. eapply2 tl_preserves_wfc. eapply2 skipn_preserves_wfc. 
(* 6 *) 
induction k; split_all; try noway. unfold removen, firstn. eapply2 derive_weak. 
eapply2 IHd. 
simpl; omega. 
(* 5 *) 
eapply2 derive_abs.
cut(derivation (removen (S k) (ty1 :: gamma)) t ty2); [auto| eapply2 IHd; omega].
(* 4 *) 
eapply2 derive_app. 
eapply2 IHd1. assert(max (maxvar t) (maxvar u) >= maxvar t) by eapply2 max_is_max. omega. 
eapply2 IHd2. assert(max (maxvar t) (maxvar u) >= maxvar u) by eapply2 max_is_max. omega. 
(* 3 *) 
eapply2 derive_inst. 
(* 2 *) 
eapply2 derive_gen1. rewrite map_removen. eapply2 IHd. 
(* 1 *) 
eapply2 derive_push1. 
Qed. 

Lemma derivation_var : 
forall gamma t ty, derivation gamma t ty -> forall i, t = Ref i -> length gamma > i.
Proof. 
intros gamma t ty i; induction i; split_all; subst. 
inversion H1; subst. omega. 
inversion H0; subst.  assert(length gamma > i) by auto. omega. 
assert(length (map (lift 1) gamma) > i0) by auto. 
rewrite map_length in *. auto. 
Qed.  


Lemma derive_via_op: 
forall gamma t ty, derivation gamma t ty -> 
forall o, t = Op o -> forall t1, derivation gamma t1 (opty o) -> derivation gamma t1 ty. 
Proof. 
intros gamma t ty d; induction d; split_all; subst. 
(* 3 *) 
apply derive_inst with ty1; auto. eapply2 IHd. 
(* 2 *)
eapply derive_gen1; auto. eapply2 IHd. 
replace(opty o) with (lift_rec (opty o) 0 1) by (case o; auto). 
unfold lift; eapply2 lift_rec_ty_preserves_derive. 
(* 1 *) 
apply derive_push1 with ty; auto. eapply2 IHd. 
Qed.


Lemma strip_context: forall gamma t ty, derivation gamma t ty -> forall o, t = Op o -> derivation nil (Op o) ty. 
Proof. 
intros gamma t ty d; induction d; split_all; invsub; subst. 
eapply2 derive_inst. 
eapply2 derive_push1. 
Qed. 


