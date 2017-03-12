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
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                     LamSF_Normal.v                                 *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import General.
Require Import Max. 
Require Import Test.
Require Import LamSF_Terms.
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term.
Require Import Components.
Require Import Compounds.
Require Import LamSF_reduction.

(* normal terms *) 

Inductive normal : lamSF -> Prop := 
| nf_ref : forall n, normal (Ref n)
| nf_op : forall o, normal (Op o)
| nf_abs : forall M, normal M -> normal (Abs M)
| nf_app : forall M1 M2, normal M1 -> normal M2 -> status (App M1 M2) <> Reducible -> 
                         normal (App M1 M2)  
.

Hint Constructors normal.


Lemma lift_rec_preserves_normal :
forall M, normal M  -> forall n k, normal(lift_rec M n k).
Proof. 
intros M nor; induction nor; split_all.
eapply2 nf_app.
assert(status (lift_rec (App M1 M2) n k) = relocate_status(status (App M1 M2)) n k). 
eapply2 lift_rec_preserves_status. 
unfold lift_rec in H0; fold lift_rec in H0. 
rewrite H0. 
unfold relocate_status. 
intro. 
gen2_case H H1 (status (App M1 M2)). 
Qed.


Lemma normal_I : normal i_op.
Proof. 
split_all; unfold_op; repeat eapply2 nf_app; intro; split_all; simpl in *; discriminate. Qed. 

Hint Resolve normal_I. 

Lemma normal_status : 
forall M, normal M -> status M <> Reducible. 
Proof. 
intros M nor; induction nor; split_all; eauto.
case o; intro; split_all. 
intro. gen2_case IHnor H (status M); gen2_case IHnor H n.
Qed. 


Lemma normal_star :  forall M, normal M -> normal (star M). 
Proof.  
intros M nor; induction nor; split_all; unfold_op; split_all. 
(* 4 *) 
case n; split_all.  eapply2 nf_app; split_all. 
(* 3 *) 
eapply2 nf_app. split_all.   
(* 2 *) 
eapply2 nf_app. split_all. 
(* 1 *) 
repeat eapply2 nf_app; unfold compound; split_all.   
Qed.

Lemma normal_component_l : forall M, normal M -> normal (left_component M). 
Proof.  
intros M nor; induction nor; split_all; unfold_op; split_all; 
repeat eapply2 nf_app; unfold compound; split_all.
Qed.

Lemma normal_component_r : forall M, normal M -> normal (right_component M). 
Proof.  intros M nor; induction nor; split_all; unfold_op; split_all. 
eapply2 normal_star. 
Qed.


Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma ref_irreducible : forall n, irreducible (Ref n) lamSF_red1. 
Proof. intro n. red. split_all. inversion H; auto. Qed. 

(* restore? 
Lemma app3_not_compound: 
forall M N1 N2 N3, status (App (App (App M N1) N2) N3) = Compound -> False. 
Proof. 
rank_tac; split_all. 
gen_case H0 (status M). 
gen_case H0 M. 
gen_case H0 l. 
gen_case H0 o. 
gen_case H0 (status l0). 
gen_case H0 (status l0); gen_case H0 (status N1). 
gen_case H0 (status l0); gen_case H0 (status N2). 
gen_case H0 l1. 
gen_case H0 o. 
gen_case H0 (status l2). 
gen_case H0 (status l2); gen_case H0 (status N1). 
gen_case H0 M. 
gen_case H0 o. 
gen_case H0 (status N1). 
gen_case H0 (status N1); gen_case H0 (status N2). 
gen_case H0 (status N1); gen_case H0 (status N3). 
gen_case H0 l. 
gen_case H0 o. 
gen_case H0 (status l0). 
gen_case H0 (status l0); gen_case H0 (status N2). 
Qed. 

*) 

Lemma Reducible_implies_reducible : 
forall M, status M = Reducible -> exists N, lamSF_red1 M N.
Proof. 
rank_tac. 
induction M; intros; try (simpl in *; discriminate). 
(* 3 *) 
gen_case H0 o. 
(* 2 *) 
simpl in *. gen2_case IHM H0 (status M). 
(* 4 *) 
assert(exists N, lamSF_red1 M N).  eapply2 IHM. omega. split_all. exist (Abs x). 
(* 3 *) 
gen2_case IHM H0 n. 
(* 2 *) 
gen2_case IHM H0 n. 
(* 1 *) 
assert(status M1 = Reducible \/ status M2 = Reducible \/ 
       (exists i, status M1 = Lam i) \/ 
       status M1 = Lazy1 \/ 
       status M1 = Unary_op \/ 
       (status M1 = Binary_op2 /\ compound M2) \/ 
       (status M1 = Eager /\ factorable M2)).
unfold factorable, compound.  
simpl in *; gen2_case H0 IHM1 (status M1); eauto;
gen2_case IHM2 H0 (status M2); auto 30. 
(* 1 *) 
inversion H1. simpl in *; elim(IHM1); split_all; try omega.  exist (App x M2).  
inversion H2. simpl in *; elim(IHM2); split_all; try omega.  exist (App M1 x).  
inversion H3. split_all. assert(exists M0, M1 = Abs M0) by eapply2 lam_is_abs. 
    split_all; subst. eauto. 
inversion H4. 
(* 2 *) 
gen2_case H H5 M1. gen_case H5 o. eauto. gen2_case H H5 l. gen_case H5 o; eauto;
try (gen_case H5 (status l0); fail). 
(* 3 *) 
eauto. 
(* 2 *) 
gen2_case H H5 l1; eauto.  gen_case H5 o; eauto. 
(* 5 *) 
gen2_case H H5 (status l2); gen2_case H H5 (status l0). 
(* 4 *) 
gen2_case H H5 (status l2); gen2_case H H5 (status l0). 
(* 3 *) 
gen2_case H H5 (status l0).
(* 2 *) 
gen_case H5 (status l3); try (gen_case H5 (status l2); fail).   
gen_case H5 (status l4);  
gen_case H5 (status l2). 
gen_case H5 (status l0). 
gen_case H5 (status l4);  
gen_case H5 (status l2). 
(* 1 *) 
inversion H5. split_all. 
gen3_case H H0 H6 M1; eauto. gen3_case H H0 H6 o; eauto. 
gen_case H6 (status l); gen_case H6 (status l0). 
inversion H6; split_all. 
gen3_case H H0 H8 M1; eauto. gen3_case H H0 H8 o; eauto. 
gen_case H8 (status l); gen_case H8 (status l0). 
(* 1 *) 
gen_case H8 M1; eauto. 
gen_case H8 o; eauto. 
gen_case H8 l; eauto. 
gen_case H8 o; eauto; try (gen_case H8 (status l0); fail). 
assert(exists o, l0 = Op o). 
gen_case H8 l0; eauto. 
gen_case H8 (status l1); eauto; 
gen_case H8 n; eauto. 
gen_case H8 (status l1); eauto;
gen_case H8 (status l2); eauto.
split_all. subst. 
assert(M2 = Op x \/ M2 <> Op x) by (repeat decide equality). inversion H7; subst; eauto. 
elim(factorable_implies_compound_or_operator M2); split_all; subst; eauto.  
(* 1 *) 
assert(status l1 = Ternary_op1). 
gen_case H8 (status l1); try (gen_case H8 (status l2); fail). 
(* 4 *) 
gen_case H8 (status l2); gen_case H8 (status l0). 
(* 3 *) 
gen_case H8 (status l0). 
gen_case H8 (status l0). 
elim(factorable_implies_compound_or_operator M2); split_all; subst; eauto.  
gen_case H7 l1; eauto. gen_case H7 o; eauto.
assert(M2 = Op Sop \/ M2 <> Op Sop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Aop \/ M2 <> Op Aop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Kop \/ M2 <> Op Kop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Eop \/ M2 <> Op Eop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Gop \/ M2 <> Op Gop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Qop \/ M2 <> Op Qop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Uop \/ M2 <> Op Uop) by (repeat decide equality). inversion H11; subst; eauto. 
assert(M2 = Op Yop \/ M2 <> Op Yop) by (repeat decide equality). inversion H11; subst; eauto. 
gen_case H7 (status l3); 
gen_case H7 (status l4). 
gen_case H7 l1. gen_case H7 o; eauto.  
assert(x = Sop \/ x <> Sop) by (repeat decide equality). inversion H10; subst; eauto.
 assert(Op x <> Op Sop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Aop \/ x <> Aop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Aop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Kop \/ x <> Kop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Kop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Eop \/ x <> Eop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Eop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Gop \/ x <> Gop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Gop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Qop \/ x <> Qop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Qop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Uop \/ x <> Uop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Uop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
assert(x = Yop \/ x <> Yop) by (repeat decide equality). inversion H10; subst; eauto. 
 assert(Op x <> Op Yop) by (intro; eapply2 H11; inversion H12; auto). eauto. 
(* 2 *) 
eauto. 
(* 1 *) 
gen_case H7 (status l3); gen_case H7 (status l4). 
Qed. 




Lemma active_irreducible : forall M, forall i, status M = Active i ->  irreducible (left_component M) lamSF_red1 ->  irreducible (right_component M) lamSF_red1 -> irreducible M lamSF_red1. 
Proof. 
rank_tac. 
induction M; intros rk i s l r;  red; split_all. 
(* 4 *) 
inversion H. 
(* 3 *) 
inversion H. 
(* 2 *)
simpl in s. gen_case s (status M); gen_case s n. 
(* 1 *) 
inversion H; subst; 
try (simpl in s; try discriminate; gen_case s (status M); gen_case s n; fail). 
(* 18 *) 
eapply2 l.
(* 17 *) 
eapply2 r. 
(* 16 *)
simpl in s.  gen_case s o. 
(* 15 *) 
simpl in s.  gen_case s o;  unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
(* 14 *) 
simpl in s. unfold compound in H3; gen2_case H3 s (status M2); or_tac.
(* 13 *) 
simpl in s. unfold factorable in H3; gen2_case H3 s (status M2); or_tac.
(* 12 *)
simpl in s.  gen_case s o. 
(* 11 *) 
simpl in s.  unfold compound in H3; gen2_case H3 s (status M2); or_tac.
(* 10 *) 
simpl in s.  gen_case s o. 
(* 9 *) 
simpl in s. unfold compound in H3; gen2_case H3 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
simpl in s. unfold factorable in H2; gen2_case H2 s (status M2); or_tac.
Qed. 


Lemma abs_irreducible : 
forall M, irreducible M lamSF_red1 ->  irreducible (Abs M) lamSF_red1. 
Proof. red; split_all. inversion H0. eapply2 H. Qed. 



Lemma normal_is_irreducible: 
forall M, normal M -> irreducible M lamSF_red1. 
Proof. 
intros M nor; induction nor; intros.  
(* 4 *) 
eapply2 ref_irreducible. 
red; split_all. inversion H. 
eapply2 abs_irreducible.
(* 1 *) 
 assert((exists i, status (App M1 M2) = Active i \/ status (App M1 M2) = Lam i) \/ 
status (App M1 M2) = Ternary_op \/
status (App M1 M2) =  Binary_op0 \/
status (App M1 M2) = Binary_op2 \/
status (App M1 M2) =  Binary_op1 \/ 
status (App M1 M2) =  Ternary_op1 \/ 
status (App M1 M2) =  Unary_op \/ 
status (App M1 M2) = Lazy2 \/ 
status (App M1 M2) = Lazy1 \/ 
status (App M1 M2) = Eager2 \/ 
status (App M1 M2) = Eager).
gen_case H (status (App M1 M2)); eauto; auto 20.  
(* 1 *) 
inversion H0; split_all. inversion H2.  
eapply2 active_irreducible.  
simpl in H1. gen_case H1 (status M1); gen_case H1 (status M2). 
(* 1 *) 
inversion H1; split_all. inversion H2.  
gen_case H4 (status M1); gen_case H4 (status M2). 
(* 1 *) 
inversion H2; split_all. inversion H3.  
gen_case H5 (status M1); gen_case H5 (status M2). 
(* 1 *) 
inversion H3; split_all. inversion H4.  
gen_case H6 (status M1); gen_case H6 (status M2). 
(* 1 *) 
inversion H4; split_all. inversion H5.  
gen_case H7 (status M1); gen_case H7 (status M2). 
(* 1 *) 
inversion H5; split_all. inversion H6.  
gen_case H8 M1. gen_case H8 o; intro; split_all; gen_case H8 (status M2). 
gen_case H8 (status l); gen_case H8 n. 
gen_case H8 (status l); gen_case H8 (status l0); gen_case H8 (status M2). 
(* 1 *) 
clear - IHnor1 IHnor2 H6. 
inversion H6; split_all. inversion H.  
gen3_case IHnor1 H H1 M1. gen3_case IHnor1 H H1 o; 
try (intro; split_all;  inversion H0; inversion H5; eapply2 IHnor2; fail). 
gen_case H (status M2). 
gen2_case H H1 (status l); gen2_case H H1 n. 
(* 2 *) 
gen3_case IHnor1 H H1 l.  gen3_case IHnor1 H H1 o; 
try (gen3_case IHnor1 H H1 (status l0); gen3_case IHnor1 H H1 (status M2); fail).
gen3_case IHnor1 H H1 (status l1); gen3_case IHnor1 H H1 n. 
gen3_case IHnor1 H H1 (status l1).
(* 6 *) 
 gen3_case IHnor1 H H1 (status l2);  
 gen3_case IHnor1 H H1 (status l0).  
 gen3_case IHnor1 H H1 (status l0).  
 gen3_case IHnor1 H H1 (status M2).  
gen3_case IHnor1 H H1 (status l0).  
gen3_case IHnor1 H H1 (status l2).  
(* 1 *) 
inversion H. 
inversion H0; split_all. 
gen3_case IHnor1 H H2 M1. gen3_case IHnor1 H H2 o;
try(intro; split_all;  inversion H1; inversion H7; eapply2 IHnor2; fail). 
gen2_case H H2 (status M2). 
gen2_case H H2 (status l); gen2_case H H2 n. 
(* 2 *) 
gen3_case IHnor1 H H2 l.  gen3_case IHnor1 H H2 o; 
try (gen3_case IHnor1 H H2 (status l0); fail); 
try (intro; split_all;  inversion H1; 
[ inversion H7; [  inversion H11 | eapply2 IHnor1] | eapply2 IHnor2]; fail). 
(* 6 *) 
gen3_case IHnor1 H H2 (status l0);  gen3_case IHnor1 H H2 (status M2). 
(* 5 *) 
gen3_case IHnor1 H H2 (status M2);  gen3_case IHnor1 H H2 n. 
(* 4 *) 
gen3_case IHnor1 H H2 (status M2).
(* 3 *) 
gen3_case IHnor1 H H2 (status l1); gen3_case IHnor1 H H2 n.       
(* 2 *)
gen3_case IHnor1 H H2 (status l1). 
gen3_case IHnor1 H H2 (status l2); 
gen3_case IHnor1 H H2 (status l0).  
gen3_case IHnor1 H H2 (status l0).  
gen3_case IHnor1 H H2 (status M2).  
gen3_case IHnor1 H H2 (status l0).  
gen3_case IHnor1 H H2 (status l2); 
gen3_case IHnor1 H H2 (status l0).  
(* 1 *) 
inversion H0. 
inversion H1; split_all. 
gen3_case IHnor1 H1 H3 M1. gen3_case IHnor1 H1 H3 o;
try(intro; split_all;  inversion H2; inversion H8; eapply2 IHnor2; fail). 
gen2_case H1 H3 (status M2). 
gen2_case H1 H3 (status l); gen2_case H1 H3 n. 
(* 2 *) 
gen3_case IHnor1 H1 H3 l.  gen3_case IHnor1 H1 H3 o; 
try (intro; intro; inv lamSF_red1; [eapply2 IHnor1 | eapply2 IHnor2]). 
(* 6 *) 
gen3_case IHnor1 H1 H3 (status l0);  gen3_case IHnor1 H1 H3 (status M2). 
(* 5 *) 
gen3_case IHnor1 H1 H3 (status M2);  gen3_case IHnor1 H1 H3 n. 
(* 4 *) 
gen3_case IHnor1 H1 H3 (status M2).
(* 3 *) 
gen3_case IHnor1 H1 H3 (status l1); gen3_case IHnor1 H1 H3 n.       
(* 2 *)
gen3_case IHnor1 H1 H3 (status l1). 
gen3_case IHnor1 H1 H3 (status l2); 
gen3_case IHnor1 H1 H3 (status l0).  
gen3_case IHnor1 H1 H3 (status l0).  
gen3_case IHnor1 H1 H3 (status M2).  
gen3_case IHnor1 H1 H3 (status l0).  
gen3_case IHnor1 H1 H3 (status l2); 
gen3_case IHnor1 H1 H3 (status l0).  
(* 1 *) 
inversion H1; split_all. 
(* 2 *) 
gen3_case IHnor1 H1 H2 M1. gen3_case IHnor1 H1 H2 o;
try (intro; intro; inv lamSF_red1; eapply2 IHnor2). 
(* 4 *) 
gen3_case IHnor1 H1 H2 (status M2). 
(* 3 *) 
gen3_case IHnor1 H1 H2 (status l); gen3_case IHnor1 H1 H2 n. 
(* 2 *) 
gen3_case IHnor1 H1 H2 l.  gen3_case IHnor1 H1 H2 o. 
(* 6 *) 
gen2_case H1 H2 (status l0); gen2_case H1 H2 (status M2). 
(* 5 *) 
gen2_case H1 H2 (status M2). 
gen2_case H1 H2 (status M2). 
gen2_case H1 H2 (status l1); gen2_case H1 H2 n. 
gen2_case H1 H2 (status l1). 
gen3_case IHnor1 H1 H2 (status l2); 
gen3_case IHnor1 H1 H2 (status l0).  
gen3_case IHnor1 H1 H2 (status l0).  
gen3_case IHnor1 H1 H2 (status M2).  
gen3_case IHnor1 H1 H2 (status l0).  
gen3_case IHnor1 H1 H2 (status l2); 
gen3_case IHnor1 H1 H2 (status l0).   
(* 1 *) 
gen3_case IHnor1 H1 H2 M1. gen3_case IHnor1 H1 H2 o.
(* 5 *) 
assert(exists o, M2 = Op o). 
gen3_case IHnor1 H1 H2 M2; eauto. 
gen3_case IHnor1 H1 H2 (status l); gen2_case H1 H2 n.
gen3_case IHnor1 H1 H2 (status l); gen3_case IHnor1 H1 H2 (status l0).  
split_all. intro; intro; inv lamSF_red1.  inversion H9. 
unfold compound in H7; gen_case H7 x; or_tac. 
intro; intro; inv lamSF_red1.  eapply2 IHnor2. 
intro; intro; inv lamSF_red1.  eapply2 IHnor2. 
gen3_case IHnor1 H1 H2 (status l); gen2_case H1 H2 n.
(* 1 *) 
gen2_case H1 H2 l.  gen3_case IHnor1 H1 H2 o;
try (intro; intro; inv lamSF_red1; try (eapply2 IHnor1; fail); try (eapply2 IHnor2; fail); fail). 
(* 5 *) 
gen3_case IHnor1 H1 H2 (status l0); 
gen3_case IHnor1 H1 H2 (status M2) . 
gen3_case IHnor1 H1 H2 (status M2).  
gen3_case IHnor1 H1 H2 (status M2).  
gen3_case IHnor1 H1 H2 (status l1); gen2_case H1 H2 n.  
gen3_case IHnor1 H1 H2 (status l1). 
gen3_case IHnor1 H1 H2 (status l2); 
gen3_case IHnor1 H1 H2 (status l0).  
gen3_case IHnor1 H1 H2 (status l0).  
gen3_case IHnor1 H1 H2 (status M2).  
gen3_case IHnor1 H1 H2 (status l0).  
gen3_case IHnor1 H1 H2 (status l2); 
gen3_case IHnor1 H1 H2 (status l0).   
Grab Existential Variables. 
apply s_op. 
Qed. 

Lemma normal_not_Reducible: forall M, normal M -> status M <> Reducible. 
Proof. 
intros; intro. elim(Reducible_implies_reducible M); split_all. eapply2 normal_is_irreducible. 
Qed.



(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Theorem progress : 
forall (M : lamSF), normal M \/ (exists N, lamSF_red1 M N) .
Proof. 
rank_tac. 
induction M; try (inversion IHM); subst; split_all; eauto.
(* 2 *) 
elim IHM; split_all; try omega. 
right; exist (Abs x).  
(* 1 *) 
elim IHM1; elim IHM2; split_all; eauto; try omega. 
clear IHp IHM1 IHM2 H.
inversion H1; subst; eauto. 
(* 3 *) 
left; eapply2 nf_app. split_all.
(* 2 *) 
case o; try (left; eapply2 nf_app; simpl; split_all; unfold compound; or_tac; fail).
gen_case H0 M2; try (left; eapply2 nf_app; simpl; split_all; unfold compound; or_tac; fail).  
left; eapply2 nf_app; simpl; split_all. case o0; split_all. 
assert(status (Abs l) <> Reducible) by eapply2 normal_not_Reducible. 
 assert((exists i, status (Abs l) = Active i \/ status (Abs l) = Lam i) \/ factorable (Abs l)). 
unfold factorable. gen_case H (status (Abs l)); eauto; auto 20.  
inversion H2; split_all. 
inversion H4; left; eapply2 nf_app; simpl in *; rewrite H3; intro; discriminate. 
elim(factorable_implies_compound_or_operator (Abs l)); split_all; subst; eauto. 
(* 3 *) 
inversion H0. 
 assert((exists i, status (App l l0) = Active i \/ status (App l l0) = Lam i) \/ 
factorable(App l l0)). unfold factorable. 
gen_case H5 (status (App l l0)); eauto; auto 20.  
inversion H6; split_all. 
inversion H8; left; eapply2 nf_app; split_all; intro; simpl in *; rewrite H7 in H9; discriminate. 
(* 3 *) 
elim(factorable_implies_compound_or_operator (App l l0)); split_all; subst; eauto. 
(* 2 *) 
eauto. 
(* 1 *) 
assert(status M2 <> Reducible) by eapply2 normal_not_Reducible. 
assert(status M0 <> Reducible) by eapply2 normal_not_Reducible. 
assert(status M3 <> Reducible) by eapply2 normal_not_Reducible. 
assert((exists i, status M2 = Active i \/ status M2 = Lam i) \/ factorable M2). 
unfold factorable. gen_case H4 (status M2); eauto; auto 20.  
assert((exists i, status M0 = Active i \/ status M0 = Lam i) \/ factorable M0). 
unfold factorable. gen_case H5 (status M0); eauto; auto 20.  
assert((exists i, status M3 = Active i \/ status M3 = Lam i) \/ factorable M3). 
unfold factorable. gen_case H6 (status M3); eauto; auto 20.  
 assert((exists i, status (App M0 M3) = Active i \/ status (App M0 M3) = Lam i) \/ 
factorable (App M0 M3)). unfold factorable.
gen_case H3 (status (App M0 M3)); eauto; auto 20.  
(* 1 *) 
inversion H10; split_all. 
inversion H12.
 left; eapply2 nf_app; simpl in *; intro;  rewrite H11 in *; discriminate. 
assert(exists N, App M0 M3 = Abs N) by eapply2 lam_is_abs. split_all. 
(* 1 *) 
unfold factorable in H11. inversion H11; split_all. inversion H12.  
gen_case H14 (status M0); gen_case H14 (status M3). 
(* 1 *) 
inversion H12; split_all. inversion H13.  
gen_case H15 (status M0); gen_case H15 (status M3). 
(* 1 *) 
inversion H13; split_all. inversion H14.  
gen_case H16 (status M0); gen_case H16 (status M3). 
(* 1 *) 
inversion H14; split_all. inversion H15.  
gen_case H17 (status M0); gen_case H17 (status M3). 
(* 1 *) 
inversion H15; split_all. inversion H16.  
gen_case H18 (status M0); gen_case H18 (status M3). 
(* 1 *) 
inversion H16; split_all. simpl in *. 
gen_case H17 (status M0); gen_case H17 (status M3). 
(* 1 *) 
inversion H17; split_all. inversion H18.  
gen_case H20 M0.  gen_case H20 o.
left; repeat eapply2 nf_app; simpl; split_all. 
left; repeat eapply2 nf_app; simpl; split_all. 
gen_case H20 (status M3). 
right; eauto. 
(* 2 *) 
gen_case H20 l. gen_case H20 o; try (gen_case H20 (status l0); fail). 
gen_case H20 (status l0); try (gen_case H20 (status M3); fail).
gen_case H20 (status M3).
gen_case H20 (status M3).
right; eauto. 
gen_case H20 (status l1).  
gen_case H20 (status l2); gen_case H20 (status l0). 
gen_case H20 (status l0). 
gen_case H20 (status M3). 
gen_case H20 (status l0). 
gen_case H20 (status l2). 
(* 1 *) 
inversion H18; split_all. inversion H19.  
gen_case H21 M0.  gen_case H21 o.
right; eauto. 
gen_case H21 (status M3). 
right; eauto. 
right; eauto. 
gen_case H21 l.  gen_case H21 o; eauto. 
gen_case H21 (status l0);  gen_case H21 (status M3).  
gen_case H21 (status M3).  
gen_case H21 (status M3).  
eauto. 
gen_case H21 (status l1).   
gen_case H21 (status l2);  gen_case H21 (status l0).  
gen_case H21 (status l0).  
gen_case H21 (status M3).  
gen_case H21 (status l0).  
gen_case H21 (status l2).  
(* 1 *) 
inversion H19; split_all. inversion H20.  
gen_case H22 M0.  gen_case H22 o; try (left; repeat eapply2 nf_app; simpl; split_all; fail).  
gen_case H22 (status M3).
right; eauto. 
gen_case H22 l.  gen_case H22 o; try (right; eauto; fail). 
gen_case H22 (status l0);  gen_case H22 (status M3).  
gen_case H22 (status M3).  
gen_case H22 (status M3).  
right; eauto. 
gen_case H22 (status l1).   
gen_case H22 (status l2);  gen_case H22 (status l0).  
gen_case H22 (status l0).  
gen_case H22 (status M3).  
gen_case H22 (status l0).  
gen_case H22 (status l2).  
(* 1 *) 
gen2_case H H20 M0.  
(* 3 *) 
gen_case H20 o; try (left; repeat eapply2 nf_app; simpl; split_all; fail).  
(* 5 *) 
assert(exists o, M3 = Op o). 
gen_case H20 M3. eauto. gen_case H20 (status l); gen_case H20 n.
gen_case H20 (status l);  gen_case H20 (status l0).
(* 5 *) 
split_all. subst. 
inversion H7; split_all.
inversion H22;
left; repeat eapply2 nf_app; simpl; case x; auto; try (intro; discriminate); rewrite H21; auto;
 try (intro; discriminate).  
assert(M2 = Op x \/ M2 <> Op x) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 4 *) 
inversion H7; split_all.
inversion H22;
left; repeat eapply2 nf_app; simpl; case x; auto; try (intro; discriminate); rewrite H21; auto;
 try (intro; discriminate).  
eauto. 
(* 3 *) 
inversion H7; split_all.
inversion H22;
left; repeat eapply2 nf_app; simpl; case x; auto; try (intro; discriminate); rewrite H21; auto;
 try (intro; discriminate).  
elim(factorable_implies_compound_or_operator M2); split_all; subst; eauto. 
(* 2 *) 
right; eauto. 
(* 1 *) 
gen_case H20 l.  2: right; eauto. 
gen_case H20 o; try (gen_case H20 (status M3); fail). 
 
(* 11 *) 
assert(exists o, l0 = Op o). 
gen_case H20 l0. eauto. gen_case H20 (status l1); gen_case H20 n.
gen_case H20 (status l2);  gen_case H20 (status l1).
split_all. subst. 
inversion H9; split_all. 
inversion H22; left; repeat eapply2 nf_app; simpl; case x; auto; try (intro; discriminate);  rewrite H21; auto;
 try (intro; discriminate).  
assert(M3 = Op x \/ M3 <> Op x) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 10 *) 
inversion H7; split_all.
inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate); rewrite H27; auto;
 try (intro; discriminate).  
elim(factorable_implies_compound_or_operator M2); split_all; subst; eauto. 
(* 9 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Sop \/ M2 <> Op Sop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 8 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Aop \/ M2 <> Op Aop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 7 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Kop \/ M2 <> Op Kop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 6 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Eop \/ M2 <> Op Eop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 5 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Gop \/ M2 <> Op Gop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 4 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Qop \/ M2 <> Op Qop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 3 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Uop \/ M2 <> Op Uop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 2 *) 
inversion H7; split_all.  inversion H. 
inversion H22; left; repeat eapply2 nf_app; simpl;  case x; auto; try (intro; discriminate);
 rewrite H27; auto;
 try (intro; discriminate).  
assert(M2 = Op Yop \/ M2 <> Op Yop) by repeat decide equality. 
inversion H22; right; subst;  eauto. 
(* 1 *) 
gen_case H20 (status l1). 
gen_case H20 (status l2); gen_case H20 (status l0). 
 gen_case H20 (status l0). 
 gen_case H20 (status M3). 
 gen_case H20 (status l0). 
gen_case H20 (status l2); gen_case H20 (status l0). 
Qed. 





Lemma irreducible_is_normal: 
forall M, irreducible M lamSF_red1 -> normal M. 
Proof. split_all. elim(progress M); split_all. assert False by eapply2 H; noway. Qed. 

Theorem irreducible_iff_normal: forall M, irreducible M lamSF_red1 <-> normal M. 
Proof. split_all. eapply2 irreducible_is_normal. eapply2 normal_is_irreducible. Qed. 


Lemma normal_is_stable: forall M, normal M -> forall N, lamSF_red M N -> N = M.
Proof. 
split_all. 
inversion H0; inv1 lamSF_red. 
assert False by eapply2 normal_is_irreducible. noway. 
Qed. 


