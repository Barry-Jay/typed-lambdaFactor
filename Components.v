(**********************************************************************)
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

(**********************************************************************)
(*               Typed LambdaFactor Calculus                          *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                     Components.v                                   *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(**********************************************************************)

Require Import Arith.
Require Import Test. 
Require Import General.
Require Import LamSF_Terms. 
Require Import LamSF_Tactics.
Require Import LamSF_Substitution_term. 


Definition s_op := Op Sop.
Definition a_op := Op Aop.
Definition k_op := Op Kop.
Definition e_op := Op Eop.
Definition g_op := Op Gop.
Definition q_op := Op Qop.
Definition u_op := Op Uop.
Definition y_op := Op Yop.
Definition i_op := App (App s_op k_op) k_op.
Definition other_left := App (App s_op k_op) i_op.
Definition abs_left := i_op . (* App (App s_op (App (App s_op (App k_op s_op)) k_op)) (App k_op i_op). *) 

Ltac unfold_op := unfold abs_left, other_left, 
i_op, s_op, a_op, k_op, e_op, g_op, q_op, u_op, y_op.


Ltac or_tac := 
match goal with 
| H : _ \/ _ |- _ =>  inversion H; [ discriminate | clear H; or_tac ]
| _ => split_all
end. 



(* rank *) 

Definition abs_rank := 18. 
(* chosen to ensure that star reduces the rank *) 

Fixpoint rank (M: lamSF) := 
match M with 
| Ref _ => 1
| Op _ => 1
| App M1 M2 => S((rank M1) + (rank M2))
| Abs M1 =>  abs_rank * rank M1
end.

Lemma rank_positive: forall M, rank M > 0. 
Proof. 
induction M; split_all; try omega. 
Qed. 


Ltac rank_tac := match goal with 
| |- forall M, ?P  => 
cut (forall p M, p >= rank M -> P ); [ intros H M;  eapply2 H | 
intro p; induction p; intro M;  [ assert(rank M >0) by eapply2 rank_positive; noway |]
]
end .



Lemma lift_rec_preserves_rank : 
forall (M: lamSF) (n k: nat), rank (lift_rec M n k) = rank M.
Proof. induction M; split_all. Qed. 


(* star abstraction *) 


 
Fixpoint star M := 
match M with 
| Ref 0 => i_op 
| Ref (S n) => App k_op (Ref n)
| Op o => App k_op (Op o)
| Abs M1 =>  App a_op (Abs (star M1))
| App M1 M2 => App (App s_op (Abs M1)) (Abs M2)
end
.

Lemma rank_star: 
forall M, rank (star M) < rank (Abs M). 
Proof. induction M; split_all; simpl in *; try omega. (* slow *)  case n; split_all; omega. Qed. 


Lemma star_monotonic: 
forall M N, 
star M = star N -> M = N. 
Proof. 
induction M; split_all. 
(* 4 *) 
gen_case H n. 
(* 5 *) 
gen_case H N; try discriminate. 
gen_case H n0; discriminate.
(* 4 *) 
gen_case H N. 
gen_case H n1. 
discriminate. 
(* 3 *) 
gen_case H N. 
gen_case H n.
discriminate. 
(* 2 *) 
gen_case H N. 
gen_case H n.
discriminate. 
inversion H. 
assert(M = l). eapply2 IHM. 
congruence. 
discriminate. 
(* 1 *) 
gen_case H N. 
gen_case H n.
discriminate. 
discriminate. 
Qed. 



Lemma lift_rec_preserves_star : forall (M : lamSF) n k, 
  lift_rec(star M) n k = star (lift_rec M (S n) k).
Proof. 
induction M; split_all. 
 case n; split_all. 
rewrite relocate_succ. auto.
rewrite IHM. auto. 
Qed. 

(* components *) 


Fixpoint right_component (M : lamSF) := 
match M with 
| Op o => k_op
| App _ M2 => M2
| Abs M1 => star M1
| _ => M
end.

Definition left_component (U : lamSF) := 
match U with 
| Op o => App k_op (Op o)
| Abs _ => abs_left
| App U1 _ => U1 
| _ => other_left 
end.


Lemma  lift_rec_preserves_components_l : forall (M : lamSF) n k, 
  lift_rec(left_component M) n k = left_component(lift_rec M n k).
Proof. induction M; split_all; case b0; case b; split_all. Qed. 

Lemma  lift_rec_preserves_components_r : forall (M : lamSF) n k, 
  lift_rec(right_component M) n k = right_component(lift_rec M n k).
Proof. induction M; split_all. 
rewrite lift_rec_preserves_star.  
auto. 
Qed. 


