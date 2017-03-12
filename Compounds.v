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
(*                     Compounds.v                                    *)
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
Require Import Components.

(* status *) 

(* If a term has a head reduction then it is Reducible. 
   If it is an abstraction with an active variable then it is a Lam.
   If it is a variable application then it is  Active. 
   Operators and compounds are characterised by the influence of additional arguments. 
*) 


Inductive status_val := 
| Reducible : status_val
| Lam : nat -> status_val     (* the active variable *) 
| Active : nat -> status_val  (* the active variable *) 
| Ternary_op (* S, A *) 
| Binary_op0 (* K *) 
| Binary_op2 (* E *) 
| Binary_op1 (* G, U *) 
| Ternary_op1 (* Q, case operators *)
| Unary_op (* Y *)  
| Lazy2 (* need two args *) 
| Lazy1 (* need one arg *) 
| Eager2 (* QM, DOM *) 
| Eager (* EO *) 
.

(* If application of an operator to one argument produces a compound, 
   then it uses the same atom_status, e.g. status (KM = Atom 0 *) 

Fixpoint status (M: lamSF) := 
match M with 
| Ref i => Active i
| Op Sop | Op Aop => Ternary_op
| Op Kop => Binary_op0
| Op Eop => Binary_op2
| Op Gop | Op Uop => Binary_op1
| Op Yop => Unary_op
| Op _ => Ternary_op1 
| Abs M1 => match status M1 with 
              | Reducible => Reducible 
              | Lam 0 => Lazy1
              | Lam (S n) => Lam n 
              | Active 0 => Lazy1
              | Active (S n) => Lam n
              | _  => Lazy1
            end 
| App M1 M2 => match status M1 with 
              | Reducible => Reducible 
              | Lam _ => Reducible
              | Active n => Active n                                    
              | Ternary_op => Lazy2 
              | Binary_op0 => Lazy1 
              | Binary_op2 => 
                match status M2 with 
                  | Reducible => Reducible 
                  | Lam n => Active n 
                  | Active n => Active n 
                  | Ternary_op 
                  | Binary_op0
                  | Binary_op2 
                  | Binary_op1 
                  | Ternary_op1 
                  | Unary_op => Eager
                  | _ => Reducible 
                end
              | Binary_op1 => Eager 
              | Ternary_op1 => Eager2
              | Unary_op => Reducible
              | Lazy2 => Lazy1 
              | Lazy1 => Reducible 
              | Eager2 => Eager 
              | Eager => 
                match status M2 with 
                  | Lam n => Active n 
                  | Active n => Active n 
                  | _ => Reducible 
                end
               end
end.

Lemma star_compound : 
forall M, status (star M) = Lazy1 \/ status(star M) = Lazy2.
Proof. induction M; split_all; try (case n); split_all.   Qed. 

Definition compound M := 
(status M = Lazy2) \/ 
(status M = Lazy1) \/ 
(status M = Eager2) \/ 
(status M = Eager). 

Definition factorable M := 
(status M = Ternary_op) \/
(status M = Binary_op0) \/
(status M = Binary_op2) \/ 
(status M = Binary_op1) \/ 
(status M = Ternary_op1) \/
(status M = Unary_op) \/
(status M = Lazy2) \/ 
(status M = Lazy1) \/ 
(status M = Eager2) \/ 
(status M = Eager). 

Lemma compounds_are_factorable: forall M, compound M -> factorable M.
Proof. split_all.  unfold factorable; inversion H; split_all;  auto 10. Qed. 

Lemma factorable_applications_are_compounds: 
forall M N, factorable (App M N) -> compound(App M N).
Proof.
unfold factorable, compound; split_all. gen_case H (status M);  
try (inversion H; [ discriminate |  
inversion H0; [ discriminate | 
inversion H1; [ discriminate | 
inversion H2; [ discriminate |  
inversion H3; [ discriminate | 
inversion H4; discriminate ]]]]]); or_tac.  
(* 2 *) 
gen_case H (status N);
try (inversion H; [ discriminate |  
inversion H0; [ discriminate | 
inversion H1; [ discriminate | 
inversion H2; [ discriminate |  
inversion H3; [ discriminate | 
inversion H4; discriminate ]]]]]); or_tac. 
(* 1 *) 
gen_case H (status N);
try (inversion H; [ discriminate |  
inversion H0; [ discriminate | 
inversion H1; [ discriminate | 
inversion H2; [ discriminate |  
inversion H3; [ discriminate | 
inversion H4; discriminate ]]]]]); or_tac. 
Qed. 

Lemma factorable_abstractions_are_compounds: 
forall M, factorable (Abs M) -> compound (Abs M). 
Proof.
unfold factorable, compound; split_all. gen_case H (status M);  or_tac; gen_case H n; or_tac. 
Qed. 


Lemma factorable_implies_compound_or_operator: 
forall M, factorable M -> (compound M \/ exists o, M = Op o).
Proof. 
unfold factorable, compound; split_all. gen_case H M; or_tac. 
right; eauto. 
gen_case H (status l); or_tac; gen_case H n; or_tac. 
gen_case H (status l); or_tac; gen_case H (status l0); or_tac.  
Qed. 


Definition preserves_components_l (red: termred) := 
forall M, factorable M -> forall N, red M N -> factorable N /\ 
multi_step red (left_component M) (left_component N).

Lemma preserves_components_l_multi_step : 
forall red, preserves_components_l red -> 
forall M, factorable M -> forall N, multi_step red M N -> factorable N /\ 
multi_step red (left_component M) (left_component N).
Proof. 
intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p. 
apply transitive_red with (left_component N); split_all. 
eapply2 p. eapply2 IHR. eapply2 p. 
Qed. 



Definition preserves_components_r (red: termred) := 
forall M, factorable M -> forall N, red M N -> factorable N /\ 
multi_step red (right_component M) (right_component N).

Lemma preserves_components_r_multi_step : 
forall red, preserves_components_r red -> 
forall M, factorable M -> forall N, multi_step red M N -> factorable N /\ 
multi_step red (right_component M) (right_component N).
Proof. 
intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p. 
apply transitive_red with (right_component N); split_all. 
eapply2 p. eapply2 IHR. eapply2 p. 
Qed. 


Definition relocate_status a n k := 
match a with 
| Lam i => Lam (relocate i n k)
| Active i => Active (relocate i n k)
| _ => a
end. 




Lemma rank_compound_l : forall M, compound M -> rank (left_component M) < rank M. 
Proof. 
induction M; split_all; inv1 compound; simpl in *; try discriminate; try (gen_case H0 o); or_tac. 
(* 4 *)  
assert(rank M >0) by eapply rank_positive; omega. 
(* 3 *) 
assert(rank M >0) by eapply rank_positive; omega. 
(* 2 *) 
gen2_case IHM1 H0 (status M1); omega. 
(* 1 *) 
gen2_case IHM1 H0 (status M1); omega. 
Qed. 

Lemma rank_compound_r : forall M, compound M -> rank (right_component M) < rank M. 
Proof. 
induction M; split_all; inv1 compound; simpl in *; try discriminate; try (gen_case H0 o); or_tac. 
(* 4 *) 
gen_case H0 (status M); gen_case H0 n.
(* 3 *)  
gen2_case IHM H0 (status M); 
assert(rank (star M) < rank (Abs M)) by eapply2 rank_star; simpl in *; omega. 
(* 2 *) 
gen2_case IHM1 H0 (status M1). omega. 
gen2_case IHM2 H0 (status M2). 
gen2_case IHM2 H0 (status M2). omega.
Qed. 



Lemma lift_rec_preserves_status : 
forall (M: lamSF) (n k: nat), status (lift_rec M n k) = relocate_status (status M) n k. 
Proof. 
rank_tac. 
induction M; split_all; try (rewrite relocate_succ; auto); 
try (eapply2 IHM1). 
(* 3 *) 
case o; split_all. 
(* 2 *) 
rewrite IHM; try omega. 
unfold relocate_status. 
case (status M); split_all. 
unfold relocate. 
elim(test (S n) n0); split_all; try noway. 
replace (k+ n0) with (S (k+pred n0)) by omega. 
replace n0 with (S (pred n0)) by omega. 
elim(test n (pred n0)); split_all; try noway. 
gen_case b n0. 
elim(test n n1); split_all; try noway. 
unfold relocate. 
elim(test (S n) n0); split_all; try noway. 
replace (k+ n0) with (S (k+pred n0)) by omega. 
replace n0 with (S (pred n0)) by omega. 
elim(test n (pred n0)); split_all; try noway. 
gen_case b n0. 
elim(test n n1); split_all; try noway. 
(* 1 *) 
rewrite IHM1; try omega. 
unfold relocate_status. 
case (status M1); split_all;
rewrite IHM2; try omega;
unfold relocate_status;
case (status M2); split_all. 
Qed. 


Hint Resolve lift_rec_preserves_status. 

Lemma lam_is_abs : forall M i, status M = Lam i -> exists N, M = Abs N. 
Proof. 
induction M; split_all; eauto. 
gen_case H o. 
gen_case H (status M1); gen_case H (status M2). 
Qed. 



Lemma subst_rec_preserves_status: 
forall (M: lamSF)(k : nat), 
(forall i, status M = Active i -> i < k) -> 
(forall i, status M = Lam i -> i < k) -> 
forall N, status (subst_rec M N k) = status M. 
Proof. 
rank_tac. 
induction M; intros. 
(* 4 *) 
invsub. insert_Ref_out; split_all.
(* 3 *) 
split_all.
(* 2 *)
simpl in *. 
gen4_case IHM H H0 H1 (status M); try (rewrite IHM; split_all; omega). 
(* 3 *) 
gen4_case IHM H H0 H1 n.
 rewrite IHM; split_all; try omega. invsub; omega. 
 rewrite IHM; split_all; try omega. invsub. assert(n0<k) by eapply2 H1. omega. 
(* 2 *) 
gen4_case IHM H H0 H1 n.
 rewrite IHM; split_all; try omega. invsub; omega. 
 rewrite IHM; split_all; try omega. invsub. assert(n0<k) by eapply2 H1. omega. 
(* 1 Applications *)
clear H1.  
assert(forall i, status M1 = Lam i -> exists N, M1 = Abs N) by eapply2 lam_is_abs. 
simpl in *. gen3_case IHM1 H0 H1 (status M1); 
try (rewrite IHM1; split_all; simpl in *; omega). 
(* 3 *) 
assert(exists N, M1 = Abs N) by eapply2 H1. split_all; subst.
simpl. 
case(status (subst_rec x N (S k))); split_all. 
case n0; split_all. 
case n0; split_all. 
(* 2 *) 
rewrite IHM1; simpl in *; split_all; try omega.
rewrite IHM2; split_all; try omega. 
rewrite H2 in H0. eapply2 H0. 
rewrite H2 in H0. eapply2 H0. 
(* 1 *) 
rewrite IHM1; simpl in *; split_all; try omega.
rewrite IHM2; split_all; try omega. 
rewrite H2 in H0. eapply2 H0. 
rewrite H2 in H0. eapply2 H0. 
Qed. 





Lemma rank_component_app_l: 
forall M N, rank (left_component (App M N)) < rank (App M N). 
Proof. split_all; omega. Qed. 

Lemma rank_component_app_r: 
forall M N, rank (right_component (App M N)) < rank (App M N). 
Proof. split_all; omega. Qed. 

Lemma rank_component_abs_l: 
forall M, rank (left_component (Abs M)) < rank (Abs M). 
Proof. 
induction M; intros.
(* 4 *)  
split_all; try omega. 
(* 3 *) 
split_all; try omega. 
(* 2 *) 
assert(rank M >0) by eapply2 rank_positive. 
unfold left_component. unfold_op; unfold rank; fold rank. 
replace (abs_rank * (abs_rank * rank M)) with (abs_rank * abs_rank * rank M) by ring.
cut (S (S (1 + S (S (1 + S (1 + 1)) + 1)) + S (1 + S (S (1 + 1) + 1)))  < abs_rank * abs_rank). 
2: unfold abs_rank; split_all; omega. intro. 
replace (rank M) with (1+ (pred (rank M))) by omega. 
replace(abs_rank * abs_rank * (1+ (pred (rank M)))) with
(abs_rank * abs_rank + abs_rank * abs_rank * (pred (rank M))) by ring. 
unfold abs_left, abs_rank; unfold_op. unfold rank at 1. 
assert(1<6*6) by (simpl; omega). omega. 
(* 1 *) 
unfold left_component, abs_left, abs_rank; unfold_op. simpl.  omega. 
Qed. 


Lemma rank_component_abs_r: 
forall M, rank (right_component (Abs M)) < rank (Abs M). 
Proof. 
unfold right_component.  intros. eapply2 rank_star. 
Qed. 



Lemma  subst_rec_preserves_star_active : 
forall (M : lamSF) N i k, status M = Active i -> i <= k  -> 
  subst_rec(star M) N k = star (subst_rec M N (S k)).
Proof. 
induction M; split_all. 
gen_case H n. 
unfold insert_Ref.
elim(compare k n0); elim(compare (S k) (S n0));split_all; try noway. 
elim a; elim a0; split_all; try noway. 
invsub; noway. 
inversion H. noway. 
elim a; split_all; try noway. 
elim a; split_all; try noway.
gen2_case IHM H (status M). 
replace (subst_rec (star M) N (S k)) with (star (subst_rec M N (S(S k)))). 
auto. 
eapply2 eq_sym. 
eapply2 IHM. 
gen_case H n. gen_case H n. 
Qed. 

Lemma  subst_rec_preserves_star_lam : 
forall (M : lamSF) N i k, status M = Lam i -> i <= k  -> 
  subst_rec(star M) N k = star (subst_rec M N (S k)).
Proof. 
induction M; split_all. 
assert(status M = Lam (S i) \/ status M = Active (S i)). 
gen2_case IHM H (status M); gen_case H n; inversion  H; subst; auto. 
inversion H1.
(* 2 *) 
rewrite (IHM N (S i) (S k)); auto. omega. 
(* 1 *) 
rewrite (subst_rec_preserves_star_active M N (S i) (S k)); auto. omega. 
Qed. 


Lemma  subst_rec_preserves_star_factorable : 
forall (M : lamSF) N k, factorable M -> 
  subst_rec(star M) N k = star(subst_rec M N (S k)).
Proof. 
induction M; split_all; inv1 factorable; simpl in *; try discriminate; or_tac. 
(* 2 *) 
gen_case H0 (status M); gen_case H0 n. 
(* 1 *)
assert(       match status M with
       | Reducible => Reducible
       | Lam 0 => Lazy1
       | Lam (S n) => Lam n
       | Active 0 => Lazy1
       | Active (S n) => Lam n
       | Ternary_op => Lazy1
       | Binary_op0 => Lazy1
       | Binary_op2 => Lazy1
       | Binary_op1 => Lazy1
       | Ternary_op1 => Lazy1
       | Unary_op => Lazy1
       | Lazy2 => Lazy1
       | Lazy1 => Lazy1
       | Eager2 => Lazy1
       | Eager => Lazy1
       end = Lazy1). 
gen_case H0 (status M). 
(* 4 *) 
or_tac. 
gen_case H0 n; or_tac. 
gen_case H0 n; or_tac. 
clear H0. 
(* 1 *) 
assert(status M = Lam 0 -> 0 <= (S k)  -> 
  subst_rec(star M) N (S k) = star (subst_rec M N (S (S k)))) by eapply2 subst_rec_preserves_star_lam.
assert(status M = Active 0 -> 0 <= (S k)  -> 
  subst_rec(star M) N (S k) = star (subst_rec M N (S (S k)))) by eapply2 subst_rec_preserves_star_active. 
unfold factorable in *. 
gen4_case IHM H H0 H1 (status M);
try (gen3_case H H0 H1 n); try (rewrite IHM; auto; right; right; auto; fail). 
(* 5 *) 
rewrite H0; auto; omega.  
rewrite H1; auto; omega.  
rewrite IHM; auto 10. 
rewrite IHM; auto 10.
rewrite IHM; auto 10.
rewrite IHM; auto 10.
Qed. 



Lemma  subst_rec_preserves_components_l : forall (M : lamSF) n k, factorable M ->
  subst_rec(left_component M) n k = left_component(subst_rec M n k).
Proof. induction M; split_all; inv1 factorable; simpl in *; or_tac. Qed. 


Lemma  subst_rec_preserves_components_active_r : 
forall (M : lamSF) i,  status M = Active i -> forall N k,  i < k ->  
subst_rec(right_component M) N k = right_component(subst_rec M N k).
Proof. 
induction M; split_all. 
(* 2 *)
invsub.  
insert_Ref_out; split_all. 
assert(forall i k, status M = Active i -> i <= k -> 
  subst_rec(star M) N k = star (subst_rec M N (S k))) 
by eapply2 subst_rec_preserves_star_active. 
gen3_case IHM H H1 (status M). 
gen_case H n. 
gen_case H n. 
Qed. 

Lemma  subst_rec_preserves_components_lam_r : 
forall (M : lamSF) i,  status M = Lam i -> forall N k,  i < k ->  
subst_rec(right_component M) N k = right_component(subst_rec M N k).
Proof. 
induction M; split_all. 
assert(status M = Lam (S i) \/ status M = Active (S i)). 
gen_case H (status M); gen_case H n; invsub. 
inversion H1. 
rewrite (subst_rec_preserves_star_lam M N (S i) k); auto. 
rewrite (subst_rec_preserves_star_active M N (S i) k); auto. 
Qed. 

Lemma  subst_rec_preserves_components_compound_r : 
forall (M : lamSF),  factorable M -> forall n k,   
subst_rec(right_component M) n k = right_component(subst_rec M n k).
Proof. 
induction M; split_all.
(* 2 *) 
inv1 factorable; simpl in *; or_tac. 
(* 1 *) 
assert(status M = Lam 0 \/ status M = Active 0 \/ factorable M). 
inv1 factorable; simpl in *; try discriminate. 
gen_case H0 (status M); gen_case H0 n0.
assert(match status M with
       | Reducible => Reducible
       | Lam 0 => Lazy1
       | Lam (S n) => Lam n
       | Active 0 => Lazy1
       | Active (S n) => Lam n
       | Ternary_op => Lazy1
       | Binary_op0 => Lazy1
       | Binary_op2 => Lazy1
       | Binary_op1 => Lazy1
       | Ternary_op1 => Lazy1
       | Unary_op => Lazy1
       | Lazy2 => Lazy1
       | Lazy1 => Lazy1
       | Eager2 => Lazy1
       | Eager => Lazy1
       end = Lazy1).
gen_case H0 (status M); or_tac; gen_case H0 n0; or_tac. 
(* 2 *) 
clear H0. 
unfold factorable. 
gen_case H (status M); try (gen_case H n0); auto 20.  
(* 1 *) 
inversion H0. rewrite (subst_rec_preserves_star_lam M n 0); auto; omega. 
inversion H1. rewrite (subst_rec_preserves_star_active M n 0); auto; omega.
rewrite (subst_rec_preserves_star_factorable M n k); auto; omega. 
Qed. 



Definition preserves_compound (red:termred) := 
forall M , compound M -> forall N, red M N -> 
compound N /\ red (left_component M) (left_component N) /\ red(right_component M) (right_component N).


Lemma preserves_compound_seq : 
forall (red1 red2:termred), preserves_compound red1 -> preserves_compound red2 -> 
                            preserves_compound (sequential red1 red2). 
Proof. 
red; split_all.  
inversion H2. 
elim(H M H1 N0); split_all. 
eapply2 H0. 
inversion H2. 
elim(H M H1 N0); split_all. 
elim(H0 N0 H9 N); split_all. 
eapply2 seq_red. 
inversion H2. 
elim(H M H1 N0); split_all. 
elim(H0 N0 H9 N); split_all. 
eapply2 seq_red. 
Qed. 


Lemma preserves_compound_multi_step : 
forall (red:termred), preserves_compound red -> preserves_compound (multi_step red). 
Proof. 
red. intros red p M c N R; induction R; split_all. 
eapply2 IHR. eapply2 p.
apply succ_red with (left_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
apply succ_red with (right_component N); auto. 
 eapply2 p. eapply2 IHR. eapply2 p.
Qed. 

Hint Resolve preserves_compound_multi_step.



Lemma lift_rec_preserves_factorable: 
forall M n k, factorable M -> factorable (lift_rec M n k).
Proof. 
intros. 
assert(status (lift_rec M n k) = relocate_status (status M) n k) 
by eapply2 lift_rec_preserves_status. 
unfold factorable in *. 
rewrite H0. 
inversion H. rewrite H1; auto. 
inversion H1. rewrite H2; auto. 
inversion H2. rewrite H3; auto. 
inversion H3. rewrite H4; auto. 
inversion H4. rewrite H5; auto 20. 
inversion H5. rewrite H6; auto 20. 
inversion H6. rewrite H7; auto 20. 
inversion H7. rewrite H8; auto 20. 
inversion H8; rewrite H9; auto 20. 
Qed. 


Lemma subst_rec_preserves_factorable: 
forall M, factorable M -> forall N k, factorable (subst_rec M N k).
Proof. 
intros M f. 
 inversion f; split_all.  
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
unfold factorable; rewrite H0; auto. 
 inversion H; split_all.  
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
unfold factorable; rewrite H1; auto. 
 inversion H0; split_all.  
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
unfold factorable; rewrite H2; auto. 
 inversion H1; split_all.  
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
unfold factorable; rewrite H3; auto. 
 inversion H2; split_all.  
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
unfold factorable; rewrite H4; auto. 
 inversion H3; split_all.  
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
unfold factorable; rewrite H5; auto. 
assert(status (subst_rec M N k) = status M) .  
eapply2 subst_rec_preserves_status; split_all. 
rewrite H5 in *. or_tac. 
rewrite H5 in *. or_tac. 
unfold factorable; rewrite H5; auto. 
Qed. 


Lemma status_app_active: 
forall M N i, status (App M N) = Active i -> 
status M = Active i \/ status N = Active i \/ status N = Lam i.  
Proof. 
induction M; split_all.  
(* 3 *) 
gen_case H o; gen_case H (status N); invsub. 
(* 2 *) 
gen_case H (status M); gen_case H n. 
(* 1 *) 
gen_case H (status M1);  gen_case H (status M2); gen_case H (status N); invsub. 
Qed. 




Lemma lift_rec_preserves_compound: 
forall M n k, compound M -> compound (lift_rec M n k).
Proof. 
intros. 
assert(status (lift_rec M n k) = relocate_status (status M) n k) 
by eapply2 lift_rec_preserves_status. 
unfold compound in *. 
rewrite H0. 
inversion H. rewrite H1; auto. 
inversion H1. rewrite H2; auto. 
inversion H2;  rewrite H3; auto. 
Qed. 



Lemma subst_rec_preserves_compound: 
forall M, compound M -> forall N k, compound (subst_rec M N k).
Proof. 
split_all. 
assert(factorable M) by eapply2 compounds_are_factorable. 
assert(factorable (subst_rec M N k)) by eapply2 subst_rec_preserves_factorable. 
elim(factorable_implies_compound_or_operator (subst_rec M N k)); split_all. 
gen2_case H H3 M.  unfold compound in H; simpl in *; or_tac. 
Qed. 

