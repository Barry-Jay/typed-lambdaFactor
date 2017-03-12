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
(*                Typed LambdaFactor Calculus                         *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                           LamSF_Terms.v                            *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Arith.
Require Import General.
Require Import Test.


(* lambda terms with operators and using de Bruijn's indices *)


Inductive operator := 
| Sop 
| Aop 
| Kop 
| Eop 
| Gop 
| Qop
| Uop
| Yop
| DSop | DAop | DKop | DEop | DGop | DQop | DUop | DYop
.

Hint Constructors operator.


Inductive lamSF:  Set :=
  | Ref : nat -> lamSF 
  | Op  : operator -> lamSF 
  | Abs : lamSF -> lamSF  
  | App : lamSF -> lamSF -> lamSF
.

Lemma decidable_term_equality : forall (M N: lamSF), M = N \/ M<> N. 
Proof. repeat(decide equality). Qed. 

(* Lifting *)

Definition relocate (i k n : nat) :=
  match test k i with
  
   (* k<=i *) | left _ => n+i
   (* k>i  *) | _ => i
  end.

Fixpoint lift_rec (L : lamSF) : nat -> nat -> lamSF :=
  fun k n => 
  match L with
  | Ref i => Ref (relocate i k n)
  | Op o => Op o
  | App M N => App (lift_rec M k n) (lift_rec N k n)
  | Abs M => Abs (lift_rec M (S k) n)
  end.

Definition lift (n : nat) (N : lamSF) := lift_rec N 0 n.

(* Substitution *)


Definition insert_Ref (N : lamSF) (i k : nat) :=
  match compare k i with
  
   (* k<i *) | inleft (left _) => Ref (pred i)
   (* k=i *) | inleft _ => lift k N
   (* k>i *) | _ => Ref i
  end.

Fixpoint subst_rec (L : lamSF) : lamSF -> nat -> lamSF :=
  fun (N : lamSF) (k : nat) =>
  match L with
  | Ref i => insert_Ref N i k
  | Op o => Op o
  | App M M' => App (subst_rec M N k) (subst_rec M' N k)
  | Abs M => Abs (subst_rec M N (S k)) 
  end.

Definition subst (N M : lamSF) := subst_rec M N 0.


