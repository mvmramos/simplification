(* ---------------------------------------------------------------------
   This file contains definitions and proof scripts related to the 
   correctness of simplification  algorithms for context-free grammars, 
   namely empty rules elimination, unit rules elimination, useless symbol
   elimination and inaccessible symbol elimination.

   More information can be found in the paper "Formalization of 
   simplification for context-free grammars", LSFA 2015.

   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
(* BASIC LEMMAS                                                          *)
(* --------------------------------------------------------------------- *)

Require Import Ring.
Require Import Omega.

Lemma lep1m2_ltp1:
forall i x: nat, i <= x + 1 - 2 -> i < x + 1.
Proof. 
intros i x H.
omega.
Qed.

Lemma lep1m2_lt:
forall i x: nat, x > 0 -> i <= x + 1 - 2 -> i < x.
Proof. 
intros i x H1 H2.
omega.
Qed.

Lemma gt_any_gt_0:
forall i j: nat,
i > j -> i > 0.
Proof.
intros i j H.
destruct i.
- apply lt_n_0 in H.
  contradiction.  
- apply gt_Sn_O.
Qed.

Lemma lt_1_eq_0:
forall i: nat,
i < 1 -> i = 0.
Proof.
intros i H.
destruct i.
- reflexivity.
- apply lt_S_n in H.
  apply lt_n_0 in H.
  contradiction. 
Qed.

Lemma n_minus_1:
forall n: nat,
n <> 0 -> n-1 < n.
Proof.
intros n H.
destruct n.
- omega.
- omega.
Qed.

Lemma gt_zero_exists:
forall i: nat,
i > 0 ->
exists j: nat, i = S j.
Proof.
intros i H.
destruct i.
- omega.
- exists i.
  reflexivity.
Qed.

Lemma max_n_n:
forall n: nat,
max n n = n.
Proof.
induction n.
- simpl. 
  reflexivity.
- simpl.
  rewrite IHn.
  reflexivity.
Qed.

Lemma max_n_0:
forall n: nat,
max n 0 = n.
Proof.
destruct n.
- simpl. 
  reflexivity.
- simpl.
  reflexivity.
Qed.
