
(* ---------------------------------------------------------------------
   This file contains definitions and proof scripts related to the 
   correctness of symbol elimination  algorithms for context-free 
   grammars, namely useless and inaccessible symbols.

   More information can be found in the paper "Formalization of symbol 
   elimination in context-free grammars", TYPES 2014.

   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)

Require Import Ascii.
Require Import String.
Require Import List.
Require Import Ring.
Require Import Omega.
Import ListNotations.

Open Scope char_scope.
Open Scope string_scope.
Open Scope list_scope.

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

(* --------------------------------------------------------------------- *)
(* LISTS                                                                 *)
(* --------------------------------------------------------------------- *)

Lemma map_expand:
forall (A B: Type) (f: A -> B) (l: list A) (s1 s2: list B), 
s1 ++ s2 = map f l ->
exists s1' s2': list A,
l = s1' ++ s2' /\ map f s1' = s1 /\ map f s2' = s2.
Proof.
intros A B f l.
induction l.
- intros s1 s2 H.
  simpl in H.
  apply app_eq_nil in H.
  destruct H as [H1 H2].
  subst.
  exists [], [].
  auto.
- intros s1 s2 H.
  simpl in H.
  destruct s1.
  + simpl in H.
    destruct s2.
    * inversion H.
    * inversion H.
      exists [], (a::l). {
      split.
      - simpl.
        reflexivity.
      - split.
        + simpl.
          reflexivity.
        + simpl. 
          reflexivity. }
  + destruct s2.
    * inversion H.
      exists (a::l), []. {
      split.
      - simpl.
        rewrite app_nil_r.
        reflexivity.
      - split.
        + simpl.
          rewrite <- H2.
          rewrite app_nil_r.
          reflexivity.
        + simpl. 
          reflexivity. }
    * inversion H.
      specialize (IHl s1 (b0::s2)).
      specialize (IHl H2).
      destruct IHl as [s1' [s2' [H3 [H4 H5]]]].
      exists (a::s1').
      exists s2'. {
      split.
      - rewrite H3.
        simpl.
        reflexivity.
      - split.
        + simpl.
          rewrite H4.
          reflexivity.
        + rewrite H5.
          reflexivity. }
Qed.

Lemma equal_app (A: Type) :
forall l1 l2 s1 s2 : list A,
l1 ++ l2 = s1 ++ s2 ->
(exists l, s1 = l1 ++ l /\ l2 = l ++ s2) \/ (exists l, l1 = s1 ++ l /\ s2 = l ++ l2).
Proof.
intros l1.
induction l1 as [|a l1 IH].
- intros l2 s1 s2 H.
  simpl in H. 
  subst. 
  simpl. 
  left.
  exists s1.
  split.
  reflexivity.
  reflexivity. 
- intros l2 s1 s2 H. 
  simpl in H.
  destruct s1 as [|a' s1].
  + simpl in H. 
    subst. 
    simpl. 
    right.
    exists (a::l1).
    split.
    * reflexivity.
    * simpl.
      reflexivity.
  + simpl in H. 
    inversion H. 
    subst a'. 
    clear H.
    apply IH in H2.
    destruct H2 as [(l & ? & ?) | (l & ? & ?)]. 
    * subst. 
      simpl.
      left.
      exists l. {
      split.
      - reflexivity.
      - reflexivity. }
    * right.
      exists l. {
      split.
      - rewrite H.
        simpl.
        reflexivity.
      - rewrite H0.
        reflexivity. }
Qed.

Lemma last_last:
forall A: Type,
forall s d: A,
forall l: list A,
last (l++[s]) d = s.
Proof.
intros A s d l.
induction l.
- simpl. 
  reflexivity.
- simpl. 
  destruct l.
  + simpl. 
    reflexivity.
  + rewrite <- app_comm_cons.
    exact IHl.
Qed.

Lemma length_ge_2:
forall A: Type,
forall a1 a2: A,
forall l: list A,
length (a1::a2::l) >= 2.
Proof.
intros A a1 a2 l.
simpl.
apply Le.le_n_S.
apply Le.le_n_S.
apply Le.le_0_n.
Qed.

Lemma length_lt_1:
forall A: Type,
forall l: list A,
length l < 1 -> l = [].
Proof.
intros A l H.
destruct l.
- reflexivity.
- replace (a::l) with ([a]++l) in H.
  + rewrite app_length in H.
    simpl in H.
    apply lt_S_n in H.
    apply lt_n_O in H.
    contradiction.
  + simpl.
    reflexivity.
Qed.

Lemma nth_cons:
forall A: Type,
forall a e: A,
forall l: list A,
forall i: nat,
nth (S i) (a::l) e = nth i l e.
Proof.
intros A a e l i.
simpl. 
destruct i.
- simpl.
  reflexivity.
- reflexivity.
Qed. 

Lemma length_not_zero:
forall A: Type,
forall l: list A,
length l > 0 -> [] <> l.
Proof.
intros A l H.
destruct l.
- simpl in H.
  apply gt_irrefl in H.
  contradiction.
- apply nil_cons.
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

Lemma not_nil:
forall A: Type,
forall l: list A,
l <> [] -> length l <> 0.
Proof.
destruct l.
- intro H.
  auto.
- intro H.
  replace (a::l) with ([a]++l). 
  + rewrite app_length.
    simpl.
    apply not_eq_sym.
    apply O_S.
  + simpl.
    reflexivity.
Qed.

Lemma list_last:
forall A: Type,
forall d: A,
forall l: list A,
removelast l <> [] -> nth (length (removelast l) - 1) (removelast l ++ [last l d]) d = last (removelast l) d.
Proof.
intros A d l H.
rewrite app_nth1 with (l:=removelast l).
- rewrite app_removelast_last with (l:=removelast l)(d:=d).
  + rewrite app_nth2.
    * rewrite app_length.
      assert (H1: Datatypes.length (removelast (removelast l)) + 1 - 1 -
                  Datatypes.length (removelast (removelast l)) = 0).
        {
        omega.
        }
      simpl. 
      rewrite H1.
      rewrite last_last.
      reflexivity.
    * rewrite app_length.
      simpl. 
      omega.
  + exact H.
- apply n_minus_1.
  apply not_nil.
  exact H.
Qed.

Lemma length_zero:
forall A: Type,
forall l: list A,
length l = 0 -> l = [].
Proof.
intros A l H.
destruct l.
- reflexivity.
- simpl in H.
  symmetry in H.
  apply O_S in H.
  contradiction.
Qed.

Lemma list_single:
forall A: Type,
forall l: list A,
forall d e: A,
nth 0 l d = e -> length l = 1 -> l = [e].
Proof.
intros A l d e H1 H2.
destruct l.
- simpl in H2.
  apply O_S in H2.
  contradiction.
- simpl in H1.
  rewrite H1.
  simpl in H2.
  inversion H2.
  apply length_zero in H0.
  rewrite H0.
  reflexivity.
Qed.

Lemma hd_nth0:
forall A: Type,
forall d: A,
forall l: list A,
hd d l = nth 0 l d.
Proof.
intros A d l.
destruct l.
- simpl.
  reflexivity.
- simpl.
  reflexivity.
Qed.

Lemma last_nth1:
forall A: Type,
forall d: A,
forall l: list A,
length l = 2 -> last l d = nth 1 l d.
Proof.
intros A d l H.
destruct l.
- simpl. 
  reflexivity.
- simpl. 
  destruct l.
  + simpl in H.
    inversion H.
  + replace (a :: a0 :: l) with ([a] ++ [a0] ++ l) in H.
    * repeat rewrite app_length in H.
      simpl in H.
      inversion H.
      apply length_zero in H1.
      subst.
      simpl.
      reflexivity. 
    * simpl.
      reflexivity.
Qed.

Lemma hd_tl_nth1:
forall A: Type,
forall d: A,
forall l: list A,
length l > 2 -> hd d (tl l) = nth 1 l d.
Proof.
intros A d l H.
destruct l.
- simpl. 
  reflexivity.
- simpl. 
  apply hd_nth0.
Qed.

Lemma last_tl_last:
forall A: Type,
forall d: A,
forall l: list A,
length l > 2 -> last (tl l) d = last l d.
Proof.
intros A d l H.
destruct l.
- simpl.
  reflexivity.
- simpl.
  destruct l.
  + simpl in H.
    apply gt_S_n in H.
    apply lt_n_0 in H.
    contradiction.
  + reflexivity.
Qed.

Lemma nth_S:
forall A: Type,
forall i: nat,
forall s s0 s1: A,
forall l: list A, 
nth (S i) (s::s0::s1::l) = nth i (s0::s1::l).
Proof.
intros A i s s0 s1 l.
destruct i.
- simpl. 
  reflexivity.
- destruct i.
  + simpl. 
    reflexivity.
  + destruct i.
    * simpl. 
      reflexivity.
    * simpl. 
      reflexivity.
Qed.

Lemma skipn_S:
forall i: nat,
forall A: Type,
forall a: A,
forall l: list A,
skipn (S i) (a :: l) = skipn i l.
Proof.
intros i A a l.
destruct i.
- simpl. 
  reflexivity.
- simpl.
  destruct l.
  + reflexivity.
  + reflexivity.
Qed. 

Lemma hd_skip:
forall i: nat,
forall A: Type,
forall d: A,
forall l: list A,
hd d (skipn i l) = nth i l d.
Proof.
intros i A d.
induction i as [| i IH].
- intros l. 
  destruct l.
  + trivial.
  + trivial.
- intros l.
  destruct l.
  + trivial.
  + simpl.
    rewrite IH.
    reflexivity.  
Qed.

Lemma last_skip:
forall i: nat,
forall A: Type,
forall d: A,
forall l: list A,
i < length l -> last (skipn i l) d = last l d.
Proof.
intros i A d.
induction i as [|i IH].
- intros l.
  destruct l.
  + trivial. 
  + trivial.
- intros l.
  destruct l.
  + trivial. 
  + simpl. 
    intros Hl.
    assert (Hl' : i < length l) by omega.
    rewrite IH. 
    * {
      destruct l. 
      - simpl in Hl'. 
        omega.
      - trivial. 
      } 
    * trivial.
Qed. 

Lemma hd_hd:
forall A: Type,
forall d: A,
forall l l': list A,
length l >= 1 -> hd d l = hd d (l ++ l').
Proof.
intros A d l l' H.
destruct l.
- simpl in H.
  apply le_Sn_0 in H.
  contradiction. 
- simpl.
  reflexivity.
Qed.

Lemma hd_first:
forall A: Type,
forall d: A,
forall l: list A,
forall i: nat,
i >= 1 -> hd d (firstn i l) = hd d l.
Proof.
intros A d l i H.
destruct l.
- destruct i.
  + simpl.
    reflexivity.
  + simpl. 
    reflexivity.
- destruct i. 
  + apply le_Sn_0 in H.
    contradiction.
  + simpl.
    reflexivity.
Qed. 

Lemma firstn_empty:
forall A: Type,
forall a: A,
forall i: nat,
a :: firstn i [] = [a].
Proof.
intros A a i.
destruct i.
- simpl. 
  reflexivity.
- simpl.
  reflexivity.
Qed. 

Lemma firstn_single:
forall A: Type,
forall a: A,
forall i: nat,
firstn (S i) [a] = [a].
intros A a i.
destruct i.
- simpl. 
  reflexivity.
- simpl. 
  reflexivity.
Qed.

Lemma nth_S':
forall i: nat,
forall A: Type,
forall a d: A,
forall l: list A,
nth (S i) (a :: l) d = nth i l d.
Proof.
intros i A a d l.
destruct i.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

Lemma firstn_S:
forall A: Type,
forall a: A,
forall l: list A,
forall i: nat,
firstn (S i) (a :: l) = a :: firstn i l.
Proof.
intros A a l.
induction l.
- intros i. simpl. reflexivity.
- intros i. destruct i.
  + simpl. reflexivity.
  + simpl. reflexivity. 
Qed.

Lemma last_cons:
forall A: Type,
forall a d: A,
forall l: list A,
l <> [] -> last (a :: l) d = last l d.
Proof.
intros A a d l H.
induction l.
- destruct H. reflexivity.
- trivial.
Qed.

Lemma not_nil_firstn:
forall A: Type,
forall l: list A,
forall i: nat,
l <> [] -> firstn (S i) l <> [].
Proof.
intros A l i H.
destruct l.
- simpl. exact H.
- simpl. apply not_eq_sym. apply nil_cons.
Qed.

Lemma nil_not_nil:
forall A: Type,
forall l: list A,
l = [] \/ l <> [].
Proof.
destruct l.
- left.
  reflexivity.
- right.
  apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma last_first_nth:
forall A: Type,
forall d: A,
forall l: list A,
forall i: nat,
length l >= S i -> last (firstn (S i) l) d = nth i l d.
Proof.
intros A d l.
induction l.
- destruct i.
  + trivial.
  + trivial.
- destruct i.
  + trivial. 
  + intros H. 
    rewrite nth_S'.  
    rewrite <- IHl.
    * rewrite firstn_S.
      {
      rewrite last_cons.
      - reflexivity.
      - apply not_nil_firstn.
        specialize (IHl i).
        replace (a::l) with ([a]++l) in H.
        + rewrite app_length in H.
          simpl in H.
          assert (H1: length l > 0) by omega.
          destruct l. 
          * simpl in H1.
            omega.   
          * apply not_eq_sym.   
            apply nil_cons.
        + simpl.
          reflexivity.
      }
    * {
      replace (a::l) with ([a]++l) in H.
      - rewrite app_length in H.
        simpl in H.
        omega.
      - simpl.
        reflexivity.
      }
Qed.  

Lemma nth_last:
forall A: Type,
forall l: list A,
forall d: A,
nth (length l - 1) l d = last l d.
Proof.
intros A l d.
destruct l.
- simpl. 
  reflexivity.
- remember (a::l) as l0. 
  rewrite app_removelast_last with (l:=l0) (d:=d).
  + rewrite app_length.
    simpl. 
    rewrite last_last.
    rewrite app_nth2.
    * assert (H: (Datatypes.length (removelast l0) + 1 - 1 - Datatypes.length (removelast l0) = 0)) by omega.
      rewrite H.
      simpl. 
      reflexivity.
    * omega.
  + rewrite Heql0.
    apply not_eq_sym. 
    replace (a::l) with ([]++a::l). 
    * apply app_cons_not_nil.
    * simpl. 
      reflexivity.
Qed.

(* --------------------------------------------------------------------- *)
(* GRAMMARS                                                              *)
(* --------------------------------------------------------------------- *)

Inductive non_terminal: Type:=
| S'
| X
| Y
| Z
| W.

Inductive terminal: Type:=
| a
| b
| c
| d
| e.

Definition sf: Type:= list (non_terminal + terminal).
Definition sentence: Type:= list terminal.

Record cfg: Type:= {
start_symbol: non_terminal;
rules: non_terminal -> sf -> Prop
}.

Inductive derives (g: cfg): sf -> sf -> Prop :=
| derives_refl: forall s: sf,
                derives g s s
| derives_step: forall s1 s2 s3: sf,
                forall left: non_terminal,
                forall right: sf,
                derives g s1 (s2 ++ inl left :: s3) ->
                rules g left right ->
                derives g s1 (s2 ++ right ++ s3).

Definition generates (g: cfg) (s: sf): Prop:=
derives g [inl (start_symbol g)] s.

Definition terminal_lift (t: terminal): non_terminal + terminal:=
inr t.

Definition produces (g: cfg)(s: sentence): Prop:=
generates g (map terminal_lift s).

Definition g_equiv (g1 g2: cfg): Prop:=
forall s: sentence,
produces g1 s <-> produces g2 s.

Definition appears (g: cfg) (s: non_terminal + terminal): Prop:=
match s with
| inl n => exists left: non_terminal,
           exists right: sf,
           rules g left right /\ ((n=left) \/ (In (inl n) right))
| inr t => exists left: non_terminal,
           exists right: sf,
           rules g left right /\ In (inr t) right
end.

Theorem derives_rule:
forall g: cfg,
forall left: non_terminal,
forall right s1 s2: sf,
rules g left right ->
derives g (s1 ++ [inl left] ++ s2) (s1 ++ right ++ s2).
Proof.
intros g left right s1 s2 H.
apply derives_step with (left:=left).
- apply derives_refl.
- exact H.
Qed.

Theorem derives_start:
forall g: cfg,
forall left: non_terminal,
forall right: sf,
rules g left right -> derives g [inl left] right.
Proof.
intros g left right H.
apply derives_rule with (s1:=[]) (s2:=[]) in H.
simpl in H.
rewrite app_nil_r in H.
exact H.
Qed.

Theorem derives_trans (g: cfg) (s1 s2 s3: sf):
derives g s1 s2 ->
derives g s2 s3 ->
derives g s1 s3.
Proof.
intros H1 H2.
induction H2. 
- exact H1.
- apply derives_step with (left:=left).
  + apply IHderives.
    exact H1.
  + exact H. 
Qed.

Inductive derives' (g: cfg): sf -> sf -> Prop :=
| derives'_refl: forall s: sf,
                 derives' g s s
| derives'_step: forall s1 s2 s3: sf,
                 forall left: non_terminal,
                 forall right: sf,
                 derives' g (s1 ++ right ++ s2) s3 ->
                 rules g left right ->
                 derives' g (s1 ++ inl left :: s2) s3.

Theorem derives'_trans (g: cfg) (s1 s2 s3: sf):
derives' g s1 s2 ->
derives' g s2 s3 ->
derives' g s1 s3.
Proof.
intros H1 H2.
induction H1. 
- exact H2.
- apply derives'_step with (right:=right).
  + apply IHderives'.
    exact H2.
  + exact H.
Qed.

Theorem derives_equiv_derives':
forall g: cfg,
forall s1 s2: sf,
derives g s1 s2 <-> derives' g s1 s2.
Proof.
intros g s1 s2.
split.
- intro H.
  induction H.
  + apply derives'_refl.
  + inversion IHderives.
    * {
      apply derives'_step with (right:=right).
      - apply derives'_refl.
      - exact H0.
      }
    * {
      apply derives'_step with (right:=right0).
      - apply derives'_trans with (s2:=(s2 ++ inl left :: s3)).
        + exact H1.
        + apply derives'_step with (right:=right).
          * apply derives'_refl.
          * exact H0.
      - exact H2.
      }
- intro H.
  induction H.
  + apply derives_refl.
  + inversion IHderives'.
    * apply derives_rule.
      exact H0.
    * {
      apply derives_trans with (s2:=s1 ++ right ++ s2).
      - apply derives_rule.
        exact H0.
      - apply derives_step with (right:=right0) in H1.
        + exact H1.
        + exact H2.
        }
Qed.

Theorem derives_context_free_add_left (g:cfg) (s1 s2 s: sf):
derives g s1 s2 -> derives g (s++s1) (s++s2).
Proof.
intros H.
induction H as [| x y z left right H1 H2 H3].
apply derives_refl.
remember (s++x) as w1.
rewrite app_assoc.
rewrite app_assoc in H2.
remember (s++y) as w2.
apply derives_step with (left:=left).
exact H2.
exact H3.
Qed.

Theorem derives_context_free_add_right (g:cfg) (s1 s2 s: sf):
derives g s1 s2 -> derives g (s1++s) (s2++s).
Proof.
intros H.
induction H as [| x y z left right H1 H2 H3].
apply derives_refl.
remember (x++s) as w1.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc in H2.
rewrite <- app_comm_cons in H2.
remember (z++s) as w2.
apply derives_step with (left:=left).
exact H2.
exact H3.
Qed.

Theorem derives_context_free_add (g:cfg) (s1 s2 s s': sf):
derives g s1 s2 -> derives g (s++s1++s') (s++s2++s').
Proof.
intros H.
apply derives_context_free_add_left.
apply derives_context_free_add_right.
exact H.
Qed.

Theorem derives_combine (g: cfg) (s1 s2 s3 s4: sf):
derives g s1 s2 /\ derives g s3 s4 -> derives g (s1++s3) (s2++s4).
Proof.
intros [H1 H2].
induction H1,H2.
apply derives_refl.
apply derives_context_free_add_left.
apply derives_step with (left:= left).
exact H2.
exact H.
apply derives_context_free_add_right.
apply derives_step with (left:=left).
exact H1.
exact H.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc in IHderives.
simpl in IHderives.
remember (s0 ++ s4 ++ right0 ++ s5) as w.
apply derives_step with (left:=left).
exact IHderives.
exact H.
Qed.

Lemma derives_subs:
forall g: cfg,
forall s1 s2 s3 s3' s4: sf,
derives g s1 (s2++s3++s4) -> 
derives g s3 s3' ->
derives g s1 (s2++s3'++s4).
Proof.
intros g s1 s2 s3 s3' s4 H1 H2.
induction H2.
- exact H1.
- specialize (IHderives H1).
  rewrite <- app_assoc in IHderives.
  simpl in IHderives.
  repeat rewrite <- app_assoc.
  remember (s5++s4) as w2.
  rewrite app_assoc.
  apply derives_step with (left:=left).
  subst.
  rewrite <- app_assoc.
  exact IHderives.
  exact H.
Qed.

Lemma derives_split:
forall g: cfg,
forall s1 s2 s3: sf,
derives g (s1 ++ s2) s3 ->
exists s1' s2': sf, s3 = s1' ++ s2' /\ derives g s1 s1' /\ derives g s2 s2'.
Proof.
intros g s1 s2 s3 H.
remember (s1++s2) as w.
induction H. 
- exists s1, s2.
  split.
  + exact Heqw.
  + split. 
    * apply derives_refl.
    * apply derives_refl.
- specialize (IHderives Heqw).
  destruct IHderives as [s1' [s2' [H10 [H11 H12]]]].
  apply equal_app in H10.
  destruct H10 as [H10 | H10].
  + destruct H10 as [l [H20 H21]].
    destruct l.
    * simpl in H21.
      {
      destruct s2'.
      - inversion H21.
      - inversion H21.
        subst.
        exists s3, (right ++ s2').
        split.
        + reflexivity.
        + split.
          * rewrite app_nil_r in H11.
            exact H11.
          * rewrite <- app_nil_l in H12.
            { 
            apply derives_step with (right:=right) in H12.
            - exact H12.
            - exact H0.
            }
      }
    * inversion H21.
      subst.
      exists (s3 ++ right ++ l), s2'.
      {
      split.
      - repeat rewrite <- app_assoc. 
        reflexivity.
      - split.
        + apply derives_step with (right:=right) in H11.
          * exact H11.
          * exact H0.
        + exact H12.
      }   
  + destruct H10 as [l [H20 H21]].
    destruct l.
    * simpl in H21.
      rewrite app_nil_r in H20.
      subst.
      exists s1', (right ++ s4).
      {
      split.
      - reflexivity.
      - split.
        exact H11.
        rewrite <- app_nil_l in H12.
        apply derives_step with (right:=right) in H12.
        + exact H12.
        + exact H0.
      }
    * {
      destruct s2'. 
      - inversion H21.
      - inversion H21.
        subst.
        exists s1', (s :: l ++ right ++ s4).
        split.
        + repeat rewrite <- app_assoc.
          reflexivity.
        + split.
          * exact H11.
          * {
            apply derives_step with (s2:=s :: l) (right:=right) in H12.
            - exact H12.
            - exact H0.
            }
      }
Qed. 

Lemma derives_nt_sentence:
forall g: cfg,
forall l1 l2: sf,
forall n: non_terminal,
forall s: sentence,
derives g (l1 ++ inl n :: l2) (map terminal_lift s) -> 
exists s': sentence,
derives g [inl n] (map terminal_lift s').
Proof.
intros g l1 l2 n s H.
apply derives_split in H.
destruct H as [s1' [s2' [H2 [_ H4]]]].
symmetry in H2.
apply map_expand in H2.
destruct H2 as [_ [s2'0 [_ [_ H5]]]].
rewrite <- H5 in H4.
replace (inl n::l2) with ([inl n]++l2) in H4.
- apply derives_split in H4.
  destruct H4 as [s1'0 [s2'1 [H6 [H7 _]]]].
  symmetry in H6.
  apply map_expand in H6.
  destruct H6 as [s1'1 [_ [_ [H8 _]]]].
  rewrite <- H8 in H7.
  exists s1'1.
  exact H7.
- simpl.
  reflexivity.
Qed.

Inductive sflist (g: cfg): list sf -> Prop:=
| sflist_empty: sflist g []
| sflist_start: forall s: sf, 
                sflist g [s]
| sflist_step: forall l: list sf,
               forall s2 s3: sf,
               forall left: non_terminal,
               forall right: sf,
               sflist g l -> last l [] = (s2 ++ inl left :: s3) ->
               rules g left right ->
               sflist g (l++[s2 ++ right ++ s3]).

Lemma lt2_sflist:
forall g: cfg,
forall l: list sf,
length l < 2 -> sflist g l.
Proof.
intros g l H.
destruct l.
- apply sflist_empty.
- replace (s::l) with ([s]++l) in H.
  + rewrite app_length in H.
    simpl in H.
    assert (H1: length l = 0) by omega.
    apply length_zero in H1.
    subst.
    apply sflist_start.
  + simpl.
    reflexivity.
Qed.

Lemma sflist_rules':
forall g: cfg,
forall n: nat,
forall l: list sf,
length l = n ->
length l >= 2-> (sflist g l -> 
                (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right)).
Proof.
intros g n.
induction n.
- intros l H1 H2.
  rewrite H1 in H2.
  apply le_Sn_0 in H2.
  contradiction.
- intros l H1 H2 H3 i H4.
  inversion H3.
  + subst.
    simpl in H1. 
    apply O_S in H1.
    contradiction.
  + subst.
    simpl in H2.
    apply le_S_n in H2.
    inversion H2.
  + specialize (IHn l0).
    rewrite <- H6 in H1.
    rewrite app_length in H1.
    simpl in H1.
    rewrite <- plus_n_Sm in H1.
    rewrite plus_0_r in H1.
    inversion H1.
    specialize (IHn H8).
    assert (H10: length l0 >= 2 \/ length l0 < 2).
      { 
      apply le_or_lt.
      }
    destruct H10.
    * specialize (IHn H7 H i).
      assert (H11: i <= length l0 -2 \/ i > length l0 - 2).
        { 
        apply le_or_lt.
        }
      {
      destruct H11.
      - specialize (IHn H9).
        destruct IHn as [left1 [right1 [s [s' [H15 [H16 H17]]]]]].
        exists left1, right1, s, s'.
        split. 
        + rewrite app_nth1.
          * exact H15.
          * omega. 
        + split.
          * {
            rewrite app_nth1.
            - exact H16.
            - omega.
            }
          * exact H17. 
      - rewrite app_removelast_last with (l:=l0) (d:=[]).
        + rewrite <- app_assoc.
          assert (H23: length (removelast l0) = length l0 - 1).
            {
            rewrite app_removelast_last with (l:=l0) (d:=[]) at 2.
            - rewrite app_length.
              simpl. 
              omega.
            - apply not_eq_sym.
              apply length_not_zero.
              omega.
            }
          assert (H21: i - length (removelast l0) >= 0).
            {
            omega.
            }
          assert (H22: i - length (removelast l0) <= 0).
            {
            subst.
            rewrite app_length in H4.
            simpl in H4.
            rewrite H23.
            omega.
            }
          assert (H20: i - length (removelast l0) = 0).
            { 
            omega. 
            }
          rewrite app_nth2.
          * exists left, right, s2, s3.
            {
            split. 
            - rewrite H0.
              rewrite H20.
              simpl.   
              reflexivity.
            - rewrite app_nth2.
              + split. 
                * rewrite H0.
                  assert (H24: (S i - Datatypes.length (removelast l0) = 1)).
                    { 
                    rewrite <- minus_Sn_m.
                    - apply eq_S in H20.
                      exact H20.
                    - omega.
                    }
                  rewrite H24.
                  simpl.
                  reflexivity.  
                * exact H5.
              + omega.
            }
          * rewrite H23.
            omega.
        + apply not_eq_sym.
          apply length_not_zero.
          omega.
      }
    * exists left, right, s2, s3.
      assert (H10: l0 = [s2 ++ inl left :: s3]).
        { 
        destruct l0. 
        - inversion H0.
          destruct s2. 
          + simpl in H10.
            inversion H10.
          + inversion H10.
        - assert (H12: length l0 = 0).
            { 
            simpl in H7.
            apply lt_S_n in H7.
            omega.
            }
          assert (H13: l0 = []).
            { 
            destruct l0.
            - reflexivity.
            - simpl in H12.
              symmetry in H12. 
              apply O_S in H12.
              contradiction.
            }
          subst. 
          simpl in H0.
          rewrite H0.
          reflexivity.
        }
      rewrite H10.
      assert (H12: length l = 2).
        { 
        rewrite <- H6.
        rewrite H10.
        simpl.
        reflexivity.
        }
      assert (H11: i = 0).
        {
        rewrite H12 in H4.
        simpl in H4.
        omega.
        }
      rewrite H11.
      {
      split. 
      - simpl. 
        reflexivity.
      - split. 
        + simpl.
          reflexivity.
        + exact H5.  
      }
Qed.

Lemma sflist_rules'':
forall g: cfg,
forall n: nat,
forall l: list sf,
length l = n ->
length l >= 2-> (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right) -> sflist g l.
Proof.
intros g n.
induction n.
- intros l H0 H1 H2.
  assert (EMPTY: l = []).
    {
    destruct l.
    - reflexivity.
    - simpl in H0.
      symmetry in H0.
      apply O_S in H0.
      contradiction.
    }
  subst.
  apply sflist_empty.
- intros l H0 H1 H2.
  rewrite app_removelast_last with (d:=[]).
  + specialize (IHn (removelast l)).
    assert (H3: length (removelast l) = n).
      {
      rewrite app_removelast_last with (l:=l) (d:=[]) in H0.
      - rewrite app_length in H0.
        simpl in H0.
        omega.
      - destruct l.
        + simpl in H1.
          apply le_Sn_0 in H1.
          contradiction.
        + apply not_eq_sym. 
          apply nil_cons.
      }
    specialize (IHn H3).
    assert (H4: length (removelast l) >= 2 \/ length (removelast l) < 2).
      {
      apply le_or_lt.
      }
    destruct H4 as [H | H].
    * specialize (IHn H).
      {
      rewrite app_removelast_last with (l:=l) (d:=[]) in H2.
      - assert (H4: sflist g (removelast l)).
          {
          apply IHn.
          intros i H4.
          specialize (H2 i).
          rewrite app_length in H2.
          simpl in H2.
          assert (H20:= H4).
          apply le_trans with (n:=i)(m:=Datatypes.length (removelast l) - 2)(p:=Datatypes.length (removelast l) + 1 - 2) in H4.
          + specialize (H2 H4).
            destruct H2 as [left [right [s [s' [H7 [H8 H9]]]]]].
            exists left, right, s, s'.
            split.
            * assert (H10: i < length (removelast l)).
                {
                omega.
                }
              {
              rewrite app_nth1 in H7.
              - rewrite H7.
                reflexivity.
              - exact H10.
              }
            * {
              split.
              - assert (H10: S i < length (removelast l)).
                  {
                  omega.
                  }
                rewrite app_nth1 in H8.
                + rewrite H8.
                  reflexivity.
                + exact H10.
              - exact H9.
              } 
          + omega.
          }
        specialize (H2 ((S n) - 2)).
        assert (H5: S n - 2 <= Datatypes.length (removelast l ++ [last l []]) - 2).
          {
          rewrite app_length.
          simpl.
          omega.
          }
        specialize (H2 H5).
        destruct H2 as [left [right [s [s' [H6 [H7 H8]]]]]].
        apply sflist_step with (s2:=s)(s3:=s')(left:=left)(right:=right) in H4.
        + assert (H9: nth (S (S n - 2)) (removelast l ++ [last l []]) [] = last l []).
            {
            simpl.
            rewrite app_nth2.
            - assert (H9: S (n - 1) - length (removelast l) = 0).
                {
                omega.
                }
              rewrite H9.
              simpl.
              reflexivity.
            - omega.
            }
          rewrite H9 in H7.
          rewrite <- H7 in H4.
          exact H4.
        + assert (H9: nth (S n - 2) (removelast l ++ [last l []]) [] = last (removelast l) []).
            {
            assert (H10: S n - 2 = length (removelast l) - 1). 
              {
              omega.
              }
            rewrite H10.
            rewrite list_last.
            * reflexivity.
            * {
              destruct l.
              - simpl in H1.
                apply le_Sn_0 in H1.
                contradiction.
              - apply not_eq_sym.
                apply length_not_zero.
                omega.
              }
            }
          rewrite H9 in H6.
          rewrite H6.
          reflexivity.
        + exact H8.
      - destruct l.
        + simpl in H1.
          apply le_Sn_0 in H1.
          contradiction.
        + apply not_eq_sym. 
          apply nil_cons.
      }
    * 
      specialize (H2 (length l - 2)).
      assert (H4: Datatypes.length l - 2 <= Datatypes.length l - 2).
        {
        omega.
        }
      specialize (H2 H4).
      clear H4.
      destruct H2 as [left [right [s [s' [H6 [H7 H8]]]]]].
      assert (H5: nth (S (Datatypes.length l - 2)) l [] = last l []).
        {
        assert (H11: S (Datatypes.length l - 2) = length l - 1).
          {
          omega.
          }
        rewrite H11.
        rewrite app_removelast_last with (l:=l) (d:=[]).
        - rewrite app_length.
          simpl.
          rewrite app_nth2.
          + assert (H12: (Datatypes.length (removelast l) + 1 - 1 - Datatypes.length (removelast l)=0)).
              {
              omega.
              }
            rewrite H12.
            simpl.
            symmetry.
            apply last_last.
          + omega.
        - apply not_eq_sym.
          apply length_not_zero.
          omega.
        }
      rewrite H5 in H7.
      assert (H9: removelast l = [s ++ inl left :: s']).
        {
        rewrite app_removelast_last with (l:=l)(d:=[]) in H6.
        - rewrite app_nth1 in H6.
          + rewrite app_length in H6.
            simpl in H6.
            assert (H13: length (removelast l) + 1 - 2 = 0).
              {
              omega.
              }
            rewrite H13 in H6.
            assert (H14: length (removelast l) = 1).
              {
              omega. 
              }
            apply list_single in H6.
            * exact H6.
            * exact H14.
          + rewrite app_length.
            simpl. 
            omega.
        - apply not_eq_sym.
          apply length_not_zero.
          omega.
        }
      unfold sf in H7.
      rewrite H7.
      unfold sf in H9.
      rewrite H9.
      {
      apply sflist_step with (left:=left).
      - apply sflist_start.
      - simpl.
        reflexivity.
      - exact H8.
      }
  + destruct l.
    * simpl in H1.
      apply le_Sn_0 in H1.
      contradiction.
    * apply not_eq_sym. 
      apply nil_cons.
Qed.

Lemma sflist_rules''':
forall g: cfg,
forall n: nat,
forall l: list sf,
length l = n ->
length l >= 2-> (sflist g l <-> 
                (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right)).
Proof.
intros g n l H H0.
split.
- generalize g n l H H0.
  apply sflist_rules'.
- generalize g n l H H0.
  apply sflist_rules''.
Qed.

Lemma sflist_rules:
forall g: cfg,
forall l: list sf,
length l >= 2-> (sflist g l <-> 
                (forall i: nat,
                 i <= (length l)-2 ->
                 exists left: non_terminal,
                 exists right s s': sf,
                 nth i l [] = s++inl left::s' /\
                 nth (S i) l [] = s++right++s' /\
                 rules g left right)).
Proof.
intros g l.
apply (sflist_rules''' g (length l) l).
reflexivity.
Qed.

Lemma sflist_elim_first:
forall g: cfg,
forall s: sf,
forall l : list sf,
sflist g (s::l) -> sflist g l.
Proof.
intros g s l H.
destruct l.
- apply sflist_empty.
- assert (LEN: length (s::s0::l) >= 2). 
  { simpl. 
    apply Le.le_n_S.
    apply Le.le_n_S.
    apply Le.le_0_n. }
  apply sflist_rules with (g:=g) in LEN.
  destruct LEN as [H1 H2].
  clear H2.
  specialize (H1 H).
  destruct l.
  + apply sflist_start.
  + apply sflist_rules.
    assert (LEN1: length (s0::s1::l) >= 2). 
    { simpl. 
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. }
    exact LEN1.
    intro i.
    specialize (H1 (S i)).
    assert (LEN2: S i <= length (s :: s0 :: s1 :: l) - 2 <->
                  i <= length (s0 :: s1 :: l) - 2).
    { split.
      - intro H2.
        simpl. 
        simpl in H2.
        apply le_S_n in H2.
        rewrite <- Minus.minus_n_O.
        exact H2.
      - intro H2.
        simpl.
        simpl in H2. 
        rewrite <- Minus.minus_n_O in H2.
        apply Le.le_n_S in H2.
        exact H2. }
    repeat rewrite nth_S in H1.
    rewrite LEN2 in H1.
    exact H1.
Qed.

Lemma sflist_elim_last:
forall g: cfg,
forall s: sf,
forall l : list sf,
sflist g (l++[s]) -> sflist g l.
Proof.
intros g s l H.
inversion H.
- symmetry in H1. 
  apply app_eq_nil in H1.
  destruct H1 as [H2 H3].
  subst.
  apply sflist_empty.
- destruct l.
  + apply sflist_empty.
  + inversion H1.
    symmetry in H3. 
    apply app_eq_nil in H3.
    destruct H3 as [H4 H5].
    subst.
    apply sflist_start.
- apply app_inj_tail in H0.
  destruct H0 as [H4 H5].
  subst.
  exact H1.
Qed.

Lemma sflist_tail:
forall g: cfg,
forall l : list sf,
sflist g l -> sflist g (tl l).
Proof.
intros g l H.
destruct l.
- simpl. 
  apply sflist_empty.
- simpl.
  apply sflist_elim_first in H.
  exact H.
Qed.

Lemma sflist_app_r:
forall g: cfg,
forall l1 l2: list sf,
sflist g (l1++l2) -> sflist g l1.
Proof.
intros g l1 l2 H.
destruct l1. 
+ apply sflist_empty. 
+ destruct l1. 
  * apply sflist_start. 
  * assert (LEN: length ((s :: s0 :: l1) ++ l2) >= 2).
    { simpl.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. 
    }
    apply sflist_rules with (g:=g) in LEN.
    destruct LEN as [H1 H2].
    clear H2.
    specialize (H1 H). 
    {
    apply sflist_rules. 
    - assert (LEN: length (s :: s0 :: l1) >= 2).
      { simpl.
        apply Le.le_n_S.
        apply Le.le_n_S.
        apply Le.le_0_n. }
      exact LEN.
    - intro i.
      specialize (H1 i).
      intro H3.
      assert (i <= Datatypes.length (s :: s0 :: l1) - 2 -> 
              i <= Datatypes.length ((s :: s0 :: l1) ++ l2) - 2).
      { intro H4.
        assert (length (s :: s0 :: l1) - 2 <= length ((s :: s0 :: l1) ++ l2) - 2).
        { destruct l2.
          - rewrite app_nil_r.
            apply le_n.
          - apply Minus.minus_le_compat_r.
            simpl. 
            apply Le.le_n_S.
            apply Le.le_n_S.
            rewrite app_length.
            apply Plus.le_plus_l. 
        }
        apply Le.le_trans with (m:=Datatypes.length (s :: s0 :: l1) - 2).
        + exact H3.
        + exact H0. 
      }
      specialize (H1 (H0 H3)).
      destruct H1 as [left [right [s1 [s' [H4 [H5 H6]]]]]]. 
      assert (H1: forall l' l'': list sf,
                  forall s' s'': sf,
                  forall i: nat,
                  i <= Datatypes.length (s' :: s'' :: l') - 1 ->
                  nth i (s' :: s'' :: l') [] = nth i ((s' :: s'' :: l')++l'') []).
                  { intros l' l'' s'0 s'' i0 H7.
                    rewrite app_nth1.
                    - reflexivity.
                    - simpl. 
                      simpl in H7. 
                      apply Lt.le_lt_n_Sm in H7.
                      exact H7.
                  }
      exists left, right, s1, s'.
      split. 
      + rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        * exact H4.
        * simpl in H3.
          rewrite <- Minus.minus_n_O in H3. 
          simpl.
          apply le_S in H3.
          exact H3.
      + rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        * { split.
            - exact H5.
            - exact H6. 
          }
        * simpl.
          apply Le.le_n_S.
          simpl in H3.
          rewrite <- Minus.minus_n_O in H3. 
          exact H3.
    }
Qed.

Lemma sflist_app_l:
forall g: cfg,
forall l1 l2: list sf,
sflist g (l1++l2) -> sflist g l2.
Proof.
intros g l1 l2 H.
destruct l2.
- apply sflist_empty.
- destruct l2.
  + apply sflist_start.
  + assert (LEN: length (l1 ++ s :: s0 :: l2) >= 2).
    { rewrite app_length.
      simpl. 
      rewrite Plus.plus_comm.
      assert (forall i j: nat, S (S i) >= 2 -> S (S i) + j >= 2).
         { intros i j.
           omega.
         }
      apply H0.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. 
    }
    apply sflist_rules with (g:=g) in LEN.
    destruct LEN as [H1 H2].
    clear H2.
    specialize (H1 H). 
    apply sflist_rules.
    assert (LEN: length (s :: s0 :: l2) >= 2).
    { simpl.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n. 
    }
    exact LEN.
    intro i.
    specialize (H1 (i + length l1)).
    intro H3.
    assert (i <= Datatypes.length (s :: s0 :: l2) - 2 -> 
            i <= Datatypes.length (l1 ++ (s :: s0 :: l2)) - 2).
      { intro H4.
        assert (length (s :: s0 :: l2) - 2 <= length (l1 ++ (s :: s0 :: l2)) - 2).
        { destruct l1.
          - rewrite app_nil_l.
            apply le_n.
          - apply Minus.minus_le_compat_r.
            simpl. 
            apply Le.le_n_S.
            rewrite app_length.
            simpl.
            rewrite <- plus_n_Sm.
            apply Le.le_n_S.
            apply Le.le_trans with (m:=S (Datatypes.length l2)).
            + apply Le.le_n_Sn.
            + apply Plus.le_plus_r.
        }
        apply Le.le_trans with (m:= Datatypes.length (s :: s0 :: l2) - 2).
        + exact H3.
        + exact H0.
      }
    assert (H3':=H3).
    apply Plus.plus_le_compat_l with (p:=length l1) in H3.
    rewrite Plus.plus_comm in H3.
    rewrite app_length in H1.
    assert (PLUS_MINUS: forall a b c: nat,
            b >= c -> a + b - c = a + (b - c)).
       { intros a b c.
         omega. 
       }
    rewrite <- PLUS_MINUS in H3. 
    * specialize (H1 H3).
      destruct H1 as [left [right [s1 [s' [H4 [H5 H6]]]]]].
      assert (H1: forall l' l'': list sf,
                  forall s' s'': sf,
                  forall i: nat,
                  i <= Datatypes.length (s' :: s'' :: l'') - 1 ->
                  nth i (s' :: s'' :: l'') [] = nth (i+length l') (l' ++ s' :: s'' :: l'') []).
                  { intros l' l'' s'0 s'' i0 H7.
                    rewrite app_nth2.
                    - rewrite Plus.plus_comm.
                      rewrite Minus.minus_plus.
                      reflexivity. 
                    - apply Plus.le_plus_r.
                  }
      exists left, right, s1, s'. {
      split. 
      - rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        + exact H4.
        + apply le_S in H3'.
          simpl in H3'.
          simpl. 
          rewrite <- Minus.minus_n_O in H3'.
          exact H3'.
      - rewrite H1 with (s':=s)(s'':=s0)(l':=l1)(l'':=l2).
        + split.
          * exact H5.
          * exact H6.
        + simpl.
          apply Le.le_n_S.
          simpl in H3'.
          rewrite <- Minus.minus_n_O in H3'.
          exact H3'. }
    * simpl.
      apply Le.le_n_S.
      apply Le.le_n_S.
      apply Le.le_0_n.
Qed.

Lemma sflist_app:
forall g: cfg,
forall l1 l2: list sf,
sflist g (l1++l2) -> sflist g l1 /\ sflist g l2.
Proof.
intros g l1 l2 H.
split.
- apply sflist_app_r in H.
  exact H.
- apply sflist_app_l in H.
  exact H.
Qed.

Lemma sflist_cat:
forall g: cfg,
forall l1 l2: list sf,
forall s: sf,
sflist g (l1 ++ [s]) /\
sflist g ([s] ++ l2) ->
sflist g (l1 ++ [s] ++ l2).
Proof.
intros g l1 l2 s [H1 H2].
assert (H3: length (l1 ++ [s] ++ l2) >= 2 \/
            length (l1 ++ [s] ++ l2) < 2).
  {
  omega.
  }
destruct H3 as [H4 | H5].
- (* length (l1 ++ [s] ++ l2) >= 2 *) 
  apply sflist_rules.
  + exact H4.
  + intros i H5.
    assert (H1':= H1).
    apply sflist_app_r in H1.
    assert (H8: length l1 >= 2 \/
                length l1 <  2).
      {
      omega.
      }
    destruct H8 as [H9 | H9].
    * (* length l1 >= 2 *) 
      assert (H9':= H9).
      apply sflist_rules with (g:=g) in H9.
      destruct H9 as [H10 _].
      specialize (H10 H1 i).
      assert (H11: i <= length l1 - 2 \/
                   i >  length l1 - 2).
        {
        omega.
        }
      {
      destruct H11 as [H12 | H12].
      - (* i <= length l1 - 2 *)
        specialize (H10 H12).
        destruct H10 as [left [right [s0 [s' [H20 [H21 H22]]]]]].
        exists left, right, s0, s'.
        split.
        + rewrite app_nth1.
          * exact H20.
          * omega.
        + split.
          * {
            rewrite app_nth1.
            - exact H21.
            - apply le_n_S in H12.
              omega.
            }
          * exact H22.
      - (* i > length l1 - 2 *)
        assert (H13: i >= length l1 \/
                     i < length l1).
          {
          omega.
          }
        destruct H13 as [H14 | H14].
        + (* i >= length l1 *)
          assert (H16: length ([s] ++ l2) >= 2 \/
                       length ([s] ++ l2) <  2).
            {
            omega.
            }
          destruct H16 as [H17 | H17].
          * (* length ([s] ++ l2) >= 2 *)
            apply sflist_rules with (g:=g) in H17.
            destruct H17 as [H17 _].
            specialize (H17 H2).
            specialize (H17 (i-length l1)).
            assert (H18: i - length l1 <= length ([s] ++ l2) - 2).
              {
              rewrite app_length.
              simpl.
              repeat rewrite app_length in H5.
              simpl in H5.
              omega.
              }
            specialize (H17 H18).
            destruct H17 as [left [right [s0 [s' [H20 [H21 H22]]]]]].
            exists left, right, s0, s'.
            {
            split.
            - rewrite app_nth2.
              + exact H20.
              + omega.
            - rewrite app_nth2.
              + split.
                * {
                  rewrite minus_Sn_m in H21.
                  - exact H21.
                  - omega.
                  }
                * exact H22.  
              + omega.
            }
          * (* length ([s] ++ l2) < 2 *)
            assert (H18: l2 = []).
              {
              rewrite app_length in H17.
              simpl in H17. 
              apply lt_S_n in H17.
              apply length_lt_1 in H17.
              exact H17.
              }
            rewrite H18.
            simpl.
            rewrite H18 in H4.
            simpl in H4.
            apply sflist_rules with (g:=g) in H4.
            destruct H4 as [H4 _].
            specialize (H4 H1').
            specialize (H4 i).
            assert (H19: i <= length (l1 ++ [s]) - 2).
              {
              rewrite app_length.
              simpl.
              subst.
              simpl in *.
              rewrite app_length in H5.
              simpl in H5.
              exact H5.
              }
            specialize (H4 H19).
            exact H4.
        + (* i < length l1 *)
          assert (H15: i = length l1 - 1). 
            { 
            omega.
            }
          assert (H16: length (l1 ++ [s]) >= 2 \/
                       length (l1 ++ [s]) <  2).
            {
            omega.
            }
          destruct H16 as [H17 | H17].
          * (* length (l1 ++ [s]) >= 2 *)
            apply sflist_rules with (g:=g) in H17.
            destruct H17 as [H17 _].
            specialize (H17 H1').
            specialize (H17 (length l1 - 1)).
            assert (H18: length l1 - 1 <= length (l1 ++ [s]) - 2).
              {
              rewrite app_length.
              simpl.
              omega.
              }
            specialize (H17 H18).
            destruct H17 as [left [right [s0 [s' [H21 [H22 H23]]]]]].
            exists left, right, s0, s'.
            {
            split.
            - rewrite H15.
              rewrite app_nth1.
              + rewrite app_nth1 in H21.
                * exact H21.
                * omega.
              + omega.
            - split.
              + rewrite H15.
                rewrite app_nth2.
                * {
                  rewrite app_nth1.
                  - rewrite app_nth2 in H22.
                    + exact H22.
                    + omega. 
                  - rewrite minus_Sn_m.
                    + simpl. 
                      omega. 
                    + omega. 
                  }
                * omega. 
              + exact H23. 
            } 
          * (* length (l1 ++ [s]) < 2 *) 
            assert (H18: l1 = []).
              { 
              rewrite app_length in H17.
              simpl in H17.
              rewrite plus_comm in H17.
              rewrite plus_Sn_m in H17.
              rewrite plus_O_n in H17.
              apply lt_S_n in H17.
              apply length_lt_1 in H17.
              exact H17.
              }
            subst.
            simpl in H9'.
            apply le_Sn_0 in H9'.
            contradiction.
      }
    * (* length l1 < 2 *)
      {
      destruct l1.
      - repeat rewrite app_nil_l.
        repeat rewrite app_nil_l in H4.
        apply sflist_rules with (g:=g) in H4.
        destruct H4 as [H4 _].
        specialize (H4 H2 i).
        rewrite app_nil_l in H5.
        specialize (H4 H5).
        exact H4. 
      - assert (H10: l1 = []).
          {
          replace (s0::l1) with ([s0]++l1) in H9.
          + rewrite app_length in H9.
            simpl in H9.
            apply lt_S_n in H9.
            apply length_lt_1 in H9.
            exact H9.
          + simpl.
            reflexivity.
          }
        subst.
        clear H1 H9.
        assert (H7: length ([s0]++[s]) >= 2).
          {
          simpl. 
          auto.
          }
        apply sflist_rules with (g:=g) in H7.
        destruct H7 as [H7 _].
        specialize (H7 H1' 0).
        assert (H8: 0 <= length ([s0] ++ [s]) - 2).
          {
          omega.
          }
        specialize (H7 H8).
        assert (H6: i = 0 \/ i = 1 \/ i >= 2).
          {
          omega.
          }
        destruct H6 as [H6 | H6].
        + rewrite H6.
          exact H7. 
        + destruct H6 as [H6 | H6].
          * rewrite H6.
            assert (H9: length ([s] ++ l2) >= 2 \/
                        length ([s] ++ l2) < 2).
              {
              omega.
              }
            {
            destruct H9 as [H9 | H9].
            - apply sflist_rules with (g:=g) in H9.
              destruct H9 as [H9 _].
              specialize (H9 H2 0).
              assert (H10: 0 <= length ([s] ++ l2) - 2).
                {
                omega.
                }
              specialize (H9 H10).
              destruct H9 as [left [right [s1 [s' [H20 [H21 H22]]]]]].
              exists left, right, s1, s'.
              split. 
              + rewrite app_nth2.
                * simpl.
                  simpl in H20.
                  exact H20.
                * simpl.
                  auto.
              + split.
                * {
                  rewrite app_nth2.
                  - simpl.
                    simpl in H21.
                    exact H21.
                  - simpl. 
                    auto.
                  }
                * exact H22.
            - assert (H10: l2 = []).
                {
                rewrite app_length in H9.
                simpl in H9.
                apply lt_S_n in H9.
                apply length_lt_1 in H9.
                exact H9.
                }
              subst.
              simpl in H5.
              apply le_Sn_0 in H5.
              contradiction.
            }
          * apply sflist_app_l in H2.
            assert (H9: length l2 >= 2 \/
                        length l2 < 2).
              {
              omega.
              }
            {
            destruct H9 as [H9 | H9].
            - apply sflist_rules with (g:=g) in H9.
              destruct H9 as [H9 _].
              specialize (H9 H2 (i-2)).
              assert (H10: i - 2 <= length l2 - 2).
                {
                repeat rewrite app_length in H5.
                simpl in H5.
                omega.
                }
              specialize (H9 H10).
              destruct H9 as [left [right [s1 [s' [H20 [H21 H22]]]]]].
              exists left, right, s1, s'.
              split.
              + rewrite app_assoc.
                rewrite app_nth2.
                * simpl.
                  exact H20.
                * simpl. 
                  exact H6.
              + split.
                * rewrite app_assoc.
                  {
                  rewrite app_nth2.
                  - rewrite minus_Sn_m in H21.
                    + replace (length ([s0] ++ [s])) with 2.
                      * exact H21.
                      * simpl.
                        reflexivity.
                    + exact H6.
                  - simpl.
                    omega.
                  }
                * exact H22.
            - destruct l2.
              + simpl in H9.
                repeat rewrite app_length in H5.
                simpl in H5.
                omega.
              + assert (H10: l2 = []).
                  {
                  replace (s1::l2) with ([s1]++l2) in H9.
                  - rewrite app_length in H9.
                    simpl in H9.
                    apply lt_S_n in H9.
                    apply length_lt_1 in H9.
                    exact H9.
                  - simpl.
                    reflexivity.
                  }
                subst.
                repeat rewrite app_length in H5.
                simpl in H5.
                omega.
            }
      }
- (* length (l1 ++ [s] ++ l2) < 2) *)
  rewrite app_length in H5.
  simpl in H5.
  rewrite <- plus_n_Sm in H5.
  apply lt_S_n in H5.
  assert (H6: length l1 + length l2 = 0).
    {
    omega.
    }
  assert (H7: length l1 = 0 /\ length l2 = 0).
    {
    omega.
    }
  destruct H7 as [H8 H9].
  apply length_zero in H8.
  apply length_zero in H9.
  subst.
  simpl.
  apply sflist_start.
Qed.

Lemma sflist_cat_rule:
forall g: cfg,
forall l1 l2: list sf,
forall left: non_terminal,
forall s s' right: sf,
sflist g (l1 ++ [s++inl left::s']) /\
sflist g ([s++right++s']++l2) /\
rules g left right ->
sflist g (l1 ++ [s++inl left::s']++[s++right++s']++l2).
Proof.
intros g l1 l2 left s s' right [H1 [H2 H3]].
apply sflist_step with (s2:=s) (s3:=s') (left:=left) (right:=right) in H1.
- rewrite app_assoc.
  apply sflist_cat.
  split.
  + exact H1.
  + exact H2.
- rewrite last_last. 
  reflexivity.
- exact H3.
Qed.

Lemma derives_sflist:
forall g: cfg,
forall s1 s2: sf,
derives g s1 s2 <->
exists l: list sf,
sflist g l /\
hd [] l = s1 /\
last l [] = s2.
Proof.
intros g s1 s2.
split.
- intro H.
  induction H.
  + exists [s].
    split.
    * apply sflist_start.
    * { split.
        - simpl.
          reflexivity.
        - simpl.
          reflexivity. } 
  + destruct IHderives as [l [H1 [H2 H3]]].
    exists (l++[s2 ++ right ++ s3]).
    split.
    * { apply sflist_step with (left:=left).
        - exact H1.
        - exact H3.
        - exact H0. }
    * { split.
        - subst.
          destruct l.
          + simpl.
            destruct s2.
            * inversion H3. 
            * inversion H3.
          + simpl.
            reflexivity.
        - apply last_last. }
- intro H.
  destruct H as [l [H1 [H2 H3]]].
  revert H3.
  generalize s2.
  induction H1.
  + simpl in H2. 
    intros l H1.
    simpl in H1.
    subst.
    apply derives_refl.
  + intros l H. simpl in H2. rewrite <- H2. simpl in H. rewrite H. apply derives_refl.
  + intros l0 H3.
    rewrite <- H3.
    rewrite last_last.
    apply derives_step with (left:=left).
    * apply IHsflist.   
      destruct l.
      simpl in H.
      destruct s0.
      inversion H.
      inversion H. 
      simpl in H2.
      simpl.
      exact H2.
      exact H.
    * exact H0.
Qed.   

Lemma exists_rule'_aux:
forall g: cfg,
forall s: sf,
forall n: non_terminal,
forall c: non_terminal + terminal,
derives g [inl n] s ->
In c s ->
s = [inl n] \/
exists left: non_terminal, exists right: sf, rules g left right /\ In c right.
Proof.
intros g s n c H1 H2.
remember [inl n] as s0.
induction H1.
- left.
  reflexivity.
- subst.
  specialize (IHderives eq_refl).
  repeat rewrite in_app_iff in H2.
  destruct H2 as [H2 | [H2 | H2]].
  + assert (H3: In c (s2 ++ inl left :: s3)).
      {
      repeat rewrite in_app_iff.
      left.
      exact H2.
      }
    specialize (IHderives H3).
    destruct IHderives as [IHderives | IHderives].
    * {
      destruct s2.
      - simpl in H2.
        contradiction.
      - inversion IHderives.
        destruct s2.
        + inversion H5.
        + inversion H5.
      }
    * right.
      exact IHderives.
  + right.
    exists left, right.
    split.
    * exact H.
    * exact H2.
  + assert (H3: In c (s2 ++ inl left :: s3)).
      {
      repeat rewrite in_app_iff.
      right.
      simpl.
      right.
      exact H2.
      }
    specialize (IHderives H3).
    destruct IHderives as [IHderives | IHderives].
    * {
      destruct s3.
      - simpl in H2.
        contradiction.
      - inversion IHderives.
        destruct s2.
        + inversion H4.
        + inversion H4.
          destruct s2.
          * inversion H6.
          * inversion H6.
      }
    * right.
      exact IHderives.
Qed.

Lemma exists_rule':
forall g: cfg,
forall s1 s2: sf,
forall n: non_terminal,
forall s: non_terminal + terminal,
derives g [inl n] (s1 ++ s :: s2) -> 
s = (inl n) /\ s1 = [] /\ s2 = [] \/
exists left: non_terminal,
exists right: sf,
rules g left right /\ In s right.
Proof.
intros g s1 s2 n s H.
apply exists_rule'_aux with (c:=s) in H.
- destruct H as [H | H].
  + left.
    split.
    * {
      destruct s1.
      - inversion H.
        reflexivity.
      - inversion H.
        destruct s1.
        + inversion H2.
        + inversion H2.
      }
    * {
      split.
      - destruct s1.
        + reflexivity.
        + inversion H.
          subst.
          destruct s1.
          * inversion H2.
          * inversion H2.
      - destruct s1.
        + inversion H.
          reflexivity.
        + inversion H.
          destruct s1.
          * subst.
            rewrite H2.
            inversion H.
          * rewrite H2.
            inversion H2.
      }
  + destruct H as [left [right [H2 H3]]].
    right.
    exists left, right.
    split.
    * exact H2.
    * exact H3.
- apply in_app_iff.
  right.
  replace (s :: s2) with ([s] ++ s2).
  + apply in_app_iff.
    left.
    simpl.
    left.
    reflexivity.
  + simpl.
    reflexivity.
Qed.

Lemma exists_rule:
forall g: cfg,
forall n: non_terminal,
forall s: sentence,
derives g [inl n] (map terminal_lift s) ->
rules g n (map terminal_lift s) \/
exists right: sf, rules g n right /\ derives g right (map terminal_lift s).
Proof.
intros g n s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
assert (H4: length l = 2 \/ length l > 2).
  {
  assert (GE2: length l >= 2).
    {
    destruct l.
    - simpl in H2.
      inversion H2.
    - simpl in H2.
      assert (NE: l <> []).
        {
        subst.
        simpl in H3.
        destruct l.
        + destruct s.
          * simpl in H3.
            inversion H3.
          * inversion H3.
        + apply not_eq_sym. 
          apply nil_cons.
        }
      apply exists_last in NE.
      destruct NE as [l' [a0 LAST]].
      rewrite LAST.
      replace (s0 :: l' ++ [a0]) with ([s0] ++ l' ++ [a0]).
      + repeat rewrite app_length.
        simpl.
        omega.
      + simpl. 
        reflexivity.
    }
  omega.
  }
inversion H1.
- subst.
  simpl in H2.
  inversion H2.
- clear H s0.
  destruct H4.
  + assert (H5: length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5.
    destruct H5 as [H6 H7].
    clear H7.
    specialize (H6 H1).
    specialize (H6 0).
    assert (H7: 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6 H7).
    clear H7.
    destruct H6 as [left [right [s0 [s' [H7 [H8 H9]]]]]].
    left.
    assert (H20: [inl n] = s0 ++ inl left :: s').
      {
      rewrite <- H2.
      rewrite <- H7.
      apply hd_nth0.
      }
    assert (H21: map terminal_lift s = s0 ++ right ++ s').
      {
      rewrite <- H3.
      rewrite <- H8.
      apply last_nth1.
      exact H.
      }
    destruct s0.
    * simpl in H20.
      inversion H20.
      rewrite <- H5 in H21.
      rewrite app_nil_l in H21.
      rewrite app_nil_r in H21.
      rewrite H21.
      exact H9.
    * inversion H20.
      {
      destruct s1.
      - simpl in H5. 
        inversion H5.
      - inversion H5.
      }
  + assert (H5: length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5.
    destruct H5 as [H6 H7].
    clear H7.
    specialize (H6 H1).
    specialize (H6 0).
    assert (H7: 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6 H7).
    clear H7.
    destruct H6 as [left [right [s0 [s' [H7 [H8 H9]]]]]].
    assert (H10: [inl n] = (s0 ++ inl left :: s')).
      {
      rewrite <- H2.
      rewrite <- H7.
      apply hd_nth0.
      }
    destruct s0.
    * simpl in H10.
      inversion H10.
      rewrite <- H4.
      right.
      rewrite <- H4 in H9.
      exists right.
      {
      split.
      - exact H9.
      - rewrite <- H5 in H8.
        rewrite app_nil_l in H8.
        rewrite app_nil_r in H8.
        apply derives_sflist.
        exists (tl l).
        split.
        + apply sflist_tail.
          exact H1.
        + split.
          * assert (H11: hd [] (tl l) = right).
              {
              rewrite <- H8.
              apply hd_tl_nth1.
              exact H.
              }
            exact H11.
          * assert (H12: last (tl l) [] = map terminal_lift s).
              {
              rewrite <- H3.
              apply last_tl_last.
              exact H.
              }
            exact H12.
      }
    * inversion H10.
      {
      destruct s1.
      - inversion H5.
      - inversion H5.
      }
- destruct H4.
  + assert (H5': length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5'.
    destruct H5' as [H6' H7'].
    clear H7'.
    specialize (H6' H1).
    specialize (H6' 0).
    assert (H7: 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6' H7).
    clear H7.
    destruct H6' as [left' [right' [s0 [s' [H7 [H8 H9]]]]]].
    left.
    assert (H20: [inl n] = s0 ++ inl left' :: s').
      {
      rewrite <- H2.
      rewrite <- H7.
      apply hd_nth0.
      }
    assert (H21: map terminal_lift s = s0 ++ right' ++ s').
      {
      rewrite <- H3.
      rewrite <- H8.
      apply last_nth1.
      exact H4.
      }
    destruct s0.
    * simpl in H20.
      inversion H20.
      rewrite <- H12 in H21.
      rewrite app_nil_l in H21.
      rewrite app_nil_r in H21.
      rewrite H21.
      exact H9.
    * inversion H20.
      {
      destruct s1.
      - simpl in H12. 
        inversion H12.
      - inversion H12.
      }
  + assert (H5': length l >= 2).
      {
      omega.
      }
    apply sflist_rules with (g:=g) in H5'.
    destruct H5' as [H6' H7'].
    clear H7'.
    specialize (H6' H1).
    specialize (H6' 0).
    assert (H7': 0 <= Datatypes.length l - 2).
      {
      omega.
      }
    specialize (H6' H7').
    clear H7'.
    destruct H6' as [left' [right' [s0' [s'' [H7' [H8' H9']]]]]].
    assert (H10': [inl n] = (s0' ++ inl left' :: s'')).
      {
      rewrite <- H2.
      rewrite <- H7'.
      apply hd_nth0.
      }
    destruct s0'.
    * simpl in H10'.
      inversion H10'.
      rewrite <- H8.
      right.
      rewrite <- H8 in H9'.
      exists right'.
      {
      split.
      - exact H9'.
      - rewrite <- H9 in H8'.
        rewrite app_nil_l in H8'.
        rewrite app_nil_r in H8'.
        apply derives_sflist.
        exists (tl l).
        split.
        + apply sflist_tail.
          exact H1.
        + split.
          * assert (H11': hd [] (tl l) = right').
              {
              rewrite <- H8'.
              apply hd_tl_nth1.
              exact H4.
              }
            exact H11'.
          * assert (H12': last (tl l) [] = map terminal_lift s).
              {
              rewrite <- H3.
              apply last_tl_last.
              exact H4.
              }
            exact H12'.
      }
    * inversion H10'.
      {
      destruct s0'.
      - inversion H9.
      - inversion H9.
      }
Qed.

Lemma g_equiv_trans:
forall g1 g2 g3: cfg,
g_equiv g1 g2 /\ g_equiv g2 g3 -> g_equiv g1 g3.
Proof.
unfold g_equiv.
intros g1 g2 g3 [H1 H2] s.
specialize (H1 s).
specialize (H2 s).
destruct H1 as [H3 H4].
destruct H2 as [H5 H6].
split.
- intros H7.
  apply H5.
  apply H3.
  exact H7.
- intros H7.
  apply H4.
  apply H6.
  exact H7.
Qed.

Lemma g_equiv_sym:
forall g1 g2: cfg,
g_equiv g1 g2 -> g_equiv g2 g1.
Proof.
unfold g_equiv.
intros g1 g2 H.
intro s.
specialize (H s).
destruct H as [H1 H2].
split.
- exact H2.
- exact H1.
Qed.

Lemma g_equiv_refl:
forall g: cfg,
g_equiv g g.
Proof.
intros g.
unfold g_equiv.
intros s.
split.
- intros H.
  exact H.
- intros H.
  exact H.
Qed.

(* --------------------------------------------------------------------- *)
(* EXAMPLES                                                              *)
(* --------------------------------------------------------------------- *)

Inductive rs1: non_terminal -> sf -> Prop:=
  r11: rs1 S' [inr a;inl S']
| r12: rs1 S' [inr b].

Definition g1: cfg:= {|
start_symbol:= S'; 
rules:= rs1
|}.

Lemma produces_g1_b:
produces g1 [b].
Proof.
unfold produces.
unfold generates.
simpl.
apply derives_start with (left:=S')(right:=[inr b]).
apply r12.
Qed.

Lemma produces_g1_aab:
produces g1 [a; a; b].
Proof.
unfold produces.
unfold generates.
simpl.
apply derives_step with (s2:=[inr a; inr a])(left:=S')(right:=[inr b]).
apply derives_step with (s2:=[inr a])(left:=S')(right:=[inr a;inl S']).
apply derives_start with (left:=S')(right:=[inr a;inl S']).
apply r11.
apply r11.
apply r12.
Qed.

Lemma produces_g1_aaaab:
produces g1 [a; a; a; a; b].
Proof.
unfold produces.
unfold generates.
simpl.
apply derives_step with (s2:=[inr a; inr a; inr a; inr a])(left:=S')(right:=[inr b]).
apply derives_step with (s2:=[inr a; inr a; inr a])(left:=S')(right:=[inr a; inl S']).
apply derives_step with (s2:=[inr a; inr a])(left:=S')(right:=[inr a; inl S']).
apply derives_step with (s2:=[inr a])(left:=S')(right:=[inr a; inl S']).
apply derives_start with (left:=S')(right:=[inr a; inl S']).
apply r11.
apply r11.
apply r11.
apply r11.
apply r12.
Qed.

Lemma sflist_g1_S':
sflist g1 [[inl S']].
Proof.
apply sflist_start.
Qed.

Lemma sflist_g1_S'_aS':
sflist g1 ([[inl S']]++[[inr a]++[inl S']]).
Proof.
apply sflist_step with (s2:=[])(left:=S')(right:=[inr a]++[inl S']).
apply sflist_start.
simpl. reflexivity.
apply r11.
Qed.

Lemma sflist_g1_S'_aS'_ab:
sflist g1 ([[inl S']]++[[inr a]++[inl S']]++[[inr a]++[inr b]]).
Proof.
apply sflist_step with (l:=[[inl S']]++[[inr a]++[inl S']])(s2:=[inr a])(left:=S')(right:=[inr b]).
apply sflist_step with (s2:=[])(left:=S')(right:=[inr a]++[inl S']).
apply sflist_start.
simpl. reflexivity.
apply r11.
simpl. reflexivity.
apply r12.
Qed.

Inductive rs2: non_terminal -> sf -> Prop:=
  rs21: rs2 W [inr d;inl Z]
| rs22: rs2 W [inr e].

Definition g2: cfg:= {|
start_symbol:= W; 
rules:= rs2
|}.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - USELESS SYMBOLS                                      *)
(* --------------------------------------------------------------------- *)

Inductive useful (g: cfg): non_terminal + terminal -> Prop:=
| useful_t:  forall t: terminal, useful g (inr t)
| useful_nt: forall n: non_terminal, (exists s: sentence, derives g [inl n] (map terminal_lift s)) -> useful g (inl n).

Definition useful_sf (g: cfg)(l: sf): Prop:=
forall s: non_terminal + terminal,
In s l -> useful g s.

Inductive g_use_rules (g: cfg): non_terminal -> sf -> Prop :=
| Lift_use : forall left: non_terminal,
             forall right: sf,
             rules g left right ->
             useful g (inl left) ->
             (forall s: non_terminal + terminal, In s right -> useful g s) ->
             g_use_rules g left right.

Definition g_use (g: cfg): cfg := {|
(* considering useful g (inl (start_symbol g)), that is,
   that g generates a non empty language *)
start_symbol:= start_symbol g;
rules:= g_use_rules g
|}.

Lemma useful_exists:
forall g: cfg,
forall n:non_terminal,
useful g (inl n) -> 
exists (left : non_terminal) (right : sf),
rules g left right /\ (n = left \/ In (inl n) right).
Proof.
intros g n H.
inversion H.
destruct H1 as [s H2].
apply exists_rule in H2.
destruct H2 as [H2 | H2].
- exists n, (map terminal_lift s).
  split.
  + exact H2.
  + left.
    reflexivity.
- destruct H2 as [right [H3 H4]].
  exists n, right.
  split.
  + exact H3.
  + left.
    reflexivity.
Qed.

Lemma useful_sf_sentence:
forall l: sf,
forall g: cfg,
useful_sf g l -> exists s': sentence, derives g l (map terminal_lift s').
Proof.
intros l g H.
induction l.
- exists [].
  simpl.
  apply derives_refl.
- replace (a0 :: l) with ([a0]++l) in H. 
  + assert (H1: forall s: non_terminal + terminal, In s l -> useful g s).
      {
      intros s H1.
      specialize (H s).
      apply H. 
      apply in_or_app.
      right.
      exact H1.
      }
    specialize (IHl H1).
    assert (H2: useful g a0).
      {
      apply H.
      simpl. 
      left.
      reflexivity.
      }
    inversion H2.
    * destruct IHl as [s' H3].
      exists (t::s').
      simpl.
      {
      replace (inr t:: l) with ([inr t] ++ l).
      - replace (terminal_lift t :: map terminal_lift s') with ([terminal_lift t] ++ map terminal_lift s').
        + apply derives_combine.
          split.
          * apply derives_refl.
          * exact H3.
        + simpl.
          reflexivity.
      - simpl.
        reflexivity.
      }
    * destruct H0 as [s1 H4].
      destruct IHl as [s2 H5].
      exists (s1 ++ s2).
      rewrite map_app.
      {
      replace (inl n :: l) with ([inl n] ++ l).
      - apply derives_combine.
        split. 
        + exact H4.
        + exact H5.
      - simpl. 
        reflexivity.
      } 
  + simpl.
    reflexivity.
Qed.

Lemma use_step:
forall g: cfg,
forall left: non_terminal,
forall right: sf,
rules g left right -> 
(forall s: non_terminal + terminal, In s right -> useful g s) ->
useful g (inl left).
Proof.
intros g left right H1 H2.
apply useful_nt.
apply derives_rule with (s1:=[]) (s2:=[]) in H1.
simpl in H1.
rewrite app_nil_r in H1.
apply useful_sf_sentence in H2. 
destruct H2 as [s' H3].
exists s'.
apply derives_trans with (s2:=right).
- exact H1.
- exact H3.
Qed.

Lemma useful_g_g_use:
forall g: cfg,
forall n: non_terminal,
useful g (inl n) -> useful (g_use g) (inl n).
Proof.
intros g n H.
induction H.
- apply useful_t.
- destruct H as [s H1].
  apply useful_nt.
  exists s.
  apply derives_sflist in H1.
  apply derives_sflist.
  destruct H1 as [l [H2 [H3 H4]]].
  exists l.
  split.
  + assert (H5: length l >= 2 \/ length l < 2).
      {
      omega.
      }
    destruct H5 as [H5 | H5].    
    * assert (H6:= H5).
      apply sflist_rules with (g:=g) in H5.
      destruct H5 as [H5 _].
      specialize (H5 H2).
      {
      apply sflist_rules.
      - exact H6.
      - intros i H7.
        specialize (H5 i H7).
        destruct H5 as [left [right [s0 [s' [H10 [H11 H12]]]]]].
        exists left, right, s0, s'.
        split. 
        + exact H10.
        + split.
          * exact H11.
          * simpl.
            {
            apply Lift_use.
            - exact H12.
            - apply useful_nt.
              assert (H20: derives g (s0 ++ inl left :: s') (map terminal_lift s)).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn i l) in H2.
                apply sflist_app_l in H2.
                exists (skipn i l).
                split.
                - exact H2.
                - split.
                  + rewrite hd_skip.
                    exact H10.
                  + rewrite last_skip.
                    * exact H4.
                    * omega.
                }
              assert (H21: exists s'': sentence, derives g [inl left] (map terminal_lift s'')).
                {
                apply derives_split in H20.
                destruct H20 as [s1' [s2' [H21 [_ H22]]]].
                replace (inl left :: s') with ([inl left] ++ s') in H22.
                - apply derives_split in H22.
                  destruct H22 as [s1'0 [s2'0 [H31 [H32 _]]]].
                  symmetry in H21. 
                  apply map_expand in H21.
                  destruct H21 as [s1'' [s2'' [H40 [H41 H42]]]].
                  rewrite <- H42 in H31.
                  symmetry in H31. 
                  apply map_expand in H31.
                  destruct H31 as [s1''' [s2''' [H50 [H51 H52]]]].
                  rewrite <- H51 in H32.
                  exists s1'''.
                  exact H32.
                - simpl.
                  reflexivity.
                }
              exact H21.
            - intros s1 H8.
              destruct s1.
              + assert (H30: derives g (s0 ++ right ++ s') (map terminal_lift s)).
                  {
                  apply derives_sflist.
                  rewrite <- (firstn_skipn (S i) l) in H2.
                  apply sflist_app_l in H2.
                  exists (skipn (S i) l).
                  split.
                  - exact H2.
                  - split.
                    + rewrite <- H11.
                      apply hd_skip.
                    + rewrite <- H4.
                      apply last_skip.
                      omega.
                  }
                assert (H31: exists s'': sentence, derives g right (map terminal_lift s'')).
                  {
                  apply derives_split in H30.
                  destruct H30 as [s1' [s2' [H35 [H36 H37]]]].
                  apply derives_split in H37.
                  destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
                  symmetry in H35.
                  apply map_expand in H35.
                  destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
                  rewrite <- H43 in H38.
                  symmetry in H38. 
                  apply map_expand in H38.
                  destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
                  rewrite <- H51 in H39.
                  exists s1'''.
                  exact H39.
                  }
                assert (H32: exists s'': sentence, derives g [inl n1] (map terminal_lift s'')).
                  {
                  apply in_split in H8.
                  destruct H8 as [l1 [l2 H60]].
                  rewrite H60 in H31.
                  destruct H31 as [s'' H61].
                  apply derives_split in H61.
                  destruct H61 as [s1' [s2' [H35 [H36 H37]]]].
                  replace (inl n1 :: l2) with ([inl n1] ++ l2) in H37.
                  - apply derives_split in H37.
                    destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
                    symmetry in H35.
                    apply map_expand in H35.
                    destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
                    rewrite <- H43 in H38.
                    symmetry in H38. 
                    apply map_expand in H38.
                    destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
                    rewrite <- H51 in H39.
                    exists s1'''.
                    exact H39.
                  - simpl. 
                    reflexivity.
                  }
                apply useful_nt.
                exact H32.
              + apply useful_t.
            }
      }
    * {
      destruct l. 
      - apply sflist_empty.
      - destruct l.
        + apply sflist_start.
        + replace (s0 :: s1 :: l) with ([s0] ++ [s1] ++ l) in H5. 
          * repeat rewrite app_length in H5.
            simpl in H5.
            repeat apply lt_S_n in H5.
            apply lt_n_0 in H5.
            contradiction. 
          * simpl. 
            reflexivity.
      }
  + split.
    * exact H3.
    * exact H4.
Qed.
Lemma useful_g_use:
forall g: cfg,
forall n: non_terminal,
appears (g_use g) (inl n) -> useful (g_use g) (inl n).
Proof.
intros g n H.
inversion H.
clear H.
destruct H0 as [right [H1 H2]].
destruct H2 as [H2| H2].
- subst.
  simpl in H1.
  inversion H1.
  subst.
  apply useful_g_g_use.
  exact H0.
- simpl in H1.
  inversion H1.
  subst.
  apply useful_g_g_use.
  specialize (H3 (inl n)).
  apply H3.
  exact H2.
Qed.

Lemma sflist_g_use_g:
forall g: cfg,
forall l: list sf,
sflist (g_use g) l -> sflist g l.
Proof.
intros g l H.
induction H.
- apply sflist_empty. 
- apply sflist_start.
- apply sflist_step with (left:=left).
  exact IHsflist.
  exact H0.
  simpl in H1.
  inversion H1.
  exact H2.
Qed.

Lemma produces_g_use_g:
forall g: cfg,
forall s: sentence,
produces (g_use g) s -> produces g s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
simpl in H2.
apply derives_sflist.
exists l.
split.
- apply sflist_g_use_g. 
  exact H1.
- split.
  + exact H2.
  + exact H3.
Qed.

Lemma sflist_g_g_use:
forall g: cfg,
forall l: list sf,
forall s: sentence,
sflist g l /\ last l [] = map (terminal_lift) s -> sflist (g_use g) l.
Proof.
intros g l s [H1 H2].
assert (H3: length l >= 2 \/ length l < 2).
  {
  omega.
  }
destruct H3 as [H3 | H3].
- assert (H3':=H3).
  apply sflist_rules with (g:=g) in H3.
  destruct H3 as [H3 _].
  specialize (H3 H1).
  apply sflist_rules.
  + exact H3'.
  + intros i H4.
    specialize (H3 i H4).
    destruct H3 as [left [right [s0 [s' [H5 [H6 H7]]]]]].
    exists left, right, s0, s'.
    split.
    * exact H5.
    * {
      split.
      - exact H6.
      - simpl.
        apply Lift_use.
        + exact H7.
        + apply useful_nt. 
          assert (H20: derives g (s0 ++ inl left :: s') (map terminal_lift s)).
            {
            apply derives_sflist.
            rewrite <- (firstn_skipn i l) in H1.
            apply sflist_app_l in H1.
            exists (skipn i l).
            split.
            - exact H1.
            - split.
              + rewrite hd_skip.
                exact H5.
              + rewrite last_skip.
                * exact H2.
                * omega.
            }
          assert (H21: exists s'': sentence, derives g [inl left] (map terminal_lift s'')).
            {
            apply derives_split in H20.
            destruct H20 as [s1' [s2' [H21 [_ H22]]]].
            replace (inl left :: s') with ([inl left] ++ s') in H22.
            - apply derives_split in H22.
              destruct H22 as [s1'0 [s2'0 [H31 [H32 _]]]].
              symmetry in H21. 
              apply map_expand in H21.
              destruct H21 as [s1'' [s2'' [H40 [H41 H42]]]].
              rewrite <- H42 in H31.
              symmetry in H31. 
              apply map_expand in H31.
              destruct H31 as [s1''' [s2''' [H50 [H51 H52]]]].
              rewrite <- H51 in H32.
              exists s1'''.
              exact H32.
            - simpl.
              reflexivity.
            }
          exact H21.
        + intros s1 H99.
          destruct s1.
          * assert (H30: derives g (s0 ++ right ++ s') (map terminal_lift s)).
              {
              apply derives_sflist.
              rewrite <- (firstn_skipn (S i) l) in H1.
              apply sflist_app_l in H1.
              exists (skipn (S i) l).
                split.
              - exact H1.
              - split.
                + rewrite <- H6.
                  apply hd_skip.
                + rewrite <- H2.
                  apply last_skip.
                  omega.
              }
            assert (H31: exists s'': sentence, derives g right (map terminal_lift s'')).
              {
              apply derives_split in H30.
              destruct H30 as [s1' [s2' [H35 [H36 H37]]]].
              apply derives_split in H37.
              destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
              symmetry in H35.
              apply map_expand in H35.
              destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
              rewrite <- H43 in H38.
              symmetry in H38. 
              apply map_expand in H38.
              destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
              rewrite <- H51 in H39.
              exists s1'''.
              exact H39.
              }
            assert (H32: exists s'': sentence, derives g [inl n] (map terminal_lift s'')).
              {
              apply in_split in H99.
              destruct H99 as [l1 [l2 H60]].
              rewrite H60 in H31.
              destruct H31 as [s'' H61].
              apply derives_split in H61.
              destruct H61 as [s1' [s2' [H35 [H36 H37]]]].
              replace (inl n :: l2) with ([inl n] ++ l2) in H37.
              - apply derives_split in H37.
                destruct H37 as [s1'0 [s2'0 [H38 [H39 H40]]]].
                symmetry in H35.
                apply map_expand in H35.
                destruct H35 as [s1'' [s2'' [H41 [H42 H43]]]].
                rewrite <- H43 in H38.
                symmetry in H38. 
                apply map_expand in H38.
                destruct H38 as [s1''' [s2''' [H50 [H51 H52]]]].
                rewrite <- H51 in H39.
                exists s1'''.
                exact H39.
              - simpl. 
                reflexivity.
              }
            apply useful_nt.
            exact H32.
          * apply useful_t.
      }   
- destruct l.
  + apply sflist_empty.
  + destruct l.
    * apply sflist_start.
    * {
      replace (s0 :: s1 :: l) with ([s0] ++ [s1] ++ l) in H3. 
      - repeat rewrite app_length in H3.
        simpl in H3.
        repeat apply lt_S_n in H3.
        apply lt_n_0 in H3.
        contradiction.
      - simpl. 
        reflexivity.
      }
Qed.

Lemma produces_g_g_use:
forall g: cfg,
forall s: sentence,
produces g s -> produces (g_use g) s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
apply derives_sflist.
exists l.
split.
- apply sflist_g_g_use with (s:=s).
  split.
  + exact H1.
  + exact H3.
- split.
  + exact H2.
  + exact H3.
Qed.

Theorem g_equiv_use:
forall g: cfg,
useful g (inl (start_symbol g)) -> g_equiv (g_use g) g.
Proof.
unfold g_equiv.
intros g H' s.
split.
- apply produces_g_use_g.
- apply produces_g_g_use.
Qed.

Theorem g_use_correct: 
forall g: cfg,
useful g (inl (start_symbol g)) ->
g_equiv (g_use g) g /\
(forall n: non_terminal, appears (g_use g) (inl n) -> useful (g_use g) (inl n)). 
Proof.
intros g H'.
split.
- apply g_equiv_use.
  exact H'.
- intros n H.
  inversion H.
  destruct H0 as [right [H1 H2]].
  simpl in H1.
  inversion H1.
  subst.
  destruct H2.
  + subst.
    apply useful_g_g_use in H3.
    exact H3.
  + specialize (H4 (inl n) H2).
    apply useful_g_g_use in H4.
    exact H4.
Qed.

(* --------------------------------------------------------------------- *)
(* EXAMPLES                                                              *)
(* --------------------------------------------------------------------- *)

Inductive rs4: non_terminal -> sf -> Prop:=
  r41: rs4 W [].

Definition g4: cfg:= {|
start_symbol:= W; 
rules:= rs4
|}.

Lemma useful_g4_W: useful g4 (inl W).
Proof.
apply useful_nt.
exists [].
apply derives_start.
simpl.
exact r41.
Qed.

Lemma useful_g1_S'_with_b: useful g1 (inl S').
Proof.
apply (useful_nt g1).
exists [b].
rewrite <- app_nil_l.
rewrite <- app_nil_r.
rewrite <- app_assoc.
apply derives_rule with (s1:=[]) (s2:=[]).
simpl.
apply r12.
Qed.

Lemma useful_g1_S'_with_aS': useful g1 (inl S').
Proof.
apply (useful_nt g1).
exists ([a] ++ [b]).
replace ([a] ++ [b]) with ([a] ++ [b] ++ []).
- repeat rewrite map_app.
  apply derives_step with (g:=g1) (left:=S').
  + simpl.
    rewrite <- app_nil_r.
    replace [terminal_lift a; inl S'] with ([terminal_lift a] ++ [inl S']).
    * rewrite <- app_nil_l.
      { 
      apply derives_step with (g:=g1) (left:=S').
      - simpl. 
        apply derives_refl.
      - apply r11.
      }
    * simpl. 
      reflexivity.
  + apply r12.
- simpl. 
  reflexivity.
Qed.

Inductive rs3: non_terminal -> sf -> Prop:=
  r31: rs3 W [inr a;inl W]
| r32: rs3 W [inr b].

Definition g3: cfg:= {|
start_symbol:= W; 
rules:= rs3
|}.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - INACCESSIBLE SYMBOLS                                 *)
(* --------------------------------------------------------------------- *)

Inductive accessible (g: cfg): non_terminal + terminal -> Prop:=
| accessible_s: forall s: non_terminal + terminal,
                (exists s1 s2: sf, derives g [inl (start_symbol g)] (s1++s::s2)) -> accessible g s.

Inductive g_acc_rules (g: cfg): non_terminal -> sf -> Prop :=
| Lift_acc : forall left: non_terminal,
             forall right: sf,
             rules g left right -> accessible g (inl left) -> g_acc_rules g left right.

Definition g_acc (g: cfg): cfg := {|
start_symbol:= start_symbol g;
rules:= g_acc_rules g
|}.

Lemma accessible_g_g_acc:
forall g: cfg,
forall s: non_terminal + terminal,
accessible g s -> accessible (g_acc g) s.
Proof.
intros g s H.
inversion H.
apply accessible_s.
clear H1.
destruct H0 as [s1 [s2 H1]].
apply derives_sflist in H1.
destruct H1 as [l [H2 [H3 H4]]].
exists s1, s2.
simpl.
apply derives_sflist.
exists l.
split. 
- assert (H5: length l >= 2 \/ length l < 2) by omega.
  destruct H5 as [H5 | H5].
  + assert (H5':=H5).
    apply sflist_rules with (g:=g) in H5.
    apply sflist_rules.
    * exact H5'.
    * intros i H6.
      destruct H5 as [H5 _].
      specialize (H5 H2 i H6).
      destruct H5 as [left [right [s3 [s' [H10 [H11 H12]]]]]].
      exists left, right, s3, s'.
      {
      split.
      - exact H10.
      - split.
        + exact H11.
        + simpl. 
          apply Lift_acc.
          * exact H12.
          * apply accessible_s.
            exists s3, s'.
            rewrite <- (firstn_skipn (S i) l) in H2.
            apply sflist_app_r in H2.
            apply derives_sflist.
            exists (firstn (S i) l).
            {
            split.
            - exact H2.
            - split.
              + rewrite <- H3.
                rewrite hd_first.
                * reflexivity.
                * omega.
              + rewrite <- H10.
                apply last_first_nth.
                omega.
            }
      }
  + destruct l.
    * apply sflist_empty.
    * {
      replace (s3::l) with ([s3]++l) in H5. 
      - rewrite app_length in H5.
        simpl in H5.
        assert (H7: length l = 0) by omega.
        apply length_zero in H7.
        rewrite H7.
        apply sflist_start.
      - simpl.
        reflexivity.
      }
- split.
  + exact H3.
  + exact H4.
Qed.

Lemma sflist_g_acc_g:
forall g: cfg,
forall l: list sf,
sflist (g_acc g) l -> sflist g l.
Proof.
intros g l H.
induction H.
- apply sflist_empty. 
- apply sflist_start.
- apply sflist_step with (left:=left).
  exact IHsflist.
  exact H0.
  simpl in H1.
  inversion H1.
  exact H2.
Qed.

Lemma produces_g_acc_g:
forall g: cfg,
forall s: sentence,
produces (g_acc g) s -> produces g s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
simpl in H2.
apply derives_sflist.
exists l.
split.
- apply sflist_g_acc_g. 
  exact H1.
- split.
  + exact H2.
  + exact H3.
Qed.

Lemma acc_step:
forall g: cfg,
forall n: non_terminal,
forall right: sf,
accessible g (inl n) -> rules g n right -> 
forall s: non_terminal + terminal,
In s right -> accessible g s.
Proof.
intros g n right H1 H2 s H3.
apply accessible_s.
inversion H1.
destruct H as [s1 [s2 H4]].
apply derives_step with (right:=right) in H4.
- apply in_split in H3.
  destruct H3 as [l1 [l2 H5]].
  rewrite H5 in H4.
  rewrite <- app_assoc in H4.
  exists (s1++l1), (l2++s2).
  rewrite <- app_assoc. 
  exact H4.
- exact H2.
Qed.

Lemma sflist_g_g_acc:
forall g: cfg,
forall l: list sf,
sflist g l /\ hd [] l = [inl (start_symbol g)] -> sflist (g_acc g) l.
Proof.
intros g l [H1 H2].
assert (H3: length l >= 2 \/ length l < 2) by omega.
destruct H3 as [H3 | H3].
- assert (H3':=H3).
  apply sflist_rules with (g:=g) in H3.
  destruct H3 as [H3 _].
  specialize (H3 H1).
  apply sflist_rules.
  + exact H3'.
  + intros i H4.
    specialize (H3 i H4).
    destruct H3 as [left [right [s0 [s' [H5 [H6 H7]]]]]].
    exists left, right, s0, s'.
    split.
    * exact H5.
    * {
      split.
      - exact H6.
      - simpl.
        apply Lift_acc.
        + exact H7.
        + apply accessible_s. 
          assert (H20: derives g [inl (start_symbol g)] (s0 ++ inl left :: s')).
            {
            apply derives_sflist.
            rewrite <- (firstn_skipn (S i) l) in H1.
            apply sflist_app_r in H1.
            exists (firstn (S i) l).
            split.
            - exact H1.
            - split.
              + rewrite hd_first.
                * exact H2.
                * omega. 
              + rewrite <- H5. 
                apply last_first_nth.
                omega.
            }
          exists s0, s'.
          exact H20.
      }
- destruct l.
  + apply sflist_empty.
  + destruct l.
    * apply sflist_start.
    * {
      replace (s :: s0 :: l) with ([s] ++ [s0] ++ l) in H3. 
      - repeat rewrite app_length in H3.
        simpl in H3.
        repeat apply lt_S_n in H3.
        apply lt_n_0 in H3.
        contradiction.
      - simpl. 
        reflexivity.
      }
Qed.

Lemma produces_g_g_acc:
forall g: cfg,
forall s: sentence,
produces g s -> produces (g_acc g) s.
Proof.
unfold produces.
unfold generates.
intros g s H.
apply derives_sflist in H.
destruct H as [l [H1 [H2 H3]]].
apply derives_sflist.
exists l.
split.
- apply sflist_g_g_acc.
  split.
  + exact H1.
  + exact H2.
- split.
  + simpl. 
    exact H2.
  + exact H3.
Qed.

Theorem g_equiv_acc:
forall g: cfg,
g_equiv (g_acc g) g.
Proof.
unfold g_equiv.
intros g s.
split.
- apply produces_g_acc_g.
- apply produces_g_g_acc.
Qed.

Theorem g_acc_correct: 
forall g: cfg,
g_equiv (g_acc g) g /\
(forall s: non_terminal + terminal, appears (g_acc g) s -> accessible (g_acc g) s). 
Proof.
intro g.
split.
- apply g_equiv_acc.
- intros n H.
  destruct n as [nt | t].
  + inversion H.
    destruct H0 as [right [H1 H2]].
    destruct H2 as [H2 | H2].
    * subst.
      simpl in H1.
      inversion H1.
      subst.
      apply accessible_g_g_acc.
      exact H2.
    * subst.
      simpl in H1.
      inversion H1.      
      apply accessible_g_g_acc.
      subst.
      {
      apply acc_step with (s:=inl nt) (right:=right) in H3.
      - exact H3.
      - exact H0.
      - exact H2.
      }
  + inversion H.
    destruct H0 as [right [H1 H2]].
    simpl in H1.
    inversion H1.
    subst.
    apply acc_step with (s:=inr t) (right:=right) in H3.
    * apply accessible_g_g_acc.
      exact H3.
    * exact H0.
    * exact H2.
Qed.

(* --------------------------------------------------------------------- *)
(* USEFUL AND ACCESSIBLE                                                 *)
(* --------------------------------------------------------------------- *)

Lemma preserve_useful:
forall g: cfg,
forall s: non_terminal + terminal,
useful g s -> 
accessible g s ->
useful (g_acc g) s.
Proof.
intros g s H1 H2.
destruct s.
- inversion H1.
  clear H.
  apply useful_nt.
  destruct H0 as [s H3].
  exists s.
  apply derives_sflist in H3.
  destruct H3 as [l [H4 [H5 H6]]].
  assert (H7: length l >= 2 \/ length l < 2) by omega.
  destruct H7 as [H7 | H7].
  + assert (H7':=H7). 
    apply sflist_rules with (g:=g) in H7.
    destruct H7 as [H7 _].
    specialize (H7 H4).
    apply derives_sflist.
    exists l.
    split.
    * {
      apply sflist_rules.
      - exact H7'.
      - intros i H8.
        specialize (H7 i H8).
        destruct H7 as [left [right [s0 [s' [H10 [H11 H12]]]]]].
        exists left, right, s0, s'.
        split.
        + exact H10.
        + split.
          * exact H11.
          * simpl.
            {
            apply Lift_acc.
            - exact H12.
            - apply accessible_s.
              inversion H2.
              destruct H as [s2 [s3 H13]].
              assert (H20: derives g [inl n] (s0 ++ inl left :: s')).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn (S i) l) in H4.
                apply sflist_app_r in H4.
                exists (firstn (S i) l).
                split. 
                - exact H4.
                - split.
                  + rewrite hd_first.
                    * exact H5.
                    * omega. 
                  + rewrite <- H10.
                    apply last_first_nth.
                    omega.
                }
              assert (H21: derives g [inl (start_symbol g)] (s2++s0++inl left::s'++s3)).
                {
                replace (s2 ++ inl n :: s3) with (s2 ++ [inl n] ++ s3) in H13.
                - apply derives_subs with (g:=g) (s1:=[inl (start_symbol g)]) (s2:=s2) (s3:=[inl n]) (s3':=(s0 ++ inl left :: s')) (s4:=s3) in H13.
                  + rewrite <- app_assoc in H13. 
                    exact H13.
                  + exact H20.
                - simpl. 
                  reflexivity.
                }
              exists (s2++s0), (s'++s3).
              rewrite <- app_assoc.
              exact H21.
            }
      }
    * {
      split.
      - exact H5.
      - exact H6.
      }
  + destruct l.
    * simpl in H5.
      inversion H5.
    * {
      replace (s0::l) with ([s0]++l) in H7.
      - rewrite app_length in H7.
        simpl in H7.
        assert (H8: length l = 0) by omega.
        apply length_zero in H8.
        subst. 
        simpl in H5.
        rewrite H5 in H6.
        simpl in H6.
        destruct s.
        + simpl in H6.
          inversion H6.
        + replace (t::s) with ([t]++s) in H6. 
          * rewrite map_app in H6.
            inversion H6.
          * simpl. 
            reflexivity.
      - simpl. 
        reflexivity.
      }
- apply useful_t.
Qed.

Lemma acc_appears:
forall g: cfg,
forall n: non_terminal,
useful g (inl (start_symbol g)) -> accessible g (inl n) -> appears g (inl n).
Proof.
intros g n H10 H.
inversion H.
destruct H0 as [s1 [s2 H2]].
clear s H H1.
simpl.
apply exists_rule' in H2.
destruct H2 as [H2 | H2].
- destruct H2 as [H2 [_ _]].
  inversion H2.
  apply (useful_exists g (start_symbol g)).
  exact H10.
- destruct H2 as [left [right [ H3 H4]]].
  exists left, right.
  split.
  + exact H3.
  + right.
    exact H4.
Qed.

Lemma still_useful:
forall g: cfg,
forall n: non_terminal,
useful g (inl (start_symbol g)) ->
accessible (g_use g) (inl n) ->
useful (g_use g) (inl n).
Proof.
intros g n H99 H.
inversion H.
destruct H0 as [s1 [s2 H2]].
clear H1.
apply exists_rule' in H2.
destruct H2 as [H2 | H2]. 
- apply useful_g_use.
  simpl in H2.
  destruct H2 as [H2 [_ _]].
  rewrite H2.  
  rewrite H2 in H.
  apply acc_appears.
  + simpl. 
    apply useful_g_g_use. 
    exact H99.
  + exact H.
- destruct H2 as [left [right [H3 H4]]].
  simpl in H3.
  inversion H3.
  subst.
  apply useful_nt.
  specialize (H2 (inl n) H4).
  inversion H2.
  destruct H6 as [s0 H7].
  exists s0.
  apply derives_sflist in H7.
  destruct H7 as [l [H10 [H11 H12]]].
  apply derives_sflist.
  exists l.
  split.
  + assert (H6: length l >= 2 \/ length l < 2) by omega.
    destruct H6 as [H6 | H6].
    * assert (H6':=H6).
      apply sflist_rules with (g:=g) in H6.
      destruct H6 as [H6 _].
      specialize (H6 H10).
      {
      apply sflist_rules.
      - exact H6'.
      - intros i H7.
        specialize (H6 i H7).
        destruct H6 as [left0 [right0 [s3 [s' [H20 [H21 H22]]]]]].
        exists left0, right0, s3, s'.
        split.
        + exact H20.
        + split.
          * exact H21.
          * simpl.
            {
            apply Lift_use.
            - exact H22.
            - assert (H30: derives g (s3 ++ inl left0 :: s') (map terminal_lift s0)).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn i l) in H10.
                apply sflist_app_l in H10.
                exists (skipn i l).
                split.
                + exact H10.
                + split.
                  * rewrite hd_skip.
                    exact H20.
                  * {
                    rewrite last_skip.
                    - exact H12.
                    - omega.
                    }
                }
              apply derives_split in H30.
              destruct H30 as [s1' [s2' [H31 [H32 H33]]]].
              symmetry in H31.
              apply map_expand in H31.
              destruct H31 as [_ [s2'0 [_ [_ H34]]]].
              rewrite <- H34 in H33.
              replace (inl left0 :: s') with ([inl left0] ++ s') in H33.
              + apply derives_split in H33.
                destruct H33 as [s1'0 [s2'1 [H35 [H36 _]]]].
                symmetry in H35.
                apply map_expand in H35.
                destruct H35 as [s1'1 [_ [_ [H37 _]]]].
                rewrite <- H37 in H36.
                apply useful_nt.
                exists s1'1.
                exact H36.
              + simpl.
                reflexivity.
            - assert (H30: derives g (s3 ++ right0 ++ s') (map terminal_lift s0)).
                {
                apply derives_sflist.
                rewrite <- (firstn_skipn (S i) l) in H10.
                apply sflist_app_l in H10.
                exists (skipn (S i) l).
                split.
                + exact H10.
                + split.
                  * rewrite hd_skip.
                    exact H21.
                  * {
                    rewrite last_skip.
                    - exact H12.
                    - omega.
                    }
                } 
              apply derives_split in H30.
              destruct H30 as [s1' [s2' [H31 [H32 H33]]]].
              symmetry in H31.
              apply map_expand in H31.
              destruct H31 as [_ [s2'0 [_ [_ H34]]]].
              rewrite <- H34 in H33.
              apply derives_split in H33.
              destruct H33 as [s1'0 [s2'1 [H35 [H36 _]]]].
              symmetry in H35.
              apply map_expand in H35.
              destruct H35 as [s1'1 [_ [_ [H37 _]]]].
              rewrite <- H37 in H36.
              intros s4 H40.
              destruct s4. 
              + apply useful_nt.
                apply in_split in H40.
                destruct H40 as [l1 [l2 H41]].
                rewrite H41 in H36.
                apply derives_nt_sentence in H36.
                destruct H36 as [s'0 H42].
                exists s'0.
                exact H42.
              + apply useful_t.
            }
      }
    * apply lt2_sflist.
      exact H6.
  + split.
    * exact H11.
    * exact H12.
Qed. 

Theorem useful_and_accessible:
forall g: cfg,
useful g (inl (start_symbol g)) ->
exists g': cfg,
(forall s: non_terminal + terminal, appears g' s -> accessible g' s) /\
(forall s: non_terminal + terminal, appears g' s -> useful g' s) /\
g_equiv g g'.
Proof.
intros g H'.
exists (g_acc (g_use g)).
split.
- intros s H.
  destruct s. 
  + inversion H.
    destruct H0 as [right [H1 H2]].
    destruct H2 as [H2 | H2].
    * subst.
      simpl in H1.
      inversion H1.
      subst.
      apply accessible_g_g_acc.
      exact H2.
    * simpl in H1.
      inversion H1.
      subst.
      apply accessible_g_g_acc.
      {
      apply acc_step with (s:=inl n) (right:=right) in H3.
      - exact H3.
      - exact H0.
      - exact H2.
      }
  + inversion H.
    destruct H0 as [right [H1 H2]].
    inversion H1.
    subst.
    apply accessible_g_g_acc.
    simpl in H1.
    inversion H1.
    subst.
    {
    apply acc_step with (s:=inr t) (right:=right) in H3.
      - exact H3.
      - exact H0.
      - exact H2.
      }
- split.
  + intros s H.
    destruct s.
    * inversion H.
      destruct H0 as [right [H1 H2]].
      {
      destruct H2 as [H2 | H2].
      - simpl in H1.
        inversion H1.
        subst.
        assert (H4:=H3).
        apply still_useful in H3.
        + apply preserve_useful.
          * exact H3.
          * exact H4.
        + exact H'.
      - inversion H1. 
        subst.
        apply acc_step with (s:=inl n) (right:=right) in H3.
        + assert (H4:=H3). 
          apply still_useful in H3.
          * {
            apply preserve_useful.
            - exact H3.
            - exact H4.
            }
          * exact H'.
        + exact H0.
        + exact H2.   
      }        
    * apply useful_t.
  + assert (H1: g_equiv (g_use g) g).
      {
      apply g_equiv_use.
      exact H'.
      }
    assert (H2: g_equiv (g_acc (g_use g)) (g_use g)).
      {
      apply g_equiv_acc.
      }
    apply g_equiv_trans with (g2:=g_use g).
    split.
    * apply g_equiv_sym.
      exact H1.
    * apply g_equiv_sym.
      exact H2.
Qed.
