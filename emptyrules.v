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
(* SIMPLIFICATION - EMPTY RULES                                          *)
(* --------------------------------------------------------------------- *)

Require Import List.
Require Import Ring.
Require Import Omega.
Require Import Decidable.

Require Import misc_arith.
Require Import misc_list.
Require Import cfg.
Require Import useless.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Open Scope list_scope.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - DEFINITIONS                            *)
(* --------------------------------------------------------------------- *)

Section EmptyRules_Definitions.

Variables non_terminal terminal: Type.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).
Notation nlist:= (list non_terminal).

Definition empty (g: cfg _ _) (s: non_terminal + terminal): Prop:=
derives g [s] [].

Inductive g_emp_rules (g: cfg _ _): non_terminal -> sf -> Prop :=
| Lift_direct : 
       forall left: non_terminal,
       forall right: sf,
       right <> [] -> rules g left right ->
       g_emp_rules g left right
| Lift_indirect:
       forall left: non_terminal,
       forall right: sf,
       g_emp_rules g left right ->
       forall s1 s2: sf, 
       forall s: non_terminal,
       right = s1 ++ (inl s) :: s2 ->
       empty g (inl s) ->
       s1 ++ s2 <> [] ->
       g_emp_rules g left (s1 ++ s2).

Lemma g_emp_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist,
In (start_symbol g) ntl /\
forall left: non_terminal,
forall right: sf,
g_emp_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal, In (inl s) right -> In s ntl).
Proof.
intros g.
destruct (rules_finite g) as [n [ntl H1]].
exists n, ntl.
split.
- destruct H1 as [H1 _].
  exact H1.
- intros left right H2.
  destruct H1 as [_ H1].
  induction H2.
  + specialize (H1 left right H0).
    destruct H1 as [H4 [H5 H6]].
    split.
    * exact H4.
    * {
      split.
      - exact H5.
      - exact H6.
      }
  + subst.
    destruct IHg_emp_rules as [H4 [H5 H6]].
    split.
    * apply length_cons_le in H4.
      exact H4.
    * {
      split.
      - exact H5.
      - intros s0 H7.
        apply H6.
        apply in_app_cons.
        exact H7.
      }
Qed.

Definition g_emp (g: cfg _ _): cfg _ _ := {|
start_symbol:= start_symbol g;
rules:= g_emp_rules g;
rules_finite:= g_emp_finite g
|}.

Definition not_derives_empty: Prop:=
forall g: cfg non_terminal terminal,
forall n: non_terminal,
~ derives g [inl n] [].

Definition has_no_empty_rules (g: cfg non_terminal terminal): Prop:=
forall left: _,
forall right: _,
rules g left right -> right <> [].

Definition has_one_empty_rule (g: cfg _ _): Prop:=
(rules g (start_symbol g) []) /\
(forall left: non_terminal,
 forall right: sf,
 left <> (start_symbol g) ->
 rules g left right -> right <> []).

Definition has_no_nullable_symbols (g: cfg _ _): Prop:=
forall s: non_terminal + terminal, ~ empty g s.

Definition generates_empty (g: cfg _ _): Prop:=
empty g (inl (start_symbol g)).

Definition produces_string_not_empty (g: cfg non_terminal terminal): Prop:=
exists s: sentence, produces g s /\ s <> [].

End EmptyRules_Definitions.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - LEMMAS AND THEOREMS                    *)
(* --------------------------------------------------------------------- *)

Section EmptyRules_Lemmas.

Variables non_terminal terminal: Type.

Notation sf := (list (non_terminal + terminal)).
Notation sentence := (list terminal).
Notation term_lift:= ((terminal_lift non_terminal) terminal).

Lemma g_emp_not_derives_empty:
forall g: cfg non_terminal terminal,
forall n: non_terminal,
~ derives (g_emp g) [inl n] [].
Proof.
intros g n H.
inversion H.
clear H.
subst.
simpl in H3.
inversion H3.
- subst.
  apply app_eq_nil in H0.
  destruct H0 as [_ H0].
  apply app_eq_nil in H0.
  destruct H0 as [H0 _]. 
  contradiction.
- subst.
  apply app_eq_nil in H0.
  destruct H0 as [_ H0].
  apply app_eq_nil in H0.
  destruct H0 as [H0 _].
  rewrite H0 in H3.
  inversion H3.
  + subst.
    destruct H2.
    reflexivity.
  + destruct H10.
    reflexivity.
Qed.

Lemma g_emp_has_no_empty_rules:
forall g: cfg non_terminal terminal,
has_no_empty_rules (g_emp g).
Proof.
intros g.
unfold has_no_empty_rules.
intros left right H.
inversion H.
- exact H0.
- exact H3.
Qed.

Lemma in_left_not_empty:
forall g: cfg non_terminal terminal,
forall x: non_terminal,
forall right: sf,
rules (g_emp g) x right -> ~ empty (g_emp g) (inl x).
Proof.
intros g x right H1 H2.
simpl in H1.
inversion H1.
- clear H1.
  subst.
  apply g_emp_not_derives_empty in H2.
  contradiction.
- clear H1. 
  subst.
  apply g_emp_not_derives_empty in H2.
  contradiction.
Qed.

Lemma in_right_not_empty:
forall g: cfg non_terminal terminal,
forall x n: non_terminal,
forall right: sf,
rules (g_emp g) x right -> In (inl n) right -> ~ empty (g_emp g) (inl n).
Proof.
intros g x n right H1 H2 H3.
simpl in H1.
inversion H1.
- clear H1.
  subst.
  apply g_emp_not_derives_empty in H3.
  contradiction.
- clear H1. 
  subst.
  apply g_emp_not_derives_empty in H3.
  contradiction.
Qed.

Lemma g_emp_has_no_nullable_symbols:
forall g: cfg non_terminal terminal,
has_no_nullable_symbols (g_emp g).
Proof.
intros g.
unfold has_no_nullable_symbols.
intros s H1.
destruct s as [nt | t].
- apply g_emp_not_derives_empty in H1.
  contradiction.
- unfold empty in H1.
  inversion H1.
  apply app_eq_nil in H.
  destruct H as [_ H].
  apply app_eq_nil in H.
  destruct H as [H _].
  subst.
  apply g_emp_has_no_empty_rules in H3.
  destruct H3.
  reflexivity.
Qed.  

Lemma rules_g_emp_g:
forall g: cfg non_terminal terminal,
forall left: non_terminal,
forall right: sf,
rules (g_emp g) left right ->
rules g left right \/ derives g [inl left] right.
Proof.
intros g left right H.
simpl in H.
induction H.
- left.
  exact H0.
- destruct IHg_emp_rules as [H3 | H3].
  + right.
    replace (s1 ++ s2) with (s1 ++ [] ++ s2).
    * {
      apply derives_subs with (s3:=[inl s]).
      - apply derives_start.
        rewrite H0 in H3.
        exact H3.
      - exact H1.
      }
    * simpl. 
      reflexivity.
  + right.
    replace (s1 ++ s2) with (s1 ++ [] ++ s2).
    * {
      apply derives_subs with (s3:=[inl s]).
      - rewrite H0 in H3.
        exact H3.
      - exact H1.
      }
    * simpl. 
      reflexivity.
Qed.

Lemma generates_g_emp_g:
forall g: cfg non_terminal terminal,
forall s: sf,
generates (g_emp g) s -> generates g s.
Proof.
unfold generates.
intros g s H.
simpl in H.
remember [inl (start_symbol g)] as w1. 
induction H.
- apply derives_refl.
- apply rules_g_emp_g in H0.
  destruct H0 as [H0 | H0].
  + apply derives_step with (left:=left).
    * apply IHderives.
      exact Heqw1.
    * exact H0.
  + apply derives_subs with (s3:=[inl left]).
    * apply IHderives.
      exact Heqw1.
    * exact H0.
Qed.

Lemma derives_g_emp_g:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sf,
derives (g_emp g) [inl n] s -> derives g [inl n] s.
Proof.
intros g n s H.
remember [inl n] as w1. 
induction H.
- apply derives_refl.
- apply rules_g_emp_g in H0.
  destruct H0 as [H0 | H0].
  + apply derives_step with (left:=left).
    * apply IHderives.
      exact Heqw1.
    * exact H0.
  + apply derives_subs with (s3:=[inl left]).
    * apply IHderives.
      exact Heqw1.
    * exact H0.
Qed.

Lemma rules_g_g_emp:
forall g: cfg _ _, 
forall left: non_terminal,
forall right: sf,
right <> [] ->
rules g left right ->
rules (g_emp g) left right.
Proof.
intros g left right H.
simpl.
apply Lift_direct.
exact H.
Qed.

Inductive sfmatch g: sf -> list sf -> Prop :=
| sfmatch_nil: 
    sfmatch g [] []
| sfmatch_term: 
    forall t xs xxs,
    sfmatch g xs xxs -> sfmatch g (inr t :: xs) ([inr t] :: xxs)
| sfmatch_nonterm: 
   forall nt xs xxs p,
    (p = [] -> empty g (inl nt)) ->
    (p <> [] -> derives (g_emp g) [inl nt] p) ->
    sfmatch g xs xxs -> sfmatch g (inl nt :: xs) (p :: xxs).

Fixpoint flatten (l: list sf): sf :=
match l with
| [] => []
| x :: xs => x ++ flatten xs
end.

Fixpoint elim_emp (l: sf) (ll: list sf): sf :=
match l with
| [] => []
| (x :: xs) => match ll with
               | [] => l
               | [] :: ll' => elim_emp xs ll'
               | p :: ll' => x :: elim_emp xs ll'
               end
end.

Lemma sfmatch_left_nil:
forall g: cfg _ _,
forall l: list sf,
sfmatch g [] l ->
l = [].
Proof.
intros g l H.
inversion H.
reflexivity.
Qed.

Lemma elim_emp_not_nil:
forall right: sf,
forall split: list sf,
elim_emp right split <> [] ->
right <> [].
Proof.
intros right split H.
destruct right.
- simpl in H.
  destruct H.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma flatten_map:
forall x: list sf,
forall y: sentence,
flatten x = map term_lift y ->
y <> [] ->
x <> [].
Proof.
intros x y H1 H2.
destruct x.
- simpl in H1.
  symmetry in H1. 
  apply map_eq_nil in H1.
  subst.
  destruct H2.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma flatten_not_nil:
forall x: sf,
flatten [x] <> [] ->
x <> [].
intros x H.
destruct x.
- simpl in H.
  destruct H.
  reflexivity.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Lemma flatten_not_nil_exists:
forall x: list sf,
flatten x <> [] ->
exists x1 x3: list sf,
exists x2: sf,
x = x1 ++ [x2] ++ x3 /\
x2 <> [].
Proof.
induction x.
- intro H.
  simpl in H.
  destruct H.
  reflexivity.
- intro H.
  simpl in H.
  apply app_not_nil in H.
  destruct H as [H | H].
  + exists [], x, a.
    split. 
    * simpl.  
      reflexivity.
    * exact H.
  + specialize (IHx H).
    destruct IHx as [x1 [x3 [x2 [H1 H2]]]].
    subst.
    exists (a :: x1), x3, x2.
    split. 
    * simpl. 
      reflexivity.
    * exact H2. 
Qed.

Lemma sfmatch_derives:
forall g: cfg _ _,
forall l1 l2: sf,
forall l: list sf,
forall x: non_terminal + terminal,
sfmatch g (l1 ++ [x] ++ l2) l ->
exists p: sf,
exists l3 l4: list sf,
l = l3 ++ [p] ++ l4 /\
sfmatch g l1 l3 /\
derives g [x] p /\
sfmatch g l2 l4.
Proof.
intros g l1.
induction l1.
- intros l2 l x H.
  simpl in H.
  inversion H.
  + (* terminal *)
    subst.
    exists [inr t], [], xxs.
    split.
    * simpl. 
      reflexivity.
    * {
      split.
      - constructor.
      - split.
        + constructor.
        + exact H3.
      }
  + (* non-terminal *)
    subst.
    exists p, [], xxs.
    split.
    * simpl.
      reflexivity.
    * {
      split. 
      - constructor. 
      - split. 
        + assert (H6: p = [] \/ p <> []).
            {
            apply nil_not_nil.
            }
          destruct H6 as [H6 | H6].
          * subst. 
            specialize (H2 (eq_refl [])).
            exact H2.
          * apply derives_g_emp_g.
            apply H3.
            exact H6.
        + exact H5.
      } 
- intros l2 l x H.
  inversion H.
  clear H. 
  + (* terminal *)
    subst.
    specialize (IHl1 l2 xxs x H3).
    destruct IHl1 as [p [l3 [l4 [H11 [H12 [H13 H14]]]]]].
    exists p, ([inr t] :: l3), l4.
    split. 
    * simpl.
      rewrite H11.
      reflexivity.
    * {
      split. 
      - apply sfmatch_term.
        exact H12.
      - split.
        + exact H13.
        + exact H14.
      }
  + (* non-terminal *)
    subst. 
    specialize (IHl1 l2 xxs x H5).
    destruct IHl1 as [p' [l3 [l4 [H11 [H12 [H13 H14]]]]]].
    exists p', ([p] ++ l3), l4.
    split.
    * simpl. 
      rewrite H11.
      reflexivity.
    * {
      split.
      - apply sfmatch_nonterm.
        + exact H2.
        + exact H3.
        + exact H12.
      - split. 
        + exact H13.
        + exact H14.
      }
Qed.

Lemma sfmatch_derives_inv:
forall g: cfg _ _,
forall l: sf,
forall l3 l4: list sf,
forall p: sf,
sfmatch g l (l3 ++ [p] ++ l4) ->
exists x: non_terminal + terminal,
exists l1 l2: sf,
l = l1 ++ [x] ++ l2 /\
sfmatch g l1 l3 /\
sfmatch g [x] [p] /\
sfmatch g l2 l4.
Proof.
intros g l l3 l4 p H.
remember (l3 ++ [p] ++ l4) as w.
generalize dependent l4.
generalize dependent l3.
generalize dependent p.
induction H.
- (* empty *)
  intros p l3 l4 H. 
  destruct l3.
  + inversion H.
  + inversion H.
- (* terminal *)
  intros p l3 l4 H1. 
  destruct l3.
  + simpl in H1.
    inversion H1.
    exists (inr t), [], xs.
    split. 
    * simpl. 
      reflexivity.
    * {
      split.
      - constructor.
      - split.
        + constructor.
          constructor.
        + rewrite <- H3.
          exact H.
      }
  + inversion H1.
    clear H1.
    subst.
    specialize (IHsfmatch p l3 l4 (eq_refl (l3 ++ p :: l4))).
    destruct IHsfmatch as [x [l1 [l2 [H1 [H2 [H3 H4]]]]]].
    rewrite H1. 
    exists x, (inr t :: l1), l2.
    split.
    * simpl. 
      reflexivity.
    * {
      split.
      - apply sfmatch_term.
        exact H2.
      - split.
        + exact H3.
        + exact H4.
      }
- (* non-terminal *)
  intros p0 l3 l4 H2.
  destruct l3.
  inversion H2.
  clear H2.
  subst.
  + assert (H5: p0 = [] \/ p0 <> []).
      {
      apply nil_not_nil.
      }
    destruct H5 as [H5 | H5].
    * subst. 
      exists (inl nt), [], xs.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + constructor.
        + split.
          * {
            constructor.
            - exact H.
            - exact H0.
            - constructor.
            }
          * exact H1.
      }
    * exists (inl nt), [], xs.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + constructor.
        + split.
          * {
            constructor.
            - exact H.
            - exact H0.
            - constructor.
            }
          * exact H1.
      }
  + assert (H5: p = [] \/ p <> []).
      {
      apply nil_not_nil.
      }
    destruct H5 as [H5 | H5].
    * inversion H2. 
      subst. 
      rewrite <- H4 in H2. 
      rewrite <- H4.
      clear H2 H4. 
      specialize (IHsfmatch p0 l3 l4).
      specialize (IHsfmatch (eq_refl (l3 ++ p0 :: l4))).
      destruct IHsfmatch as [x [l1 [l2 [H2 [H3 [H4 H5]]]]]].
      rewrite H2.
      exists x, (inl nt :: l1), l2.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + apply sfmatch_nonterm.
          * exact H.
          * exact H0.
          * exact H3.
        + split.
          * exact H4.
          * exact H5.
      }
    * inversion H2.
      clear H2.
      subst.
      specialize (IHsfmatch p0 l3 l4).
      specialize (IHsfmatch (eq_refl (l3 ++ p0 :: l4))).
      destruct IHsfmatch as [x [l1 [l2 [H2 [H3 [H4 H6]]]]]].
      rewrite H2.
      exists x, (inl nt :: l1), l2.
      {
      split. 
      - simpl. 
        reflexivity.
      - split.
        + apply sfmatch_nonterm.
          * exact H.
          * exact H0.
          * exact H3.
        + split.
          * exact H4.
          * exact H6.
      }
Qed.

Lemma sfmatch_elim_emp_not_nil:
forall g: cfg _ _,
forall x: non_terminal + terminal,
forall p: sf,
sfmatch g [x] [p] ->
p <> [] ->
elim_emp [x] [p] <> [].
Proof.
intros g x p H1 H2.
inversion H1.
- simpl.
  apply not_eq_sym. 
  apply nil_cons.
- subst.
  destruct p.
  + destruct H2.
    reflexivity.
  + simpl.
    apply not_eq_sym.
    apply nil_cons.
Qed. 

Lemma sfmatch_combine:
forall g: cfg _ _,
forall l1 l3: sf,
forall l2 l4: list sf,
sfmatch g l1 l2 ->
sfmatch g l3 l4 ->
sfmatch g (l1 ++ l3) (l2 ++ l4).
Proof.
intros g l1 l3 l2 l4 H1.
induction H1.
- simpl. 
  auto.
- intros H2.
  specialize (IHsfmatch H2).
  apply sfmatch_term with (t:= t) in IHsfmatch.
  exact IHsfmatch.
- intros H2.
  specialize (IHsfmatch H2).
  assert (H3: p = [] \/ p <> []).
    {
    apply nil_not_nil.
    }
  destruct H3 as [H3 | H3].
  + specialize (H H3).
    apply sfmatch_nonterm with (nt:= nt) (p:= p) in IHsfmatch.
    * exact IHsfmatch.
    * intros _.
      exact H.
    * exact H0.
  + specialize (H0 H3).
    apply sfmatch_nonterm with (nt:= nt) (p:= p) in IHsfmatch.
    * exact IHsfmatch.
    * exact H.
    * intros _.
      exact H0.
Qed.

Lemma elim_emp_split:
forall g: cfg _ _,
forall l1 l3: sf,
forall l2 l4: list sf,
sfmatch g l1 l2 ->
sfmatch g l3 l4 ->
elim_emp (l1 ++ l3) (l2 ++ l4) = (elim_emp l1 l2) ++ (elim_emp l3 l4).
Proof.
intros g l1 l3 l2 l4 H.
generalize dependent l4.
generalize dependent l3.
induction H.
- subst.
  intros. 
  simpl. 
  reflexivity.
- intros. 
  simpl.
  apply app_eq.
  apply IHsfmatch.
  exact H0.
- intros l3 l4 H2.
  assert (H3: p = [] \/ p <> []).
    {
    apply nil_not_nil.
    }
  destruct H3 as [H3 | H3].
  + subst.
    simpl.
    apply IHsfmatch.
    exact H2.
  + destruct p. 
    * destruct H3. 
      reflexivity.
    * simpl. 
      apply app_eq.
      apply IHsfmatch.
      exact H2.
Qed.

Lemma elim_emp_not_nil_add_left:
forall g: cfg _ _,
forall l1 l1': sf,
forall l2 l2': list sf,
sfmatch g l1 l2 ->
elim_emp l1 l2 <> [] ->
sfmatch g l1' l2' ->
elim_emp (l1' ++ l1) (l2' ++ l2) <> [].
Proof.
intros g l1 l1' l2 l2' H.
generalize dependent l2'.
generalize dependent l1'.
inversion H.
- intros.
  simpl in H2.
  destruct H2.
  reflexivity.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    right.
    exact H3.
  + exact H4.
  + apply sfmatch_term.
    exact H0.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    right.
    exact H5.
  + exact H6.
  + apply sfmatch_nonterm.
    * exact H0.
    * exact H1.
    * exact H2.
Qed.

Lemma elim_emp_not_nil_add_right:
forall g: cfg _ _,
forall l1 l1': sf,
forall l2 l2': list sf,
sfmatch g l1 l2 ->
elim_emp l1 l2 <> [] ->
sfmatch g l1' l2' ->
elim_emp (l1 ++ l1') (l2 ++ l2') <> [].
Proof.
intros g l1 l1' l2 l2' H.
generalize dependent l2'.
generalize dependent l1'.
inversion H.
- intros.
  simpl in H2.
  destruct H2.
  reflexivity.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    left.
    exact H3.
  + rewrite H1. 
    rewrite H2. 
    exact H.
  + exact H4.
- intros.
  rewrite elim_emp_split with (g:= g).
  + apply app_not_nil_inv.
    left.
    exact H5.
  + rewrite H3. 
    rewrite H4. 
    exact H.
  + exact H6. 
Qed.

Lemma elim_emp_not_emp:
forall g: cfg _ _,
forall l1 l2: sf,
forall x: non_terminal + terminal,
forall l3 l4: list sf,
forall p: sf,
sfmatch g l1 l3 ->
sfmatch g [x] [p] ->
sfmatch g l2 l4 ->
p <> [] ->
elim_emp (l1 ++ [x] ++ l2) (l3 ++ [p] ++ l4) <> [].
Proof.
intros g l1 l2 x l3 l4 p H2 H3 H4 H5.
destruct x.
- (* non-terminal *)
  assert (H3':= H3). 
  apply sfmatch_elim_emp_not_nil in H3.
  + assert (H3'':= H3').
    apply elim_emp_not_nil_add_left with (l1':= l1) (l2':= l3) in H3'.
    * {
      apply elim_emp_not_nil_add_right with (g:= g) (l1':= l2) (l2':= l4) in H3'.
      - repeat rewrite <- app_assoc in H3'. 
        exact H3'.
      - apply sfmatch_combine.
        + exact H2.
        + exact H3''. 
      - exact H4.
      }
    * exact H3.
    * exact H2.
  + exact H5.
- (* terminal *)
  assert (H3':= H3).
  apply sfmatch_elim_emp_not_nil in H3.
  + assert (H3'':= H3').
    apply elim_emp_not_nil_add_left with (g:= g) (l1':= l1) (l2':= l3) in H3'.
    * {
      apply elim_emp_not_nil_add_right with (g:= g) (l1':= l2) (l2':= l4) in H3'.
      - repeat rewrite <- app_assoc in H3'. 
        exact H3'.
      - apply sfmatch_combine.
        + exact H2.
        + exact H3''. 
      - exact H4.
      }
    * exact H3.
    * exact H2.
  + exact H5.
Qed.

Lemma flatten_elim_emp:
forall x: sf,
forall y: list sf,
forall g: cfg _ _,
sfmatch g x y ->
flatten y <> [] ->
elim_emp x y  <> [].
Proof.
intros x y g H3 H4.
apply flatten_not_nil_exists in H4.
destruct H4 as [x1 [x2 [x3 [H5 H6]]]].
assert (H3':= H3).
rewrite H5 in H3. 
apply sfmatch_derives_inv in H3.
destruct H3 as [x0 [l1 [l2 [H11 [H12 [H13 H14]]]]]].
subst.
apply elim_emp_not_emp with (g:= g).
- exact H12.
- exact H13.
- exact H14.
- exact H6.
Qed.

Lemma sfmatch_derives_first:
forall g: cfg _ _,
forall l1: sf,
forall l2: list sf,
sfmatch g l1 l2 ->
(l1 = [] /\ l2 = []) \/
(exists a1: non_terminal + terminal,
 exists l1': sf,
 exists a2: sf,
 exists l2': list sf,
 l1 = a1 :: l1' /\
 l2 = a2 :: l2' /\
 derives g [a1] a2 /\ sfmatch g l1' l2').
Proof.
intros g l1 l2 H.
assert (H1: l1 = [] \/ l1 <> []).
  {
  apply nil_not_nil.
  }
destruct H1 as [H1 | H1].
- left.
  subst.
  inversion H.
  auto.
- right.
  destruct l1.
  + destruct H1.
    reflexivity.
  + clear H1.
    change (s :: l1) with ([] ++ [s] ++ l1) in H.
    apply sfmatch_derives in H.
    destruct H as [p [l3 [l4 [H2 [H3 [H4 H5]]]]]].
    apply sfmatch_left_nil in H3.
    exists s, l1, p, l4.
    split. 
    * reflexivity.
    * {
      split.
      - rewrite H3 in H2.
        exact H2.
      - split.
        + exact H4.
        + exact H5.
      }
Qed.  

Lemma right_emp_prop_aux:
forall g left r2 rl2,
sfmatch g r2 rl2 ->
forall r1 rl1,
sfmatch g r1 rl1 ->
elim_emp (r1 ++ r2) (rl1 ++ rl2) <> [] ->
rules (g_emp g) left (r1 ++ r2) ->
rules (g_emp g) left (r1 ++ elim_emp r2 rl2).
Proof.
intros g left r2 rl2 HH.
elim HH.
- (* empty *)
  intros.
  rewrite app_nil_r in *. 
  auto.
- (* terminal *)
  intros.
  simpl.
  replace (r1 ++ inr t :: elim_emp xs xxs) with ((r1 ++ [inr t]) ++ elim_emp xs xxs).
  + apply H0 with (rl1 ++ [[inr t]]).
    * apply sfmatch_combine. 
      auto.
      constructor.
      constructor.
    * repeat rewrite <- app_assoc. 
      simpl. 
      auto.
    * rewrite <- app_assoc. 
      auto.
  + repeat rewrite <- app_assoc. 
    simpl. 
    auto.
- (* non-terminal *)
  intros.
  simpl.
  destruct p.
  + (* empty *)
    apply H2 with rl1. 
    * auto.
    * {
      rewrite elim_emp_split with (g:=g) in H4. 
      - simpl in H4.
        rewrite <- elim_emp_split with (g:=g) in H4; auto.
      - auto.
      - constructor.
        + auto.
        + auto.
        + auto.
      }
    * simpl. 
      {
      econstructor 2.   
      - exact H5.
      - reflexivity.
      - apply H. 
        auto.
      - red.
        intros.
        apply app_eq_nil in H6. 
        destruct H6. 
        subst.
        elim H4. 
        simpl.
        inversion_clear H3. 
        reflexivity.
      }
  + (* not empty *)
    replace (r1 ++ inl nt :: elim_emp xs xxs) with ((r1 ++ [inl nt]) ++ elim_emp xs xxs).
    * {
      apply H2 with (rl1 ++ [s :: p]).
      - apply sfmatch_combine. 
        + auto.
        + constructor. 
          * auto.
          * auto. 
          * constructor.
      - repeat rewrite <- app_assoc. 
        simpl. 
        auto.
      - rewrite <- app_assoc. 
        auto.
      }
    * repeat rewrite <- app_assoc.
      simpl. 
      auto.
Qed.

Lemma right_emp_prop:
forall (g: cfg _ _),
forall left: non_terminal,
forall right: sf,
forall right_list: list sf,
rules g left right ->
sfmatch g right right_list ->
elim_emp right right_list <> [] ->
rules (g_emp g) left (elim_emp right right_list).
Proof.
intros.
assert (Hemp: rules (g_emp g) left right).
  { 
  apply rules_g_g_emp.
  - apply elim_emp_not_nil with (split:= right_list).
    exact H1.
  - exact H.
  }
change (elim_emp right right_list) with ([] ++ (elim_emp right right_list)).
apply right_emp_prop_aux with [].
- auto.
- constructor.
- assumption.
- assumption.
Qed.

Lemma derives_g_g_emp:
forall g: cfg _ _,
forall n: non_terminal,
forall s: sentence,
s <> [] ->
derives g [inl n] (map term_lift s) -> derives (g_emp g) [inl n] (map term_lift s).
Proof.
intros g n s H1 H2.
rewrite derives_equiv_derives6 in H2.
destruct H2 as [i H3].
generalize dependent n.
generalize dependent s.
generalize (le_refl i). 
generalize i at 1 3 as i'.
induction i.
- intros i' Hi' s H1 n H2. 
  apply le_n_0_eq in Hi'. 
  subst.
  apply derives6_0_eq in H2. 
  destruct s.
  + simpl in H2.
    inversion H2.
  + simpl in H2.
    inversion H2.
- intros i' Hi' s H1 n H2.
  inversion H2.
  + apply derives_refl.
  + assert (H10: s1 = [] /\ s2 = []).
      {  
      destruct s1.
      - split.
        + reflexivity.    
        + inversion H.   
          reflexivity.
      - inversion H.
        destruct s1.
        + inversion H8.
        + inversion H8.
      }
    destruct H10 as  [H11 H12].
    subst.
    rewrite app_nil_l.
    rewrite app_nil_l in H.
    rewrite <- H in H2.
    clear H.
    simpl in H4.
    rewrite app_nil_r in H4.
    clear H2.
    (* estrutura intermédia que particiona as derivações do rhs da regra *)
    assert (H10: exists right2: list sf,
                 sfmatch g right right2 /\
                 flatten right2 = map term_lift s).
      {
      apply le_S_n in Hi'.
      generalize i0 Hi' s H4. 
      clear i0 Hi' H4 H0 n s H1 left.
      elim right.
      - (* nil case *)
        intros.
        inversion H4.
        + symmetry in H2.  
          apply map_eq_nil in H2.
          subst.
          exists []. 
          split. 
          * constructor.
          * simpl. 
            reflexivity.
        + apply app_eq_nil in H.
          destruct H as [_ H]. 
          inversion H.
      - (* cons case *)
        intros.
        destruct a.
        + (* non_terminal *)
          change (inl n::l) with ([inl n]++l) in H4.
          generalize H4. 
          intros H4'.
          apply derives6_split in H4'.
          destruct H4' as [s1' [s2' [n1 [n2 [HH1 [HH2 [HH3 HH4]]]]]]].
          symmetry in HH1. 
          apply map_expand in HH1. 
          destruct HH1 as [s0a [s0b [? [? ?]]]]. 
          subst.
          assert (Hn2: n2 <= i) by omega.
          specialize (H n2 Hn2 s0b HH4). 
          destruct H as [right2' [H1 H2]].
          exists ((map term_lift s0a)::right2').
          simpl.
          rewrite H2.
          simpl. 
          split.
          * assert (H20: s0a = [] \/ s0a <> []).
              {
              apply nil_not_nil.
              }
            {
            constructor.
            - destruct H20 as [H20 | H20].
              + subst. 
                simpl.
                intros _.
                assert (H5: exists n1: nat, derives6 g n1 [inl n] (map term_lift [])).
                  {
                  exists n1.
                  exact HH3.
                  }
                rewrite <- derives_equiv_derives6 in H5.
                exact H5.
              + intros. 
                apply map_eq_nil in H.
                rewrite H in H20. 
                destruct H20.
                reflexivity.
            - destruct H20 as [H20 | H20].
              + intros.
                rewrite H20 in H.
                simpl in H.
                destruct H.
                reflexivity.
              + intros.
                assert (H10: n1 <= i).  
                  {
                  omega. 
                  }
              specialize (IHi n1 H10 s0a H20 n HH3). 
              exact IHi.
            - exact H1.
            }
          * rewrite map_app. 
            reflexivity.
        + (* terminal *)
          generalize H4.
          change (inr t :: l) with ((map term_lift [t])++l).
          intros H4'. 
          apply derives6_t_list_left in H4'.
          destruct H4' as [s' Hs'].
          rewrite Hs' in H4.
          replace (inr t::l) with (map term_lift [t] ++ l) in H4; [|reflexivity]. 
          apply derives6_tl_tl in H4.
          generalize Hs'.
          apply map_map_app in Hs'. 
          destruct Hs' as [s'' Hs''].
          rewrite Hs'' in H4.
          specialize (@H _ Hi' s'' H4). 
          destruct H as [right2' [HH1 HH2]].
          intros.
          exists ([inr t]::right2').
          simpl.
          rewrite Hs'. 
          unfold terminal_lift. 
          split. 
          * apply sfmatch_term.
            exact HH1.
          * simpl. 
            rewrite Hs''.
            rewrite <- HH2.
            reflexivity.
      }
    clear IHi. 
    destruct H10 as [right2 [HH1 HH2]].
    pose (right':= elim_emp right right2).
    assert (H11: rules (g_emp g) left right').
      { 
      apply right_emp_prop. 
      - exact H0.
      - exact HH1. 
      - apply flatten_elim_emp with (g:=g). 
        + exact HH1.
        + rewrite HH2. 
          apply map_not_nil_inv. 
          exact H1. 
      }
    apply derives_trans with (s2:=right').
    * apply derives_start. 
      exact H11.
    * (* indução sobre right..., usando [sfmatch] para lidar com não terminais *)
      unfold right'.
      generalize s right2 HH1 HH2. 
      clear s H1 right2 HH1 HH2 right' H11 H4 H0.
      {
      elim right.
      - simpl. 
        intros.
        inversion HH1.
        subst. 
        simpl in HH2.
        inversion HH2.
        constructor.
      - simpl. 
        intros.
        inversion HH1.
        + (* terminal *)
          subst. 
          simpl in HH2.
          destruct s. 
          * inversion HH2.
          * simpl.
            change (inr t :: elim_emp l xxs) with ([inr t]++elim_emp l xxs).
            change (term_lift t0 :: map term_lift s) with ([inr t0]++ map term_lift s).
            inversion HH2.
            rewrite <- H1.
            apply derives_context_free_add_left.
            rewrite H2.
            {
            apply H.
            - exact H3.
            - exact H2.
            }
        + (* non_terminal *)
          destruct p.
          * (* nullable *)
            subst.
            {
            apply H.
            - exact H5. 
            - exact HH2.
            }
          * (* non-nullable *)
            subst. 
            apply map_expand in HH2.
            destruct HH2 as [sa [sb [Hs [Hs1 Hs2]]]]; subst s.
            rewrite map_app.
            change (inl nt :: elim_emp l xxs) with ([inl nt]++ elim_emp l xxs).
            apply derives_combine.
            {
            split. 
            - rewrite Hs1.
              apply H3.
              apply not_eq_sym.
              apply nil_cons.
            - apply H with (right2:= xxs) (s:= sb).
              + exact H5.
              + symmetry.
                fold flatten in Hs2.
                exact Hs2.
            }
      }
Qed.

Theorem g_emp_correct: 
forall g: cfg non_terminal terminal,
g_equiv_without_empty (g_emp g) g /\
has_no_empty_rules (g_emp g).
Proof.
intro g.
split.
- unfold g_equiv_without_empty.
  intros s H.
  split.
  + apply derives_g_emp_g.
  + apply derives_g_g_emp.
    exact H.
- unfold has_no_empty_rules.
  intros left right H.
  destruct right.
  + inversion H.
    * destruct H0.
      reflexivity.
    * {
      inversion H.
      - destruct H6.
        reflexivity.
      - rewrite H6 in H11.
        destruct H11.
        reflexivity.
      }
  + apply not_eq_sym.
    apply nil_cons.
Qed.  

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - DEFINITIONS TO INCLUDE EMPTY STRING    *)
(* --------------------------------------------------------------------- *)

Inductive non_terminal': Type:=
| Lift_nt: non_terminal -> non_terminal'
| New_ss.

Notation sf' := (list (non_terminal' + terminal)).
Notation term_lift':= ((terminal_lift non_terminal') terminal).
Notation nlist:= (list non_terminal).
Notation nlist':= (list non_terminal').

Definition non_terminal_lift (n: non_terminal): non_terminal':=
Lift_nt n.

Definition symbol_lift (s: non_terminal + terminal): non_terminal' + terminal:=
match s with
| inr t => inr t
| inl n => inl (Lift_nt n)
end.

Definition sf_lift (s: sf): sf':=
map symbol_lift s.

Definition sf_list_lift (l: list sf): list sf':=
map sf_lift l.

Inductive g_emp'_rules (g: cfg _ _): non_terminal' -> sf' -> Prop :=
| Lift_all:
       forall left: non_terminal,
       forall right: sf,
       rules (g_emp g) left right ->
       g_emp'_rules g (Lift_nt left) (map symbol_lift right)
| Lift_empty:
       empty g (inl (start_symbol (g_emp g))) -> g_emp'_rules g New_ss []
| Lift_start:
       g_emp'_rules g New_ss [inl (Lift_nt (start_symbol (g_emp g)))].

Definition map_pair (i: (non_terminal * sf)): (non_terminal' * sf'):=
match i with
| (n, l) => (Lift_nt n, map symbol_lift l)
end.

Lemma length_map_ge:
forall n: nat,
forall s: sf,
length s >= n ->
length (map symbol_lift s) >= n.
Proof.
induction n,s.
- simpl.
  auto.
- simpl. 
  intros H.
  omega.
- simpl.
  auto.
- simpl. 
  intros H.
  apply le_S_n in H.
  specialize (IHn s0 H).
  apply le_n_S in IHn.
  exact IHn.
Qed.

Lemma length_map_le:
forall n: nat,
forall s: sf,
length s <= n ->
length (map symbol_lift s) <= n.
Proof.
induction n,s.
- simpl.
  auto.
- simpl. 
  intros H.
  omega.
- simpl.
  auto.
- simpl. 
  intros H.
  apply le_S_n in H.
  specialize (IHn s0 H).
  apply le_n_S in IHn.
  exact IHn.
Qed.

Lemma in_map_exists:
forall s': non_terminal',
forall l: sf,
In (inl s') (map symbol_lift l) ->
exists s: non_terminal,
s' = Lift_nt s /\
In (inl s) l.
Proof.
intros s' l H.
apply in_split in H.
destruct H as [l1 [l2 H]].
symmetry in H.
apply map_expand in H.
destruct H as [s1' [s2' [H1 [H2 H3]]]].
change (inl s' :: l2) with ([inl s'] ++ l2) in H3.
symmetry in H3.
apply map_expand in H3.
destruct H3 as [s1'0 [s2'0 [H4 [H5 H6]]]].
destruct s1'0.
- inversion H5.
- inversion H5.
  destruct s.
  + simpl in H0. 
    inversion H0. 
    exists n.
    split. 
    * reflexivity.
    * rewrite H1. 
      apply in_or_app.
      right.
      rewrite H4.
      apply in_or_app.
      left.
      simpl. 
      left.
      reflexivity.
  + simpl in H0.
    inversion H0.
Qed.

Lemma in_lift_map:
forall n: non_terminal,
forall ntl: nlist,
In n ntl ->
In (Lift_nt n) (map non_terminal_lift ntl).
Proof.
intros n ntl H.
induction ntl.
- simpl in H.
  contradiction.
- simpl. 
  simpl in H.
  destruct H as [H | H].
  + left.
    subst.
    reflexivity.
  + right.
    apply IHntl.
    exact H.
Qed.

(*
Lemma g_emp_length_min:
forall g: cfg _ _,
forall left : non_terminal,
forall right : sf,
g_emp_rules g left right ->
length right >= 1.
Proof.
intros g left right H.
inversion H.
- subst. 
  apply not_nil in H0.
  omega.
- subst.
  destruct s1, s2.
  + destruct H3.
    reflexivity.
  + subst. 
    simpl. 
    omega.
  + subst. 
    simpl. 
    omega.
  + subst. 
    simpl.
    omega.
Qed.
*)

(*
Lemma temp:
forall g: cfg _ _,
forall n: nat,
forall ntl: nlist,
(forall (left : non_terminal) (right : sf),
        rules (g_emp g) left right ->
        length right <= n /\
        In left ntl /\ (forall s : non_terminal, In (inl s) right -> In s ntl)) ->
n >= 1.
Proof.
intros g n ntl H.
apply g_emp_length_min.
Qed.
*)

Lemma g_emp_length_min:
forall g: cfg _ _,
forall left : non_terminal,
forall right : sf,
forall n: nat,
g_emp_rules g left right ->
length right = n ->
n >= 1.
Proof.
intros g left right n H1 H2.
inversion H1.
- subst. 
  apply not_nil in H.
  omega.
- subst.
  destruct s1, s2.
  + destruct H4.
    reflexivity.
  + subst. 
    simpl. 
    omega.
  + subst. 
    simpl. 
    omega.
  + subst. 
    simpl.
    omega.
Qed.

(*
Lemma temp1:
forall g: cfg _ _,
forall ntl: nlist,
forall n: nat,
(forall left : non_terminal,
 forall right : sf,
 g_emp_rules g left right ->
 length right <= n /\
 In left ntl /\ (forall s : non_terminal, In (inl s) right -> In s ntl)) ->
(forall left : non_terminal,
 forall right : sf,
 g_emp_rules g left right ->
 length right <= n).
Proof.
intros g ntl n H1 left right H2.
specialize (H1 left right H2).
destruct H1 as [H1 [_ _]].
exact H1.
Qed.

Lemma temp3:
forall g: cfg _ _,
forall n: nat,
(forall left : non_terminal,
 forall right : sf,
 g_emp_rules g left right ->
 length right <= n) ->
(forall left : non_terminal',
 forall right : sf',
 g_emp'_rules g left right ->
 length right = 0 \/
 (length right >= 1 /\ length right <= n \/
  length right = 1)).
Proof.
intros g n H1 left right H2.
inversion H2.
- subst.
  specialize (H1 left0 right0 H).
  right.
  left.
  split.
  + apply temp2 with (g:= g) in H.
    apply length_map_ge.
    exact H.
  + apply length_map_le.
    exact H1.
- left.
  simpl.
  reflexivity.
- right.
  right.
  simpl.
  reflexivity.
Qed.

Lemma temp4:
forall A: Type,
forall l: list A,
forall n: nat,
(length l = 0 \/
 length l >= 1 /\ length l <= n \/ length l = 1) -> length l <= n.
Proof.
intros A l n H.
destruct H as [H | H].
- omega.
- destruct H as [H | H].
  + omega.
  + admit.
Qed.

Lemma temp5:
forall g: cfg _ _,
forall n: nat,
(forall left : non_terminal,
 forall right : sf,
 g_emp_rules g left right ->
 length right <= n) ->
(forall left : non_terminal',
 forall right : sf',
 g_emp'_rules g left right ->
 length right <= n).
Proof.
intros g n H. 
assert (H1: 
(forall left : non_terminal,
 forall right : sf,
 g_emp_rules g left right ->
 length right <= n) ->
(forall left : non_terminal',
 forall right : sf',
 g_emp'_rules g left right ->
 length right = 0 \/
 (length right >= 1 /\ length right <= n \/
  length right = 1))).
  {
  apply temp3.
  }
specialize (H1 H).
intros left right H2.
specialize (H1 left right H2).
apply temp4 in H1. 
exact H1.
Qed.
*)

Lemma g_emp'_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist',
In New_ss ntl /\
forall left: non_terminal',
forall right: sf',
g_emp'_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal', In (inl s) right -> In s ntl).
Proof.
intros g.
destruct (rules_finite (g_emp g)) as [n [ntl H1]].
destruct H1 as [H H1].
exists n, (New_ss :: map non_terminal_lift ntl).
split.
- simpl; left; reflexivity.
- intros left right H2.
  inversion H2.
  + specialize (H1 left0 right0 H0).
    subst.
    destruct H1 as [H3 [H4 H5]].
    split. 
    * apply length_map_le. 
      exact H3.
    * {
      split.
      - apply in_cons.
        apply in_lift_map. 
        exact H4.
      - intros s' H6.
        apply in_cons.
        apply in_map_exists in H6. 
        destruct H6 as [s [H7 H8]].
        rewrite H7.
        specialize (H5 s H8).
        apply in_lift_map.
        exact H5.
      } 
  + subst.
    split.
    * simpl. 
      omega.
    * {
      split. 
      - simpl. 
        left. 
        reflexivity.
      - intros s H3.
        simpl in H3.
        contradiction.
      }
  + split.
    * subst.
      simpl.
      admit.
    * {
      split.
      - simpl. 
        left.
        reflexivity.
      - intros s H4.
        simpl in H4.
        destruct H4 as [H4 | H4].
        + inversion H4.
          apply in_cons.
          apply in_lift_map.
          simpl in H.
          exact H.
        + contradiction.
        }
Qed.

Definition g_emp' (g: cfg non_terminal terminal): cfg non_terminal' terminal := {|
start_symbol:= New_ss;
rules:= g_emp'_rules g;
rules_finite:= g_emp'_finite g
|}.

Inductive g_map_rules (g: cfg non_terminal terminal): non_terminal' -> sf' -> Prop :=
| Map_all:
       forall left: non_terminal,
       forall right: sf,
       rules g left right ->
       g_map_rules g (Lift_nt left) (map symbol_lift right).

Lemma g_map_finite:
forall g: cfg _ _,
exists n: nat,
exists ntl: nlist',
In (non_terminal_lift (start_symbol g)) ntl /\
forall left: non_terminal',
forall right: sf',
g_map_rules g left right ->
(length right <= n) /\
(In left ntl) /\
(forall s: non_terminal', In (inl s) right -> In s ntl).
Proof.
intros g.
destruct (rules_finite g) as [n [ntl H1]].
exists n, (map non_terminal_lift ntl).
split.
- destruct H1 as [H1 _]. 
  apply in_lift_map. 
  exact H1. 
- destruct H1 as [H' H1]. 
  intros left right H2.
  inversion H2.
  subst.
  specialize (H1 left0 right0 H).
  destruct H1 as [H4 [H5 H6]].
  split.
  + apply length_map_le. 
    exact H4.
  + split.
    * apply in_lift_map.
      exact H5.
    * intros s H7.
      apply in_map_exists in H7.
      destruct H7 as [s0 [H8 H9]].
      rewrite H8.
      apply in_lift_map.
      specialize (H6 s0 H9).
      exact H6.
Qed.

Definition g_map (g: cfg non_terminal terminal): cfg non_terminal' terminal := {|
start_symbol:= non_terminal_lift (start_symbol g);
rules:= g_map_rules g;
rules_finite:= g_map_finite g
|}.

Definition New_ss_not_in_sf (s: sf'): Prop:=
~ In (inl New_ss) s.

Definition New_ss_not_in_sflist (l': list sf'): Prop:=
forall s': sf',
In s' l' ->
New_ss_not_in_sf s'.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - LEMMAS TO INCLUDE EMPTY STRING         *)
(* --------------------------------------------------------------------- *)

Lemma New_ss_not_in_right_g_emp'_v1:
forall g: cfg _ _,
forall left: non_terminal',
forall s1 s2: sf',
~ rules (g_emp' g) left (s1 ++ [inl (start_symbol (g_emp' g))] ++ s2).
Proof.
intros g left s1 s2 H.
inversion H.
clear H.
- inversion H2.
  clear H2.
  + subst.
    symmetry in H0.
    apply map_expand in H0.
    destruct H0 as [s1' [s2' [_ [_ H0]]]].
    symmetry in H0.
    change (inl New_ss :: s2) with ([inl New_ss] ++ s2) in H0.
    apply map_expand in H0.
    destruct H0 as [s1'0 [s2'0 [_ [H0 _]]]].
    destruct s1'0.
    * inversion H0.
    * inversion H0.
      {
      destruct s.
      - simpl in H2. 
        inversion H2.
      - inversion H2.
      }
  + subst.
    symmetry in H0.
    apply map_expand in H0.
    destruct H0 as [s1' [s2' [_ [_ H0]]]].
    destruct s2'.
    * simpl in H0.
      inversion H0.
    * symmetry in H0.
      change (inl New_ss :: s2) with ([inl New_ss] ++ s2) in H0.
      apply map_expand in H0.
      destruct H0 as [s1'0 [s2'0 [_ [H0 _]]]].
      {
      destruct s1'0.
      - simpl in H0.
        inversion H0.
      - simpl in H0.
        inversion H0.
        destruct s5.
        + simpl in H3.
          inversion H3.
        + simpl in H3.
          inversion H3.
      }
- destruct s1.
  + inversion H0.
  + inversion H0.
- subst.
  simpl in H.
  inversion H.
  + destruct s1. 
    * inversion H0.
    * inversion H0.
  + destruct s1.
    * inversion H0.
    * inversion H0.
      {
      destruct s1.
      - inversion H4.
      - inversion H4.
      }
Qed.

Lemma New_ss_not_in_right_g_emp'_v2:
forall g: cfg _ _,
forall left: non_terminal',
forall right: sf',
rules (g_emp' g) left right ->
New_ss_not_in_sf right.
Proof.
intros g left right H1 H2.
apply in_split in H2.
destruct H2 as [l1 [l2 H3]].
rewrite H3 in H1.
change ((l1 ++ inl New_ss :: l2)) with ((l1 ++ [inl New_ss] ++ l2)) in H1.
apply New_ss_not_in_right_g_emp'_v1 in H1.
contradiction.
Qed.

Lemma hd_lift_equiv_lift_hd:
forall l: list sf,
hd [] (sf_list_lift l) = sf_lift (hd [] l).
Proof.
destruct l.
- simpl. 
  reflexivity.
- simpl. 
  reflexivity.
Qed.

Lemma last_lift_equiv_lift_last:
forall l: list sf,
last (sf_list_lift l) [] = sf_lift (last l []).
Proof.
induction l.
- simpl. 
  reflexivity.
- simpl sf_list_lift.
  assert (H: l = [] \/ l <> []).
    {
    apply nil_not_nil.
    }
  destruct H as [H | H].
  + subst.
    simpl. 
    reflexivity.
  + assert (H2: sf_list_lift l <> []).
      {
      destruct l.
      - destruct H.
        reflexivity.
      - simpl. 
        apply not_eq_sym.
        apply nil_cons.
      }
    repeat rewrite last_cons.
    * exact IHl.
    * exact H.
    * exact H2.
Qed.

Lemma map_lift_equiv_lift_map:
forall s: sentence,
sf_lift (map term_lift s) =
map term_lift' s.
Proof.
intros s.
induction s.
- simpl. 
  reflexivity.
- simpl map.
  simpl sf_lift. 
  change (term_lift' a) with (@inr non_terminal' terminal a).
  apply app_eq.
  exact IHs.
Qed.

Lemma sf_lift_app_distrib:
forall s1 s2: sf,
sf_lift (s1 ++ s2) = sf_lift s1 ++ sf_lift s2.
Proof.
induction s1.
- intros s2.
  simpl. 
  reflexivity.
- intros s2.
  simpl. 
  apply app_eq.
  apply IHs1.
Qed.

Lemma sf_lift_eq_nil:
forall l: sf,
sf_lift l = [] -> l = [].
Proof.
destruct l.
- simpl. 
  auto.
- simpl. 
  intros H.
  change (symbol_lift s :: sf_lift l) with ([symbol_lift s] ++ sf_lift l) in H.
  apply app_eq_nil in H.
  destruct H as [H _].
  inversion H.
Qed.

Lemma sf_list_lift_eq_nil:
forall l: list sf,
sf_list_lift l = [] -> l = [].
Proof.
destruct l.
- simpl. 
  auto.
- simpl. 
  intros H.
  change (sf_lift l :: sf_list_lift l0) with ([sf_lift l] ++ sf_list_lift l0) in H.
  apply app_eq_nil in H.
  destruct H as [H _].
  inversion H.
Qed.

Lemma symbol_lift_eq:
forall a b: non_terminal + terminal,
symbol_lift a = symbol_lift b ->
a = b.
Proof.
intros a b H.
destruct a, b.
- simpl in H.
  inversion H.
  reflexivity. 
- simpl in H. 
  inversion H.
- simpl in H. 
  inversion H.
- simpl in H.
  inversion H.
  reflexivity. 
Qed.

Lemma sf_lift_eq:
forall l1 l2: sf,
sf_lift l1 = sf_lift l2 ->
l1 = l2.
Proof.
induction l1.
- intros l2 H. 
  simpl in H. 
  symmetry in H. 
  apply sf_lift_eq_nil in H. 
  symmetry. 
  assumption. 
- intros l2 H.
  simpl in H.
  destruct l2.
  + inversion H.
  + simpl in H.
    inversion H.
    specialize (IHl1 l2 H2).
    rewrite IHl1.
    apply symbol_lift_eq with (b:= s) in H1.
    rewrite H1.
    reflexivity.
Qed.

Lemma sf_list_lift_eq:
forall l1 l2: list sf,
sf_list_lift l1 = sf_list_lift l2 ->
l1 = l2.
Proof.
induction l1, l2.
- auto. 
- simpl.
  intros H.
  symmetry in H.
  change (sf_lift l :: sf_list_lift l2) with ([sf_lift l] ++ sf_list_lift l2) in H.
  apply app_eq_nil in H. 
  destruct H as [H1 _]. 
  inversion H1.
- simpl.
  intros H.
  change (sf_lift a :: sf_list_lift l1) with ([sf_lift a] ++ sf_list_lift l1) in H.
  apply app_eq_nil in H. 
  destruct H as [H1 _]. 
  inversion H1.
- intros H.
  simpl in H.
  inversion H. 
  specialize (IHl1 l2 H2).
  rewrite IHl1.
  apply sf_lift_eq in H1.
  rewrite H1.
  reflexivity.
Qed.

Lemma derives_g_emp'_or:
forall g: cfg _ _,
forall s: sentence,
derives (g_emp' g) [inl (start_symbol (g_emp' g))] (map term_lift' s) ->
s = [] \/
derives (g_emp' g) [inl (Lift_nt (start_symbol (g_emp g)))] (map term_lift' s).
Proof.
intros g s H.
destruct s.
- left.
  reflexivity.
- right.
  apply exists_rule in H.
  destruct H.
  + inversion H.
  + destruct H as [right [H1 H2]].
    inversion H1.
    * subst.
      apply derives_empty in H2.
      inversion H2.
    * subst.
      exact H2.
Qed.

Lemma symbol_lift_exists:
forall a': non_terminal' + terminal,
a' <> (inl New_ss) ->
exists a: non_terminal + terminal,
a' = symbol_lift a.
Proof.
intros a'.
destruct a'.
- destruct n.
  + exists (inl n).  
    simpl.
    reflexivity.
  + intros H. 
    destruct H. 
    reflexivity. 
- exists (inr t).
  simpl. 
  reflexivity. 
Qed.

Lemma sf_lift_exists:
forall s': sf',
~ In (inl New_ss) s' ->
exists s: sf,
s' = sf_lift s.
Proof.
intros s' H.
induction s'.
- exists [].
  simpl.
  reflexivity.
- assert (H1: ~ In (inl New_ss) s'). 
    {
    intros H1. 
    apply H. 
    apply in_cons. 
    exact H1. 
    }
  specialize (IHs' H1). 
  destruct IHs' as [s H2].
  assert (H3: a <> (inl New_ss) -> exists b: non_terminal + terminal, a = symbol_lift b).
    {
    intros H3. 
    apply symbol_lift_exists.
    exact H3.
    }
  simpl in H.
  apply not_or in H.
  destruct H as [H _].
  specialize (H3 H).
  destruct H3 as [b H3].
  exists (b :: s).
  simpl. 
  rewrite <- H3.
  apply app_eq.
  exact H2.
Qed.

Lemma sf_list_lift_exists:
forall l': list sf',
New_ss_not_in_sflist l' ->
exists l: list sf,
l' = sf_list_lift l.
Proof.
intros l' H.
induction l'.
- exists []. 
  simpl.
  reflexivity. 
- assert (H0: (forall s' : sf', In s' (a :: l') -> ~ In (inl New_ss) s') ->
              (forall s' : sf', In s' l' -> ~ In (inl New_ss) s')).
    {
    intros H1 s' H2.
    specialize (H1 s').
    apply H1.
    simpl. 
    right. 
    exact H2.
    }
  specialize (H0 H).
  specialize (IHl' H0).
  destruct IHl' as [l H1].
  assert (H2: exists b: sf, a = sf_lift b).
    {
    apply sf_lift_exists.
    specialize (H a).
    apply H.
    simpl.
    left.
    reflexivity.
    }
  destruct H2 as [b H2].
  exists (b :: l).
  simpl. 
  rewrite <- H2.
  apply app_eq.
  exact H1.
Qed.

Lemma hd_lift_hd:
forall n: non_terminal,
forall l': list sf',
forall l: list sf,
hd [] l' = [inl (Lift_nt n)] ->
l' = sf_list_lift l ->
hd [] l = [inl n].
Proof.
intros n l' l H1 H2.
rewrite H2 in H1.
rewrite hd_lift_equiv_lift_hd in H1.
change [inl (Lift_nt n)] with (sf_lift ([inl n])) in H1.
apply sf_lift_eq in H1.
exact H1.
Qed.  

Lemma last_lift_last:
forall l': list sf',
forall l: list sf,
forall s: sentence,
last l' [] = map term_lift' s ->
l' = sf_list_lift l ->
last l [] = map term_lift s.
Proof.
intros l' l s H1 H2.
rewrite H2 in H1.
clear H2 l'.
rewrite last_lift_equiv_lift_last in H1.
rewrite <- map_lift_equiv_lift_map in H1.
apply sf_lift_eq in H1.
exact H1.
Qed.

Lemma New_ss_not_in_sf_cat:
forall l1 l2: sf',
New_ss_not_in_sf l1 ->
New_ss_not_in_sf l2 ->
New_ss_not_in_sf (l1 ++ l2).
Proof.
intros l1.
destruct l1.
- intros l2 H1 H2.
  simpl. 
  exact H2.
- intros l2 H1 H2.
  unfold New_ss_not_in_sf.
  intros H3. 
  apply in_app_or in H3.
  destruct H3 as [H3 | H3].
  + specialize (H1 H3).
    contradiction.
  + specialize (H2 H3).
    contradiction.
Qed.

Lemma New_ss_not_in_sf_split:
forall l1 l2: sf',
New_ss_not_in_sf (l1 ++ l2) ->
New_ss_not_in_sf l1 /\
New_ss_not_in_sf l2.
Proof.
intros l1.
destruct l1.
- intros l2 H.
  split.
  + unfold New_ss_not_in_sf.
    simpl.
    auto.
  + exact H.
- intros l2 H1.
  split.
  + intros H2. 
    unfold New_ss_not_in_sf in H1.
    simpl in H1.
    apply H1.
    change (s :: l1) with ([s] ++ l1) in H2.
    apply in_app_or in H2.
    destruct H2 as [H2 | H2].
    * left.
      simpl in H2. 
      {
      destruct H2 as [H2 | H2].
      - exact H2.
      - contradiction.
      }
    * right.
      apply in_or_app.
      left.
      exact H2.
  + unfold New_ss_not_in_sf in H1. 
    unfold New_ss_not_in_sf.
    intros H2.
    apply H1.
    apply in_or_app.
    right.
    exact H2.
Qed.

Lemma New_ss_not_in_sflist_cat:
forall l1 l2: list sf',
New_ss_not_in_sflist l1 ->
New_ss_not_in_sflist l2 ->
New_ss_not_in_sflist (l1 ++ l2).
Proof.
intros l1.
destruct l1.
- intros l2 H1 H2.
  simpl. 
  exact H2.
- intros l2 H1 H2.
  unfold New_ss_not_in_sflist.
  intros s' H3. 
  apply in_app_or in H3.
  destruct H3 as [H3 | H3].
  + specialize (H1 s' H3).
    exact H1.
  + specialize (H2 s' H3).
    exact H2.
Qed.

Lemma New_ss_not_in_sflist_split:
forall l1 l2: list sf',
New_ss_not_in_sflist (l1 ++ l2) ->
New_ss_not_in_sflist l1 /\
New_ss_not_in_sflist l2.
Proof.
intros l1.
destruct l1.
- intros l2 H.
  split.
  + unfold New_ss_not_in_sflist.
    intros s' H1.
    simpl in H1.
    contradiction.
  + exact H.
- intros l2 H1.
  split.
  + intros s' H2. 
    unfold New_ss_not_in_sflist in H1.
    simpl in H1.
    apply H1.
    change (l :: l1) with ([l] ++ l1) in H2.
    apply in_app_or in H2.
    destruct H2 as [H2 | H2].
    * left.
      simpl in H2. 
      {
      destruct H2 as [H2 | H2].
      - exact H2.
      - contradiction.
      }
    * right.
      apply in_or_app.
      left.
      exact H2.
  + unfold New_ss_not_in_sflist in H1. 
    unfold New_ss_not_in_sflist.
    intros s' H2.
    apply H1.
    apply in_or_app.
    right.
    exact H2.
Qed.

Lemma New_ss_not_in_map:
forall s: sf,
New_ss_not_in_sf (map symbol_lift s).
Proof.
intros s.
induction s.
- simpl.
  unfold New_ss_not_in_sf.
  simpl.
  auto.
- simpl.
  unfold New_ss_not_in_sf.
  intros H.
  change (symbol_lift a :: map symbol_lift s) with ([symbol_lift a] ++ map symbol_lift s) in H.
  apply in_app_or in H.
  destruct H as [H | H].
  + simpl in H.
    destruct H as [H | H].
    * {
      destruct a.
      - simpl in H.
        discriminate H.
      - simpl in H.
        inversion H.
      }
    * contradiction.
  + apply IHs.
    exact H. 
Qed.

Lemma New_ss_not_in_sflist_g_emp':
forall g: cfg _ _,
forall l': list sf',
sflist (g_emp' g) l' ->
hd [] l' = [inl (Lift_nt (start_symbol (g_emp g)))] ->
New_ss_not_in_sflist l'.
Proof.
intros g l' H.
induction H.
- intros H.
  simpl in H.
  inversion H.
- intros H.
  simpl in H.
  rewrite H.
  unfold New_ss_not_in_sflist.
  intros s' H1.
  simpl in H1.
  destruct H1 as [H1 | H1].
  + rewrite <- H1.
    simpl. 
    intros H2.
    destruct H2 as [H2 | H2].
    * inversion H2.
    * contradiction.
  + contradiction.
- intros H2.
  assert (H3: l = [] \/ l <> []).
    {
    apply nil_not_nil.
    }
  destruct H3 as [H3 | H3].
  + subst.
    simpl in H0.
    destruct s2.
    * inversion H0.
    * inversion H0.
  + apply not_nil_ge_1 in H3.
    apply hd_hd with (d:= []) (l':= [s2 ++ right ++ s3]) in H3.
    rewrite <- H3 in H2.
    specialize (IHsflist H2).
    clear H2 H3.
    assert (H2: New_ss_not_in_sf s2 /\ New_ss_not_in_sf s3 /\ left <> New_ss).
      {
      rewrite app_removelast_last with (d:= []) (l:= l) in IHsflist.
      - apply New_ss_not_in_sflist_split in IHsflist.
        destruct IHsflist as [_ IHsflist].
        specialize (IHsflist (last l []) (in_eq (last l []) [])).
        rewrite H0 in IHsflist.
        apply New_ss_not_in_sf_split in IHsflist.
        destruct IHsflist as [H3 H4].
        change (inl left :: s3) with ([inl left] ++ s3) in H4.
        apply New_ss_not_in_sf_split in H4.
        destruct H4 as [H4 H5].
        split. 
        + exact H3.
        + split. 
          * exact H5.
          * unfold New_ss_not_in_sf in H4.
            apply not_in_not_eq in H4. 
            apply inl_neq with (Y:= terminal).
            apply not_eq_sym. 
            exact H4.
      - apply last_not_nil with (d:= []).
        rewrite H0.
        apply not_eq_sym.
        apply app_cons_not_nil.
      }
    destruct H2 as [H3 [H4 H5]].
    apply New_ss_not_in_right_g_emp'_v2 in H1.
    assert (H7: New_ss_not_in_sflist [s2 ++ right ++ s3]).
      {
      unfold New_ss_not_in_sflist.
      intros s' H8.
      simpl in H8.
      destruct H8 as [H8 | H8].
      - rewrite <- H8.
        apply New_ss_not_in_sf_cat.
        + exact H3.
        + apply New_ss_not_in_sf_cat.
          * exact H1.
          * exact H4.
      - contradiction.
      }
      apply New_ss_not_in_sflist_cat.
      * exact IHsflist.
      * exact H7.
Qed.

Lemma sf_lift_cat:
forall l: sf,
forall l1 l2: sf',
sf_lift l = l1 ++ l2 ->
exists l1' l2',
l = l1' ++ l2' /\
l1 = sf_lift l1' /\
l2 = sf_lift l2'.
Proof.
induction l, l1.
- intros l2 H.
  exists [], [].
  auto. 
- intros l2 H.
  simpl in H.
  inversion H.
- intros l2 H. 
  simpl in H.
  destruct l2. 
  + inversion H.
  + inversion H.
    specialize (IHl [] l2 H2).
    destruct IHl as [l1' [l2' [H3 [H4 H5]]]].
    exists [], (a :: l).
    split.
    * reflexivity.
    * {
      split. 
      - reflexivity.
      - simpl.
        reflexivity.
      }
- intros l2 H.
  simpl in H.
  inversion H.
  specialize (IHl l1 l2 H2).
  destruct IHl as [l1' [l2' [H3 [H4 H5]]]].
  exists (a :: l1'), l2'.
  split.
  + rewrite H3.
    reflexivity.
  + split.
    * simpl.
      rewrite H4.
      reflexivity.
    * exact H5.
Qed.

Lemma sf_lift_eq_nt:
forall l: sf,
forall a: non_terminal',
sf_lift l = [inl a] ->
exists b: non_terminal,
l = [inl b].
Proof.
intros l a H.
destruct l.
- simpl in H.
  inversion H.
- simpl in H.
  inversion H.
  apply sf_lift_eq_nil in H2.
  rewrite H2.
  destruct s. 
  + exists n.
    reflexivity.
  + inversion H1.
Qed.

Lemma sflist_g_emp_g_emp':
forall g: cfg _ _,
forall l: _,
sflist (g_emp g) l ->
sflist (g_emp' g) (sf_list_lift l).
Proof.
intros g l. 
induction l.
- intros H. 
  simpl.
  apply sflist_empty.
- intros H.
  assert (H':= H).
  apply sflist_tail in H.
  simpl in H.
  specialize (IHl H).
  simpl.
  rewrite sflist_equiv_sflist6.
  change (sf_lift a :: sf_list_lift l) with ([sf_lift a] ++ sf_list_lift l).
  destruct l.
  + simpl. 
    apply sflist6_start.
  + apply sflist6_step with (s2:= sf_lift l).
    * rewrite sflist_equiv_sflist6 in IHl. 
      exact IHl. 
    * simpl. 
      reflexivity.
    * rewrite sflist_equiv_sflist6 in H'.
      inversion H'.
      simpl in H3.
      rewrite <- H3 in H4.
      clear H0 H1 H2 H3.
      unfold derives_direct in H4.
      destruct H4 as [s' [s'' [left [right [H6 [H7 H8]]]]]].
      unfold derives_direct.
      exists (sf_lift s').
      exists (sf_lift s'').
      exists (Lift_nt left).
      exists (sf_lift right).
      {
      split.
      - rewrite H6.
        repeat rewrite sf_lift_app_distrib.
        simpl.
        reflexivity.
      - split. 
        + rewrite H7.
          repeat rewrite sf_lift_app_distrib.
          reflexivity.
        + apply Lift_all.
          exact H8.
      }
Qed.

Lemma sflist_g_emp'_g_emp:
forall g: cfg _ _,
forall l': _,
forall l: _,
l' = sf_list_lift l ->
hd [] l' = [inl (Lift_nt (start_symbol (g_emp g)))] ->
sflist (g_emp' g) l' ->
sflist (g_emp g) l.
Proof.
intros g l' l H1 H2 H3.
apply New_ss_not_in_sflist_g_emp' in H2.
- generalize dependent H3. 
  generalize dependent H2.
  generalize dependent H1. 
  generalize dependent l. 
  induction l'.
  + intros l H1. 
    symmetry in H1.
    apply sf_list_lift_eq_nil in H1.
    subst.
    constructor.
  + destruct l. 
    * constructor.
    * intros H1 H2 H3.    
      simpl in H1.
      inversion H1.
      change (a :: l') with ([a] ++ l') in H2.
      apply New_ss_not_in_sflist_split in H2.
      destruct H2 as [_ H2].
      assert (H3':= H3).       
      change (a :: l') with ([a] ++ l') in H3.
      apply sflist_app in H3.
      destruct H3 as [_ H3].
      specialize (IHl' l0 H4 H2 H3).
      rewrite sflist_equiv_sflist6 in H3'.
      rewrite sflist_equiv_sflist6.
      rewrite H4 in H3'.
      rewrite H0 in H3'.
      {
      destruct l0.
      - constructor.
      - simpl in H3'.
        apply sflist6_step with (s2:= l0).
        + rewrite <- sflist_equiv_sflist6.
          exact IHl'.
        + simpl.
          reflexivity.
        + inversion H3'.
          simpl in H7.
          rewrite <- H7 in H8.
          clear IHl' H H0 H1 H3 H3' H5 H6 H7.
          (* break l *) 
          unfold derives_direct in H8.
          unfold derives_direct.
          destruct H8 as [s' [s'' [left [right [H10 [H11 H12]]]]]].
          apply sf_lift_cat in H10.
          destruct H10 as [l1' [l2' [H101 [H102 H103]]]].
          symmetry in H103.
          apply sf_lift_cat in H103.
          destruct H103 as [l1'0 [l2'0 [H103 [H104 H105]]]].
          rewrite H103 in H101.
          clear H103.
          (* break l0 *)
          apply sf_lift_cat in H11.
          destruct H11 as [l1'1 [l2'1 [H111 [H112 H113]]]].
          symmetry in H113.
          apply sf_lift_cat in H113.
          destruct H113 as [l1'2 [l2'2 [H113 [H114 H115]]]].
          rewrite H113 in H111.
          clear H113.
          (* fix l0 *)
          rewrite H112 in H102.
          apply sf_lift_eq in H102.
          rewrite H102 in H111.
          rewrite H115 in H105.
          apply sf_lift_eq in H105.
          rewrite H105 in H111.
          (* find l1'0 *)                  
          assert (H104':= H104).
          symmetry in H104.
          apply sf_lift_eq_nt in H104.
          destruct H104 as [b H104].
          rewrite H104 in H101.
          (* find l1'2 *)
          symmetry in H114.
          assert (H30: New_ss_not_in_sf (sf_lift l1'2)).
            {
            rewrite H4 in H2.
            simpl in H2.
            change (sf_lift l0 :: sf_list_lift l1) with ([sf_lift l0] ++ sf_list_lift l1) in H2.
            apply New_ss_not_in_sflist_split in H2.
            destruct H2 as [H2 _].
            rewrite H111 in H2.
            unfold New_ss_not_in_sflist in H2.
            specialize (H2 (sf_lift (l1' ++ l1'2 ++ l2'0)) (in_eq (sf_lift (l1' ++ l1'2 ++ l2'0)) [])).
            rewrite sf_lift_app_distrib in H2.
            apply New_ss_not_in_sf_split in H2.
            destruct H2 as [_ H2].
            rewrite sf_lift_app_distrib in H2.
            apply New_ss_not_in_sf_split in H2.
            destruct H2 as [H2 _].
            exact H2.
            }
          apply sf_lift_exists in H30.
          destruct H30 as [s H30].
          apply sf_lift_eq in H30.
          rewrite H30 in H111.
          (* prove goal *)
          exists l1', l2'0, b, s.
          split.
          * exact H101.
          * {
            split.
            - exact H111.
            - inversion H12.
              + (* substitute right0 for s *)
                rewrite H30 in H114.
                rewrite <- H114 in H1.
                apply sf_lift_eq in H1.
                rewrite H1 in H.
                (* substitute left0 for b *)
                rewrite <- H0 in H104'.
                rewrite H104 in H104'.
                simpl in H104'.
                inversion H104'.
                rewrite H5 in H.
                exact H.
              + rewrite <- H0 in H104'.
                rewrite H104 in H104'.
                simpl in H104'.
                inversion H104'.
              + rewrite <- H in H104'.
                rewrite H104 in H104'.
                simpl in H104'.
                inversion H104'.                
            }
      }
- exact H3.
Qed.

Lemma g_emp_equiv_g_emp'_aux:
forall g: cfg _ _,
forall s: sentence,
derives (g_emp g) [inl (start_symbol (g_emp g))] (map term_lift s) <->
derives (g_emp' g) [inl (Lift_nt (start_symbol (g_emp g)))] (map term_lift' s).
Proof.
intros g s.
split.
- repeat rewrite derives_sflist. 
  intros H.
  destruct H as [l [H1 [H2 H3]]].
  exists (sf_list_lift l).
  split.
  + apply sflist_g_emp_g_emp'.
    exact H1.
  + split. 
    * rewrite hd_lift_equiv_lift_hd. 
      rewrite H2. 
      simpl. 
      reflexivity.
    * rewrite last_lift_equiv_lift_last.
      rewrite H3. 
      apply map_lift_equiv_lift_map.
- repeat rewrite derives_sflist.
  intros H.
  destruct H as [l' [H1 [H2 H3]]].
  assert (H4: exists l: list sf, l' = sf_list_lift l).
    {
    apply sf_list_lift_exists.
    apply New_ss_not_in_sflist_g_emp' in H1.
    - exact H1.
    - exact H2. 
    }
  destruct H4 as [l H4].
  exists l.
  split.
  + apply sflist_g_emp'_g_emp with (l':= l').
    * exact H4.
    * exact H2.
    * exact H1.
  + split.
    * {
      apply hd_lift_hd with (l':= l').
      - exact H2.
      - exact H4.
      }
    * {
      apply last_lift_last with (l:= l) in H3.
      - exact H3.
      - exact H4.
      }
Qed.

Lemma g_emp'_not_derives_empty:
forall g: cfg _ _,
~ derives (g_emp' g) [inl (Lift_nt (start_symbol g))] [].
Proof.
intros g H.
change (start_symbol g) with (start_symbol (g_emp g)) in H.
rewrite <- (g_emp_equiv_g_emp'_aux g []) in H.
simpl in H.
apply g_emp_not_derives_empty in H.
exact H.
Qed.

Lemma g_emp_equiv_g_emp':
forall g: cfg _ _,
forall s: sentence,
(s <> [] -> 
 derives (g_emp' g) [inl (start_symbol (g_emp' g))] (map term_lift' s) ->
 derives (g_emp  g) [inl (start_symbol (g_emp  g))] (map term_lift s)) 
/\
(derives (g_emp  g) [inl (start_symbol (g_emp  g))] (map term_lift s) ->
 derives (g_emp' g) [inl (start_symbol (g_emp' g))] (map term_lift' s)).
Proof.
intros g s.
split.
- intros H1 H2. 
  apply derives_g_emp'_or in H2.
  destruct H2 as [H2 | H2].
  + subst.
    destruct H1.
    reflexivity.
  + rewrite g_emp_equiv_g_emp'_aux.
    exact H2.
- intros H.
  rewrite g_emp_equiv_g_emp'_aux in H.
  simpl.
  apply derives_trans with (s2:=[inl (Lift_nt (start_symbol (g_emp g)))]). 
  + apply derives_start.
    apply Lift_start.
  + exact H.
Qed.

Lemma sflist_g_g_map:
forall g: cfg _ _,
forall l: list sf,
sflist g l ->
sflist (g_map g) (sf_list_lift l).
Proof.
intros g l.
induction l.
- intros H.
  simpl. 
  constructor.
- intros H.
  assert (H':= H).
  apply sflist_tail in H.
  simpl in H.
  specialize (IHl H).
  simpl.
  rewrite sflist_equiv_sflist6.
  change (sf_lift a :: sf_list_lift l) with ([sf_lift a] ++ sf_list_lift l).
  destruct l.
  + simpl.
    apply sflist6_start.
  + apply sflist6_step with (s2:= sf_lift l).
    * rewrite sflist_equiv_sflist6 in IHl.
      exact IHl.
    * simpl.
      reflexivity.
    * rewrite sflist_equiv_sflist6 in H'.
      inversion H'.
      simpl in H3.
      rewrite <- H3 in H4.
      clear H0 H1 H2 H3.
      unfold derives_direct in H4.
      destruct H4 as [s' [s'' [left [right [H6 [H7 H8]]]]]].
      unfold derives_direct.
      exists (sf_lift s').
      exists (sf_lift s'').
      exists (Lift_nt left).
      exists (sf_lift right).
      {
      split.
      - rewrite H6.
        repeat rewrite sf_lift_app_distrib.
        simpl.
        reflexivity.
      - split.
        + rewrite H7.
          repeat rewrite sf_lift_app_distrib.
          reflexivity.
        + apply Map_all.
          exact H8.
      }
Qed.

Lemma sflist_g_map_g:
forall g: cfg _ _,
forall l: _,
sflist (g_map g) (sf_list_lift l) ->
sflist g l.
Proof.
intros g l.
induction l.
- intros H.
  constructor.
- intros H.
  assert (H':= H).
  apply sflist_tail in H.
  simpl in H.
  specialize (IHl H). 
  rewrite sflist_equiv_sflist6.
  change (a :: l) with ([a] ++ l).
  destruct l.
  + simpl.
    apply sflist6_start.
  + apply sflist6_step with (s2:= l).
    * rewrite sflist_equiv_sflist6 in IHl.
      exact IHl.
    * simpl.
      reflexivity.
    * rewrite sflist_equiv_sflist6 in H'.
      inversion H'.
      simpl in H3.
      rewrite <- H3 in H4.
      clear H0 H1 H2 H3.
      unfold derives_direct in H4.
      destruct H4 as [s' [s'' [left [right [H6 [H7 H8]]]]]].
      unfold derives_direct.
      apply sf_lift_cat in H6.
      destruct H6 as [l1' [l2' [H6 [H61 H62]]]].
      symmetry in H62.
      apply sf_lift_cat in H62.
      destruct H62 as [l1'0 [l2'0 [H6' [H62 H63]]]].
      rewrite H6' in H6.
      clear H6'.
      symmetry in H62.
      assert (H62':= H62).
      apply sf_lift_eq_nt in H62.
      destruct H62 as [b H62].
      apply sf_lift_cat in H7.
      destruct H7 as [l1'1 [l2'1 [H7 [H71 H72]]]].
      symmetry in H72.
      apply sf_lift_cat in H72.
      destruct H72 as [l1'2 [l2'2 [H7' [H72 H73]]]].
      rewrite H7' in H7.
      clear H7'.
      symmetry in H72.
      assert (H10: New_ss_not_in_sf (sf_lift l1'2)).
        {
        apply New_ss_not_in_map.
        }
      apply sf_lift_exists in H10.
      destruct H10 as [s H10].
      apply sf_lift_eq in H10.
      exists l1', l2'0, b, s.
      {
      split.
      - rewrite H62 in H6.
        exact H6.
      - split.
        + rewrite H10 in H7.
          rewrite H71 in H61.
          apply sf_lift_eq in H61.
          rewrite H61 in H7.
          rewrite H73 in H63.
          apply sf_lift_eq in H63.
          rewrite H63 in H7.
          exact H7.
        + rewrite <- H72 in H8.
          rewrite H10 in H8.
          rewrite H62 in H62'.
          simpl in H62'.
          inversion H62'.
          rewrite <- H1 in H8.
          inversion H8.
          change (map symbol_lift right0) with (sf_lift right0) in H2.
          apply sf_lift_eq in H2.
          rewrite H2 in H3.
          exact H3.
      }
Qed.

Lemma New_ss_not_in_right_g_map:
forall g: cfg _ _,
forall left: non_terminal',
forall right: sf',
rules (g_map g) left right ->
New_ss_not_in_sf right.
Proof.
intros g left right H1 H2.
inversion H1.
subst.
assert (H': New_ss_not_in_sf (map symbol_lift right0)).
  {
  apply New_ss_not_in_map.
  }
unfold New_ss_not_in_sf in H'.
contradiction.
Qed.

Lemma New_ss_not_in_sflist_g_map:
forall g: cfg _ _,
forall l': list sf',
sflist (g_map g) l' ->
hd [] l' = [inl (Lift_nt (start_symbol g))] ->
New_ss_not_in_sflist l'.
Proof.
intros g l' H.
induction H.
- intros H.
  simpl in H.
  inversion H.
- intros H.
  simpl in H.
  rewrite H.
  unfold New_ss_not_in_sflist.
  intros s' H1.
  simpl in H1.
  destruct H1 as [H1 | H1].
  + rewrite <- H1.
    simpl.
    intros H2.
    destruct H2 as [H2 | H2].
    * inversion H2.
    * contradiction.
  + contradiction.
- intros H2.
  assert (H3: l = [] \/ l <> []).
    {
    apply nil_not_nil.
    }
  destruct H3 as [H3 | H3].
  + subst.
    simpl in H0.
    destruct s2.
    * inversion H0.
    * inversion H0.
  + apply not_nil_ge_1 in H3.
    apply hd_hd with (d:= []) (l':= [s2 ++ right ++ s3]) in H3.
    rewrite <- H3 in H2.
    specialize (IHsflist H2).
    clear H2 H3.
    assert (H2: New_ss_not_in_sf s2 /\ New_ss_not_in_sf s3 /\ left <> New_ss).
      {
      rewrite app_removelast_last with (d:= []) (l:= l) in IHsflist.
      - apply New_ss_not_in_sflist_split in IHsflist.
        destruct IHsflist as [_ IHsflist].
        specialize (IHsflist (last l []) (in_eq (last l []) [])).
        rewrite H0 in IHsflist.
        apply New_ss_not_in_sf_split in IHsflist.
        destruct IHsflist as [H3 H4].
        change (inl left :: s3) with ([inl left] ++ s3) in H4.
        apply New_ss_not_in_sf_split in H4.
        destruct H4 as [H4 H5].
        split.
        + exact H3.
        + split.
          * exact H5.
          * unfold New_ss_not_in_sf in H4.
            apply not_in_not_eq in H4.
            apply inl_neq with (Y:= terminal).
            apply not_eq_sym.
            exact H4.
      - apply last_not_nil with (d:= []).
        rewrite H0.
        apply not_eq_sym.
        apply app_cons_not_nil.
      }
    destruct H2 as [H3 [H4 H5]].
    apply New_ss_not_in_right_g_map in H1.
    assert (H7: New_ss_not_in_sflist [s2 ++ right ++ s3]).
      {
      unfold New_ss_not_in_sflist.
      intros s' H8.
      simpl in H8.
      destruct H8 as [H8 | H8].
      - rewrite <- H8.
        apply New_ss_not_in_sf_cat.
        + exact H3.
        + apply New_ss_not_in_sf_cat.
          * exact H1.
          * exact H4.
      - contradiction.
      }
      apply New_ss_not_in_sflist_cat.
      * exact IHsflist.
      * exact H7.
Qed.

Lemma derives_g_g_map:
forall g: cfg _ _,
forall s: sentence,
derives g [inl (start_symbol g)] (map term_lift s) <->
derives (g_map g) [(symbol_lift (inl (start_symbol g)))] (sf_lift (map term_lift s)).
Proof.
intros g s.
split.
- repeat rewrite derives_sflist.
  intros H.
  destruct H as [l [H1 [H2 H3]]].
  exists (sf_list_lift l).
  split.
  + apply sflist_g_g_map.
    exact H1.
  + split.
    * rewrite hd_lift_equiv_lift_hd.
      rewrite H2.
      simpl.
      reflexivity.
    * rewrite last_lift_equiv_lift_last. 
      rewrite H3.
      reflexivity.
- repeat rewrite derives_sflist.
  intros H.
  destruct H as [l [H1 [H2 H3]]].
  assert (H4: exists l': list sf, l = sf_list_lift l').
    {
    apply sf_list_lift_exists.
    apply New_ss_not_in_sflist_g_map in H1.
    - exact H1.
    - exact H2.
    }
  destruct H4 as [l' H4].
  exists l'.
  split.
  + apply sflist_g_map_g.
    rewrite <- H4. 
    exact H1.
  + split.
    * {
      apply hd_lift_hd with (l':= l).
      - exact H2.
      - exact H4.
      }
    * {
      rewrite H4 in H3. 
      rewrite last_lift_equiv_lift_last in H3.
      apply sf_lift_eq in H3.
      exact H3.
      }
Qed.

Lemma lift_terminal_lift:
forall s: sentence,
sf_lift (map term_lift s) = map term_lift' s.
Proof.
intros s.
induction s.
-simpl. 
 reflexivity.
- simpl.
  apply app_eq.
  exact IHs.
Qed.

Lemma g_equiv_g_map:
forall g: cfg _ _,
forall s: sentence,
derives g [inl (start_symbol g)] (map term_lift s) <->
derives (g_map  g) [inl (start_symbol (g_map  g))] (map term_lift' s).
Proof.
intros g s.
split.
- intros H.
  replace (map term_lift' s) with (sf_lift (map term_lift s)).
  + apply derives_g_g_map.
    exact H.
  + apply lift_terminal_lift.
- intros H.
  replace (map term_lift' s) with (sf_lift (map term_lift s)) in H.
  + apply derives_g_g_map in H.
    exact H.
  + apply lift_terminal_lift.
Qed.

Lemma g_equiv_map:
forall g1 g2: cfg non_terminal terminal,
g_equiv g1 g2 <-> g_equiv (g_map g1) (g_map g2).
Proof.
unfold g_equiv.
unfold produces.
unfold generates.
intros g1 g2.
split. 
- intros H1 s. 
  split.
  + intros H2.
    apply g_equiv_g_map in H2.
    specialize (H1 s).
    destruct H1 as [H1 _].
    specialize (H1 H2).
    apply g_equiv_g_map in H1.
    exact H1.
  + intros H2.
    apply g_equiv_g_map in H2.
    specialize (H1 s).
    destruct H1 as [_ H1].
    specialize (H1 H2).
    apply g_equiv_g_map in H1.
    exact H1.
- intros H1 s. 
  split.
  + intros H2.
    apply g_equiv_g_map in H2.
    specialize (H1 s).
    destruct H1 as [H1 _].
    specialize (H1 H2).
    apply g_equiv_g_map in H1.
    exact H1.
  + intros H2.
    apply g_equiv_g_map in H2.
    specialize (H1 s).
    destruct H1 as [_ H1].
    specialize (H1 H2).
    apply g_equiv_g_map in H1.
    exact H1.
Qed.

Lemma g_emp'_has_one_empty_rule:
forall g: cfg _ _,
generates_empty g -> has_one_empty_rule (g_emp' g).
Proof.
unfold generates_empty.
intros g H.
split.
- apply Lift_empty.
  simpl.
  exact H.
- intros left right H1 H2.
  inversion H2.
  + inversion_clear H0.
    * apply map_not_nil_inv.
      exact H5.
    * apply map_not_nil_inv.
      exact H8.
  + simpl in H1.
    subst. 
    destruct H1.
    reflexivity.
  + apply not_eq_sym.
    apply nil_cons.
Qed.

Lemma g_emp'_has_no_empty_rules:
forall g: cfg _ _,
~ generates_empty g -> has_no_empty_rules (g_emp' g).
Proof.
unfold generates_empty.
intros g H.
intros left right H1.
inversion H1.
- inversion H0.
  + apply map_not_nil_inv.
    exact H4.
  + apply map_not_nil_inv.
    exact H7.
- subst.
  inversion H1.
  simpl in H2.
  contradiction.
- apply not_eq_sym.
  apply nil_cons.
Qed.

Theorem g_emp'_correct: 
forall g: cfg _ _,
g_equiv (g_emp' g) g /\
(generates_empty g -> has_one_empty_rule (g_emp' g)) /\ 
(~ generates_empty g -> has_no_empty_rules (g_emp' g)).
Proof.
intros g.
split.
- unfold g_equiv.
  intros s.
  unfold produces.
  unfold generates.
  split.
  + intros H.
    assert (H0: s = [] \/ s <> []). 
      {
      apply nil_not_nil.
      }
    destruct H0 as [H0 | H0].
    * subst.
      inversion H.
      apply app_eq_nil in H0.
      destruct H0 as [_ H0].
      apply app_eq_nil in H0.
      destruct H0 as [H0 _].
      subst.
      {
      inversion H3.
      - apply map_eq_nil in H0. 
        subst. 
        apply g_emp_has_no_empty_rules in H4.
        destruct H4.
        reflexivity.
      - simpl in H0.
        simpl.
        unfold empty in H0.
        exact H0.
      }
    * {
      apply g_emp_equiv_g_emp' in H.
      - apply derives_g_emp_g.
        exact H.
      - exact H0.
      }
  + intros H.
    assert (H0: s = [] \/ s <> []). 
      {
      apply nil_not_nil.
      }
    destruct H0 as [H0 | H0].
    * subst.
      apply derives_start.
      constructor.
      simpl.
      simpl in H. 
      unfold empty.
      exact H.
    * {
      apply derives_g_g_emp in H.
      - apply g_emp_equiv_g_emp' in H.
        exact H.
      - exact H0.
      }
- split.
  + (* g does generate empty *)
    apply g_emp'_has_one_empty_rule.
  + (* g does not generate empty *)
    apply g_emp'_has_no_empty_rules.
Qed.

(* --------------------------------------------------------------------- *)
(* SIMPLIFICATION - EMPTY RULES - ALTERNATIVE DEFINITION                 *)
(* --------------------------------------------------------------------- *)

Inductive empty'' (g: cfg non_terminal terminal): non_terminal + terminal -> Prop:=
| empty_direct: forall left: non_terminal,   
                rules g left [] -> empty'' g (inl left)
| empty_step: forall left: non_terminal,
              forall right: sf,
              rules g left right ->
              (forall s: non_terminal + terminal, In s right -> empty'' g s) ->
              empty'' g (inl left).

Lemma empty_equiv_empty'':
forall g: cfg _ _,
forall n: non_terminal,
empty g (inl n) -> empty'' g (inl n).
Proof.
admit.
Qed.

Lemma empty''_equiv_empty:
forall g: cfg _ _,
forall n: non_terminal,
empty'' g (inl n) -> empty g (inl n).
Proof.
admit.
Qed.

End EmptyRules_Lemmas.
