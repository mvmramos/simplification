(* ---------------------------------------------------------------------
   This file contains definitions and proof scripts related to the 
   correctness of closure algorithms for context-free grammars, namely 
   union, concatenation and Kleene star operations.

   More information can be found in the paper "Formalization of closure 
   properties for context-free grammars", LSFA 2014.

   Marcus Vinícius Midena Ramos
   mvmramos@gmail.com
   --------------------------------------------------------------------- *)

Require Import Ascii.
Require Import String.
Require Import List.
Import ListNotations.

Open Scope char_scope.
Open Scope string_scope.
Open Scope list_scope.

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

Lemma cons_app:
forall (A: Type) (s: A) (l: list A),
s::l=[s]++l.
Proof.
intros.
simpl.
reflexivity.
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

(* --------------------------------------------------------------------- *)
(* DEFINITIONS                                                           *)
(* --------------------------------------------------------------------- *)

Record cfg: Type:= {
non_terminal: Type;
terminal: Type;
start_symbol: non_terminal;
sf:= list (non_terminal + terminal);
rules: non_terminal -> sf -> Prop
}.

Inductive derives (g: cfg) : sf g -> sf g -> Prop :=
| derives_refl: forall s, 
                derives g s s
| derives_step: forall s1 s2 s3: sf g,
                forall left: non_terminal g,
                forall right: sf g,
                derives g s1 (s2 ++ inl left :: s3) ->
                rules g left right ->
                derives g s1 (s2 ++ right ++ s3).

Definition generates (g: cfg) (s: sf g): Prop:=
derives g [inl (start_symbol g)] s.

Definition convert (g: cfg) (t: terminal g): non_terminal g + terminal g:= inr t.

Definition produces (g: cfg) (s: list (terminal g)): Prop:=
generates g (map (convert g) s).

Theorem derives_direct:
forall g: cfg,
forall left: non_terminal g,
forall right: sf g,
rules g left right -> derives g [inl left] right.
Proof.
intros g left right H.
rewrite <- app_nil_l.
rewrite <- app_nil_r.
rewrite <- app_assoc.
apply derives_step with (left:=left).
rewrite app_nil_l.
apply derives_refl.
exact H.
Qed.

Theorem derives_context_free_add_left (g:cfg) (s1 s2 s: sf g):
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

Theorem derives_context_free_add_right (g:cfg) (s1 s2 s: sf g):
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

Theorem derives_context_free_add (g:cfg) (s1 s2 s s': sf g):
derives g s1 s2 -> derives g (s++s1++s') (s++s2++s').
Proof.
intros H.
apply derives_context_free_add_left.
apply derives_context_free_add_right.
exact H.
Qed.

Theorem derives_trans (g: cfg) (s1 s2 s3: sf g):
derives g s1 s2 ->
derives g s2 s3 ->
derives g s1 s3.
Proof.
intros H1 H2.
induction H2 as [ s | x y z left right H3 H4 H5]. 
- trivial.
- econstructor. 
  apply H4. 
  exact H1.
  exact H5.
Qed.

Theorem derives_combine (g: cfg) (s1 s2 s3 s4: sf g):
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

Theorem derives_multiple (g: cfg) (s1 s2 s3: sf g) (left: non_terminal g) (right1 right2: sf g):
derives g s1 (s2 ++ inl left :: s3) ->
rules g left right1 ->
rules g left right2 ->
derives g s1 (s2 ++ right1 ++ s3) /\ derives g s1 (s2 ++ right2 ++ s3).
Proof.
intros H1 H2 H3.
split.
apply derives_step with (left:=left).
exact H1.
exact H2.
apply derives_step with (left:=left).
exact H1.
exact H3.
Qed.

(* --------------------------------------------------------------------- *)
(* UNION                                                                 *)
(* --------------------------------------------------------------------- *)

Inductive g_uni_t (g1 g2: cfg): Type:=
| Transf1_uni_t: terminal g1 -> g_uni_t g1 g2
| Transf2_uni_t: terminal g2 -> g_uni_t g1 g2.

Inductive g_uni_nt (g1 g2: cfg): Type :=
| Start_uni : g_uni_nt g1 g2
| Transf1_uni_nt : non_terminal g1 -> g_uni_nt g1 g2
| Transf2_uni_nt : non_terminal g2 -> g_uni_nt g1 g2.

Definition g_uni_sf_lift1 (g1 g2: cfg)(c: non_terminal g1 + terminal g1): g_uni_nt g1 g2 + g_uni_t g1 g2:=
  match c with
  | inl nt => inl (Transf1_uni_nt g1 g2 nt)
  | inr t  => inr (Transf1_uni_t g1 g2 t)
  end.

Definition g_uni_sf_lift2 (g1 g2: cfg)(c: non_terminal g2 + terminal g2): g_uni_nt g1 g2 + g_uni_t g1 g2:=
  match c with
  | inl nt => inl (Transf2_uni_nt g1 g2 nt)
  | inr t  => inr (Transf2_uni_t g1 g2 t)
  end.

Inductive g_uni_rules (g1 g2: cfg): g_uni_nt g1 g2 -> list (g_uni_nt g1 g2 + g_uni_t g1 g2) -> Prop :=
| Start1_uni: g_uni_rules g1 g2 (Start_uni g1 g2) [inl (Transf1_uni_nt g1 g2 (start_symbol g1))]
| Start2_uni: g_uni_rules g1 g2 (Start_uni g1 g2) [inl (Transf2_uni_nt g1 g2 (start_symbol g2))]
| Lift1_uni: forall nt s,
             rules g1 nt s ->
             g_uni_rules g1 g2 (Transf1_uni_nt g1 g2 nt) (map (g_uni_sf_lift1 g1 g2) s)
| Lift2_uni: forall nt s,
             rules g2 nt s ->
             g_uni_rules g1 g2 (Transf2_uni_nt g1 g2 nt) (map (g_uni_sf_lift2 g1 g2) s).

Definition g_uni (g1 g2: cfg): cfg := {|
non_terminal:= g_uni_nt g1 g2;
terminal:= g_uni_t g1 g2;
start_symbol:= Start_uni g1 g2;
rules:= g_uni_rules g1 g2
|}.

Lemma derives_add_uni_left (g1 g2: cfg)(s1 s2: sf g1):
derives g1 s1 s2 ->
derives (g_uni g1 g2) 
        (map (g_uni_sf_lift1 g1 g2) s1)
        (map (g_uni_sf_lift1 g1 g2) s2).
Proof.
intros H.
induction H as [|x y z left right H1 H2 H3].
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in H2. 
  simpl in H2.
  apply derives_step with (left:=(Transf1_uni_nt g1 g2 left)).
  exact H2.
  simpl.
  apply Lift1_uni.
  exact H3.
Qed.

Lemma derives_add_uni_right (g1 g2: cfg)(s1 s2: sf g2):
derives g2 s1 s2 ->
derives (g_uni g1 g2) 
        (map (g_uni_sf_lift2 g1 g2) s1)
        (map (g_uni_sf_lift2 g1 g2) s2).
Proof.
intros H.
induction H as [|x y z left right H1 H2 H3].
- apply derives_refl.
- rewrite map_app.
  rewrite map_app.
  rewrite map_app in H2. 
  simpl in H2.
  apply derives_step with (left:=(Transf2_uni_nt g1 g2 left)).
  exact H2.
  simpl.
  apply Lift2_uni.
  exact H3.
Qed.

Theorem g_uni_correct_left (g1 g2: cfg)(s: sf g1):
generates g1 s ->
generates (g_uni g1 g2)
          (map (g_uni_sf_lift1 g1 g2) s).
Proof.
unfold generates. 
intros H.
apply derives_trans with (s2:= map (g_uni_sf_lift1 g1 g2) [(inl (start_symbol g1))]).
- simpl. 
  match goal with
  | |- derives _ ?s1 ?s2 =>
       change s1 with ([] ++ s1)%list;
       change s2 with ([] ++ s2 ++ [])%list
  end.
  apply derives_step with (left:=(Start_uni g1 g2)).
  + apply derives_refl.
  + simpl.
    apply Start1_uni.
- apply derives_add_uni_left.
  exact H.
Qed.

Theorem g_uni_correct_right (g1 g2: cfg)(s: sf g2):
generates g2 s ->
generates (g_uni g1 g2)
          (map (g_uni_sf_lift2 g1 g2) s).
Proof.
unfold generates. 
intros H.
apply derives_trans with (s2:= map (g_uni_sf_lift2 g1 g2) [(inl (start_symbol g2))]).
- simpl.
  match goal with
  | |- derives _ ?s1 ?s2 =>
       change s1 with ([] ++ s1)%list;
       change s2 with ([] ++ s2 ++ [])%list
  end.
  apply derives_step with (left:=(Start_uni g1 g2)).
  + apply derives_refl.
  + simpl.
    apply Start2_uni.
- apply derives_add_uni_right.
  exact H.
Qed.

Theorem g_uni_correct (g1 g2: cfg)(s1: sf g1)(s2: sf g2):
(generates g1 s1 -> generates (g_uni g1 g2) (map (g_uni_sf_lift1 g1 g2) s1)) /\
(generates g2 s2 -> generates (g_uni g1 g2) (map (g_uni_sf_lift2 g1 g2) s2)).
Proof.
split.
- apply g_uni_correct_left.
- apply g_uni_correct_right.
Qed.

Theorem g_uni_correct_inv (g1 g2: cfg)(s: sf (g_uni g1 g2)):
generates (g_uni g1 g2) s ->
(s=[inl (start_symbol (g_uni g1 g2))]) \/
(exists s1: sf g1,
(s=(map (g_uni_sf_lift1 g1 g2) s1) /\ generates g1 s1)) \/
(exists s2: sf g2,
(s=(map (g_uni_sf_lift2 g1 g2) s2) /\ generates g2 s2)).
Proof.
unfold generates.
remember [inl (start_symbol (g_uni g1 g2))] as init.
intro H.
induction H.
  (* Base case *)
- left. reflexivity.
- (* Induction hypothesis *)
  subst.
  specialize (IHderives eq_refl).
  destruct IHderives.
  + (* IHderives, first case *) 
    destruct s2.
    * (* First case, left = Start_uni *)
      simpl in H1. inversion H1. subst. {
      inversion H0. subst. clear H1.
      - (* First case, right = start_symbol g1 *) 
        simpl in *. 
        right.
        left.
        exists [inl (start_symbol g1)].
        split.
        + simpl. reflexivity.
        + apply derives_refl.
      - (* Second case, right = start_symbol g2 *)
        simpl in *.
        right.
        right.
        exists [inl (start_symbol g2)].
        split.
        + simpl. reflexivity.
        + apply derives_refl. }
    * (* Second case, left = non_terminal (g_uni g1 g2 *)
      simpl in H1.
      inversion H1. {
      destruct s2.
      - simpl in H4. inversion H4.
      - inversion H4. }
  + (* IHderives, second case *)
    destruct H1.
    * (* H1, first case: comes from g1 *)
      destruct H1 as [x [H1 H2]]. {
      inversion H0.
      - (* First rule: Start1_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. 
            inversion H1. {
            destruct s.
            - inversion H4.
            - inversion H4. }
        + simpl in *.
          assert (IN: In (inl (Start_uni g1 g2)) (map (g_uni_sf_lift1 g1 g2) x)). 
          { rewrite <- H1. simpl. right. apply in_app_iff. right. simpl. left. reflexivity. }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Second rule: Start2_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. inversion H1. {
            destruct s.
            - inversion H4.
            - inversion H4. }
        + simpl in *.
          assert (IN: In (inl (Start_uni g1 g2)) (map (g_uni_sf_lift1 g1 g2) x)). 
          { rewrite <- H1. simpl. right. apply in_app_iff. right. simpl. left. reflexivity. }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Third rule: Lift1_uni *)
        (* Should be true *)
        right.
        left.
        apply map_expand in H1.
        destruct H1 as [s1' [s2'[H6 [H7 H8]]]].
        replace (inl left::s3) with ([inl left]++s3) in H8.
        + symmetry in H8.
          apply map_expand in H8.
          destruct H8 as [m [n [H9 [H10 H11]]]].
          exists (s1'++s++n).
          split.
          * subst.
            repeat rewrite map_app.
            reflexivity.
          * subst. {
            destruct m. 
            - inversion H10.
            - simpl in H10.
              inversion H10.
              destruct s0.
              + inversion H4.
                subst.
                apply map_eq_nil in H5.
                subst.
                apply derives_step with (right:=s) in H2.
                exact H2.
                exact H3.
              + inversion H4. }
        + simpl. 
          reflexivity.
      - (* Forth rule: Lift2_uni *)
        (* Should be false *)
        simpl in *. subst. 
        assert (IN: In (inl (Transf2_uni_nt g1 g2 nt)) (map (g_uni_sf_lift1 g1 g2) x)). 
        { rewrite <- H1. rewrite in_app_iff. right. simpl. left. reflexivity. }
        rewrite in_map_iff in IN.
        destruct IN as [x0 [H4 H5]].
        destruct x0.
        + inversion H4. 
        + inversion H4. }
    * (* H1, second case: comes from g2 *)
      destruct H1 as [x [H1 H2]]. {
      inversion H0.
      - (* First rule: Start1_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. 
            inversion H1. {
            destruct s.
            - inversion H4.
            - inversion H4. }
        + simpl in *.
          assert (IN: In (inl (Start_uni g1 g2)) (map (g_uni_sf_lift2 g1 g2) x)). 
          { rewrite <- H1. simpl. right. apply in_app_iff. right. simpl. left. reflexivity. }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Second rule: Start2_uni *)
        (* Contradiction, x cannot contain Start_uni *)
        simpl in *. subst. 
        destruct s2.
        + simpl in H1. 
          destruct x.
          * inversion H1. 
          * simpl in H1. inversion H1. {
            destruct s.
            - inversion H4.
            - inversion H4. }
        + simpl in *.
          assert (IN: In (inl (Start_uni g1 g2)) (map (g_uni_sf_lift2 g1 g2) x)). 
          { rewrite <- H1. simpl. right. apply in_app_iff. right. simpl. left. reflexivity. }
          rewrite in_map_iff in IN.
          destruct IN.
          destruct H3.
          destruct x0.
          * simpl in H3. inversion H3.
          * simpl in H3. inversion H3. 
      - (* Third rule: Lift1_uni *)
        (* Should be false *)
        simpl in *. subst. 
        assert (IN: In (inl (Transf1_uni_nt g1 g2 nt)) (map (g_uni_sf_lift2 g1 g2) x)). 
        { rewrite <- H1. rewrite in_app_iff. right. simpl. left. reflexivity. }
        rewrite in_map_iff in IN.
        destruct IN as [x0 [H4 H5]].
        destruct x0.
        + inversion H4. 
        + inversion H4.
      - (* Forth rule: Lift2_uni *)
        (* Should be true *)
        right.
        right.
        apply map_expand in H1.
        destruct H1 as [s1' [s2'[H6 [H7 H8]]]].
        replace (inl left::s3) with ([inl left]++s3) in H8.
        + symmetry in H8.
          apply map_expand in H8.
          destruct H8 as [m [n [H9 [H10 H11]]]].
          exists (s1'++s++n).
          split.
          * subst.
            repeat rewrite map_app.
            reflexivity.
          * subst. {
            destruct m. 
            - inversion H10.
            - simpl in H10.
              inversion H10.
              destruct s0.
              + inversion H4.
                subst.
                apply map_eq_nil in H5.
                subst.
                apply derives_step with (right:=s) in H2.
                exact H2.
                exact H3.
              + inversion H4. }
        + simpl. 
          reflexivity. }
Qed.

(* --------------------------------------------------------------------- *)
(* CONCATENATION                                                         *)
(* --------------------------------------------------------------------- *)

Inductive g_cat_t (g1 g2: cfg): Type:= 
| Transf1_cat_t: terminal g1 -> g_cat_t g1 g2
| Transf2_cat_t: terminal g2 -> g_cat_t g1 g2.

Inductive g_cat_nt (g1 g2: cfg): Type :=
| Start_cat : g_cat_nt g1 g2
| Transf1_cat_nt : non_terminal g1 -> g_cat_nt g1 g2
| Transf2_cat_nt : non_terminal g2 -> g_cat_nt g1 g2.

Definition g_cat_sf_lift1 (g1 g2: cfg)(c: non_terminal g1 + terminal g1): g_cat_nt g1 g2 + g_cat_t g1 g2:=
  match c with
  | inl nt => inl (Transf1_cat_nt g1 g2 nt)
  | inr t  => inr (Transf1_cat_t g1 g2 t)
  end.

Definition g_cat_sf_lift2 (g1 g2: cfg)(c: non_terminal g2 + terminal g2): g_cat_nt g1 g2 + g_cat_t g1 g2:=
  match c with
  | inl nt => inl (Transf2_cat_nt g1 g2 nt)
  | inr t  => inr (Transf2_cat_t g1 g2 t)
  end.

Inductive g_cat_rules (g1 g2: cfg): g_cat_nt g1 g2 -> list (g_cat_nt g1 g2 + g_cat_t g1 g2) -> Prop :=
| New_cat: g_cat_rules g1 g2 (Start_cat g1 g2) ([inl (Transf1_cat_nt g1 g2 (start_symbol g1))]++[inl (Transf2_cat_nt g1 g2 (start_symbol g2))])
| Lift1_cat: forall nt s,
             rules g1 nt s ->
             g_cat_rules g1 g2 (Transf1_cat_nt g1 g2 nt) (map (g_cat_sf_lift1 g1 g2) s)
| Lift2_cat: forall nt s,
             rules g2 nt s ->
             g_cat_rules g1 g2 (Transf2_cat_nt g1 g2 nt) (map (g_cat_sf_lift2 g1 g2) s).

Definition g_cat (g1 g2: cfg): cfg := {|
non_terminal:= g_cat_nt g1 g2;
terminal:= g_cat_t g1 g2;
start_symbol:= Start_cat g1 g2;
rules:= g_cat_rules g1 g2
|}.

Lemma derives_add_cat_left (g1 g2: cfg)(s s': sf g1):
derives g1 s s' -> derives (g_cat g1 g2) (map (g_cat_sf_lift1 g1 g2) s) (map (g_cat_sf_lift1 g1 g2) s'). 
Proof.
intro H.
induction H as [| x y z left right H1 H2 H3].
apply derives_refl.
rewrite map_app.
rewrite map_app.
rewrite map_app in H2.
simpl in H2.
apply derives_step with (left:=(Transf1_cat_nt g1 g2 left)).
exact H2.
simpl.
apply Lift1_cat.
apply H3.
Qed.

Lemma derives_add_cat_right (g1 g2: cfg)(s s': sf g2):
derives g2 s s' -> derives (g_cat g1 g2) (map (g_cat_sf_lift2 g1 g2) s) (map (g_cat_sf_lift2 g1 g2) s'). 
Proof.
intro H.
induction H as [| x y z left right H1 H2 H3].
apply derives_refl.
rewrite map_app.
rewrite map_app.
rewrite map_app in H2.
simpl in H2.
apply derives_step with (left:=(Transf2_cat_nt g1 g2 left)).
exact H2.
simpl.
apply Lift2_cat.
apply H3.
Qed.

Lemma g_cat_correct_aux (g1 g2: cfg)(s11 s12: sf g1)(s21 s22: sf g2):
derives g1 s11 s12 /\ derives g2 s21 s22 ->
derives (g_cat g1 g2) 
        ((map (g_cat_sf_lift1 g1 g2) s11)++(map (g_cat_sf_lift2 g1 g2) s21)) 
        ((map (g_cat_sf_lift1 g1 g2) s12)++(map (g_cat_sf_lift2 g1 g2) s22)).
Proof.
intros [H1 H2].
induction H1, H2.
apply derives_refl.
rewrite map_app.
rewrite map_app.
apply derives_trans with (s2:=
  (map (g_cat_sf_lift1 g1 g2) s ++
   map (g_cat_sf_lift2 g1 g2) (s2 ++ [inl left] ++ s3))).
apply derives_context_free_add_left.
apply derives_add_cat_right.
simpl.
exact H2.
apply derives_context_free_add_left.
rewrite map_app.
rewrite map_app.
simpl.
apply derives_step with (left:=(Transf2_cat_nt g1 g2 left)).
apply derives_refl.
simpl.
apply Lift2_cat.
exact H.
apply derives_context_free_add_right.
apply derives_add_cat_left.
apply derives_step with (left:=left).
exact H1.
exact H.
rewrite map_app.
rewrite map_app.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite map_app.
rewrite map_app.
rewrite map_app in IHderives.
rewrite map_app in IHderives.
rewrite <- app_assoc in IHderives.
simpl in IHderives.
rewrite map_app in IHderives.
remember ((map (g_cat_sf_lift1 g1 g2) s1 ++
           map (g_cat_sf_lift2 g1 g2) s0)) as w1.
remember (map (g_cat_sf_lift1 g1 g2) s3 ++
          map (g_cat_sf_lift2 g1 g2) s4 ++
          map (g_cat_sf_lift2 g1 g2) right0 ++
          map (g_cat_sf_lift2 g1 g2) s5) as w2.
apply derives_step with (left:=(Transf1_cat_nt g1 g2 left)).
exact IHderives.
simpl.
apply Lift1_cat.
exact H.
Qed.

Theorem g_cat_correct (g1 g2: cfg)(s1: sf g1)(s2: sf g2):
generates g1 s1 /\ generates g2 s2 ->
generates (g_cat g1 g2)
          ((map (g_cat_sf_lift1 g1 g2) s1)++(map (g_cat_sf_lift2 g1 g2) s2)).
Proof.
unfold generates.
intros H.
destruct H as [H1 H2].
apply derives_trans with (s2:=(map (g_cat_sf_lift1 g1 g2) [(inl (start_symbol g1))]++map (g_cat_sf_lift2 g1 g2) [(inl (start_symbol g2))])).
match goal with
| |- derives _ ?s1 ?s2 =>
     change s1 with ([] ++ s1);
     change s2 with ([] ++ s2 ++ [])
end.
apply derives_step with (left:=(start_symbol (g_cat g1 g2))).
apply derives_refl.
simpl.
apply New_cat.
apply g_cat_correct_aux.
split.
exact H1.
exact H2.
Qed.

Theorem g_cat_correct_inv (g1 g2: cfg)(s: sf (g_cat g1 g2)):
generates (g_cat g1 g2) s ->
s = [inl (start_symbol (g_cat g1 g2))] \/
exists s1: sf g1,
exists s2: sf g2,
s =(map (g_cat_sf_lift1 g1 g2) s1)++(map (g_cat_sf_lift2 g1 g2) s2) /\
generates g1 s1 /\
generates g2 s2.
Proof.
unfold generates.
remember ([inl (start_symbol (g_cat g1 g2))]) as init.
intros H.
induction H.
- left. reflexivity.
- subst. 
  specialize (IHderives eq_refl).
  destruct IHderives.
  + (* IHderives, first case *)
    (* A primeira cadeia gerada é a raiz da gramática *)
    destruct s2.
    * (* Se s2 é vazio, a primeira regra está sendo aplicada *)
      simpl in H1. inversion H1. subst. clear H1.
      simpl in H0. inversion H0. clear H0 H2.
      simpl in *.
      right.
      exists [inl (start_symbol g1)], [inl (start_symbol g2)]. { 
      split. 
        - simpl. reflexivity. 
        - split. apply derives_refl. apply derives_refl. }
    * (* Se s2 não é vazio, temos uma contradição *)
      simpl in H1. {
      destruct s2. 
      - simpl in *. inversion H1. 
      - simpl in *. inversion H1. }
  + (* IHderives, second case *)
    (* A primeira cadeia gerada é a concatenação de map x com map x0 *)
    destruct H1 as (? & ? & ? & ? & ?).
    (* Análise da regra usada *)
    inversion H0. 
    subst. 
    clear H0.
    * (* Case 1: rule New_cat *)
      (* Contradiction: H1 cannot contain Start_cat *)
      assert (IN : In (inl (Start_cat g1 g2)) (map (g_cat_sf_lift1 g1 g2) x ++ map (g_cat_sf_lift2 g1 g2) x0)).
      { rewrite <- H1. 
        rewrite in_app_iff. right. simpl. left. reflexivity. }
      rewrite in_app_iff in IN.
      (* Start_cat is in x or x0 *) {
      destruct IN.
      - (* Start_cat is in x, contradiction *)
        rewrite in_map_iff in H0. destruct H0 as (? & ? & ?).
        (* But Start_cat = lift x1 and x cannot contain x1 *)
        destruct x1. 
        + simpl in H0. inversion H0. 
        + simpl in H0. inversion H0.
      - (* Start_cat is in x0, contradiction *)
        rewrite in_map_iff in H0. destruct H0 as (? & ? & ?).
        destruct x1.
        + simpl in H0. inversion H0. 
        + simpl in H0. inversion H0. }
    * (* Case 2: rule Lift1_cat *)
      (* A rule of g1 has been used *)
      subst.
      (* Consider both situations in H1 *)
      assert (IN : In (inl (Transf1_cat_nt g1 g2 nt)) (map (g_cat_sf_lift1 g1 g2) x ++ map (g_cat_sf_lift2 g1 g2) x0)).
      { rewrite <- H1. 
        rewrite in_app_iff. right. simpl. left. reflexivity. }
      rewrite in_app_iff in IN.
      (* Transf1_cat_nt is in x or x0 *) {
      destruct IN.
      - (* Transf1_cat_nt is in x, ok *)
        apply equal_app in H1.
        destruct H1.
        + destruct H1 as [l [H1 H6]].
          right. {
          destruct l.
          * destruct x0.
            - simpl in H6.
              inversion H6.
            - simpl in H6.
              inversion H6.
              destruct s0.
              + inversion H8.
              + inversion H8.
          * inversion H6.
            subst. 
            clear H6. {
            apply derives_step with (right:=(map (g_cat_sf_lift1 g1 g2) s)) in H.
            - symmetry in H1.
              apply map_expand in H1.
              destruct H1 as [s1' [s2' [H6 [H7 H8]]]].
              replace (inl (Transf1_cat_nt g1 g2 nt) :: l) with ([inl (Transf1_cat_nt g1 g2 nt)]++l) in H8.
              + symmetry in H8.
                apply map_expand in H8.
                destruct H8 as [s1'' [s2'' [H9 [H10 H11]]]].
                exists (s1'++s++s2''), x0.
                split.
                * repeat rewrite map_app.
                  subst.
                  repeat rewrite <- app_assoc.
                  reflexivity.
                * { split.
                    - subst. 
                      destruct s1''.
                      + simpl in H10.
                        inversion H10.
                      + inversion H10.  
                        destruct s0.
                        * inversion H6.
                          apply map_eq_nil in H7.
                          subst. {
                          apply derives_step with (right:= s) in H2.
                          - exact H2.
                          - exact H4. }
                        * inversion H6.
                    - exact H3. }
              + simpl.
                reflexivity.
            - exact H0. } }
        + destruct H1 as [l [H1 H6]].
          assert (IN: In (inl (Transf1_cat_nt g1 g2 nt)) (map (g_cat_sf_lift2 g1 g2) x0)).
          { rewrite H6. apply in_app_iff. right. simpl. left. reflexivity. }
          apply in_map_iff in IN. 
          destruct IN.
          destruct H7. 
          destruct x1.
          inversion H7.
          inversion H7.
      - (* Transf1_cat_nt is in x0, contradiction *)
        rewrite in_map_iff in H5.
        destruct H5.
        destruct H5.
        destruct x1.
        + inversion H5.
        + inversion H5. }
    * (* Case 3: rule Lift2_cat *)
      (* A rule of g2 has been used *)
      subst.
      (* Consider both situations in H1 *)
      assert (IN : In (inl (Transf2_cat_nt g1 g2 nt)) (map (g_cat_sf_lift1 g1 g2) x ++ map (g_cat_sf_lift2 g1 g2) x0)).
      { rewrite <- H1. 
        rewrite in_app_iff. right. simpl. left. reflexivity. }
      rewrite in_app_iff in IN.
      (* Transf2_cat_nt is in x or x0 *) {
      destruct IN.
      - (* Transf2_cat_nt is in x, contradiction *)
        rewrite in_map_iff in H5.
        destruct H5.
        destruct H5.
        destruct x1.
        + inversion H5.
        + inversion H5.
      - (* Transf2_cat_nt is in x0, ok *)
        apply equal_app in H1.
        destruct H1.
        + destruct H1 as [l [H1 H6]].
          right. {
          destruct l.
          * destruct x0.
            - simpl in H6.
              inversion H6.
            - simpl in H6.
              inversion H6.
              rewrite app_nil_r in H1.
              subst.
              exists x.
              exists (s++x0).
              split. 
              rewrite map_app.
              reflexivity.
              split.
              exact H2.
              inversion H6.
              destruct s0.
              + simpl in H7. 
                inversion H7.
                subst.
                rewrite <- app_nil_l in H3. {
                apply derives_step with (right:=s) in H3.
                * exact H3.
                * exact H4. }
              + inversion H7.
          * inversion H6.
            subst.
            clear H6.
            assert (IN : In (inl (Transf2_cat_nt g1 g2 nt)) (map (g_cat_sf_lift1 g1 g2) x)).
            { rewrite H1. rewrite in_app_iff. right. simpl. left. reflexivity. }
            rewrite in_map_iff in IN.
            destruct IN as [x0' [H6 H7]]. {
            destruct x0'.
            - simpl in H6.
              inversion H6.
            - inversion H6. } }
        + destruct H1 as [l [H7 H8]].
          subst. 
          symmetry in H8.
          apply map_expand in H8.
          destruct H8 as [ s1' [s2' [H10 [H11 H12]]]].
          subst.
          destruct s2'.
          * inversion H12.
          * inversion H12.
            subst. 
            right.
            exists x.
            exists (s1'++s++s2').
            split.
            rewrite <- app_assoc.
            repeat rewrite map_app.
            reflexivity.
            split.
            exact H2. {
            destruct s0.
            - inversion H6.
              subst.
              apply derives_step with (right:=s) in H3.
              exact H3.
              exact H4.
            - inversion H6. } }
Qed.

(* --------------------------------------------------------------------- *)
(* CLOSURE                                                               *)
(* --------------------------------------------------------------------- *)

Inductive g_clo_t (g: cfg): Type:= 
| Transf_clo_t: terminal g -> g_clo_t g.

Inductive g_clo_nt (g: cfg): Type :=
| Start_clo : g_clo_nt g
| Transf_clo_nt : non_terminal g -> g_clo_nt g.

Definition g_clo_sf_lift (g: cfg)(c: non_terminal g + terminal g): g_clo_nt g + g_clo_t g:=
  match c with
  | inl nt => inl (Transf_clo_nt g nt)
  | inr t  => inr (Transf_clo_t g t)
  end.

Inductive g_clo_rules (g: cfg): g_clo_nt g -> list (g_clo_nt g + g_clo_t g) -> Prop :=
| New1_clo: g_clo_rules g (Start_clo g) ([inl (Start_clo g)]++[inl (Transf_clo_nt g (start_symbol g))])
| New2_clo: g_clo_rules g (Start_clo g) []
| Lift_clo: forall nt s,
            rules g nt s ->
            g_clo_rules g (Transf_clo_nt g nt) (map (g_clo_sf_lift g) s).

Definition g_clo (g: cfg): cfg := {|
non_terminal:= g_clo_nt g;
terminal:= g_clo_t g;
start_symbol:= Start_clo g;
rules:= g_clo_rules g
|}.

Theorem derives_add_clo (g: cfg) (s1 s2: sf g):
derives g s1 s2 -> derives (g_clo g) (map (g_clo_sf_lift g) s1) (map (g_clo_sf_lift g) s2).
Proof.
intro H.
induction H.
apply derives_refl.
rewrite map_app.
rewrite map_app.
rewrite map_app in IHderives.
simpl in IHderives.
apply derives_step with (g := g_clo g) (left:=(Transf_clo_nt g left)).
exact IHderives.
simpl.
apply Lift_clo.
exact H0.
Qed.

Theorem g_clo_correct (g: cfg)(s: sf g)(s': sf (g_clo g)):
generates (g_clo g) nil /\
(generates (g_clo g) s' /\ generates g s -> generates (g_clo g) (s'++ (map (g_clo_sf_lift g)) s)).
Proof.
unfold generates.
split.
simpl.
rewrite <- app_nil_l.
rewrite <- app_nil_r.
rewrite <- app_assoc.
apply derives_step with (left:=Start_clo g).
rewrite app_nil_l.
apply derives_refl.
simpl.
apply New2_clo.
intros [H1 H2].
apply derives_trans with (s2:=[inl (Start_clo g)]++(map (g_clo_sf_lift g) [inl (start_symbol g)])).
simpl.
apply (derives_direct (g_clo g) (Start_clo g) ([inl (Start_clo g); inl (Transf_clo_nt g (start_symbol g))])).
simpl.
apply New1_clo.
apply derives_add_clo in H2.
apply derives_combine with (g:= (g_clo g)).
split.
exact H1.
exact H2.
Qed.

Theorem g_clo_correct_inv (g: cfg)(s: sf (g_clo g)):
generates (g_clo g) s -> 
(s=[]) \/
(s=[inl (start_symbol (g_clo g))]) \/
(exists s': sf (g_clo g), 
 exists s'': sf g,
 generates (g_clo g) s' /\ generates g s'' /\ s=s'++map (g_clo_sf_lift g) s'').
Proof.
unfold generates.
remember ([inl (start_symbol (g_clo g))]) as init.
intro H.
induction H.
- right.
  left.  
  reflexivity.
- subst.
  specialize (IHderives eq_refl).
  destruct IHderives.
  + destruct s2.
    * inversion H1. 
    * inversion H1.
  + destruct H1.
    * { destruct s2.
        - inversion H1.
          subst.
          inversion H0.
          + simpl in *.
            right.
            right. 
            exists [inl (Start_clo g)].
            exists [inl (start_symbol g)].
            split.
            apply derives_refl.
            split.
            apply derives_refl.
            simpl. 
            reflexivity.
          + left.
            trivial.
        - right. 
          right. 
          inversion H1.
          destruct s2.
          + inversion H4. 
          + inversion H4.  }
    * destruct H1 as [s' [s'' [H2 [H3 H4]]]]. { 
      inversion H0.
      - (* First case, rule New1_clo *)
        subst. simpl in *.
        assert (IN : In (inl (Start_clo g)) (s'++map (g_clo_sf_lift g) s'')).
        { simpl in *. rewrite <- H4. apply in_app_iff. right. simpl. left. reflexivity. }
        apply in_app_iff in IN.
        destruct IN.
        + (* Start_clo is in s', ok *)
          apply equal_app in H4. {
          destruct H4.
          * destruct H4 as [l [H5 H6]].
            destruct l.
            - simpl in H6.
              rewrite cons_app in H6.
              apply map_expand in H6.
              destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
              subst.
              destruct s1'.
              + inversion H8.
              + inversion H8. {
                destruct s.
                * inversion H5.
                * inversion H5. }
            - right.
              right.
              inversion H6.
              subst.
              exists (s2++inl (Start_clo g)::inl (Transf_clo_nt g (start_symbol g))::l).
              exists s''.
              split.
              + { apply derives_step with (right:=[@inl (non_terminal (g_clo g))(terminal (g_clo g)) (Start_clo g); @inl (non_terminal (g_clo g))(terminal (g_clo g)) (Transf_clo_nt g (start_symbol g))]) in H2.
                  * exact H2.
                  * exact H0. } 
              + { split.
                  * exact H3.
                  * rewrite <- app_assoc.
                    simpl.
                    reflexivity. }
          * destruct H4 as [l [H5 H6]].
            symmetry in H6.
            apply map_expand in H6.
            destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
            destruct s2'.
            - inversion H9.
            - inversion H9.
              destruct s.
              + inversion H6.
              + inversion H6. }
        + (* Start_clo is in s'', contradiction *)
          rewrite in_map_iff in H1. 
          destruct H1 as [x [H5 H6]].
          destruct x.
          * inversion H5.
          * inversion H5.   
      - (* Second case, rule New2_clo *)
        simpl in *.
        subst.
        assert (IN: In (inl (Start_clo g)) (s' ++ map (g_clo_sf_lift g) s'')).
        { simpl in *. rewrite <- H4. rewrite in_app_iff. right. simpl. left. reflexivity. }
        apply in_app_iff in IN.
        destruct IN.
        + (* Start_clo is in s', ok *)
          right.
          right.
          apply equal_app in H4.
          destruct H4.
          * destruct H4 as [l [H5 H6]]. {
            destruct l.
            - simpl in H6.
              rewrite cons_app in H6.
              apply map_expand in H6.
              destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
              destruct s1'.
              + inversion H8.
              + simpl in H8. 
                inversion H8.
                destruct s.
                * inversion H6.
                * inversion H6.
            - inversion H6.
              subst. 
              exists (s2++l).
              exists s''.
              split.
              + replace (s2++l) with (s2++[]++l).
                * { apply derives_step with (left:=(Start_clo g)).
                    - exact H2.
                    - exact H0. }
                * simpl.
                  reflexivity.
              + split.
                * exact H3.
                * rewrite <- app_assoc.
                  reflexivity. }
          * destruct H4 as [l [H5 H6]].
            symmetry in H6.
            apply map_expand in H6.
            destruct H6 as [s1' [s2' [H7 [H8 H9]]]]. {
            destruct s2'. 
            - inversion H9.
            - inversion H9.
              destruct s.
              + inversion H6.
              + inversion H6. }  
        + (* Start_clo is in s'', contradiction *)
          rewrite in_map_iff in H1. 
          destruct H1 as [x [H5 H6]].
          destruct x.
          * inversion H5.
          * inversion H5.   
      - (* Third case, rule Lift_clo *)
        right.
        right.
        subst.
        apply equal_app in H4.
        destruct H4.
        + destruct H4 as [l [H5 H6]].
          subst.
          destruct l.
          * simpl in H6.
            rewrite cons_app in H6.
            apply map_expand in H6.
            destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
            subst.
            exists s2.
            exists (s++s2'). {
            split.
            - rewrite app_nil_r in H2. 
              exact H2.
            - split.
              + destruct s1'.
                * inversion H8.
                * inversion H8. {
                  destruct s0.
                  - inversion H5.
                    subst.
                    apply map_eq_nil in H6.
                    subst.
                    rewrite <- app_nil_l in H3.
                    apply derives_step with (right:=s) in H3.
                    + exact H3.
                    + exact H1.
                  - inversion H5. }
              + rewrite map_app.
                reflexivity. }
          * inversion H6.
            subst.  
            exists (s2 ++ map (g_clo_sf_lift g) s ++ l).
            exists s''. {
            split. 
            - apply derives_step with (right:=(map (g_clo_sf_lift g) s)) in H2.
              + exact H2.
              + exact H0.
            - split.
              + exact H3.
              + repeat rewrite <- app_assoc.
                reflexivity. }
        + destruct H4 as [l [H5 H6]].
          subst.
          symmetry in H6.
          apply map_expand in H6.
          destruct H6 as [s1' [s2' [H7 [H8 H9]]]].
          subst.
          rewrite cons_app in H9.
          symmetry in H9.
          apply map_expand in H9.
          destruct H9 as [s1'' [s2'0 [H6 [H7 H8]]]].
          subst.
          exists s'.
          exists (s1'++s++s2'0).
          split.
          * exact H2.
          * { split.
              - destruct s1''.
                + inversion H7.
                + simpl in H7.
                  inversion H7.
                  destruct s0.
                  * inversion H5.
                    subst. 
                    apply map_eq_nil in H6.
                    subst. {
                    apply derives_step with (right:=s) in H3.
                    - exact H3.
                    - exact H1. } 
                  * inversion H5.
              - rewrite <- app_assoc.
                repeat rewrite map_app.
                reflexivity. } }
Qed.

(* --------------------------------------------------------------------- *)
(* EXAMPLES                                                              *)
(* --------------------------------------------------------------------- *)

Inductive nt1: Type:= S | X | Y.
Inductive  t1: Type:= a | b | c.
Inductive rs1: nt1 -> list (nt1+t1) -> Prop:=
  r11: rs1 S [inr a;inl S]
| r12: rs1 S [inr b].
Definition g1:= {|
non_terminal:= nt1; 
terminal:= t1; 
start_symbol:= S; 
rules:= rs1
|}.

Lemma generates_g1_b: generates g1 [inr b].
Proof.
unfold generates.
apply derives_direct.
simpl.
apply r12.
Qed.

Lemma generates_g1_aab: generates g1 ([inr a]++[inr a]++[inr b]).
Proof.
unfold generates.
rewrite <- app_nil_l.
rewrite <- app_nil_r.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- (app_nil_l [inl (start_symbol g1)]).
rewrite <- (app_nil_r [inl (start_symbol g1)]).
apply derives_step with (left:=S)(s2:=[] ++ [inr a] ++ [inr a]).
rewrite <- app_nil_r.
rewrite <- app_assoc.
rewrite <- app_assoc.
rewrite <- app_assoc.
apply derives_step with (left:=S)(right:=[inr a]++[inl S]).
rewrite app_nil_l.
rewrite app_nil_r.
apply derives_direct.
apply r11.
apply r11.
apply r12.
Qed.

Inductive nt2: Type:= W | Z.
Inductive  t2: Type:= d | e | f.
Inductive rs2: nt2 -> list (nt2+t2) -> Prop:=
  rs21: rs2 W [inr d;inl Z]
| rs22: rs2 W [inr e].
Definition g2:= {|
non_terminal:= nt2; 
terminal:= t2; 
start_symbol:= W; 
rules:= rs2
|}.

Definition g3:= g_uni g1 g2.
Definition g4:= g_cat g1 g2.
Definition g5:= g_clo g1.
