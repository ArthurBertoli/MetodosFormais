(* Lista 7 resolvida - Expressões Regulares *)

Require Export Coq.Init.Logic.
Require Export Coq.Bool.Bool.
Require Export Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)

  where "s =~ re" := (exp_match s re).


Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.


(* Exercício 1 *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  - generalize dependent s1. induction s2 as [|h t IH]; simpl; intros s1 H.
    + inversion H. reflexivity.
    + inversion H; subst.
      * inversion H1; subst.
        -- inversion H3; subst.
           specialize (IH s'). rewrite <- IH in H2. subst. reflexivity.
        -- simpl in H2. subst. reflexivity.
      * inversion H2.
  - intros ->. clear s1. induction s2 as [|h t IH]; simpl.
    + apply MEmpty.
    + apply MApp.
      * apply MChar.
      * apply IH.
Qed.


Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
    | EmptySet => false
    | EmptyStr => true
    | Char _ => true
    | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
    | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
    | Star re1 => true
  end.

(* Exercício 2 *)

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros [s H]. induction H; simpl; try reflexivity.
    + rewrite andb_true_iff. split; assumption.
    + rewrite orb_true_iff. now left.
    + rewrite orb_true_iff. now right.
  - induction re; simpl; try (intros H; discriminate H);
    try (intros _; exists []; constructor).
    + intros _. exists [t]. apply MChar.
    + intros H. apply andb_true_iff in H. destruct H as [H1 H2].
      apply IPre1 in H1. apply IPre2 in H2.
      destruct H1 as [s1 Hs1], H2 as [s2 Hs2].
      exists (s1 ++ s2). apply MApp; assumption.
    + intros H. apply orb_true_iff in H. destruct H.
      * apply IPre1 in H. destruct H as [s Hs]. exists s. apply MUnionL. assumption.
      * apply IPre2 in H. destruct H as [s Hs]. exists s. apply MUnionR. assumption.
    + intros _. exists []. apply MStar0.
Qed.


(* Exercício 3 *)

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 => pumping_constant re1 + pumping_constant re2
  | Union re1 re2 => pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma length_app : forall A (l1 l2:list A), length (l1++l2) = length l1 + length l2.
Proof. intros. induction l1; simpl; [reflexivity|]. rewrite IHl1. reflexivity. Qed.

Lemma napp_length : forall T n (l:list T), length (napp n l) = n * length l.
Proof.
  intros. induction n; simpl; [reflexivity|]. rewrite length_app, IHn. lia.
Qed.

Lemma app_assoc' : forall A (l1 l2 l3:list A), l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof. intros; reflexivity. Qed.

Lemma le_sum_compare : forall a b c d,
  a + b <= c + d -> a <= c \/ b <= d.
Proof.
  intros. lia.
Qed.

Lemma exists_match_app_in_prefix : forall T re s1 s2 s,
  s = s1 ++ s2 -> s =~ re -> exists t1 t2, s1 = t1 ++ t2.
Proof.
  intros. exists s1, []. reflexivity.
Qed.

Lemma weak_pumping_star_aux : forall T re s,
  s =~ Star re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    (forall m, s1 ++ napp m s2 ++ s3 =~ Star re).
Proof.
  intros T re s H. induction H; intros Hlen.
  - simpl in Hlen. lia.
  - rewrite length_app in Hlen.
    remember (length s1) as L1.
    remember (length s2) as L2.
    assert (pumping_constant re <= L1 \/ pumping_constant re <= L2)
      by (apply le_sum_compare; lia).
    destruct H0 as [HL1 | HL2].
    + destruct (IH1 HL1) as (a & b & c & Heq & Hne & Hforall).
      exists a, b, (c ++ s2). split.
      * rewrite Heq, app_assoc'. reflexivity.
      * split; [assumption|].
        intros m. rewrite <- app_assoc'. apply MStarApp; [apply Hforall|assumption].
    + destruct (IH2 HL2) as (a & b & c & Heq & Hne & Hforall).
      exists (s1 ++ a), b, c. split.
      * rewrite Heq. rewrite <- app_assoc'. reflexivity.
      * split; [assumption|].
        intros m. rewrite app_assoc'. apply MStarApp; [assumption|apply Hforall].
Qed.

Lemma weak_pumping_app_union : forall T re s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    (forall m, s1 ++ napp m s2 ++ s3 =~ re).
Proof.
  intros T re s Hmatch Hlen.
  induction Hmatch; try (simpl in Hlen; lia).
  - (* App *)
    simpl in Hlen. rewrite length_app in Hlen.
    apply le_sum_compare in Hlen. destruct Hlen as [Hleft | Hright].
    + destruct (IHHmatch1 Hleft) as (a & b & c & Heq & Hne & Hforall).
      exists a, b, (c ++ s2). split.
      * rewrite Heq, app_assoc'. reflexivity.
      * split; [assumption|].
        intros m. rewrite <- app_assoc'. apply MApp; [apply Hforall|assumption].
    + destruct (IHHmatch2 Hright) as (a & b & c & Heq & Hne & Hforall).
      exists (s1 ++ a), b, c. split.
      * rewrite Heq. rewrite <- app_assoc'. reflexivity.
      * split; [assumption|].
        intros m. rewrite app_assoc'. apply MApp; [assumption|apply Hforall].
  - (* UnionL *)
    destruct (IHHmatch Hlen) as (a & b & c & Heq & Hne & Hforall).
    exists a, b, c. repeat split; try assumption.
    intros m. apply MUnionL. apply Hforall.
  - (* UnionR *)
    destruct (IHHmatch Hlen) as (a & b & c & Heq & Hne & Hforall).
    exists a, b, c. repeat split; try assumption.
    intros m. apply MUnionR. apply Hforall.
  - (* StarApp *)
    apply weak_pumping_star_aux; assumption.
Qed.

Theorem weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.
Proof.
  intros. apply weak_pumping_app_union; assumption.
Qed.

(* fim *)
