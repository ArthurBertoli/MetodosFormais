Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.PeanoNat.

(** * Lista de Exercícios 3 — listas e polimorfismo resolvida *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** Prova de length (l1 ++ l2) = length l1 + length l2 *)
Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1; intros; simpl.
  - reflexivity.
  - rewrite IHl1. reflexivity.
Qed.

(** Prova rev (l1 ++ l2) = rev l2 ++ rev l1 *)
Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  induction l1; intros; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.

(** Prova de fold com concatenação *)
Theorem app_comm_fold :forall {X Y} (f: X->Y->Y) l1 l2 b,
  fold f (l1 ++ l2) b = fold f l1 (fold f l2 b).
Proof.
  induction l1; intros; simpl.
  - reflexivity.
  - rewrite IHl1. reflexivity.
Qed.

(** fold_length *)
Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Lemma fold_length_head : forall X (h : X) (t : list X),
  fold_length (h::t) = S (fold_length t).
Proof.
  intros. simpl. reflexivity.
Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite fold_length_head. rewrite IHl. reflexivity.
Qed.

(** fold_map *)
Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y :=
  fold (fun h t => f h :: t) l [].

Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

(** foldl — versão esquerda para direita *)
Fixpoint foldl {X Y: Type} (f: Y->X->Y) (b: Y) (l: list X) : Y :=
  match l with
  | [] => b
  | h::t => foldl f (f b h) t
  end.

Example test_foldl : foldl minus 10 [1; 2; 3] = 4.
Proof. reflexivity. Qed.
