Require Export Arith.

(** Lista 6 Operadores Relacionais resolvida*)


Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. apply le_0_n.
Qed.

Print le_n.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. apply le_S. assumption.
Qed.

Lemma n_le_m__Sn_le_Sm' : forall a b, a <= b -> S a <= S b.
Proof.
  intros a b H. apply le_S. assumption.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H.
  inversion H.
  - apply le_0_n.
  - assumption.
Qed.

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. eapply le_trans; eassumption.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b.
  induction b.
  - simpl. apply le_n.
  - simpl. apply le_S. assumption.
Qed.

Theorem lt_ge_cases : forall n m,
  n < m \/ n >= m.
Proof.
  intros n m. unfold ge.
  destruct (le_gt_dec m n).
  - right. assumption.
  - left. assumption.
Qed.

Inductive le' : nat -> nat -> Prop :=
  | le_0' m : le' 0 m
  | le_S' n m (H : le' n m) : le' (S n) (S m).

Lemma n_le'_m__Sn_le'_Sm : forall a b, le' a b -> le' (S a) (S b).
Proof.
  intros a b H. apply le_S'. assumption.
Qed.

Lemma le'_n_n : forall a, le' a a.
Proof.
  induction a.
  - constructor.
  - apply le_S'. assumption.
Qed.

Lemma le'_n_Sm : forall a b, le' a b -> le' a (S b).
Proof.
  intros a b H.
  induction H.
  - constructor.
  - apply le_S'. assumption.
Qed.

Theorem le_le' : forall a b, le a b <-> le' a b.
Proof.
  split.
  - intros H. induction H.
    + apply le_0'.
    + apply le_S'. assumption.
  - intros H. induction H.
    + apply le_0_n.
    + apply le_n_S. assumption.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m H.
  split.
  - apply (lt_le_trans _ (n1 + n2)).
    + apply lt_n_Sm. rewrite <- plus_n_O. apply le_plus_l.
    + apply lt_le_trans with (m:=m).
      * assumption.
      * apply le_n.
  - apply (lt_le_trans _ (n1 + n2)).
    + rewrite plus_comm. apply lt_n_Sm. rewrite <- plus_n_O. apply le_plus_l.
    + apply lt_le_trans with (m:=m); auto with arith.
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros n m H. apply lt_n_S. assumption.
Qed.
