Require Export Coq.Lists.List.
Import ListNotations.

(** Lista 5 lógica resolvida *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  intros X P H [x Hn].
  apply Hn. apply H.
Qed.

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q. split.
  - intros [x [HP | HQ]].
    + left. exists x. exact HP.
    + right. exists x. exact HQ.
  - intros [[x HP] | [x HQ]].
    + exists x. left. exact HP.
    + exists x. right. exact HQ.
Qed.

Theorem dist_exists_and : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x /\ Q x) -> (exists x, P x) /\ (exists x, Q x).
Proof.
  intros X P Q [x [HP HQ]]. split; [exists x | exists x]; assumption.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x H. induction l as [|h t IH].
  - simpl in H. contradiction.
  - simpl in H. simpl. destruct H as [Heq | Hin].
    + left. rewrite Heq. reflexivity.
    + right. apply IH. assumption.
Qed.

Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  - induction l as [|h t IH]; simpl.
    + intros H. contradiction.
    + simpl. intros H. destruct H as [Heq | Hin].
      * exists h. split; [assumption | left; reflexivity].
      * apply IH in Hin. destruct Hin as [x [Hfx Hinx]].
        exists x. split; [assumption | right; assumption].
  - intros [x [Hfx Hinx]]. induction l as [|h t IH]; simpl in *.
    + contradiction.
    + destruct Hinx as [Heq | Hin].
      * subst. left. assumption.
      * right. apply IH. exists x. split; assumption.
Qed.

Lemma In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a. split.
  - induction l as [|h t IH]; simpl.
    + intros H. right. assumption.
    + intros H. simpl in H. destruct H as [Heq | Hin].
      * left. left. assumption.
      * apply IH in Hin. destruct Hin as [Hl | Hr]; [left; right; assumption | right; assumption].
  - induction l as [|h t IH]; simpl.
    + intros H. assumption.
    + intros [ [Heq | Hin] | Hr].
      * left. left. assumption.
      * left. right. apply IH. left; assumption.
      * right. assumption.
Qed.

Theorem excluded_middle_irrefutable: forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  intros P H. apply H. right. intro HP. apply H. left. exact HP.
Qed.

Theorem disj_impl : forall (P Q: Prop),
 (~P \/ Q) -> P -> Q.
Proof.
  intros P Q H Ptrue. destruct H as [nP | Qtrue].
  - exfalso. apply nP. assumption.
  - assumption.
Qed.

Theorem Peirce_double_negation: forall (P:Prop), (forall R S: Prop,
  (((R->S)->R)->R)) -> (~~ P -> P).
Proof.
  intros P Hclass NN.
  specialize (Hclass P False) as H.
  apply H. intro n. exfalso. apply NN. assumption.
Qed.

Theorem double_negation_excluded_middle : forall (P:Prop),
  (forall (R:Prop), (~~ R -> R)) -> (P \/ ~P).
Proof.
  intros P H.
  apply H. apply excluded_middle_irrefutable.
Qed.
