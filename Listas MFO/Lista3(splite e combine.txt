Require Export Coq.Lists.List.
Import ListNotations.

(** Lista 3 split e combine resolvida *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: combine tx ty
  end.

Fixpoint split {X Y : Type} (l : list (X*Y)) : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
      let '(lx, ly) := split t in (x :: lx, y :: ly)
  end.

Lemma eq_cons : forall (X:Type) (l1 l2: list X) (x: X),
  l1 = l2 -> x :: l1 = x :: l2.
Proof.
  intros X l1 l2 x H. rewrite H. reflexivity.
Qed.

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  induction l as [| [x y] t IH]; intros l1 l2 H.
  - simpl in H. inversion H. reflexivity.
  - simpl in H.
    destruct (split t) eqn:Hs. inversion H; subst.
    simpl. f_equal.
    apply IH. assumption.
Qed.

Theorem split_combine : forall X Y (l1 : list X) (l2 : list Y) (l : list (X*Y)),
  length l1 = length l2 -> combine l1 l2 = l -> split l = (l1, l2).
Proof.
  revert l2 l.
  induction l1 as [|x t IH]; intros l2 l Hlen Hcomb.
  - destruct l2; simpl in Hlen; try discriminate.
    simpl in Hcomb. inversion Hcomb; subst. reflexivity.
  - destruct l2 as [|y t2]; simpl in Hlen; try discriminate.
    simpl in Hcomb. inversion Hcomb; subst.
    simpl. f_equal.
    apply IH; auto.
Qed.
