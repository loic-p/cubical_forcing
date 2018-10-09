Require Import Coq.Arith.Minus.

(** Redefinition of simple arithmetic *)

(* The definitions already present in the standard library are very complicated and take ages to quote *)

Theorem le_0_n : forall n, 0 <= n.
Proof.
  intro n. induction n.
  - apply le_n.
  - apply le_S. exact IHn.
Qed.

Theorem lt_0_succ : forall n, 0 < S n.
Proof.
  intro n. induction n.
  - now apply le_n.
  - apply le_S. exact IHn.
Qed.

Theorem pos_ge_0 : forall n, S n <= 0 -> False.
Proof.
  intros n H. inversion H.
Qed.

Theorem le_S_n : forall n m, S n <= S m -> n <= m.
Proof.
  intros n m. revert n. induction m.
  - intros n H. inversion H.
    + apply le_n.
    + apply pos_ge_0 in H1. destruct H1.
  - intros n H. inversion H.
    + apply le_n.
    + apply IHm in H1. apply le_S. exact H1.
Qed.

Theorem le_n_S : forall n m, n <= m -> S n <= S m.
Proof.
  intros n m. revert n. induction m.
  - intros n H. inversion H. apply le_n.
  - intros n H. inversion H.
    + apply le_n.
    + apply le_S. now apply IHm.
Qed.

Theorem add_0_r : forall n, n + 0 = n.
Proof.
  intro n. induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_S : forall n m : nat, n + S m = S (n + m).
Proof.
  intro n. induction n.
  - intro m. reflexivity.
  - intro m. simpl. rewrite IHn. reflexivity.
Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  intro n. induction n.
  - intro m. rewrite (add_0_r m). reflexivity.
  - intro m. simpl. rewrite IHn. rewrite add_S. reflexivity.
Qed.

Theorem le_plus_n : forall n m p, p + n <= p + m -> n <= m.
Proof.
  intros n m. induction p.
  - intro H. exact H.
  - intro H. simpl in H. apply le_S_n in H. exact (IHp H).
Qed.

Definition le_imp_eq_lt : forall n m : nat, n <= m -> (n = m) + (n < m).
  intro n. induction n.
  - intros m H. destruct m.
    + left. reflexivity.
    + right. apply lt_0_succ.
  - intros m H. destruct m.
    + apply pos_ge_0 in H. destruct H.
    + destruct (IHn m).
      * now apply le_S_n.
      * rewrite e. left. reflexivity.
      * right. now apply le_n_S.
Defined.

Definition lt_eq_lt_dec :  forall n m : nat, {n < m} + {n = m} + {m < n}.
  intros n m. induction m.
  - assert (0 <= n). apply le_0_n. apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + now right.
  - destruct IHm as [[H | H] | H].
    + left. left. now apply le_S.
    + rewrite H. left. left. now apply le_n.
    + apply le_imp_eq_lt in H. destruct H.
      * left. right. now rewrite e.
      * right. exact l.
Defined.

Definition le_lt_dec : forall n m : nat, {n <= m} + {m < n}.
  intros n m. destruct (lt_eq_lt_dec n m) as [[H | H] | H].
  - left. apply le_S_n. apply le_S. exact H.
  - left. rewrite H. apply le_n.
  - right. exact H.
Defined.

Definition lt_eq_lt_dec' :  forall n m : nat, {n < m} + {n = m} + {m < n}.
  intros n m. induction n.
  - assert (0 <= m). apply le_0_n. apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + left. now left.
  - destruct IHn as [[H | H] | H].
    + apply le_imp_eq_lt in H. destruct H.
      * left. right. exact e.
      * left. left. exact l.
    + rewrite H. right. now apply le_n.
    + right. now apply le_S.
Defined.

Definition lt_eq_eq_lt_dec (m n : nat) : {m < n} + {m = n} + {m = S n} + {m > S n}.
Proof.
  destruct (lt_eq_lt_dec m n) as [[H | H] | H].
  - left. left. now left.
  - left. left. now right.
  - apply le_imp_eq_lt in H. destruct H.
    + left. now right.
    + right. exact l.
Defined.

Theorem le_trans : forall n m p, n <= m -> m <= p -> n <= p.
Proof.
  intros n m p. revert n m. induction p.
  - destruct m.
    + trivial.
    + intros H H'. apply pos_ge_0 in H'. destruct H'.
  - intros n m H. destruct m, n.
    + intro H'. apply le_0_n.
    + apply pos_ge_0 in H. destruct H.
    + intro H'. apply le_0_n.
    + intro H'. apply le_S_n in H. apply le_S_n in H'. apply le_n_S.
      eapply IHp. apply H. exact H'.
Qed.

Theorem sub_add_S {a b c : nat} : S b <= a -> a - S b + S c = a - b + c.
Proof.
  revert c. induction b.
  - intros c H. destruct a.
    + inversion H.
    + simpl. rewrite <- Minus.minus_n_O. apply add_S.
  - intros c H. destruct a.
    + inversion H.
    + simpl. apply eq_add_S.
      change (S (a - S b + S c)) with (S (a - S b) + S c). erewrite Minus.minus_Sn_m.
      change (S (a - b + c)) with (S (a - b) + c). erewrite Minus.minus_Sn_m.
      apply IHb.
      * apply le_S_n. eapply le_trans. exact H. apply le_S. apply le_n.
      * apply le_S_n. apply le_S_n. eapply le_trans. exact H. apply le_S. apply le_n.
      * now apply le_S_n.
Qed.

Theorem sub_sub {a b c : nat} : b <= a -> c <= b -> a - (b - c) = a - b + c.
Proof.
  revert c. induction b.
  - intros c Hb Hc. inversion Hc. easy.
  - intros c Hb Hc. destruct c.
    + simpl. easy.
    + simpl. erewrite IHb.
      * symmetry. apply sub_add_S. exact Hb.
      * apply le_S_n. eapply le_trans. exact Hb. apply le_S. apply le_n.
      * apply le_S_n. exact Hc.
Qed.