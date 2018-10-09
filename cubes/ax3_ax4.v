Require Import List.
Require Import String.
Require Import Omega.
Require Import Cubes.axioms
        Cubes.sprop_utils
        Cubes.arith_lemmas
        Cubes.hott_lemmas
        Cubes.cubes
        Cubes.cubic_dec
        Cubes.cartesian
        Cubes.forcing_setup
        Cubes.interval
        Cubes.ax2.

Import MonadNotation.

(** Connection algebra structure *)

Definition join_arrow {p : nat} (f : 1 + 1 ~> p) : 1 ~> p.
  destruct (recover_word f) as [w H].
  pose (join_c (zero_finset 0)) as g.
  refine ( g o f.1s ; _ )s. apply spair_s with (a := join (zero_finset 0) w).
  apply eq_eqs. apply (f_equal (fun x => g o x)) in H. exact H.
Defined.

Definition meet_arrow {p : nat} (f : 1 + 1 ~> p) : 1 ~> p.
  destruct (recover_word f) as [w H].
  pose (meet_c (zero_finset 0)) as g.
  refine ( g o f.1s ; _ )s. apply spair_s with (a := meet (zero_finset 0) w).
  apply eq_eqs. apply (f_equal (fun x => g o x)) in H. exact H.
Defined.

Run TemplateProgram (tImplementTC ax2_TC "join_TC" "join_i" (I -> I -> I)).
Next Obligation.
  rename X into i1. rename X0 into i2.
  specialize (i1 p id). specialize (i2 p id).
  pose (fuse_arrows (i1, i2)). exact (join_arrow a).
Defined.

Run TemplateProgram (tImplementTC join_TC "meet_TC" "meet_i" (I -> I -> I)).
Next Obligation.
  rename X into i1. rename X0 into i2.
  specialize (i1 p id). specialize (i2 p id).
  pose (fuse_arrows (i1, i2)). exact (meet_arrow a).
Defined.

Notation "a ⊓ b" := (meet_i a b) (at level 65, left associativity).
Notation "a ⊔ b" := (join_i a b) (at level 65, left associativity).





(** Axiom 3 : computational behaviour of ⊓ *)

Theorem ax3 : forall i : I, I0 ⊓ i = I0 /\ i ⊓ I0 = I0 /\ I1 ⊓ i = i /\ i ⊓ I1 = i.
Admitted.

Definition ax3_TC := meet_TC.





(** Axiom 4 : computational behaviour of ⊔ *)

Run TemplateProgram (tImplementTC ax3_TC "ax4_1_TC" "ax4_1" (forall i : I, I0 ⊔ i = i)).
Next Obligation.
  assert ((fun (p0 : nat) (α : p ~> p0) => join_iᵗ p0 (fun (p1 : nat) (_ : p0 ~> p1) => I0ᵗ p1) (fun (p1 : nat) (α0 : p0 ~> p1) => i p1 (id ô α0 ô (id ô α ô id)))) = (fun (p0 : nat) (α : p ~> p0) => i p0 (id ô (id ô α ô id)))).
  apply funext_dep. intro q. apply funext_dep. intro α.
  unfold join_iᵗ. unfold join_iᵗ_obligation_1.
  apply eq_sexist.
  apply funext. intro c.
  apply funext. intros [x px].
  destruct x.
  - replace (join_arrow (fuse_arrows (I0ᵗ q, i q (id ô id ô (id ô α ô id))))).1s with (join_c (zero_finset 0) o (fuse_arrows (I0ᵗ q, i q α)).1s).
    + Transparent fuse_cube_maps.
      compute.
      match goal with
      | [ |- _ _ (exist _ 0 ?XX) = _ _ (exist _ 0 px) ] => erewrite (Peano_dec.le_unique _ _ XX px)
      end. reflexivity.
    + unfold join_arrow.
      destruct (recover_word (fuse_arrows (I0ᵗ q, i q (id ô id ô (id ô α ô id))))). reflexivity.
  - assert False. easy. inversion H.
  - rewrite H. apply eq_reflᵗ.
Defined.


Theorem ax4 : forall i : I, I0 ⊔ i = i /\ i ⊔ I0 = i /\ I1 ⊔ i = I1 /\ i ⊔ I1 = I1.
  intro i. split.
  exact (ax4_1 i).
  admit.
Admitted.

Definition ax4_TC := ax4_1_TC.
