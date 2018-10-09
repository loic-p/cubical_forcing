Require Import Omega.
Require Import Cubes.axioms
        Cubes.sprop_utils
        Cubes.arith_lemmas
        Cubes.hott_lemmas
        Cubes.cubes
        Cubes.cubic_dec.

(** Cartesian structure *)

(* based on the decidability part. This actually only requires the category of cubes having contractions *)

Definition fuse_cube_maps {a b c : nat} : (cube a -> cube b) * (cube a -> cube c) -> (cube a -> cube (b + c)).
  intros [f g] d [x p].
  destruct (le_lt_dec b x).
  - assert (x - b < c). apply le_plus_n with (p := b). rewrite add_S.
    rewrite <- Minus.le_plus_minus. exact p. exact l.
    apply (g d). exists (x - b). exact H.
  - apply (f d). exists x. exact l.
Defined.

Theorem fused_monotone {a b c : nat} (f : cube a -> cube b) (g : cube a -> cube c) :
  monotone f -> monotone g -> monotone (fuse_cube_maps (f, g)).
Proof.
  intros Hf Hg d e Hde [x Hx]. simpl.
  destruct (le_lt_dec b x).
  - apply Hg. exact Hde.
  - apply Hf. exact Hde.
Qed.

Definition fuse_arrows {a b c : nat} : (a ~> c) * (b ~> c) -> (a + b ~> c).
  intros [f g].
  refine ( fuse_cube_maps (f.1s, g.1s) ; _ )s.
  pose proof (arrow_monotone f). pose proof (arrow_monotone g).
  assert (admissible' (fuse_cube_maps (f.1s, g.1s))).
  apply adm_if_monotone. now apply fused_monotone.
  destruct H1 as [w H1].
  eapply spair_s. apply eq_eqs. exact H1.
Defined.

Definition split_cube_map {a b c : nat} : (cube a -> cube (b + c)) -> (cube a -> cube b) * (cube a -> cube c).
  intro f. split.
  - intros d [x p]. apply (f d). exists x. omega.
  - intros d [x p]. apply (f d). exists (b + x). unfold lt. rewrite <- add_S.
    apply Plus.plus_le_compat_l. exact p.
Defined.

Theorem splitted_monotone {a b c : nat} (f : cube a -> cube (b + c)) :
  monotone f -> monotone (fst (split_cube_map f)) /\ monotone (snd (split_cube_map f)).
Proof.
  intro Hf. split ; intros d e Hde [x Hx] ; simpl ; apply Hf ; exact Hde.
Qed.

Definition split_arrow {a b c : nat} : (a + b ~> c) -> (a ~> c) * (b ~> c).
  intro f. split.
  - refine ( fst (split_cube_map f.1s) ; _ )s.
    pose proof (arrow_monotone f). destruct (splitted_monotone f.1s H) as [H1 _].
    assert (admissible' (fst (split_cube_map f.1s))). apply adm_if_monotone. exact H1.
    destruct H0 as [w H0]. eapply spair_s. apply eq_eqs. exact H0.
  - refine ( snd (split_cube_map f.1s) ; _ )s.
    pose proof (arrow_monotone f). destruct (splitted_monotone f.1s H) as [_ H1].
    assert (admissible' (snd (split_cube_map f.1s))). apply adm_if_monotone. exact H1.
    destruct H0 as [w H0]. eapply spair_s. apply eq_eqs. exact H0.
Defined.

Theorem cartesian_lemma1 {a b c : nat} : forall f : cube a -> cube (b + c), fuse_cube_maps (split_cube_map f) = f.
  intro f.
  apply funext. intro d.
  apply funext. intros [x p].
  simpl. destruct (le_lt_dec b x).
  - assert (forall p' : b + (x - b) < b + c, exist (fun m : nat => m < b + c) (b + (x - b)) p' = exist (fun m : nat => m < b + c) x p).
    rewrite <- Minus.le_plus_minus. intro p'. rewrite (Peano_dec.le_unique (S x) (b + c) p p'). reflexivity.
    exact l.
    rewrite H. reflexivity.
  - erewrite (Peano_dec.le_unique _ _ _ p). reflexivity.
Qed.

Theorem cartesian_lemma2 {a b c : nat}
  : forall (f : cube a -> cube b) (g : cube a -> cube c), split_cube_map (fuse_cube_maps (f, g)) = (f, g).
  intros f g. apply injective_projections.
  - apply funext. intro d.
    apply funext. intros [x p].
    simpl. destruct (le_lt_dec b x).
    + assert False. omega. inversion H.
    + erewrite (Peano_dec.le_unique _ _ l p). reflexivity.
  - apply funext. intro d.
    apply funext. intros [x p].
    simpl. destruct (le_lt_dec b (b + x)).
    + assert (forall p' : b + x - b < c, exist (fun m : nat => m < c) (b + x - b) p' = exist (fun m : nat => m < c) x p).
      replace (b + x - b) with x. intro p'. erewrite (Peano_dec.le_unique _ _ p p'). reflexivity.
      omega.
      rewrite H. reflexivity.
    + assert False. omega. inversion H.
Qed.

Theorem cartesian_iso1 {a b c : nat} : fuse_arrows o split_arrow = fun x : a + b ~> c => x.
Proof.
  apply funext. intro f. apply eq_sexist.
  Opaque fuse_cube_maps. Opaque split_cube_map. simpl.
  rewrite <- (surjective_pairing (split_cube_map f.1s)).
  apply cartesian_lemma1.
Qed.

Theorem cartesian_iso2 {a b c : nat} : split_arrow o fuse_arrows = fun x : (a ~> c) * (b ~> c) => x.
Proof.
  apply funext. intros [f g]. apply injective_projections.
  - apply eq_sexist. compute.
    pose proof (cartesian_lemma2 f.1s g.1s).
    apply (f_equal fst) in H. exact H.
  - apply eq_sexist. compute.
    pose proof (cartesian_lemma2 f.1s g.1s). apply (f_equal snd) in H. exact H.
Qed.
