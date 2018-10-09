Require Import Omega.
Require Import Cubes.axioms
        Cubes.sprop_utils
        Cubes.arith_lemmas
        Cubes.hott_lemmas
        Cubes.cubes.



(** Decidability of a function being cubic *)

(* uses the fact that for the full category of cubes, being admissible is the same as being monotone *)
(* WIP *)

Definition zero_finset (p : nat) : finset (S p).
  exists 0. omega.
Defined.

Definition unique : cube 0.
  unfold cube. unfold finset. intros [m H]. apply pos_ge_0 in H. inversion H.
Defined.

Definition cube_le {a : nat} (c d : cube a) : Prop :=
  forall x : finset a, (c x = true) -> (d x = true).

Definition monotone {a b : nat} (f : cube a -> cube b) :=
  forall c d : cube a, cube_le c d -> cube_le (f c) (f d).

Definition extend_cube {a : nat} (c : cube a) (b : bool) : cube (S a).
  intros [i p]. destruct i.
  - exact b.
  - apply le_S_n in p. apply c. exists i. exact p.
Defined.

Definition restr_map {a : nat} (f : cube (S a) -> cube 1) (b : bool) : cube a -> cube 1 :=
  fun x : cube a => f (extend_cube x b).

Theorem monotone_restr {a : nat} (f : cube (S a) -> cube 1) (b : bool) (H : monotone f)
  : monotone (restr_map f b).
Proof.
  intros c d H1. apply H.
  intros [x p]. destruct x.
  - easy.
  - simpl. apply H1.
Qed.

Definition fuse_cube {a b : nat} : (cube a) * (cube b) -> cube (a + b).
  intros [c d] [p i]. destruct (Compare_dec.le_lt_dec a p).
  - assert (p - a < b). omega.
    apply d. exists (p - a). exact H.
  - apply c. exists p. exact l.
Defined.

Definition split_cube {a b : nat} : cube (a + b) -> (cube a) * (cube b).
  intro c. split.
  - intros [x p]. apply c. exists x. omega.
  - intros [x p]. apply c. exists (x + a). omega.
Defined.

Fixpoint dup_word_aux1 {a : nat} (b : nat) (c : nat) (Hb : b <= a) (Hc : c <= b) : word (S b + a) (S b + a).
  destruct c.
  - exact empty.
  - simpl. apply exch.
    + exists (a - b + c). destruct b.
      * inversion Hc.
      * rewrite <- sub_sub. apply le_trans with (m := S a).
        -- apply le_n_S. apply PeanoNat.Nat.le_sub_l.
        -- simpl. apply le_n_S. omega.
        -- exact Hb.
        -- apply le_S. apply le_S_n. exact Hc.
    + apply (dup_word_aux1 a b c Hb). omega.
Defined.

Definition dup_map_aux1 {a : nat} (b : nat) (c : nat) (Hb : b <= a) (Hc : c <= b) : cube (S b + a) -> cube (S b + a).
  intro d. intros [x Hx].
  destruct (lt_eq_lt_dec (a - b + c) x) as [[H | H] | H].
  - apply d. exists x. exact Hx.
  - apply d. exists (a - b). apply le_trans with (m := S (a - b + c)).
    + apply le_n_S. apply Plus.le_plus_l.
    + rewrite H. exact Hx.
  - destruct (le_lt_dec (a - b) x).
    + apply d. exists (S x). simpl. apply le_n_S. eapply le_trans.
      * exact H.
      * apply le_trans with (m := a + c). apply Plus.plus_le_compat_r. apply PeanoNat.Nat.le_sub_l.
        rewrite add_comm. apply Plus.plus_le_compat_r. exact Hc.
    + apply d. exists x. exact Hx.
Defined.

Theorem dup_adm_aux1 {a : nat} (b : nat) (c : nat) (Hb : b <= a) (Hc : c <= b)
  : comp_word (dup_word_aux1 b c Hb Hc) = dup_map_aux1 b c Hb Hc.
Proof.
  revert Hc. induction c.
  - intro Hc. apply funext. intro d. apply funext. intros [x Hx]. simpl.
    destruct (lt_eq_lt_dec (a - b + 0) x) as [[H | H] | H].
    + easy.
    + pose H as H'. clearbody H'. rewrite add_0_r in H'. apply f_equal.
      apply eq_finset. simpl. symmetry. exact H'.
    + destruct (le_lt_dec (a - b) x).
      * assert False. omega. inversion H0.
      * reflexivity.
  - intro Hc. apply funext. intro d. apply funext. intros [x Hx]. simpl. rewrite IHc.
    match goal with
    | |- (?FF o ?GG) ?XX ?YY = _ => change ((FF o GG) XX) with (FF (GG XX))
    end. unfold dup_map_aux1.
    destruct (lt_eq_lt_dec (a - b + S c) x) as [[H | H] | H].
    + destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[H1 | H1] | H1].
      * assert False. destruct H1 ; omega. inversion H0.
      * omega.
      * destruct (lt_eq_lt_dec (a - b + c) x) as [[H2 | H2] | H2].
        -- reflexivity.
        -- omega.
        -- omega.
    + destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[[H1 | H1] | H1] | H1].
      * omega.
      * omega.
      * destruct (lt_eq_lt_dec (a - b + c) (a - b + c)) as [[H2 | H2] | H2].
        -- omega.
        -- apply f_equal. apply eq_finset. simpl. reflexivity.
        -- omega.
      * omega.
    + destruct (le_lt_dec (a - b) x).
      * destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[[H1 | H1] | H1] | H1].
        -- destruct (lt_eq_lt_dec (a - b + c) x) as [[H2 | H2] | H2].
           ++ omega.
           ++ omega.
           ++ apply f_equal. apply eq_finset. simpl. reflexivity.
        -- destruct (lt_eq_lt_dec (a - b + c) (S (a - b + c))) as [[H2 | H2] | H2].
           ++ apply f_equal. apply eq_finset. simpl. omega.
           ++ omega.
           ++ omega.
        -- omega.
        -- omega.
      * destruct (lt_eq_eq_lt_dec x (a - b + c)) as [[[H1 | H1] | H1] | H1].
        -- destruct (lt_eq_lt_dec (a - b + c) x) as [[H2 | H2] | H2].
           ++ omega.
           ++ omega.
           ++ reflexivity.
        -- omega.
        -- omega.
        -- omega.
Qed.

Fixpoint dup_word_aux2 {a : nat} (b : nat) (Hb : b <= a) : word a (b + a).
  destruct b.
  - exact empty.
  - eapply concat_word.
    + apply (dup_word_aux1 b b). omega. apply le_n.
    + simpl. apply contr.
      * exists (a - (S b)). eapply PeanoNat.Nat.le_trans.
        -- apply PeanoNat.Nat.sub_lt. exact Hb.
           omega.
        -- rewrite add_comm. exact (PeanoNat.Nat.le_add_r a b).
      * apply (dup_word_aux2 a b). omega.
Defined.

Definition dup_map_aux2 {a : nat} (b : nat) (Hb : b <= a) : cube a -> cube (b + a).
  intros d [x Hx].
  destruct (le_lt_dec a x).
  - apply d. exists (x - b). apply le_plus_n with (p := b). rewrite add_S. rewrite <- Minus.le_plus_minus.
    + exact Hx.
    + eapply le_trans. exact Hb. exact l.
  - apply d. exists x. exact l.
Defined.

Theorem dup_adm_aux2 {a : nat} (b : nat) (Hb : b <= a) : comp_word (dup_word_aux2 b Hb) = dup_map_aux2 b Hb.
Proof.
  revert Hb. induction b.
  - intro H. apply funext. intro d. apply funext. intros [x Hx].
    simpl. destruct (le_lt_dec a x).
    + omega.
    + apply f_equal. apply eq_finset. simpl. reflexivity.
  - intro Hb. apply funext. intro d. apply funext. intros [x Hx]. simpl.
    rewrite <- concat_sound.
    unfold fcompose. etransitivity. refine (apD10 _ _ _ _). refine (apD10 _ _ _ _).
    apply dup_adm_aux1. cbn. rewrite IHb. cbn. destruct (le_lt_dec a x).
    + destruct (lt_eq_lt_dec (a - b + b) x) as [[H | H] | H].
      * destruct (lt_eq_eq_lt_dec x (a - S b)) as [[[H1 | H1] | H1] | H1].
        -- omega.
        -- omega.
        -- omega.
        -- destruct x.
           ++ omega.
           ++ simpl. destruct (le_lt_dec a x).
              ** apply f_equal. apply eq_finset. simpl. reflexivity.
              ** omega.
      * destruct (lt_eq_eq_lt_dec (a - b) (a - S b)) as [[[H1 | H1] | H1] | H1].
        -- omega.
        -- omega.
        -- destruct (le_lt_dec a (a - S b)).
           ++ omega.
           ++ apply f_equal. apply eq_finset. simpl. omega.
        -- omega.
      * omega.
    + destruct (lt_eq_lt_dec (a - b + b) x) as [[H | H] | H].
      * omega.
      * omega.
      * destruct (le_lt_dec (a - b) x).
        -- destruct (lt_eq_eq_lt_dec (S x) (a - S b)) as [[[H1 | H1] | H1] | H1] ; try reflexivity ; omega.
        -- destruct (lt_eq_eq_lt_dec x (a - S b)) as [[[H1 | H1] | H1] | H1].
           ++ reflexivity.
           ++ destruct (le_lt_dec a (a - S b)).
              ** omega.
              ** apply f_equal. apply eq_finset. simpl. omega.
           ++ omega.
           ++ omega.
Qed.

Definition dup_word (a : nat) : word a (a + a).
  apply dup_word_aux2. omega.
Defined.

Definition dup_map (a : nat) : cube a -> cube (a + a).
  intros d [x Hx].
  destruct (le_lt_dec a x).
  - apply d. exists (x - a). apply le_plus_n with (p := a). rewrite add_S. rewrite <- Minus.le_plus_minus.
    + exact Hx.
    + exact l.
  - apply d. exists x. exact l.
Defined.

Theorem dup_adm (a : nat) : comp_word (dup_word a) = dup_map a.
Proof.
  unfold dup_word. rewrite dup_adm_aux2.
  apply funext. intro d. apply funext. intros [x Hx].
  simpl. destruct (le_lt_dec a x).
  - apply f_equal. apply eq_finset. simpl. reflexivity.
  - reflexivity.
Qed.

Fixpoint tensor_word_aux {a b} c d (w : word a b) : word (c + a + d) (c + b + d).
  destruct w.
  - exact empty.
  - apply degen.
    + destruct f as [x Hx]. exists (c + x). apply le_n_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. apply le_S_n. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - refine (transport (fun X => word _ (X + d)) (sym (add_S _ _)) _). simpl. apply face.
    + destruct f as [x Hx]. exists (c + x). apply le_n_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. apply le_S_n. assumption. apply Nat.le_add_r.
    + exact b0.
    + exact (tensor_word_aux a b c d w).
  - apply meet.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - apply join.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - refine (transport (fun X => word _ (X + d)) (sym (add_S _ _)) _). simpl. apply exch.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + refine (transport (fun X => word _ (X + d)) (add_S _ _) _). exact (tensor_word_aux a (S b) c d w).
  - refine (transport (fun X => word _ (X + d)) (sym (add_S _ _)) _). simpl. apply contr.
    + destruct f as [x Hx]. exists (c + x). unfold lt. rewrite <- add_S. apply le_trans with (m := c + b).
      apply Plus.plus_le_compat_l. assumption. apply Nat.le_add_r.
    + exact (tensor_word_aux a b c d w).
Defined.

Definition tensor_map_aux {a b} c d (f : cube a -> cube b) : cube (c + a + d) -> cube (c + b + d).
  intros γ [x Hx].
  destruct (le_lt_dec c x).
  - destruct (le_lt_dec (c + b) x).
    + apply γ. exists (x - b + a). rewrite <- Nat.add_assoc. rewrite (add_comm a d). rewrite Nat.add_assoc.
      apply plus_lt_compat_r. apply le_plus_n with (p := b).
      rewrite add_comm. simpl. rewrite Nat.sub_add. rewrite add_comm. rewrite <- Nat.add_assoc.
      rewrite (add_comm d b). rewrite Nat.add_assoc. exact Hx. apply le_trans with (m := c + b).
      apply le_plus_r. exact l0.
    + apply f.
      * intros [y Hy]. apply γ. exists (c + y). apply le_trans with (m := c + a).
        apply Plus.plus_lt_compat_l. exact Hy. apply Nat.le_add_r.
      * exists (x - c). eapply le_plus_n with (p := c). apply le_trans with (m := S x). rewrite add_S. apply le_n_S.
      rewrite <- Minus.le_plus_minus. apply le_n. exact l. exact l0.
  - apply γ. exists x. apply PeanoNat.Nat.lt_lt_add_r. apply PeanoNat.Nat.lt_lt_add_r. exact l.
Defined.

Lemma transport_finset {a b x : nat} {e : a = b} (f : nat -> nat) {H : x < f a} :
  transport (fun X : nat => finset (f X)) e (exist (fun m => m < f a) x H) = exist _ x (transport (fun m => x < f m) e H).
Proof.
  destruct e. reflexivity.
Qed.

Theorem tensor_adm_aux {a b c d} (w : word a b) : comp_word (tensor_word_aux c d w) = tensor_map_aux c d (comp_word w).
Proof.
  revert c d. induction w ; intros c d ; apply funext ; intro γ ; apply funext ; intros [x Hx] ; simpl.
  { destruct (le_lt_dec c x). destruct (le_lt_dec (c + a) x).
    all: apply f_equal ; apply eq_finset ; simpl ; omega. }
  all: destruct f as [y Hy].
  - unfold fcompose. etransitivity.
    { refine (apD10 _ _ _ _). apply f_equal. refine (apD10 _ _ _ γ).
      refine (ap_transport _ _ (e := add_S c b) (fun X Y => comp_word (b := X + d) Y)). }
    cbn. rewrite IHw. rewrite transport_codomain.
    destruct (lt_eq_lt_dec x (c + y)) as [[H | H] | H].
    all: etransitivity ; [ refine (transport_domain _) | ].
    all: etransitivity ; [ refine (f_equal _ _) ; refine (transport_finset (fun X => X + d)) | ].
    all: unfold tensor_map_aux.
    all: repeat match goal with
    | |- context [ match ?d with _ => _ end ] =>
      destruct d
    end.
    all: try (f_equal ; apply eq_finset ; simpl ; try (destruct c) ; omega).
    all: try omega.
  (** * Now all other cases should be roughly the same *)
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Definition tensor_word {a b a' b'} (w : word a b) (w' : word a' b') : word (a + a') (b + b').
  eapply concat_word.
  - exact (tensor_word_aux 0 b' w).
  - simpl. refine (transport (fun X => word X (a + b')) (add_0_r (a + a')) _).
    refine (transport (fun X => word (a + a' + 0) X) (add_0_r (a + b')) _).
    exact (tensor_word_aux a 0 w').
Defined.

Definition tensor_map {a b a' b'} (w : cube a -> cube b) (w' : cube a' -> cube b') : cube (a + a') -> cube (b + b').
  intros d [x Hx].
  destruct (le_lt_dec b x).
  - apply w'.
    + intros [y Hy]. apply d. exists (a + y). apply plus_lt_compat_l. exact Hy.
    + exists (x - b). apply plus_lt_reg_l with (p := b). rewrite le_plus_minus_r ; assumption.
  - apply w.
    + intros [y Hy]. apply d. exists y. apply Nat.lt_lt_add_r. exact Hy.
    + exists x. exact l.
Defined.

Lemma transport_cube {a b : nat} {e : a = b} (c : cube a) (d : finset b)
  : transport cube e c d = c (transport finset (sym e) d).
Proof.
  destruct e. reflexivity.
Qed.

Lemma transport_cube' {a b x : nat} {e : a = b} (c : cube a) (H : x < b)
  : transport cube e c (exist (fun m => m < b) x H) = c (exist _ x (transport (fun m => x < m) (sym e) H)).
Proof.
  destruct e. reflexivity.
Qed.

Theorem tensor_adm {a b a' b'} (w : word a b) (w' : word a' b')
  : comp_word (tensor_word w w') = tensor_map (comp_word w) (comp_word w').
Proof.
  unfold tensor_word. rewrite <- concat_sound.
  unfold fcompose. apply funext. intro d. etransitivity.
  { match goal with
    | |- ?XX ?YY ?ZZ = _ => refine (apD10 _ _ _ ZZ)
    end. refine (tensor_adm_aux _). }
  etransitivity.
  { apply f_equal. refine (apD10 _ _ _ d). etransitivity.
    refine (ap_transport _ _ (fun X Y => comp_word (a := X) Y)). apply f_equal. etransitivity.
    refine (ap_transport _ _ (fun X Y => comp_word (b := X) Y)). apply f_equal. refine (tensor_adm_aux _). }
  etransitivity.
  { apply f_equal. etransitivity. apply transport_domain.
    set (y := (transport cube (sym (add_0_r (a + a'))) d)). apply transport_codomain. }
  apply funext. intros [x Hx]. simpl.
  destruct (le_lt_dec 0 x) ; try omega. unfold tensor_map_aux. destruct (le_lt_dec b x).
  - etransitivity. apply transport_cube'. destruct (le_lt_dec a (x - b + a)) ; try omega.
    destruct (le_lt_dec (a + b') (x - b + a)) ; try omega. f_equal.
    + apply funext. intros [y Hy]. etransitivity. apply transport_cube'. f_equal.
      apply eq_finset. simpl. reflexivity.
    + apply eq_finset. simpl. omega.
  - f_equal.
    + apply funext. intros [y Hy]. etransitivity. apply transport_cube'. destruct (le_lt_dec a y) ; try omega.
      etransitivity. apply transport_cube'. f_equal. apply eq_finset. simpl. reflexivity.
    + apply eq_finset. simpl. omega.
Qed.

Definition product_word {a b b'} (w : word a b) (w' : word a b') : word a (b + b').
  eapply concat_word.
  - exact (tensor_word w w').
  - exact (dup_word a).
Defined.

(* Definition product_map {a b b'} (f : cube a -> cube b) (g : cube ) *)

Definition binary_and_word : word 2 1.
  apply meet.
  - exact (zero_finset 0).
  - exact empty.
Defined.

Definition binary_and_map : cube 2 -> cube 1.
  intros d x. apply andb.
  - apply d. exact (zero_finset 1).
  - apply d. exists 1. omega.
Defined.

Theorem binary_and_adm : comp_word (binary_and_word) = binary_and_map.
Proof.
  apply funext. intro d. apply funext. intros [x Hx]. simpl. unfold fcompose.
  destruct x ; try omega.
  unfold binary_and_map. f_equal.
  - f_equal. apply eq_finset. simpl. reflexivity.
  - f_equal. apply eq_finset. simpl. reflexivity.
Qed.

Definition binary_or_word : word 2 1.
  apply join.
  - exact (zero_finset 0).
  - exact empty.
Defined.

Definition binary_or_map : cube 2 -> cube 1.
  intros d x. apply orb.
  - apply d. exact (zero_finset 1).
  - apply d. exists 1. omega.
Defined.

Theorem binary_or_adm : comp_word (binary_or_word) = binary_or_map.
Proof.
  apply funext. intro d. apply funext. intros [x Hx]. simpl. unfold fcompose.
  destruct x ; try omega.
  unfold binary_or_map. f_equal.
  - f_equal. apply eq_finset. simpl. reflexivity.
  - f_equal. apply eq_finset. simpl. reflexivity.
Qed.

Definition simpl_word_aux {a : nat} (w : word a 1) : word (S a) 1.
  eapply concat_word.
  - exact binary_and_word.
  - change (S a) with (1 + a). change 2 with (1 + 1).
    apply tensor_word.
    + exact empty.
    + exact w.
Defined.

Definition simpl_map_aux {a : nat} (f : cube a -> cube 1) : cube (S a) -> cube 1.
  intros d x. apply andb.
  - apply f. apply degen_c.
    + exact (zero_finset a).
    + exact d.
    + exact x.
  - apply d. exact (zero_finset a).
Defined.

Theorem restr_adm {a : nat} {b : bool} {w : word (S a) 1}
  : comp_word (concat_word w (face (zero_finset a) b empty)) = restr_map (comp_word w) b.
Proof.
  rewrite <- concat_sound. apply funext. intro d.
  unfold restr_map. unfold fcompose. f_equal.
  apply funext. intros [x Hx]. simpl. unfold fcompose. destruct x ; reflexivity.
Qed.

Theorem simpl_adm_aux {a : nat} (w : word a 1)
  : comp_word (simpl_word_aux w) = simpl_map_aux (comp_word w).
Proof.
  unfold simpl_word_aux. rewrite <- concat_sound. unfold fcompose. apply funext ; intro d.
  rewrite binary_and_adm. etransitivity.
  { apply f_equal. refine (apD10 _ _ _ d).
    change (S a) with (1 + a). change 2 with (1 + 1).
    exact (tensor_adm empty w). }
  apply funext. intros [x Hx]. destruct x ; try omega.
  unfold simpl_map_aux. unfold binary_and_map. rewrite Bool.andb_comm at 1.
  remember (d (zero_finset a)) as b. destruct b.
  - f_equal.
    + simpl. f_equal.
      * apply funext. intros [y Hy]. destruct y ; f_equal ; apply eq_finset ; reflexivity.
      * apply eq_finset. reflexivity.
    + simpl. rewrite Heqb. apply f_equal. apply eq_finset. reflexivity.
  - rewrite Bool.andb_false_r. apply Bool.andb_false_intro2.
    simpl. rewrite Heqb. f_equal. apply eq_finset. reflexivity.
Qed.

Definition simpl_word {a : nat} (w w' : word a 1) : word (S a) 1.
  eapply concat_word.
  - exact binary_or_word.
  - change 2 with (1 + 1). apply product_word.
    + exact (simpl_word_aux w).
    + eapply concat_word. exact w'. apply degen.
      * exact (zero_finset a).
      * exact empty.
Defined.

Definition simpl_map {a : nat} (f g : cube a -> cube 1) : cube (S a) -> cube 1.
  intros d x. apply orb.
  - apply andb.
    + apply f.
      * apply degen_c.
        -- exact (zero_finset a).
        -- exact d.
      * exact x.
    + apply d. exact (zero_finset a).
  - apply g.
    + apply degen_c.
      * exact (zero_finset a).
      * exact d.
    + exact x.
Defined.

Theorem simpl_adm {a : nat} (w w' : word a 1)
  : comp_word (simpl_word w w') = simpl_map (comp_word w) (comp_word w').
Proof.
  unfold simpl_word. rewrite <- concat_sound. unfold fcompose. apply funext. intro d.
  rewrite binary_or_adm. etransitivity.
  { apply f_equal. refine (apD10 _ _ _ d). unfold product_word. rewrite <- concat_sound.
    unfold fcompose. apply funext. intro e.
    rewrite dup_adm. etransitivity. refine (apD10 _ _ _ (dup_map (S a) e)).
    exact (tensor_adm (simpl_word_aux w) (concat_word w' (degen (zero_finset a) empty))).
    rewrite simpl_adm_aux. rewrite <- concat_sound. reflexivity. }
  unfold simpl_map. unfold binary_or_map. apply funext. intros [x Hx]. destruct x ; try omega.
  - f_equal.
    + unfold simpl_map_aux. simpl. f_equal. f_equal.
      * apply funext. intros [y Hy]. destruct y.
        -- destruct (le_lt_dec (S a) 1) ; try omega. f_equal. apply eq_finset. reflexivity.
        -- destruct (le_lt_dec (S a) (S (S y))) ; try omega. f_equal. apply eq_finset. reflexivity.
      * apply eq_finset. reflexivity.
      * f_equal. apply eq_finset. reflexivity.
    + unfold simpl_map_aux. unfold fcompose. simpl. unfold fcompose. f_equal.
      * apply funext. intros [y Hy]. destruct y.
        -- destruct (le_lt_dec (S a) (S (a + 1))) ; try omega. f_equal. apply eq_finset. simpl. omega.
        -- destruct (le_lt_dec (S a) (S (a + (S (S y))))) ; try omega. f_equal. apply eq_finset. simpl. omega.
      * apply eq_finset. reflexivity.
Qed.

Theorem simpl_monotone {a : nat} (f : cube (S a) -> cube 1) (Hf : monotone f)
  : simpl_map (restr_map f true) (restr_map f false) = f.
Proof.
  apply funext. intro d. apply funext. intros [x Hx].
  unfold simpl_map. remember (d (zero_finset a)) as e. destruct e.
  - rewrite Bool.andb_true_r. unfold restr_map.
    assert (cube_le (extend_cube (degen_c (zero_finset a) d) false) (extend_cube (degen_c (zero_finset a) d) true)).
    { intros [y Hy]. destruct y.
      - simpl. intro H. reflexivity.
      - simpl. destruct y.
        + easy.
        + easy. }
    unfold monotone in Hf.
    specialize (Hf (extend_cube (degen_c (zero_finset a) d) false) (extend_cube (degen_c (zero_finset a) d) true) H).
    specialize (Hf (exist (fun m : nat => m < 1) x Hx)).
    assert ((extend_cube (degen_c (zero_finset a) d) true) = d).
    { apply funext. intros [y Hy]. destruct y.
      - simpl. rewrite Heqe. f_equal. apply eq_finset. reflexivity.
      - simpl. destruct y ; f_equal ; apply eq_finset ; reflexivity. }
    rewrite <- H0 at 3.
    destruct (f (extend_cube (degen_c (zero_finset a) d) false) (exist (fun m : nat => m < 1) x Hx)).
    + rewrite Bool.orb_true_r. symmetry. apply Hf. reflexivity.
    + rewrite Bool.orb_false_r. reflexivity.
  - rewrite Bool.andb_false_r. rewrite Bool.orb_false_l. unfold restr_map. f_equal.
    apply funext. intros [y Hy]. simpl. destruct y.
    + rewrite Heqe. f_equal. apply eq_finset. reflexivity.
    + destruct y ;f_equal ; apply eq_finset ; reflexivity.
Qed.

Theorem recover_word_1 {a : nat} (f : cube a -> cube 1) (Hf : monotone f) : { w : word a 1 | f = comp_word w }.
Proof.
  revert f Hf. induction a ; intros f Hf.
  - remember (f unique (zero_finset 0)) as fu. destruct fu.
    + unshelve refine (exist _ _ _).
      * exact (face (zero_finset 0) true empty).
      * apply funext. intro d. apply funext. intros [x Hx]. destruct x ; try omega.
        simpl. unfold fcompose. rewrite Heqfu. f_equal.
        apply funext. intros [y Hy]. omega. apply eq_finset. reflexivity.
    + unshelve refine (exist _ _ _).
      * exact (face (zero_finset 0) false empty).
      * apply funext. intro d. apply funext. intros [x Hx]. destruct x ; try omega.
        simpl. unfold fcompose. rewrite Heqfu. f_equal.
        apply funext. intros [y Hy]. omega. apply eq_finset. reflexivity.
  - pose proof (IHa (restr_map f true) (monotone_restr f true Hf)) as [w Hw].
    pose proof (IHa (restr_map f false) (monotone_restr f false Hf)) as [w' Hw'].
    pose proof (simpl_monotone f Hf). rewrite <- H.
    rewrite Hw. rewrite Hw'. rewrite <- simpl_adm.
    refine (exist _ _ _). reflexivity.
Qed.

Theorem monotone_impl_adm_1 {a : nat} (f : cube a -> cube 1) : monotone f -> admissible' f.
Proof.
  induction a.
  - admit.
  - intro H. remember H as H1. clear HeqH1.
    apply monotone_restr with (b := true) in H. apply monotone_restr with (b := false) in H1.
    apply IHa in H. apply IHa in H1.
Admitted.

Theorem adm_if_monotone {a b : nat} (f : cube a -> cube b) : monotone f -> admissible' f.
Admitted.

Theorem monotone_if_adm {a b : nat} (f : cube a -> cube b) : admissible' f -> monotone f.
Admitted.

Theorem decide_adm {a b : nat} (f : cube a -> cube b) :
  admissible' f + (admissible' f -> False).
Admitted.

Theorem recover_word {a b : nat} (f : a ~> b)
  : { w : word b a | f.1s = comp_word w }.
Proof.
  destruct (decide_adm (f.1s)) as [H | H].
  - destruct H. refine (exist _ _ _). exact e.
  - assert sFalse. destruct f as [f H1]. destruct H1 as [w H1].
    assert False. apply H. exists w. simpl. apply eqs_eq. exact H1.
    destruct H0.
    destruct H0.
Qed.

Theorem arrow_monotone {a b : nat} (f : a ~> b)
  : monotone f.1s.
Proof.
  apply monotone_if_adm. apply recover_word.
Qed.
