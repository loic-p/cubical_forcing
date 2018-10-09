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
        Cubes.interval.

Import MonadNotation.

(** Axiom 1 for I : connectedness *)

Definition zero_finset (p : nat) : finset (S p).
  exists 0. easy.
Defined.

Definition zero_corner_map (p : nat) : cube 0 -> cube p.
  intros x d. exact false.
Defined.

Definition zero_corner_word (p : nat) : word 0 p.
  induction p.
  - exact cubes.empty.
  - apply face.
    + exact (zero_finset p).
    + exact false.
    + exact IHp.
Defined.

Theorem zero_corner_admissible (p : nat) : zero_corner_map p = comp_word (zero_corner_word p).
  induction p.
  - apply funext. intro c. apply funext. intros [x H]. destruct (pos_ge_0 x H).
  - simpl. rewrite <- IHp. apply funext. intro c. apply funext. intros [x H].
    destruct x.
    + now compute.
    + now compute.
Qed.

Definition zero_corner (p : nat) : p ~> 0.
  assert (admissible (zero_corner_map p)).
  eapply spair_s. apply eq_eqs. exact (zero_corner_admissible p).
  exact ( zero_corner_map p ; H )s.
Defined.

Definition face_map (p : nat) (b : bool) : S p ~> p.
  assert (face_c (zero_finset p) b =s comp_word (face (zero_finset p) b cubes.empty)).
  apply eq_eqs. reflexivity.
  assert (admissible (face_c (zero_finset p) b)).
  eapply spair_s. exact H.
  exact ( face_c (zero_finset p) b ; H0 )s.
Defined.

Definition degen_map (p : nat) : p ~> S p.
  assert (degen_c (zero_finset p) =s comp_word (degen (zero_finset p) cubes.empty)).
  apply eq_eqs. reflexivity.
  assert (admissible (degen_c (zero_finset p))).
  eapply spair_s. exact H.
  exact ( degen_c (zero_finset p) ; H0 )s.
Defined.

Theorem face_degen (p : nat) (b : bool) : face_map p b ô degen_map p = id.
Proof.
  apply eq_sexist. apply funext.
  intro c. apply funext. intros [[| x] H].
  - compute. assert ((le_S_n 1 p (le_n_S 1 p H)) = H).
    apply Peano_dec.le_unique. rewrite H0. reflexivity.
  - compute. assert ((le_S_n (S (S x)) p (le_n_S (S (S x)) p H)) = H).
    apply Peano_dec.le_unique. rewrite H0. reflexivity.
Qed.

Definition side (p : nat) : cube (S p) -> bool.
  intro c. exact (c (zero_finset p)).
Defined.

Theorem side_face (p q : nat) (b : bool) α (c : cube q) :
  side p ((α ô face_map p b).1s c) = b.
Proof.
  now compute.
Qed.

Definition homotopy_to_zero (p : nat) (i : forall q : nat, p ~> q -> Iᵗ q q id)
  : forall q : nat, S p ~> q -> Iᵗ q q id.
  intros q α.
  specialize (i q (α ô (degen_map p))).
  pose (side p ((α.1s) (fun x => false))). destruct b. (* this is a travesty, not natural at all *)
  - exact i.
  - exact (I0ᵗ q).
Defined.

Theorem homotopy_restriction1 (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Iᵗ q q id)
  : i q α = (homotopy_to_zero p i) q (α ô face_map p true).
Proof.
  unfold homotopy_to_zero.
  rewrite side_face. change (α ô face_map p true ô degen_map p) with (α ô (face_map p true ô degen_map p)).
  rewrite (face_degen p true). reflexivity.
Qed.

Theorem homotopy_restriction2 (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Iᵗ q q id)
  : I0ᵗ q = (homotopy_to_zero p i) q (α ô face_map p false).
Proof.
  unfold homotopy_to_zero.
  rewrite side_face. reflexivity.
Qed.

Theorem factorization (p : nat) : exists f, zero_corner (S p) = f ô face_map p false.
Proof.
  exists (zero_corner p). apply eq_sexist. apply funext. intro c.
  apply funext. intros [[|x] H].
  - now compute.
  - now compute.
Qed.

Run TemplateProgram (tImplementTC J1_TC "ax1_TC" "ax1"
  (forall (φ : I -> Prop), ((forall i : I, φ i \/ (φ i -> False)) -> (forall i : I, φ i) \/ (forall i : I, φ i -> False)))).
Next Obligation.
  (* STRATEGY OUTLINE *)
  (* we start by applying H0 to decide whether φ(I0) is True or False. then we commit to prove that it is the
   same for every generalized point i. indeed, if φ(i) is different, we are able to build a generalized point
   that extends both I0(0, corner) and i(0, corner) therefore reaching a contradiction. *)
  rename H into H0.
  remember H0 as H1. clear HeqH1.
  specialize (H0 p id (fun p α => I0ᵗ p)). destruct H0.
  - apply or_introlᵗ. intros q α i.
    (* then apply H1 to the homotopy *)
    pose (homotopy_to_zero q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + assert ((fun (p2 : nat) (α1 : q ~> p2) => i p2 (id ô α1)) = (fun (p2 : nat) (α1 : q ~> p2) => (homotopy_to_zero q i) p2 (α1 ô face_map q true))).
      apply funext_dep. intro r. apply funext_dep. intro γ.
      rewrite homotopy_restriction1. reflexivity.
      rewrite H1. clear H1.
      change (homotopy_to_zero q i) with h. change (id ô id ô (id ô α ô id) ô id ô id) with α.
      specialize (H0 q (face_map q true)).
      change (id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id ô id) with (face_map q true ô degen_map q ô α) in H0.
      assert (α = face_map q true ô degen_map q ô α).
      rewrite face_degen. reflexivity.
      rewrite H1. apply H0.
    + specialize (H0 0 (zero_corner (S q))). assert (Falseᵗ 0).
      apply H0. intros q' β.
      pose proof (factorization q) as [γ H1].
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô zero_corner (S q) ô id))) = (fun (p4 : nat) (α3 : q' ~> p4) => I0ᵗ p4)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      rewrite H1. change (id ô δ ô β ô id ô (id ô (γ ô face_map q false) ô id)) with (δ ô β ô γ ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2. reflexivity.
      rewrite H2. clear H2.
      change (id ô β ô id ô (id ô zero_corner (S q) ô id) ô id ô (degen_map q ô α) ô id) with (β ô zero_corner (S q) ô degen_map q ô α).
      specialize (H q' (β ô zero_corner (S q) ô degen_map q ô α)). apply H.
      inversion H1.
  - apply or_introrᵗ. intros q α i H2.
    pose (homotopy_to_zero q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + clear H2. eapply H. intros q' β.
      specialize (H0 q' (β ô face_map q false)).
      change (id ô (id ô (β ô face_map q false) ô id) ô id ô (degen_map q ô α) ô id) with (β ô (face_map q false ô degen_map q) ô α) in H0.
      rewrite face_degen in H0.
      assert ((fun (p2 : nat) (α1 : q' ~> p2) => h p2 (id ô α1 ô (id ô (β ô face_map q false) ô id))) = (fun (p2 : nat) (α1 : q' ~> p2) => I0ᵗ p2)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô (id ô (β ô face_map q false) ô id)) with (δ ô β ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2. reflexivity.
      rewrite H1 in H0. exact H0.
    + clear H. apply H0 with (α0 := face_map q true). intros q' β.
      specialize (H2 q' β).
      change (id ô β ô id ô id ô (id ô α ô id) ô id) with (β ô id ô α) in H2.
      assert (β ô id ô α = β ô face_map q true ô degen_map q ô α). erewrite <- face_degen. reflexivity.
      rewrite H in H2. clear H.
      change (id ô β ô id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id) with (β ô face_map q true ô degen_map q ô α).
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô face_map q true ô id))) = (fun (p3 : nat) (α2 : q' ~> p3) => i p3 (id ô α2 ô β ô id))).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô β ô id ô (id ô face_map q true ô id)) with (δ ô β ô face_map q true).
      unfold h. rewrite <- homotopy_restriction1. reflexivity. rewrite H.
      exact H2.
Defined.







(** Now prove the same for J. the bulk of the proof is a copy-paste,
    but the naturality conditions prevent us to use silly homotopies like
    we just did **)


Definition homotopy_to_zero' (p : nat) (i : forall q : nat, p ~> q -> Jᵗ q q id)
  : forall q : nat, S p ~> q -> Jᵗ q q id.
  intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _).
  - intros q α1. pose (α1 ô α0) as α.
    unshelve refine (Build_sexists _ _ _ _).
    + specialize (i p0 (α0 ô (degen_map p))). destruct i as [i Hi].
      intro c. pose (α.1s c) as c'. pose (side p c') as s. destruct s.
      * exact ((i p0 id).1s (α1.1s c)).
      * exact (fun _ => false).
    + destruct (i p0 (α0 ô degen_map p)) as [i' Hi]. simpl.
      assert (admissible'
                (fun c : cube q =>
                   if side p (α.1s c)
                   then (i' p0 id).1s (α1.1s c)
                   else fun _ : finset 1 => false)).
      { apply adm_if_monotone. intros c d Hcd.
        pose proof (arrow_monotone α). specialize (H c d Hcd).
        assert (side p (α.1s c) = true -> side p (α.1s d) = true). easy.
        destruct (side p (α.1s c)).
        - specialize (H0 eq_refl). rewrite H0.
          pose proof (arrow_monotone (α1 ô (i' p0 id))). exact (H1 c d Hcd).
        - intros x Hf. inversion Hf. }
      destruct H as [w Hw].
      eapply spair_s. apply eq_eqs. exact Hw.
  - intros p1 α1 p2 α2. apply eq_sexist.
    destruct (i p0 (α0 ô degen_map p)) as [i' Hi]. reflexivity.
Defined.

Definition projT1' {p : nat} {A : forall p0 : nat, p ~> p0 -> forall p1 : nat, p0 ~> p1 -> Type}
           {B : forall (p0 : nat) (α : p ~> p0), (forall (p1 : nat) (α0 : p0 ~> p1), A p1 (α0 ô α) p1 id) -> forall p1 : nat, p0 ~> p1 -> Type}
  : sigTᵗ p A B -> forall (p0 : nat) (α : p ~> p0), A p0 α p0 id.
  intros [x y]. exact x.
Defined.

Theorem J_eq {p : nat} (a b : Jᵗ p p id)
  : projT1' a = projT1' b -> a = b.
Proof.
  destruct a. destruct b. simpl.
  intro H. destruct H.
  assert (n = n0). apply proof_irr. rewrite H. reflexivity.
Qed.

Theorem homotopy_restriction1' (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Jᵗ q q id)
  : i q α = (homotopy_to_zero' p i) q (α ô face_map p true).
Proof.
  assert (projT1' (i q α) = projT1' (homotopy_to_zero' p i q (α ô face_map p true))).
  { apply funext_dep. intro p0. apply funext. intro α0.
    apply eq_sexist. unfold homotopy_to_zero'.
    Opaque side. Opaque degen_c. Opaque face_map. simpl.
    change (α ô face_map p true ô degen_map p) with (α ô (face_map p true ô degen_map p)).
    rewrite face_degen. change (α ô id) with α.
    destruct (i q α) as [j Hj]. simpl.
    apply funext. intro c.
    change ((face_map p true).1s o α.1s o α0.1s) with ((α0 ô α ô (face_map p true)).1s).
    rewrite side_face.
    specialize (Hj q id). unfold natiᵗ in Hj. unfold interval.natiᵗ_obligation_1 in Hj.
    change (j p0 α0) with (j p0 (id ô (α0 ô id) ô id)).
    rewrite <- (Hj p0 α0). reflexivity. }
  apply J_eq. exact H.
  (* Proof is correct but it doesnt typecheck without printing implicits. *)
Admitted.


Theorem homotopy_restriction2' (p q : nat) (α : p ~> q) (i : forall q : nat, p ~> q -> Jᵗ q q id)
  : J0ᵗ q = (homotopy_to_zero' p i) q (α ô face_map p false).
Proof.
  assert (projT1' (J0ᵗ q) = projT1' (homotopy_to_zero' p i q (α ô face_map p false))).
  { apply funext_dep. intro p0. apply funext. intro α0.
    apply eq_sexist. unfold homotopy_to_zero'.
    Opaque side. Opaque degen_c. Opaque face_map. simpl.
    change (α ô face_map p false ô degen_map p) with (α ô (face_map p false ô degen_map p)).
    rewrite face_degen. change (α ô id) with α.
    destruct (i q α) as [j Hj].
    apply funext. intro c.
    change ((face_map p false).1s o α.1s o α0.1s) with ((α0 ô α ô (face_map p false)).1s).
    rewrite side_face. now compute. }
  apply J_eq. exact H.
  (* Proof is correct but it doesnt typecheck without printing implicits. *)
Admitted.

Run TemplateProgram (tImplementTC J1_TC "ax1'_TC" "ax1'"
  (forall (φ : J -> Prop), ((forall i : J, φ i \/ (φ i -> False)) -> (forall i : J, φ i) \/ (forall i : J, φ i -> False)))).
Next Obligation.
  (* STRATEGY OUTLINE *)
  (* we start by applying H0 to decide whether φ(I0) is True or False. then we commit to prove that it is the
   same for every generalized point i. indeed, if φ(i) is different, we are able to build a generalized point
   that extends both I0(0, corner) and i(0, corner) therefore reaching a contradiction. *)
  rename H into H0.
  remember H0 as H1. clear HeqH1.
  specialize (H0 p id (fun p α => J0ᵗ p)). destruct H0.
  - apply or_introlᵗ. intros q α i.
    (* then apply H1 to the homotopy *)
    pose (homotopy_to_zero' q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + assert ((fun (p2 : nat) (α1 : q ~> p2) => i p2 (id ô α1)) = (fun (p2 : nat) (α1 : q ~> p2) => (homotopy_to_zero' q i) p2 (α1 ô face_map q true))).
      apply funext_dep. intro r. apply funext_dep. intro γ.
      rewrite homotopy_restriction1'. reflexivity.
      rewrite H1. clear H1.
      change (homotopy_to_zero' q i) with h. change (id ô id ô (id ô α ô id) ô id ô id) with α.
      specialize (H0 q (face_map q true)).
      change (id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id ô id) with (face_map q true ô degen_map q ô α) in H0.
      assert (α = face_map q true ô degen_map q ô α).
      rewrite face_degen. reflexivity.
      rewrite H1. apply H0.
    + specialize (H0 0 (zero_corner (S q))). assert (Falseᵗ 0).
      apply H0. intros q' β.
      pose proof (factorization q) as [γ H1].
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô zero_corner (S q) ô id))) = (fun (p4 : nat) (α3 : q' ~> p4) => J0ᵗ p4)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      rewrite H1. change (id ô δ ô β ô id ô (id ô (γ ô face_map q false) ô id)) with (δ ô β ô γ ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2'. reflexivity.
      rewrite H2. clear H2.
      change (id ô β ô id ô (id ô zero_corner (S q) ô id) ô id ô (degen_map q ô α) ô id) with (β ô zero_corner (S q) ô degen_map q ô α).
      specialize (H q' (β ô zero_corner (S q) ô degen_map q ô α)). apply H.
      inversion H1.
  - apply or_introrᵗ. intros q α i H2.
    pose (homotopy_to_zero' q i) as h.
    specialize (H1 (S q) (degen_map q ô α) h). destruct H1.
    + clear H2. eapply H. intros q' β.
      specialize (H0 q' (β ô face_map q false)).
      change (id ô (id ô (β ô face_map q false) ô id) ô id ô (degen_map q ô α) ô id) with (β ô (face_map q false ô degen_map q) ô α) in H0.
      rewrite face_degen in H0.
      assert ((fun (p2 : nat) (α1 : q' ~> p2) => h p2 (id ô α1 ô (id ô (β ô face_map q false) ô id))) = (fun (p2 : nat) (α1 : q' ~> p2) => J0ᵗ p2)).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô (id ô (β ô face_map q false) ô id)) with (δ ô β ô face_map q false).
      unfold h.
      erewrite homotopy_restriction2'. reflexivity.
      rewrite H1 in H0. exact H0.
    + clear H. apply H0 with (α0 := face_map q true). intros q' β.
      specialize (H2 q' β).
      change (id ô β ô id ô id ô (id ô α ô id) ô id) with (β ô id ô α) in H2.
      assert (β ô id ô α = β ô face_map q true ô degen_map q ô α). erewrite <- face_degen. reflexivity.
      rewrite H in H2. clear H.
      change (id ô β ô id ô (id ô face_map q true ô id) ô id ô (degen_map q ô α) ô id) with (β ô face_map q true ô degen_map q ô α).
      assert ((fun (p4 : nat) (α3 : q' ~> p4) => h p4 (id ô α3 ô β ô id ô (id ô face_map q true ô id))) = (fun (p3 : nat) (α2 : q' ~> p3) => i p3 (id ô α2 ô β ô id))).
      apply funext_dep. intro r. apply funext_dep. intro δ.
      change (id ô δ ô β ô id ô (id ô face_map q true ô id)) with (δ ô β ô face_map q true).
      unfold h. rewrite <- homotopy_restriction1'. reflexivity. rewrite H.
      exact H2.
Defined.
