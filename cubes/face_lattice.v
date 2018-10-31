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
        Cubes.ax3_ax4.

Import MonadNotation.

(** Face lattice *)

Definition constraint (n : nat) := (finset n) -> (option bool).

Definition face_lattice (n : nat) := list (constraint n).

Definition join_faces {n : nat} : face_lattice n -> face_lattice n -> face_lattice n.
  intro f. induction f.
  - intro f. exact f.
  - intro f'. exact (a::(IHf f')).
Defined.

Definition subsumed_c {p : nat} (c1 : constraint p) (c2 : constraint p) : bool.
  induction p.
  - exact true.
  - refine (andb _ _).
    + apply IHp.
      * intros [x Hx]. apply c1. refine (exist _ x _). refine (lt_trans _ _ _ Hx _).
        apply le_n.
      * intros [x Hx]. apply c2. refine (exist _ x _). refine (lt_trans _ _ _ Hx _).
        apply le_n.
    + assert (finset (S p)) as x.
      { refine (exist _ p _). exact (le_n (S p)). }
      destruct (c2 x) as [b2 |] ; destruct (c1 x) as [b1 |].
      * exact (Bool.eqb b1 b2).
      * exact false.
      * exact true.
      * exact true.
Defined.

Notation "c1 ≤c c2" := ((subsumed_c c1 c2) = true) (at level 70, right associativity).

Definition empty_constraint (n : nat) : constraint n.
  intro x. exact None.
Defined.

Definition belongs_c {n : nat} (c : constraint n) (f : face_lattice n) : bool.
  revert c. induction f as [|hd tl].
  - intro c. exact false.
  - intro c. exact (orb (IHtl c) (subsumed_c c hd)).
Defined.

Notation "c ∈c f" := ((belongs_c c f) = true) (at level 70, right associativity).

Definition covering {n : nat} (f : face_lattice n) : Prop :=
  empty_constraint n ∈c f.

Definition subsumed_f {n : nat} (f1 f2 : face_lattice n) : bool.
  revert f2. induction f1.
  - intro f2. exact true.
  - intro f2. exact (andb (belongs_c a f2) (IHf1 f2)).
Defined.

Notation "f1 ≤f f2" := ((subsumed_f f1 f2) = true) (at level 70, right associativity).

Definition equiv_f {p : nat} (f1 f2 : face_lattice p) : bool :=
  andb (subsumed_f f1 f2) (subsumed_f f2 f1).

Notation "f1 ≃f f2" := ((equiv_f f1 f2) = true) (at level 70, right associativity).

Definition restrict_c {p q : nat} (c : constraint p) (w : word q p) : face_lattice q.
  induction w.
  exact (cons c nil). all : destruct f as [y Hy].
  - apply IHw. intros [x Hx]. destruct (lt_eq_lt_dec x y) as [[H | H] | H].
    + apply c. exists x. eapply le_trans. exact H. exact (le_S_n y b Hy).
    + exact (None).
    + apply c. destruct x. destruct (pos_ge_0 y H). exists x. exact (lt_S_n x b Hx).
  - apply IHw. intros [x Hx]. destruct (le_lt_dec y x) as [H | H].
    + apply c. exists (S x). exact (lt_n_S x b Hx).
    + apply c. exists x. eapply le_trans. exact Hx. easy.
  - destruct (c (exist _ y Hy)). destruct b0.
    { refine (join_faces _ _) ; apply IHw ; intros [x Hx].
      - destruct (lt_eq_lt_dec x y) as [[H | H] | H].
        + apply c. exists x. omega.
        + exact None.
        + apply c. destruct x ; try omega. exists x. omega.
      - destruct (lt_eq_lt_dec x (S y)) as [[H | H] | H].
        + apply c. exists x. omega.
        + exact None.
        + apply c. destruct x ; try omega. exists x. omega. }
    all : apply IHw ; intros [x Hx] ; destruct (le_lt_dec x y) as [H | H] ; apply c.
      + exists x. omega.
      + destruct x ; try omega. exists x. omega.
      + exists x. omega.
      + destruct x ; try omega. exists x. omega.
  - destruct (c (exist _ y Hy)). destruct b0. Focus 2.
    refine (join_faces _ _) ; apply IHw ; intros [x Hx].
      + destruct (lt_eq_lt_dec x y) as [[H | H] | H].
        * apply c. exists x. omega. Focus 2.
        * exact None. Focus 2.
        * apply c. destruct x ; try omega. exists x. omega. Focus 2.
      + destruct (lt_eq_lt_dec x (S y)) as [[H | H] | H].
        * apply c. exists x. omega. Focus 2.
        * exact None. Focus 2.
        * apply c. destruct x ; try omega. exists x. omega.
    all : apply IHw ; intros [x Hx] ; destruct (le_lt_dec x y) as [H | H] ; apply c.
      + exists x. omega.
      + destruct x ; try omega. exists x. omega.
      + exists x. omega.
      + destruct x ; try omega. exists x. omega.
  - apply IHw. intros [x Hx]. destruct (lt_eq_eq_lt_dec x y) as [[[H | H] | H] | H].
    + apply c. exists x. exact Hx.
    + apply c. exists (S x). omega.
    + apply c. destruct x ; try omega. exists x. omega.
    + apply c. exists x. exact Hx.
  - assert (option bool -> face_lattice a) as aux.
    { intro b'. apply IHw. intros [x Hx]. destruct (lt_eq_lt_dec x y) as [[H | H]| H].
      - apply c. exists x. omega.
      - exact b'.
      - apply c. exists (S x). omega. }
    assert (finset (S b)) as z1. { exists y. omega. }
    assert (finset (S b)) as z2. { exists (S y). omega. }
    destruct (c z1) as [b1 |] ; destruct (c z2) as [b2 |].
    + destruct b1 ; destruct b2.
      * exact (aux (Some true)).
      * exact nil.
      * exact nil.
      * exact (aux (Some false)).
    + exact (aux (Some b1)).
    + exact (aux (Some b2)).
    + exact (aux (None)).
Defined.

Definition restrict_f {p q : nat} (f1 : face_lattice p) (α : p ~> q) : face_lattice q.
  destruct (recover_word α) as [w Hw]. induction f1 as [| hd tl].
  - exact nil.
  - refine (join_faces _ _).
    + exact IHtl.
    + exact (restrict_c hd w).
Defined.

Notation "f1 |_ α" := (restrict_f f1 α) (at level 65).


Definition last_finset (n : nat) : finset (S n).
  exists n. easy.
Defined.

Definition finset_inj (n : nat) : finset n -> finset (S n).
  intros [m p]. exists m. apply le_S. exact p.
Defined.


(* Should I setoid ? Should I SProp *)

Run TemplateProgram (tImplementTC ax4_TC "F_TC" "F" Type).
Next Obligation.
  exact (face_lattice p0).
Defined.



Run TemplateProgram (tImplementTC F_TC "natf_TC" "natf" (F -> Prop)).
Next Obligation.
  rename X into f. rename X0 into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1),
            (f p0 α0) |_ α1 ≃f (f p1 (α1 ô α0))).
Defined.

Run TemplateProgram (tImplementTC natf_TC "covers_TC" "covers" (F -> Prop)).
Next Obligation.
  rename X0 into α0. rename X into f.
  exact (covering (f p0 α0)).
Defined.

Run TemplateProgram (tImplementTC covers_TC "realize_TC" "realize" (F -> Prop)).
Next Obligation.
  rename X0 into α. rename X into f.
  specialize (f p0 α). exact (covering f). (* the problem is probably with this one, should give more constraint *)
Defined.

Definition sieve_equiv {p : nat} (S1 S2 : forall q : nat, p ~> q -> Prop) :=
  forall (q : nat) (α : p ~> q), S1 q α <-> S2 q α.

Notation "S ≈ T" := (sieve_equiv S T) (at level 65, left associativity).

(** Cofibrant propositions *)

Run TemplateProgram (tImplementTC realize_TC "cof_TC" "cof" (Prop -> Prop)).
Next Obligation.
  rename X0 into α. rename X into S.
  specialize (S p id).
  exact (exists f : (forall p0 : nat, p ~> p0 -> Fᵗ p0 p0 id),
            (fun (p0 : nat) (α : p ~> p0) => covering (f p0 α)) ≈ S).
Defined.

(* this one seems a better definition. However, i need to put it in the translation database, and i dont
 know how to do this without dirty hacks. Also, I need sigma-types translation. *)
Definition cof' : Prop -> Prop := fun s => exists f : F, s = realize f.








Definition isEquiv (A B : Type) : Type :=
  Σ (f : A -> B) (g : B -> A), (f o g = fun x => x) /\ (g o f = fun x => x).

Notation "A ≅ B" := (isEquiv A B) (at level 65, left associativity).

Run TemplateProgram (TC1 <- tTranslate cof_TC "fcompose" ;;
                         TC2 <- tTranslate TC1 "isEquiv" ;;
                         tmDefinition "isEq_TC" TC2).

Definition projEq1' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
  : isEquivᵗ p A B p id -> (forall (p0 : nat) (α : p ~> p0),
                              (forall (p1 : nat) (α0 : p0 ~> p1), A p1 (α0 ô α) p1 id) ->
                              B p0 α p0 id).
  intros [x _]. exact x.
Defined.

Definition projEq2' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
  : isEquivᵗ p A B p id -> (forall (p0 : nat) (α : p ~> p0),
                              (forall (p1 : nat) (α0 : p0 ~> p1), B p1 (α0 ô α) p1 id) ->
                              A p0 α p0 id).
  intros [x y]. destruct (y p id) as [z _]. exact z.
Defined.

Definition projEq3' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           (ie : isEquivᵗ p A B p id)
           : (forall (p0 : 𝐂_obj) (α : p ~> p0),
                 eqᵗ p0
                     (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) =>
                        (forall (p3 : nat) (α2 : p2 ~> p3),
                            B p3 (α2 ô α1 ô α0 ô α) p3 id) ->
                        B p2 (α1 ô α0 ô α) p2 id)
                     (fun (p1 : nat) (α0 : p0 ~> p1) =>
                        fcomposeᵗ p1
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α)))
                     (fun (p1 : nat) (α0 : p0 ~> p1)
                        (x : forall (p2 : nat) (α1 : p1 ~> p2),
                            B p2 (α1 ô α0 ô α) p2 id) =>
                        x p1 id)).
  destruct ie as [x y]. simpl.
  destruct (y p id) as [z t]. destruct (t p id) as [a b].
  exact a.
Defined.

Definition projEq4' {p : nat} {A : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           {B : forall p0 : nat, p ~> p0 -> (fun (p1 : nat) (_ : p0 ~> p1) => forall p2 : nat, p1 ~> p2 -> Type) p0 id}
           (ie : isEquivᵗ p A B p id)
           : (forall (p0 : 𝐂_obj) (α : p ~> p0),
                 eqᵗ p0
                     (fun (p1 : nat) (α0 : p0 ~> p1) (p2 : nat) (α1 : p1 ~> p2) =>
                        (forall (p3 : nat) (α2 : p2 ~> p3),
                            A p3 (α2 ô α1 ô α0 ô α) p3 id) ->
                        A p2 (α1 ô α0 ô α) p2 id)
                     (fun (p1 : nat) (α0 : p0 ~> p1) =>
                        fcomposeᵗ p1
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     B p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) =>
                                     A p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq2' ie p2 (α1 ô α0 ô α))
                                  (fun (p2 : nat) (α1 : p1 ~> p2) => projEq1' ie p2 (α1 ô α0 ô α)))
                     (fun (p1 : nat) (α0 : p0 ~> p1)
                        (x : forall (p2 : nat) (α1 : p1 ~> p2),
                            A p2 (α1 ô α0 ô α) p2 id) =>
                        x p1 id)).
  destruct ie as [x y]. simpl. destruct (y p id) as [z t]. destruct (t p id) as [a b]. exact b.
Defined.

Lemma subsumed_c_refl {p : nat} (c : constraint p) : c ≤c c.
Proof.
  induction p.
  - now compute.
  - simpl. apply andb_true_intro. split.
    + apply IHp.
    + destruct (c (exist (fun m : nat => m < S p) p (le_n (S p)))).
      * destruct b ; easy.
      * easy.
Qed.

Lemma restrict_empty_c {p q : nat} {w : word q p} :
  empty_constraint q ∈c (restrict_c (empty_constraint p) w).
Proof.
  induction w.
  simpl. apply subsumed_c_refl.
  all : simpl ; refine (transport (fun x => empty_constraint a ∈c x) _ IHw) ;
    destruct f as [y Hy] ; refine (apD10 _ _ _ w) ; refine (f_equal restrict_c _) ;
    apply funext ; intros [x Hx].
  - destruct (lt_eq_lt_dec x y) as [[H | H] | H] ; now compute.
  - destruct (le_lt_dec y x) as [H | H] ; now compute.
  - destruct (le_lt_dec x y) as [H | H] ; now compute.
  - destruct (le_lt_dec x y) as [H | H] ; now compute.
  - destruct (lt_eq_eq_lt_dec x y) as [[[H | H] | H] | H] ; now compute.
  - destruct (lt_eq_lt_dec x y) as [[H | H] | H] ; now compute.
Qed.

Lemma belongs_join {p : nat} (c : constraint p) (f g : face_lattice p) :
  (c ∈c (join_faces f g)) <-> (c ∈c f) \/ (c ∈c g).
Proof.
  split.
  - induction f.
    + simpl. intro H. right. exact H.
    + simpl. intro H. apply Bool.orb_true_elim in H. destruct H.
      * apply IHf in e. destruct e.
        left. apply Bool.orb_true_intro. left. exact H.
        right. exact H.
      * left. apply Bool.orb_true_intro. right. exact e.
  - intros [H | H].
    + induction f.
      * simpl in H. inversion H.
      * simpl in H. simpl. apply Bool.orb_true_elim in H. destruct H.
        -- apply IHf in e. apply Bool.orb_true_intro. left. exact e.
        -- apply Bool.orb_true_intro. right. exact e.
    + induction f.
      * simpl. exact H.
      * simpl. apply Bool.orb_true_intro. left. exact IHf.
Qed.

Lemma empty_terminal {p : nat} (c : constraint p) :
  (empty_constraint p ≤c c) -> c = empty_constraint p.
Proof.
  intro H. induction p.
  - apply funext. intros [x Hx]. omega.
  - simpl in H. apply Bool.andb_true_iff in H. destruct H.
    apply funext. intros [x Hx]. destruct (le_lt_dec p x) as [Hx' | Hx'].
    + assert (x = p). omega. unfold empty_constraint.
      assert (c (exist (fun m : nat => m < S p) p (le_n (S p))) = None).
      { destruct (c (exist (fun m : nat => m < S p) p (le_n (S p)))). inversion H0. easy. }
      revert Hx. rewrite H1. intro Hp. assert (Hp = le_n (S p)).
      { apply le_unique. }
      rewrite H3. exact H2.
    + clear H0.
      assert ((fun H : finset p =>
        let (x, Hx) := H in
        empty_constraint (S p)
                         (exist (fun m : nat => m < S p) x (Nat.lt_trans x p (S p) Hx (le_n (S p))))) = (empty_constraint p)).
      { apply funext. intros [y Hy]. unfold empty_constraint. easy. }
      rewrite H0 in H. apply (IHp _) in H.
      apply (apD10 _ _) with (x0 := (exist (fun x => x < p) x Hx')) in H.
      unfold empty_constraint. unfold empty_constraint in H.
      assert (Hx = (Nat.lt_trans x p (S p) Hx' (le_n (S p)))). { apply le_unique. }
      rewrite H1. exact H.
Qed.

Lemma restrict_covering_f {p q : nat} (α : p ~> q) (f : face_lattice p) :
  (empty_constraint p ∈c f) -> (empty_constraint q ∈c f |_ α).
Proof.
  induction f.
  - simpl. easy.
  - intro H. simpl in H. apply Bool.orb_true_elim in H. destruct H.
    + apply IHf in e. unfold restrict_f in e.
      unfold restrict_f. destruct (recover_word α) as [w Hw]. simpl.
      apply belongs_join. left. exact e.
    + apply empty_terminal in e. unfold restrict_f. destruct (recover_word α) as [w Hw].
      simpl. apply belongs_join. right. rewrite e. apply restrict_empty_c.
Qed.

Theorem restrict_covering {p q : nat} (α : p ~> q) {f : face_lattice p}
  : covering f -> covering (f |_ α).
Proof.
  intro H. unfold covering in H. pose (belongs_c (empty_constraint p) f) as b. remember b.
  destruct b0 ; unfold b in Heqb0.
  - symmetry in Heqb0. apply (restrict_covering_f α) in Heqb0. unfold covering.
    rewrite Heqb0. easy.
  - rewrite <- Heqb0 in H. inversion H.
Qed.

Theorem equiv_covering {p : nat} {f g : face_lattice p} :
  f ≃f g -> (covering f -> covering g).
Proof.
  intro H. unfold equiv_f in H. apply Bool.andb_true_iff in H. destruct H. clear H0.
  induction f.
  - intro H'. compute in H'. inversion H'.
  - simpl in H. apply Bool.andb_true_iff in H. destruct H. specialize (IHf H0).
    intro H'. unfold covering in H'. simpl in H'. apply Bool.orb_true_elim in H'.
    destruct H'.
    + apply IHf. exact e.
    + apply empty_terminal in e. rewrite e in H. exact H.
Qed.


(* these constructions are slightly weird, it is the result of me using Prop when
   i should have used bool.
   TODO : use bool and get rid of useless lemmas. *)

Definition covering_dec {p : nat} (f : face_lattice p) : { covering f } + { ~ covering f }.
  pose (belongs_c (empty_constraint p) f) as b. remember b. unfold b in Heqb0. destruct b0.
  - left. unfold covering. rewrite <- Heqb0. easy.
  - right. unfold covering. rewrite <- Heqb0. easy.
Defined.

Theorem covering_assumption {p : nat} {f : face_lattice p} (c : covering f)
  : covering_dec f = left c.
Proof.
  destruct (covering_dec f).
  - apply f_equal. apply proof_irr.
  - absurd (covering f). exact n. exact c.
Qed.

Theorem noncovering_assumption {p : nat} {f : face_lattice p} (c : ~ covering f) : covering_dec f = right c.
Proof.
  destruct (covering_dec f).
  - absurd (covering f). exact c. exact c0.
  - apply f_equal. apply proof_irr.
Qed.




Run TemplateProgram (tImplementTC isEq_TC "ax9_TC" "ax9"
                                  (forall (f : F) (Hf : natf f)
                                     (A : covers f -> Type) (B : Type) (s : forall u : (covers f), A u ≅ B),
                                      Σ (B' : Type) (s' : B' ≅ B), (forall u : (covers f), A u = B'))).
Next Obligation.
  revert p f H A B X.   intros p f H A B X.
  rename X into s. rename H into Hf.
  unfold Fᵗ in f. unfold Fᵗ_obligation_1 in f.
  unshelve refine (existTᵗ _ _ _ _ _).
  (* Define B' *)
  - intros p0 α0 p1 α1.
    refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p0 α0))) ; intro c.
    + eapply (A p0 α0).
      * intros p2 α2.
        specialize (Hf p0 α0 p2 α2). simpl in Hf. apply equiv_covering in Hf.
        apply Hf. apply restrict_covering. exact c.
      * exact α1.
    + exact (B p0 α0 p1 α1).
  - intros p0 α0. unshelve refine (existTᵗ _ _ _ _ _).
    (* Prove B ≅ B' *)
    + intros p1 α1. unfold isEquivᵗ. unshelve refine (existTᵗ _ _ _ _ _).
      (* First direction of equivalence *)
      * intros p2 α2 HB'.
        refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p2 (α2 ô α1 ô α0)))) ; intro c.
        -- specialize (s p2 (α2 ô α1 ô α0)).
           assert (forall (p3 : nat) (α3 : p2 ~> p3),
                      coversᵗ p3 (fun (p4 : nat) (α4 : p3 ~> p4) => f p4 (α4 ô α3 ô α2 ô α1 ô α0)) p3 id) as Hc'.
           { intros p3 α3.
             clear HB'. specialize (Hf p2 (α2 ô α1 ô α0) p3 α3). simpl in Hf.
             apply equiv_covering in Hf. apply Hf. apply restrict_covering. exact c. }
           pose (projEq1' (s Hc')) as g. specialize (g p2 id). apply g.
           intros p3 α3. specialize (HB' p3 α3).
           pose proof (Hf p2 (α2 ô α1 ô α0) p3 α3) as Hf'. simpl in Hf'.
           apply equiv_covering in Hf'.
           Focus 2. apply restrict_covering. exact c.
           apply (transport _ (covering_assumption Hf')) in HB'. simpl in HB'.
           refine (transport (fun x => A p3 _ x p3 id) _ HB').
           apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr.
        -- specialize (HB' p2 id).
           apply (transport _ (noncovering_assumption c)) in HB'. simpl in HB'.
           exact HB'.
      * intros p2 α2. unshelve refine (existTᵗ _ _ _ _ _).
        (* Second direction of equivalence *)
        -- intros p3 α3 HB.
           match goal with
           | |- ?GG => refine (sumbool_rect (fun X => GG) _ _ (covering_dec (f p3 (α3 ô α2 ô α1 ô α0)))) ; intro c
           end.
           ++ apply (transport _ (sym (covering_assumption c))). simpl.
              assert (forall (p4 : nat) (α4 : p3 ~> p4),
                         coversᵗ p4 (fun (p5 : nat) (α5 : p4 ~> p5) => f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)) p4 id) as Hc'.
              { intros p4 α4. specialize (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4). simpl in Hf.
                apply equiv_covering in Hf. apply Hf. apply restrict_covering. exact c. }
              pose (projEq2' (s p3 (α3 ô α2 ô α1 ô α0) Hc')) as g. specialize (g p3 id). simpl in g.
              specialize (g HB).
              refine (transport (fun x => A p3 _ x p3 id) _ g).
              apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr.
           ++ apply (transport _ (sym (noncovering_assumption c))). simpl.
              exact (HB p3 id).
        -- intros p3 α3. apply conjᵗ.
           (* First identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption
          (equiv_covering
             (Hf p5
                (id ô id ô (id ô α5 ô id) ô (id ô α4 ô id) ô (id ô α3 ô id) ô α2 ô α1 ô α0)
                p6 α6) (restrict_covering α6 c)))) as H.
                 match goal with
                 | |- transport ?X2 ?X3 (transport ?X4 ?X5 (sumbool_rect ?X6 ?X7 ?X8 _)) = ?X1 =>
                   apply (transport (fun x => transport X2 X3 (transport X4 X5 (sumbool_rect X6 X7 X8 x)) = X1) H)
                 end. simpl. etransitivity.
                 refine (f_equal _ _). eapply (sym (transport_trans _ _ _ _)).
                 etransitivity. refine (f_equal _ _).
                 apply transport_sym_trans. etransitivity.
                 refine (sym (transport_trans _ _ _ _)).
                 refine (transport_ap (fun x => (projEq2'
                                                (s p6 (id ô (id ô α6) ô (id ô α5 ô id) ô (id ô α4 ô id) ô α3 ô α2 ô α1 ô α0) x) p6 id
                                                (fun (p7 : nat) (α7 : p6 ~> p7) => b p7 (id ô α7 ô α6)))) _).
                 simpl.
                 pose (s p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)
                         (fun (p6 : nat) (α6 : p5 ~> p6) =>
                            (equiv_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) (restrict_covering α6 c)))) as ss.
                 pose proof (projEq3' ss p5 id) as Hs. inversion Hs. clear Hs.
                 unfold fcomposeᵗ in H0. unfold ss in H0.
                 apply apD10 with (x := p5) in H0. apply apD10 with (x := id) in H0.
                 apply apD10 with (x := b) in H0.
                 (** * I think we need some kind of naturality for s, unless we somehow manage to call it with a higher forcing condition *)
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b p5 id => apply (transport (fun x => GG1 x = b p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_sym_trans _ _ _). reflexivity.
           (* Second identity of equivalence *)
           ++ intros p4 α4. apply eq_is_eq.
              apply funext_dep. intro p5. apply funext_dep. intro α5.
              unfold fcomposeᵗ. apply funext_dep. intro b'.
              refine (sumbool_rect (fun X => _) _ _ (covering_dec (f p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)))) ; intro c.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (covering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _). refine (f_equal _ _). refine (f_equal _ _).
                 apply funext_dep. intro p6. apply funext_dep. intro α6.
                 pose proof (sym (covering_assumption (equiv_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) (restrict_covering α6 c)))).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) H)
                 end. simpl. reflexivity. etransitivity. refine (f_equal _ _). refine (f_equal _ _).
                 reflexivity.
                 (** * Same here *)
                 destruct admitok.
              ** match goal with
                 | |- ?GG1 _ = b' p5 id => apply (transport (fun x => GG1 x = b' p5 id) (sym (noncovering_assumption c)))
                 end. simpl. etransitivity. refine (f_equal _ _).
                 match goal with
                 | |- ?GG1 _ = ?GG2 => apply (transport (fun x => GG1 x = GG2) (sym (noncovering_assumption c)))
                 end. simpl. reflexivity. etransitivity.
                 match goal with
                 | |- transport ?P1 ?E1 (transport ?P2 ?E2 ?X) = ?Y =>
                   exact (sym (transport_trans P1 E2 E1 X))
                 end. etransitivity. refine (transport_trans_sym _ _ _).
                 reflexivity.
    (* Prove A u = B' *)
    + intros p1 α1. intro Hφ. apply eq_is_eq.
      apply funext_dep. intro p2. apply funext_dep. intro α2.
      apply funext_dep. intro p3. apply funext. intro α3. simpl.
      change (id ô (id ô α2 ô id) ô id ô (id ô α1 ô id) ô α0) with (α2 ô α1 ô α0).
      destruct (covering_dec (f p2 (α2 ô α1 ô α0))).
      * assert ((fun (p5 : nat) (α4 : p2 ~> p5) => Hφ p5 (id ô α4 ô (id ô α2 ô id))) =
                (fun (p4 : nat) (α4 : p2 ~> p4) => equiv_covering (Hf p2 (α2 ô α1 ô α0) p4 α4) (restrict_covering α4 c))) as Hpi.
        { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
        refine (f_equal (fun x => A p2 _ x _ _) _). exact Hpi.
      * destruct (n (Hφ p2 α2)).
Defined.

Set Printing Universes.
Print test.