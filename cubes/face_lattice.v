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

Definition empty_constraint {n : nat} : constraint n -> Prop.
  intro c. exact (forall m : finset n, c m = None).
Defined.

Fixpoint covering {n : nat} (f : face_lattice n) : Prop :=
  match f with
  | nil => False
  | c::tl => (empty_constraint c) \/ (covering tl)
  end.

Theorem covering_join {n : nat} (f g : face_lattice n) :
  covering (join_faces f g) <-> covering f \/ covering g.
Proof.
  revert g. induction f.
  - intro g. simpl. split.
    + intro H ; now right.
    + intros [H | H] ; easy.
  - intro g. simpl. split.
    + intros [H | H]. left ; now left. apply (IHf g) in H. destruct H. left ; now right. now right.
    + intros [[H | H] | H]. now left. right. apply (IHf g). now left. right. apply (IHf g). now right.
Qed.

Definition last_finset (n : nat) : finset (S n).
  exists n. easy.
Defined.

Definition finset_inj (n : nat) : finset n -> finset (S n).
  intros [m p]. exists m. apply le_S. exact p.
Defined.

Theorem constraint_dec {n : nat} (c : constraint n) : {empty_constraint c} + {~ empty_constraint c}.
  revert c. induction n.
  - intro c. left. intros [m p]. inversion p.
  - intro c. pose (c (last_finset n)) as l. remember l as l'. destruct l'.
    + right. intro H. specialize (H (last_finset n)). change l with (c (last_finset n)) in Heql'.
      rewrite H in Heql'. inversion Heql'.
    + specialize (IHn (c o (finset_inj n))). destruct IHn.
      * left. intros [m p]. destruct (Compare_dec.le_lt_eq_dec (S m) (S n) p) as [H1 | H1].
        -- apply le_S_n in H1. specialize (e (exist (fun m : nat => m < n) m H1)).
           compute in e. rewrite <- e. erewrite (Peano_dec.le_unique _ _ p (le_S (S m) n H1)). reflexivity.
        -- inversion H1. destruct H0. rewrite Heql'. unfold l. compute.
           erewrite (Peano_dec.le_unique _ _ p (PeanoNat.Nat.lt_succ_diag_r m)). reflexivity.
      * right. intro H1. apply n0. intro m. specialize (H1 (finset_inj n m)). rewrite <- H1. reflexivity.
Qed.

Theorem covering_dec {n : nat} (f : face_lattice n) : {covering f} + {~ covering f}.
  induction f.
  - right. intro H. inversion H.
  - destruct IHf.
    + left. simpl. now right.
    + destruct (constraint_dec a).
      * left. simpl. now left.
      * right. intros [H1 | H1] ; easy.
Qed.


(* Should I setoid ? Should I SProp *)

Run TemplateProgram (tImplementTC ax4_TC "F_TC" "F" Type).
Next Obligation.
  exact (face_lattice p0).
Defined.

Definition restricts {p q : nat} (f1 : face_lattice p) (α : p ~> q) (f2 : face_lattice q) : Prop.
Admitted.

Run TemplateProgram (tImplementTC F_TC "natf_TC" "natf" (F -> Prop)).
Next Obligation.
  rename X into f. rename X0 into α0.
  exact (forall (p1 : nat) (α1 : p0 ~> p1), restricts (f p0 α0) α1 (f p1 (α1 ô α0))).
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





(** axioms on cof *)

Definition extremity {p : nat} (b : bool) (i : cube p -> cube 1) : face_lattice p.
Admitted.

Theorem extremity_correct {p : nat} (b : bool) (i : cube p -> cube 1) :
  covering (extremity b i) <-> i = I_end_map p b.
Admitted.

Run TemplateProgram (tImplementTC cof_TC "ax5_1_TC" "ax5_1" (forall (i : I) (Hi : nati i), cof (i = I0))).
Next Obligation.
  specialize (H p id).
  unshelve refine (ex_intro _ _ _).
  - intros p0 α0. exact (extremity false (i p0 α0).1s).
  - intros p0 α0. split.
    + intro H1. apply eq_is_eq. apply (extremity_correct false (i p0 α0).1s) in H1.
      apply funext_dep. intro p1. apply funext. intro α1. apply eq_sexist. simpl.
      change (id ô (id ô α1 ô α0) ô id ô id) with (id ô (α1 ô α0 ô id) ô id ô id).
      rewrite <- H.
      change (α1 ô α0 ô i p (id ô id ô id ô id)) with (α1 ô (α0 ô i p (id ô id ô id ô id))).
      rewrite H.
      change (id ô (α0 ô id) ô id ô id) with α0. simpl. rewrite H1.
      now compute.
    + destruct admitok.
Defined.

(* This thing cannot work, for in our vision of presheaves a disjunction isnt sheaf-like *)
(* Run TemplateProgram (tImplementTC ax5_1_TC "ax6_TC" "ax6" (forall (φ ψ : Prop) (Hφ : cof φ) (Hψ : cof ψ), cof (φ \/ ψ))). *)







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

Theorem covering_assumption {p : nat} {f : face_lattice p} (c : covering f) : covering_dec f = left c.
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



Theorem restrict_covering {p q : nat} {α : p ~> q} {f1 : face_lattice p} {f2 : face_lattice q}
        (H : restricts f1 α f2)
  : covering f1 -> covering f2.
Proof.
Admitted.

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
      * intros p2 α2. unfold coversᵗ. unfold coversᵗ_obligation_1.
        change (id ô id ô α2 ô id ô α0 ô id ô id) with (α2 ô α0).
        eapply restrict_covering.
        -- specialize (Hf p0 α0 p2 α2). exact Hf.
        -- exact c.
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
           { intros p3 α3. eapply restrict_covering.
             - exact (Hf p2 (α2 ô α1 ô α0) p3 α3).
             - exact c. }
           pose (projEq1' (s Hc')) as g. specialize (g p2 id). apply g.
           intros p3 α3. specialize (HB' p3 α3).
           apply (restrict_covering (Hf p2 (α2 ô α1 ô α0) p3 α3)) in c.
           assert ((fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c) =
                   (fun (p4 : nat) (α4 : p3 ~> p4) => Hc' p4 (id ô α4 ô (α3 ô id)))) as Hpi.
           { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
           apply (transport _ (covering_assumption c)) in HB'. simpl in HB'.
           apply (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x p3 id) Hpi) in HB'.
           exact HB'.
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
              { intros p4 α4. eapply restrict_covering.
                - exact (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4).
                - exact c. }
              pose (projEq2' (s p3 (α3 ô α2 ô α1 ô α0) Hc')) as g. specialize (g p3 id). simpl in g.
              assert ((fun (p2 : nat) (α1 : p3 ~> p2) => Hc' p2 (id ô α1 ô id)) =
                      (fun (p4 : nat) (α4 : p3 ~> p4) => restrict_covering (Hf p3 (α3 ô α2 ô α1 ô α0) p4 α4) c)) as Hpi.
              { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
              refine (transport (fun x => A p3 (α3 ô α2 ô α1 ô α0) x _ _) Hpi _). apply g.
              intros p4 α4.
              exact (HB p4 α4).
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
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
                 match goal with
                 | |- transport ?X2 ?X3 (transport ?X4 ?X5 (sumbool_rect ?X6 ?X7 ?X8 _)) = ?X1 =>
                   apply (transport (fun x => transport X2 X3 (transport X4 X5 (sumbool_rect X6 X7 X8 x)) = X1) H)
                 end. simpl. etransitivity.
                 refine (f_equal _ _). eapply (sym (transport_trans _ _ _ _)).
                 etransitivity. refine (f_equal _ _). apply transport_sym_trans. etransitivity.
                 refine (sym (transport_trans _ _ _ _)).
                 refine (transport_ap (fun x => (projEq2'
                                                (s p6 (id ô (id ô α6) ô (id ô α5 ô id) ô (id ô α4 ô id) ô α3 ô α2 ô α1 ô α0) x) p6 id
                                                (fun (p7 : nat) (α7 : p6 ~> p7) => b p7 (id ô α7 ô α6)))) _).
                 simpl.

                 pose ((s p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0)
                          (fun (p6 : nat) (α6 : p5 ~> p6) =>
                             restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))) as ss.
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
                 pose proof (sym (covering_assumption (restrict_covering (Hf p5 (α5 ô α4 ô α3 ô α2 ô α1 ô α0) p6 α6) c))).
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
                (fun (p4 : nat) (α4 : p2 ~> p4) => restrict_covering (Hf p2 (α2 ô α1 ô α0) p4 α4) c)) as Hpi.
        { apply funext_dep. intro p4. apply funext_dep. intro α4. apply proof_irr. }
        refine (f_equal (fun x => A p2 _ x _ _) _). exact Hpi.
      * destruct (n (Hφ p2 α2)).
Defined.

Set Printing Universes.
Print test.