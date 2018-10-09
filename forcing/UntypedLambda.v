Require Import GRTT_SProp.

Import Later.
Import Fix.
Import FoldUnfold.

Section UntypedLambda.

  Definition F := (fun T => T -> T).

  Definition 𝒟  := mu F.

  Definition fun_ {n} (f : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟) : ⊳[n]𝒟
    := nfoldp (fun T : Type => T -> T) (fun A => later_unapp A A) f.

  Definition defun_ {n} (f : ⊳[n] 𝒟) : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟
    := nunfoldp (fun T : Type => T -> T) (fun A => later_app A A) f.

  Definition switchD {n} : ⊳[1+n]𝒟 -> ⊳[n]𝒟 := fun t => fun_ (fun _ => t).
  Notation "↓ a" := (switchD a) (at level 40).

  Definition applD {n} : ⊳[n]𝒟 -> ⊳[n]𝒟 -> ⊳[n]𝒟 := fun f s => ↓ ((defun_ f) (nextp s)).

  Definition one_step {n} (x: ⊳[n]𝒟) := ↓ (nextp x).
  Notation "→ a" := (one_step a) (at level 40).

  Lemma switchD_nextp {n : nat} (t : ⊳[1+n] 𝒟) : (switchD (n:=1+n) (nextp t)) = nextp (↓t).
  Proof.
    unfold switchD,fun_.
    rewrite <- (nfold_next F (fun A : Type => later_app A A));
      try (intros ? ?; apply later_unapp_app).
    apply f_equal.
    apply functional_extensionality_dep. intros t'.
    symmetry. apply later_app_const_β.
    Qed.

  Notation "t1 @ t2" := (applD t1 t2) (at level 40).
  Notation "t1 '@[' n ']' t2" := (applD (n:=n) t1 t2) (at level 40).

  Lemma nextp_applD {n} (t t' : ⊳[n] 𝒟) : (nextp t) @[1+n] (nextp t') = nextp (t @ t').
  Proof.
    unfold applD. rewrite <- switchD_nextp. apply f_equal.
    unfold defun_.
    repeat rewrite nunfold_next.
    rewrite later_app_next_β. reflexivity.
  Qed.

  Lemma defun_fun_id {n} (f : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟) : defun_ (fun_ f) = f.
  Proof.
    unfold fun_,defun_.
    rewrite nunfold_nfold_id; try (intros ? ?; apply later_app_unapp).
    reflexivity.
  Qed.

  Arguments later_app {_ _}.
  Arguments later_unapp {_ _}.

  Arguments foldp {_}.
  Arguments unfoldp {_}.

  Arguments nfoldp {_ _ _}.
  Arguments nunfoldp {_ _ _}.


  Lemma fun_nextp {n} (f : ⊳[1+n]𝒟 -> ⊳[1+n]𝒟)
    : fun_ (n:=1+n) (later_app (nextp f)) = nextp (fun_ f).
  Proof.
    unfold fun_. apply nfold_next with (h:= fun A => @later_app A A).
    intros ? ?; apply later_unapp_app.
  Qed.

  Lemma later_funct_applD n g :
    later_app (nextp (fun t => g @ t)) = fun t => (nextp g) @[1+n] t.
  Proof.
    apply functional_extensionality_dep. fold nlater in *.
    intros t.
    unfold later_funct_arrow. unfold applD,defun_.
    unfold switchD at 2. unfold fun_. simpl.
    unfold later_funct_arrow. fold nlater in *.
    assert (H : (later_unapp (fun _ : ⊳ (⊳ (⊳[ n] 𝒟)) => (nextp (nunfoldp  (later_f:=fun A => @later_app A A)) ⊙ nextp g) ⊙ nextp t)
              = later_unapp(fun _ => nextp ((nunfoldp (later_f:=fun A => @later_app A A) g) t)))).
    { apply f_equal. apply functional_extensionality_dep. intros. repeat rewrite later_app_next_β. reflexivity. }
    simpl in H.
    unfold 𝒟,F in *. rewrite H.
    rewrite later_unapp_const_β.
    rewrite later_app_next_β. unfold switchD,fun_. simpl.
    fold F. fold 𝒟.
    pose (fun t => nfoldp (later_f:=fun A => @later_unapp A A)
                 (fun _ : ⊳ (⊳[ n] 𝒟) => nunfoldp (later_f:=fun A => @later_app A A)  g t)) as q.
    assert (nextp (fun t0 : ⊳[ n] 𝒟 => q (nextp t0)) ⊙ t = nextp (q t)).
    rewrite later_app_next_app_1_β with (g:=q). reflexivity.
    subst q. apply H0.
  Qed.

  Lemma later_funct_applD_2 n g (f : forall {n}, ⊳[n]𝒟 -> ⊳[n]𝒟)
        (f_next : forall a, f (n:=1+n) (nextp a) = nextp (f a)) t :
    later_app (nextp (fun t => g @ (f t))) t = (nextp g) @[1+n] (f (n:=1+n) t).
  Proof.
    fold nlater in *.
    unfold later_funct_arrow. unfold applD,defun_.
    unfold switchD at 2. unfold fun_. simpl.
    unfold later_funct_arrow. fold nlater in *.
    assert (H : (later_unapp (fun _ : ⊳ (⊳ (⊳[ n] 𝒟)) =>
                 (nextp (nunfoldp (later_f:=fun A => @later_app A A)) ⊙ nextp g) ⊙ nextp (f (S n) t))
                    =
                    later_unapp (fun _ => nextp ((nunfoldp (later_f:=fun A => @later_app A A) g) (f (S n) t))))).
    { apply f_equal. apply functional_extensionality_dep. intros. repeat rewrite later_app_next_β. reflexivity. }
    simpl in H.
    unfold 𝒟,F in *. rewrite H.
    rewrite later_unapp_const_β.
    rewrite later_app_next_β. unfold switchD,fun_. simpl.
    fold F in *. fold 𝒟 in *. unfold later_funct_arrow.
    pose (fun x => nfoldp (later_f:=fun A => @later_unapp A A) (fun _ : ⊳ (⊳[ n] 𝒟) => nunfoldp (later_f:=fun A => @later_app A A) g (f (1+n) x))) as q.
    assert
      (nextp (fun t0 : ⊳[ n] 𝒟 => q (nextp (t0))) ⊙ t = nextp (q t)).
    {rewrite later_app_next_app_1_β with (g:=q). reflexivity. }
    subst q. simpl in H0. rewrite <- H0. f_equal. f_equal.
    apply functional_extensionality_dep. intros x. f_equal.
    apply functional_extensionality_dep. intros y.
    rewrite <- f_next. reflexivity.
  Qed.

  Definition idD {n : nat} : ⊳[n]𝒟 := fun_ (fun x => x).

  Lemma idD_is_id {n} (t : ⊳[n]𝒟) : idD @ t = → t.
  Proof.
    unfold idD,applD. rewrite defun_fun_id.
    reflexivity.
  Qed.

  Definition Ω {n} := fun_ (fun (x : ⊳[1+n]𝒟) => x @ x).

  Lemma Ω_unfold {n :nat} : Ω (n:=n) @ Ω = → (Ω @ Ω).
  Proof.
    unfold Ω at 1. unfold applD at 1.
    rewrite defun_fun_id. rewrite nextp_applD.
    reflexivity.
  Qed.

  Definition Y_aux {n} (f : ⊳[n]𝒟) := fun x => f @ (x @ x).

  Lemma Y_aux_nextp {n} (g : ⊳[1+n]𝒟) :
    fun_ (Y_aux (n:=2+n) (nextp g)) = nextp (fun_ (Y_aux g)).
  Proof.
    rewrite <- fun_nextp. apply f_equal.
    apply functional_extensionality_dep. intros t.
    unfold Y_aux at 1.
    assert (H := later_funct_applD_2 _ g (fun _ x => x @ x)). fold nlater in *. simpl in *.
    rewrite <- H. reflexivity.
    intros a. apply (nextp_applD (n:=1+n)).
  Qed.

  Definition Y' {n} (f : ⊳[ 1 + n] 𝒟) : ⊳[ 1 + n] 𝒟
    := fun_ (Y_aux (n:=2+n) (nextp f)).

  Lemma Y'_nextp {n} (f : ⊳[1+n] 𝒟) :
    (Y' (n:=1+n) (nextp f)) @ (Y' (n:=1+n) (nextp f)) = nextp ((Y' f) @ (Y' f)).
  Proof.
    unfold Y'.
    repeat rewrite <- (@nextp_applD (1+n)).
    pose (Y_aux_nextp (n:=1+n) (nextp f)) as H. simpl in *.
    rewrite H. reflexivity.
  Qed.

  Definition Y {n} := fun_ (fun (f : ⊳[1+n]𝒟) => (Y' f) @ (Y' f)).

  Lemma Y_unfold : forall n (f : ⊳[1+n]𝒟), (Y @ f) = → → (f @ ((Y' f) @ (Y' f))).
  Proof.
    intros.
    unfold Y,applD. unfold Y' at 1. repeat rewrite defun_fun_id.
    unfold Y_aux. rewrite (@nextp_applD (2+n)).
    rewrite (Y'_nextp (n:=n)).
    rewrite (@nextp_applD (2+n)). rewrite (@nextp_applD (1+n)).
    rewrite @switchD_nextp. reflexivity.
  Qed.

End UntypedLambda.
