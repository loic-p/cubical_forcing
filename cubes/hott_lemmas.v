(** HoTT lemmas for equality manipulation *)

Definition transport {A : Type} (P : A -> Type) {a b : A} : a = b -> P a -> P b.
Proof.
  intro H. destruct H. intro H. exact H.
Defined.

Definition sym {A : Type} {a b : A} : a = b -> b = a.
Proof.
  intro H. destruct H. reflexivity.
Defined.

Definition trans {A : Type} {a b c : A} : a = b -> b = c -> a = c.
Proof.
  intro H. destruct H. intro H. exact H.
Defined.

Theorem trans_id {A : Type} {a b : A} {e : a = b} : trans e eq_refl = e.
Proof.
  destruct e. reflexivity.
Qed.

Theorem id_trans {A : Type} {a b : A} {e : a = b} : trans eq_refl e = e.
Proof.
  reflexivity.
Qed.

Theorem trans_sym {A : Type} {a b : A} {e : a = b} : trans e (sym e) = eq_refl.
Proof.
  destruct e. reflexivity.
Qed.

Theorem sym_trans {A : Type} {a b : A} (e : a = b) : trans (sym e) e = eq_refl.
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_id {A : Type} {P : A -> Type} {a : A} {x : P a}
  : transport P eq_refl x = x.
Proof.
  reflexivity.
Qed.

Theorem transport_trans {A : Type} (P : A -> Type) {a b c : A} (e : a = b) (e' : b = c) (x : P a)
  : transport P (trans e e') x = transport P e' (transport P e x).
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_sym_trans {A : Type} (P : A -> Type) {a b : A} (e : a = b) (x : P b)
  : transport P (trans (sym e) e) x = x.
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_trans_sym {A : Type} (P : A -> Type) {a b : A} (e : a = b) (x : P a)
  : transport P (trans e (sym e)) x = x.
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_ap {A P a b} (f : forall x : A, P x) (e : a = b) : transport P e (f a) = f b.
Proof.
  destruct e. reflexivity.
Qed.

Theorem apD10 {A B} (f g : forall x : A, B x) : f = g -> forall x : A, f x = g x.
Proof.
  intro e. destruct e. intro x. reflexivity.
Qed.

Theorem exist_transp {A} {P : A -> Prop} {x y} (a : P x) (e : x = y) : exist P x a = exist P y (transport P e a).
Proof.
  destruct e. reflexivity.
Qed.

Theorem ap_transport {A x y} (P Q : A -> Type) {a : P x} {e : x = y} (f : forall x : A, P x -> Q x)
  : f y (transport P e a) = transport Q e (f x a).
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_domain {A B a b} {P : A -> Type} {e : a = b} {y : P b} (f : P a -> B)
  : transport (fun x : A => P x -> B) e f y = f (transport P (sym e) y).
Proof.
  destruct e. reflexivity.
Qed.

Theorem transport_codomain {A B a b} {y : B} {P : A -> Type} {e : a = b} (f : B -> P a)
  : transport (fun x : A => B -> P x) e f y = transport P e (f y).
Proof.
  destruct e. reflexivity.
Qed.