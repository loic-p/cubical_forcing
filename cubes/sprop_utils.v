Set Primitive Projections.

(** SProp manipulation and notations *)

Inductive sBox (P : SProp) : Prop :=
| wrap : P -> sBox P.

Theorem unwrap (P : SProp) (b : sBox P) : P.
Proof.
  destruct b. exact H.
Qed.

Inductive eq_s {A : Type} : A -> A -> SProp :=
| refl_s : forall a : A, eq_s a a.

Notation "A '=s' B" := (eq_s A B) (at level 65, left associativity).

Theorem eqs_eq {A : Type} {a b : A} : a =s b -> a = b.
Proof.
  intro H. destruct H. reflexivity.
Qed.

Theorem eq_eqs {A : Type} {a b : A} : a = b -> a =s b.
Proof.
  intro H. apply unwrap. rewrite H. apply wrap. apply refl_s.
Qed.

Theorem ssym {A : Type} {a b : A} (p : eq_s a b) : eq_s b a.
Proof.
  destruct p. apply refl_s.
Qed.

Theorem srewrite {A : Type} {a b : A} (P : A -> SProp) (α : P a) (p : a =s b) : P b.
Proof.
  destruct p. exact α.
Qed.

Inductive sexists_s (A : Type) (B : A -> SProp) : SProp :=
| spair_s : forall a : A, B a -> sexists_s A B.

Record sexists {A : Type} (B : A -> SProp) : Type :=
  {
    spi1 : A ;
    spi2 : B spi1
  }.

Print sexists.

Inductive sFalse : SProp :=.

Notation "x .1s" := x.(spi1 _) (at level 3).
Notation "x .2s" := x.(spi2 _) (at level 3).

Notation "( a ; b )s" := {| spi1 := a ; spi2 := b |}.

Theorem eq_sexist {A : Type} {P : A -> SProp} (a b : sexists P) (e : a.1s = b.1s) :
  a = b.
  destruct a, b. simpl in e. destruct e. reflexivity.
Qed.