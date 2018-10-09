Require Export FunctionalExtensionality.

Set Primitive Projections.

Definition fcompose {A B C : Type} (f : B -> C) (g : A -> B) : A -> C :=
  fun x : A => f (g x).

Notation "f 'o' g" := (fcompose f g) (at level 50, left associativity).

Definition funext {A B : Type} := @functional_extensionality A B.
Definition funext_dep {A : Type} {B : A -> Type} := @functional_extensionality_dep A B.
Definition proof_irr {A : Prop} {a b : A} : a = b. Admitted.
Definition admitok : False. Admitted.
