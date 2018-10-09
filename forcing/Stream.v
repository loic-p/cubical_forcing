Require Import Template.monad_utils Template.Ast Template.AstUtils
        Template.AstUtils Template.Template.
Require Import Forcing.translation_utils.
Require Import Forcing.GRTT_SProp.

Import Later Fix FoldUnfold.

Definition stream := fun A => mu (fun X  => prod A X).

Definition stcons {A: Type} (a : A) (S : ⊳ stream A) := foldp _ (a,S).

Notation "a ::: S" := (stcons a S) (at level 40).

Definition sthead {A : Type} (S : stream A) : A := fst (unfoldp _ S).

Definition sttail {A : Type} (S : stream A) : ⊳ (stream A) := snd (unfoldp _ S).

Definition const_stream {A : Type} (a : A) : stream A :=
  fixp (fun x => a ::: x).

Definition iterate {A : Type}: ⊳ (A -> A) -> A -> stream A
  := fun f => fixp (fun g a => a ::: (g ⊙ (f ⊙ nextp a))).

Definition nats : stream nat := iterate (nextp S) 0.

Definition stmap {A : Type} f (S : stream A) : stream A :=
  fixp (fun x => f (sthead S) ::: x).
