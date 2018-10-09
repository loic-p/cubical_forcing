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
        Cubes.ax1.

Import MonadNotation.

(** Axiom 2 : distinct end points *)

Definition lowest_corner (p : nat) : cube p.
  intro. exact false.
Defined.

Run TemplateProgram (tImplementTC ax1'_TC "ax2_TC" "ax2" (I0 = I1 -> False)).
Next Obligation.
  specialize (H p id). inversion H.
  assert (I0ᵗ p = I1ᵗ p).
  change (I0ᵗ p) with ((fun (p1 : nat) (_ : p ~> p1) => I0ᵗ p1) p id). rewrite H1. reflexivity.
  assert (I_end_map p false = I_end_map p true).
  change (I_end_map p false) with ((I0ᵗ p).1s). rewrite H0. reflexivity.
  assert (false = true).
  change false with (I_end_map p false (lowest_corner p) (zero_finset 0)). rewrite H2. reflexivity.
  inversion H3.
Defined.