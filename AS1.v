(********* line 709 ***********)


(** **** Exercise: 2 stars, recommended (mult_1_plus) *)
Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(********* line 987 ***********)

(** **** Exercise: 2 stars, recommended (basic_induction) *)
Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem plus_n_Sm : forall n m : nat, 
  S (n + m) = n + (S m).
Proof. 
  (* FILL IN HERE *) Admitted.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

(** **** Exercise: 2 stars (double_plus) *)
Lemma double_plus : forall n, double n = n + n .
Proof.  
  (* FILL IN HERE *) Admitted.
(** [] *)

(********* line 1125 ***********)

(** **** Exercise: 2 stars, optional (beq_nat_refl_informal) *)
(** Write an informal proof of the following theorem, using the
    informal proof of [plus_assoc] as a model.  Don't just
    paraphrase the Coq tactics into English!
 
    Theorem: [true = beq_nat n n] for any [n].
    
    Proof: (* FILL IN HERE *)
[]
 *)

(********* line 1229 ***********)

(** **** Exercise: 4 stars, recommended (mult_comm) *)
(** Use [assert] to help prove this theorem.  You shouldn't need to
    use induction. *)

Theorem plus_swap : forall n m p : nat, 
  n + (m + p) = m + (n + p).
Proof.
  (* FILL IN HERE *) Admitted.


(** Now prove commutativity of multiplication.  (You will probably
    need to define and prove a separate subsidiary theorem to be used
    in the proof of this one.)  You may find that [plus_swap] comes in
    handy. *)

Theorem mult_comm : forall m n : nat,
 m * n = n * m.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(********* line 1378 ***********)

(** **** Exercise: 4 stars, recommended (binary) *)
(** Consider a different, more efficient representation of natural
    numbers using a binary rather than unary system.  That is, instead
    of saying that each natural number is either zero or the successor
    of a natural number, we can say that each binary number is either

      - zero,
      - twice a binary number, or
      - one more than twice a binary number.

    (a) First, write an inductive definition of the type [bin]
        corresponding to this description of binary numbers. 

    (Hint: recall that the definition of [nat] from class,
    Inductive nat : Type :=
      | O : nat
      | S : nat -> nat.
    says nothing about what [O] and [S] "mean".  It just says "[O] is
    a nat (whatever that is), and if [n] is a nat then so is [S n]".
    The interpretation of [O] as zero and [S] as successor/plus one
    comes from the way that we use nat values, by writing functions to
    do things with them, proving things about them, and so on.  Your
    definition of [bin] should be correspondingly simple; it is the
    functions you will write next that will give it mathematical
    meaning.)

    (b) Next, write an increment function for binary numbers, and a
        function to convert binary numbers to unary numbers.

    (c) Finally, prove that your increment and binary-to-unary
        functions commute: that is, incrementing a binary number and
        then converting it to unary yields the same result as first
        converting it to unary and then incrementing.  
*)

(* FILL IN HERE *)
(** [] *)


(* this one is for extra credit. It is difficult *)

(** **** Exercise: 5 stars (binary_inverse) *)
(** This exercise is a continuation of the previous exercise about
    binary numbers.  You will need your definitions and theorems from
    the previous exercise to complete this one.

    (a) First, write a function to convert natural numbers to binary
        numbers.  Then prove that starting with any natural number,
        converting to binary, then converting back yields the same
        natural number you started with.

    (b) You might naturally think that we should also prove the
        opposite direction: that starting with a binary number,
        converting to a natural, and then back to binary yields the
        same number we started with.  However, it is not true!
        Explain what the problem is.

    (c) Define a function [normalize] from binary numbers to binary
        numbers such that for any binary number b, converting to a
        natural and then back to binary yields [(normalize b)].  Prove
        it.
*)
