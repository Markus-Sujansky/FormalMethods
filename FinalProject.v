From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. 
Import ListNotations.
From Coq Require Import Strings.String.
From Coq Require Import List.
Require Import Ascii String.
Require Import Program.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Arith.PeanoNat.

(** #<h1>Markus and Jacob Formal Methods Final Project</h1># *)

(** An introduction to our project:

Our initial goal was to a model a the three-ion molecule system found in nature.
This describes how groups of three molecules natural settle in a complete state.
A complete state is described as when the valence (outer) shell of an ion is completely filled with elections.
Oftentimes, this occurs when 8 elections occupy the outer shell.

In order to do this, ions form bonds between each other. Each bond adds an electron to the valence shell of the two electrons
beind bonded.
*)

(** 
In the first part of our project, we first focused on writing up what the combinations of ions would look like.

# <!DOCTYPE html>
<html lang="en">
<head>
    <title>PDF Viewer</title>
</head>
<body>
    <!-- Embedding a PDF using <embed> -->
    <embed src="Picture1.pdf" type="application/pdf" width="100%" height="500px" />
</body>
</html> #

We determined at any complete state of 3 ions must have valence electron combinations that match one of the 6 above described combinations.

*)

(** In the next part of our project we translated our write-up into a more formalized pseudocode 
which we could then completely formalize in coq 

# <!DOCTYPE html>
<html lang="en">
<head>
    <title>PDF Viewer</title>
</head>
<body>
    <!-- Embedding a PDF using <embed> -->
    <embed src="Picture2.pdf" type="application/pdf" width="100%" height="500px" />
</body>
</html> #

*)


(** ** Elements *)
Inductive Element : Type :=
    | H | He | Li | Be | B | C | N | O | F | Ne | Na | Mg | Al | Si | P | Cl | Ar | K | Ca
    | Ga | Ge | As | Se | Br | Kr | Rb | Sr | In | Sn | Sb | Te | I | Xe | Cs | Ba | Tl | Pb
    | Bi | Po | At | Rn.

(** ** System Data Structure *)
Inductive system : Type :=
    | Sys : nat -> nat -> nat -> system.

(** ** System Operations *)
(** Functions to manipulate and query a `system`. *)

(** Increment the left and middle parts of the system. *)
Definition left_middle_add (sys: system) : system :=
  match sys with
  | Sys l m r => Sys (S l) (S m) r
  end.

(** Increment the middle and right parts of the system. *)
Definition right_middle_add (sys: system) : system :=
  match sys with
  | Sys l m r => Sys l (S m) (S r)
  end.

(** Check if all parts of a system are equal to 8. *)
Definition is_complete_state_system (sys: system) : bool :=
  match sys with
  | Sys l m r =>
    (l =? 8) && (m =? 8) && (r =? 8)
  end.

(** ** Example Systems *)
Definition example_system : system := Sys 1 2 3.

(** The system after incrementing the left and middle parts. *)
Definition modified_system : system := left_middle_add(example_system).

(** The system after incrementing the middle and right parts. *)
Definition modified_system' : system := right_middle_add(example_system).

(** ** System Adjustment Functions *)
(** Functions to adjust the left and right parts to reach a specific state. *)

(** Increment the left and middle parts to reach 8, with a limit on steps. *)
Fixpoint make_left_eight (sys: system) (max_steps : nat) : system :=
  match max_steps with
  | 0 => sys  (* Avoid infinite recursion *)
  | S n => match sys with
           | Sys l m r =>
             if l =? 8 then sys (* If left is 8, return the system *)
             else make_left_eight (Sys (S l) (S m) r) n (* Increment and recurse *)
           end
  end.

(** Increment the middle and right parts to reach 8, with a limit on steps. *)
Fixpoint make_right_eight (sys: system) (max_steps : nat) : system :=
  match max_steps with
  | 0 => sys  (* Avoid infinite recursion *)
  | S n => match sys with
           | Sys l m r =>
             if r =? 8 then sys  (* If right is 8, return the system *)
             else make_right_eight (Sys l (S m) (S r)) n (* Increment and recurse *)
           end
  end.

(** ** Eight-Eight-Eight Possibility Check *)
(** Check whether a system can reach a state where all parts are 8 within a certain number of steps. *)
Definition is_eight_eight_eight_possible (sys: system) (max_steps: nat) : bool :=
  let sys_left_eight := make_left_eight sys max_steps in
  let sys_right_eight := make_right_eight sys_left_eight max_steps in
  match sys_right_eight with
  | Sys l m _ => (m =? 8)
  end.

(** ** Example System for Testing *)
Definition example_system2 : system := Sys 5 4 7.

(** Check if it's possible to get to "eight-eight-eight" *)
Compute is_eight_eight_eight_possible (example_system2) (100).

(** ** Correct and Incorrect Systems *)
(** Definitions of correct and incorrect systems for testing the eight-eight-eight condition. *)
Definition correct_system1 : system := Sys 5 4 7.
Definition correct_system2 : system := Sys 6 4 6.
Definition correct_system3 : system := Sys 6 5 7.
Definition correct_system4 : system := Sys 7 4 5.
Definition correct_system5 : system := Sys 7 5 6.
Definition correct_system6 : system := Sys 7 6 7.

Definition incorrect_system1 : system := Sys 7 4 7.
Definition incorrect_system2 : system := Sys 1 1 2.

(** ** Tests for Correct Systems *)
Compute is_eight_eight_eight_possible correct_system1 100.
Compute is_eight_eight_eight_possible correct_system2 100.
Compute is_eight_eight_eight_possible correct_system3 100.
Compute is_eight_eight_eight_possible correct_system4 100.
Compute is_eight_eight_eight_possible correct_system5 100.
Compute is_eight_eight_eight_possible correct_system6 100.

(** ** Tests for Incorrect Systems *)
Compute is_eight_eight_eight_possible incorrect_system1 100.
Compute is_eight_eight_eight_possible incorrect_system2 100.

(** ** Other Operations *)
Definition system_eq (sys1 sys2 : system) : bool :=
  match sys1, sys2 with
  | Sys l1 m1 r1, Sys l2 m2 r2 =>
      (l1 =? l2) && (m1 =? m2) && (r1 =? r2)
  end.

Fixpoint member (v : system) (s : list system) : bool :=
  match s with 
  | nil => false
  | x :: y => if system_eq v x then true else member v y
  end.

Definition getMiddle (sys : system) : nat :=
    match sys with
    | Sys _ y _ => y
    end.

(** ** Theorem: Eight-Eight-Eight Possibility Implies Correct Middle *)
Theorem is_eight_eight_eight_possible_implies_correct :
    forall sys : system,
    is_eight_eight_eight_possible sys 100 = true ->
    getMiddle(make_right_eight(make_left_eight sys 100) 100) = 8.
Proof. 
  intros sys H.
  unfold is_eight_eight_eight_possible in H.
  destruct sys as [l m r].
  destruct (make_left_eight (Sys l m r) 100) eqn: H_left.
  destruct (make_right_eight (Sys n n0 n1) 100) eqn: H_right.
  simpl in H.
  unfold getMiddle. apply Nat.eqb_eq in H. simpl. apply H.
Qed.

(** Concluding remarks / where we believe we can take this project in the future / applications*)