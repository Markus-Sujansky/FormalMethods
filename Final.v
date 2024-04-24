From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. 
Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Import Maps.
From Coq Require Import List.
Require Import Ascii String.
Require Import Program.

Inductive Element : Type :=
    | H | He | Li | Be | B | C | N | O | F | Ne | Na | Mg | Al | Si | P | S | Cl | Ar | K | Ca
    | Ga | Ge | As | Se | Br | Kr | Rb | Sr | In | Sn | Sb | Te | I | Xe | Cs | Ba | Tl | Pb
    | Bi | Po | At | Rn.
  
Inductive Charge : Type :=
    | Positive | Negative | Neutral.

Inductive Ion : Type :=
    | VI (e : Element) (c : Charge) (n : nat).
  
Definition OuterShell (i : Ion) : nat :=
    match i with
    | VI H _ _ => 2
    | VI He _ _ => 2
    | VI _ _ _ => 8
    end.
  
Inductive Bond : Type :=
   | Single.

Definition getElement (ion : Ion) : Element :=
    match ion with
    | VI e _ _ => e
    end.

Definition getValence (ion : Ion) : nat :=
    match ion with
    | VI _ _ v => v
    end.

  
  (* Helper function to check if an ion is fully bonded *)
Definition fully_bonded (ion : Ion) (bond : nat) : bool :=
    match ion with 
    | VI _ _ v => if (v + bond) =? (OuterShell ion) then true else false
    end.

Inductive BondOption : Type :=
    | Some (n m : nat)
    | None.

  (* Function to find the correct orientation and bonds for the molecule *)

Definition orient_molecule (m1 m2 m3 : Ion) : BondOption :=
    match getValence m1 with
    | 5 => match getValence m2 with 
        | 4 => if ((getValence m3) =? 7) then Some 3 1 else None
        | _ => None
        end
    | 6 => match getValence m2 with 
        | 4 => if ((getValence m3) =? 6) then Some 2 2 else None
        | 5 => if ((getValence m3) =? 7) then Some 2 1 else None
        | _ => None
        end
    | 7 => match getValence m2 with
        | 4 => if ((getValence m3) =? 5) then Some 1 2 else None
        | 5 => if ((getValence m3) =? 6) then Some 1 2 else None
        | 6 => if ((getValence m3) =? 7) then Some 1 1 else None
        | _ => None
        end
    | _ => None
    end.
  
 

Theorem Valence_Filled : forall (x y z: Ion) (n m : nat), 
    (orient_molecule x y z = Some n m) -> 
        fully_bonded x n && fully_bonded y (n+m) && fully_bonded z m.
            (*Throws an error for some reason about the line "fully_bonded x n && fully_bonded y (n+m) && fully_bonded z m", something
                about needing to be a set, not a bool*)
        (*AKA:
            If our function returns Some n m, then applying values n and m for bond
            representation to the function "fully_bonded" will also return true for
            all three ions
        *)
