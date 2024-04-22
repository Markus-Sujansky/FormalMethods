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
  
Definition Molecule := list Ion.

  
  Inductive Bond : Type :=
    | Single.
  
  (* Function to calculate the number of bonds needed for each ion *)
  Definition bonds_needed (elem : Element) : nat :=
    match elem with
    | H => 1
    | _ => 2 (* Assuming all other elements need 2 bonds to fill outer shell *)
    end.

Definition getElement (ion : Ion) : Element :=
    match ion with
    | VI e _ _ => e
    end.

Definition getCharge (ion : Ion) : Charge :=
  match ion with
  | VI _ c _ => c
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

Definition resetIon (ion : Ion) (bond : nat) : Ion :=
    match ion with
    | VI e c v => match bond with
        | _ => VI e c (v + bond)
        end
    end.

    (* THE PLAN: Recursive Backtracking
    1. Check the following orientations in order:
    
        1 - 2 - 3
        1 - 2 = 3
        1 - 2 -= 3
        1 = 2 - 3
        1 = 2 = 3
        1 -= 2 - 3

    Make sure to write that the most electronegative element is to be place in the middle

    *)
  
  (* Function to find the correct orientation and bonds for the molecule *)



Fixpoint orient_molecule (m1 m2 m3 : Ion) (b1 b2 : nat) : bool :=
    match fully_bonded m1 b1 with
    | true => match fully_bonded m2 (b1+b2) with
        | true => fully_bonded m3 b2 (*CASE TRUE*)
        | false =>  if (b2 =? 3) then false else orient_molecule (resetIon m1 b1)
        (resetIon (resetIon m2 b2) b1)(resetIon m3 b2) (b1)(b2+1)
        end
    | false => match fully_bonded m2 (b1+b2) with
        | true => match fully_bonded m3 b2 with
            | true => false
            | false => match b1 with
                | 1 => match b2 with
                    | 1 => orient_molecule (resetIon m1 b1) (resetIon (resetIon m2 b2) b1)
                        (resetIon m3 b2) (b1)(b2+1)
                    | 2 => orient_molecule (resetIon m1 b1) (resetIon (resetIon m2 b2) b1)
                        (resetIon m3 b2) (b1)(b2+1)
                    | 3 => orient_molecule (resetIon m1 b1)(resetIon (resetIon m2 b2) b1)
                        (resetIon m3 b2) (b1+1)(b2-2)
                    | _ => false
                    end
                | 2 => match b2 with
                    | 1 => orient_molecule (resetIon m1 b1) (resetIon (resetIon m2 b2) b1)
                    (resetIon m3 b2) (b1)(b2+1)
                    | 2 => orient_molecule (resetIon m1 b1)(resetIon (resetIon m2 b2) b1)
                        (resetIon m3 b2) (b1+1)(b2-1)
                    | _ => false
                    end
                | 3 => false
                | _ => false
                end
            end
        | false => match b1 with
            | 1 => match b2 with
                | 1 => orient_molecule (resetIon m1 b1) (resetIon (resetIon m2 b2) b1)
                    (resetIon m3 b2) (b1)(b2+1)
                | 2 => orient_molecule (resetIon m1 b1) (resetIon (resetIon m2 b2) b1)
                    (resetIon m3 b2) (b1)(b2+1)
                | 3 => orient_molecule (resetIon m1 b1)(resetIon (resetIon m2 b2) b1)
                    (resetIon m3 b2) (b1+1)(b2-2)
                | _ => false
                end
            | 2 => match b2 with
                | 1 => orient_molecule (resetIon m1 b1) (resetIon (resetIon m2 b2) b1)
                (resetIon m3 b2) (b1)(b2+1)
                | 2 => orient_molecule (resetIon m1 b1)(resetIon (resetIon m2 b2) b1)
                (resetIon m3 b2) (b1+1)(b2-1)
                | _ => false
                end
            | 3 => false
            | _ => false
            end
        end
    end.
  

Theorem Valence_Filled : forall (x y z: Ion)(n m:nat), (*Can we even say that? Can we say any nat?*)
    orient_molecule (x y z)(n m) -> 
        andb((fully_bonded z m))andb((fully_bonded x n)(fully_bonded y (n+m))).

        (*AKA:
            If our recursive function returns TRUE, then applying values n and m for bond
            representation to the function "fully_bonded" will also return true for
            all three ions
        *)