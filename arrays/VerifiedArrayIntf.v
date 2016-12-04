Require Import List.
Require Import VerifiedNatIntf.
Require Import ArrayIntf CanonicalArrImpl CommutingArrayIntf.

Set Implicit Arguments.

(* An extension of CommutingArrayInterface that include various correctness
 * properties that correct implementations of the array interface should
 * satisfy. *)
Module Type VerifiedArrayInterface (N:VerifiedNatInterface)
    <: CommutingArrayInterface N.
  Parameter M : Type -> Type.

  Parameter make : forall A : Type, nat -> A -> M A.
  Parameter len : forall A : Type, M A -> N.N.
  Parameter get : forall A : Type, M A -> N.N -> option A.
  Parameter set : forall A : Type, M A -> N.N -> A -> M A.
  Parameter concat : forall A : Type, M A -> M A -> M A.

  Parameter convert : forall A : Type, M A -> list A.

  Module Canon := CanonicalArrayImpl N.

  Axiom make_commutes : forall (A : Type) n (x : A),
    convert (make n x) = Canon.make n x.
  Axiom len_commutes : forall (A : Type) (l : M A),
    len l =  Canon.len (convert l).
  Axiom get_commutes : forall A (l : M A) index,
    get l index = Canon.get (convert l) index.
  Axiom set_commutes : forall A (l : M A) index x,
    convert (set l index x) = Canon.set (convert l) index x.
  Axiom concat_commutes : forall A (l : M A) (l' : M A),
    convert (concat l l') = Canon.concat (convert l) (convert l').

  Axiom concat_assoc : forall A (l1 l2 l3 : M A),
    convert (concat (concat l1 l2) l3) = convert (concat l1 (concat l2 l3)).
End VerifiedArrayInterface.

(* A functor which produces an implementation of VerifiedArrayInterface from
 * an implementation of CommutingArrayInterface. *) 
Module VerifiedCommutingArrayInterface (N:VerifiedNatInterface)
                                       (A:CommutingArrayInterface N)
    : VerifiedArrayInterface N.
  Definition M := A.M.
  Definition make := A.make.
  Definition len := A.len.
  Definition get := A.get.
  Definition set := A.set.
  Definition concat := A.concat.
  Definition convert := A.convert.

  Module Canon := A.Canon.

  Definition make_commutes := A.make_commutes.
  Definition len_commutes := A.len_commutes.
  Definition get_commutes := A.get_commutes.
  Definition set_commutes := A.set_commutes.
  Definition concat_commutes := A.concat_commutes.

  Lemma concat_assoc : forall A (l1 l2 l3 : M A),
      convert (concat (concat l1 l2) l3) = convert (concat l1 (concat l2 l3)).
    intros A l1 l2 l3.
    rewrite A.concat_commutes.
    rewrite A.concat_commutes.
    rewrite A.concat_commutes.
    rewrite A.concat_commutes.
    rewrite A.Canon.concat_def.
    rewrite A.Canon.concat_def.
    rewrite A.Canon.concat_def.
    rewrite A.Canon.concat_def.
    symmetry; apply app_assoc.
  Defined.
End VerifiedCommutingArrayInterface.