Require Import List.
Require Import VerifiedNatIntf.
Require Import ArrayIntf CanonicalArrImpl CommutingArrayIntf.

Set Implicit Arguments.

Module Type VerifiedArrayInterface (N:VerifiedNaturalInterface)
    <: ArrayInterface N.
  Parameter M : Type -> Type.

  Parameter make : forall A : Type, nat -> A -> M A.
  Parameter len : forall A : Type, M A -> N.N.
  Parameter get : forall A : Type, M A -> N.N -> option A.
  Parameter set : forall A : Type, M A -> N.N -> A -> M A.
  Parameter concat : forall A : Type, M A -> M A -> M A.

  Parameter inject : forall A : Type, M A -> list A.

  Module Canon := CanonicalArrayImpl N.

  Axiom make_commutes : forall (A : Type) n (x : A),
    inject (make n x) = Canon.make n x.
  Axiom len_commutes : forall (A : Type) (l : M A),
    len l =  Canon.len (inject l).
  Axiom get_commutes : forall A (l : M A) index,
    get l index = Canon.get (inject l) index.
  Axiom set_commutes : forall A (l : M A) index x,
    inject (set l index x) = Canon.set (inject l) index x.
  Axiom concat_commutes : forall A (l : M A) (l' : M A),
    inject (concat l l') = Canon.concat (inject l) (inject l').

  Axiom concat_assoc : forall A (l1 l2 l3 : M A),
    inject (concat (concat l1 l2) l3) = inject (concat l1 (concat l2 l3)).
End VerifiedArrayInterface.

Module VerifiedCommutingArrayInterface (N:VerifiedNaturalInterface)
                                       (A:CommutingArrayInterface N)
    : VerifiedArrayInterface N.
  Definition M := A.M.
  Definition make := A.make.
  Definition len := A.len.
  Definition get := A.get.
  Definition set := A.set.
  Definition concat := A.concat.
  Definition inject := A.inject.

  Module Canon := A.Canon.

  Definition make_commutes := A.make_commutes.
  Definition len_commutes := A.len_commutes.
  Definition get_commutes := A.get_commutes.
  Definition set_commutes := A.set_commutes.
  Definition concat_commutes := A.concat_commutes.

  Lemma concat_assoc : forall A (l1 l2 l3 : M A),
      inject (concat (concat l1 l2) l3) = inject (concat l1 (concat l2 l3)).
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