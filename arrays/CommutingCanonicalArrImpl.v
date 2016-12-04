Require Import VerifiedNatIntf.
Require Import CanonicalArrImpl CommutingArrayIntf.

Set Implicit Arguments.

(* An implementation of CommutingArrayInterface using the definitions in
 * CanonicalArrayImpl. Of course, all of the commutativity properties hold
 * trivially. *)
Module CommutingCanonicalArrayImpl (N : VerifiedNaturalInterface)
    : CommutingArrayInterface N.
  Module Canon := CanonicalArrayImpl N.
  Definition M := Canon.M.
  Definition make := Canon.make.
  Definition len := Canon.len.
  Definition get := Canon.get.
  Definition set := Canon.set.
  Definition concat := Canon.concat.

  Definition convert A (m:M A) := m.

  Lemma make_commutes : forall (A : Type) n (x : A),
      convert (make n x) = Canon.make n x.
    auto.
  Defined.

  Lemma len_commutes : forall (A : Type) (l : M A),
      len l =  Canon.len (convert l).
    auto.
  Defined.

  Lemma get_commutes : forall A (l : M A) index,
      get l index = Canon.get (convert l) index.
    auto.
  Defined.

  Lemma set_commutes : forall A (l : M A) index x,
      convert (set l index x) = Canon.set (convert l) index x.
    auto.
  Defined.

  Lemma concat_commutes : forall A (l : M A) (l' : M A),
      convert (concat l l') = Canon.concat (convert l) (convert l').
    auto.
  Defined.
End CommutingCanonicalArrayImpl.
