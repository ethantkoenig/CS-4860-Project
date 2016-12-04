Require Import VerifiedNatIntf.
Require Import CanonicalArrImpl CommutingArrayIntf.

Set Implicit Arguments.

Module CommutingCanonicalArrayImpl (N : VerifiedNaturalInterface)
    : CommutingArrayInterface N.
  Module Canon := CanonicalArrayImpl N.
  Definition M := Canon.M.
  Definition make := Canon.make.
  Definition len := Canon.len.
  Definition get := Canon.get.
  Definition set := Canon.set.
  Definition concat := Canon.concat.

  Definition inject A (m:M A) := m.

  Lemma make_commutes : forall (A : Type) n (x : A),
      inject (make n x) = Canon.make n x.
    auto.
  Defined.

  Lemma len_commutes : forall (A : Type) (l : M A),
      len l =  Canon.len (inject l).
    auto.
  Defined.

  Lemma get_commutes : forall A (l : M A) index,
      get l index = Canon.get (inject l) index.
    auto.
  Defined.

  Lemma set_commutes : forall A (l : M A) index x,
      inject (set l index x) = Canon.set (inject l) index x.
    auto.
  Defined.

  Lemma concat_commutes : forall A (l : M A) (l' : M A),
      inject (concat l l') = Canon.concat (inject l) (inject l').
    auto.
  Defined.
End CommutingCanonicalArrayImpl.
