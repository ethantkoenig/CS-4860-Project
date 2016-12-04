Require Import CanonicalNatImpl CommutingNatIntf.

(* An implementation of CommutingNaturalInterface using the definitions in
 * CanonicalNaturalImpl. Of course, all of the commutativity properties hold
 * trivially *)
Module CommutingCanonicalNaturalImpl <: CommutingNaturalInterface.
  Definition N := CanonicalNaturalImpl.N.
  Definition zero := CanonicalNaturalImpl.zero.
  Definition succ := CanonicalNaturalImpl.succ.
  Definition pred := CanonicalNaturalImpl.pred.
  Definition add := CanonicalNaturalImpl.add.
  Definition sub := CanonicalNaturalImpl.sub.
  Definition comp := CanonicalNaturalImpl.comp.

  Definition convert (n:N) := n.
  Lemma convert_injective : forall n n' : N, convert n = convert n' -> n = n'.
    auto.
  Defined.

  Lemma zero_commutes : convert zero = CanonicalNaturalImpl.zero.
    auto.
  Defined.

  Lemma succ_commutes : forall n : N,
      convert (succ n) = CanonicalNaturalImpl.succ (convert n).
    auto.
  Defined.

  Lemma pred_commutes : forall n : N,
      convert (pred n) = CanonicalNaturalImpl.pred (convert n).
    auto.
  Defined.

  Lemma add_commutes : forall n n' : N,
      convert (add n n') = CanonicalNaturalImpl.add (convert n) (convert n').
    auto.
  Defined.

  Lemma sub_commutes : forall n n' : N,
      convert (sub n n') = CanonicalNaturalImpl.sub (convert n) (convert n').
    auto.
  Defined.

  Lemma comp_commutes : forall n n' : N,
      comp n n' = CanonicalNaturalImpl.comp (convert n) (convert n').
    auto.
  Defined.
End CommutingCanonicalNaturalImpl.
