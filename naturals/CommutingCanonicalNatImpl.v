Require Import CanonicalNatImpl CommutingNatIntf.

(* An implementation of CommutingNatInterface using the definitions in
 * CanonicalNat. Of course, all of the commutativity properties hold
 * trivially *)
Module CommutingCanonicalNat <: CommutingNatInterface.
  Definition N := CanonicalNat.N.
  Definition zero := CanonicalNat.zero.
  Definition succ := CanonicalNat.succ.
  Definition pred := CanonicalNat.pred.
  Definition add := CanonicalNat.add.
  Definition sub := CanonicalNat.sub.
  Definition comp := CanonicalNat.comp.

  Definition convert (n:N) := n.
  Lemma convert_injective : forall n n' : N, convert n = convert n' -> n = n'.
    auto.
  Defined.

  Lemma zero_commutes : convert zero = CanonicalNat.zero.
    auto.
  Defined.

  Lemma succ_commutes : forall n : N,
      convert (succ n) = CanonicalNat.succ (convert n).
    auto.
  Defined.

  Lemma pred_commutes : forall n : N,
      convert (pred n) = CanonicalNat.pred (convert n).
    auto.
  Defined.

  Lemma add_commutes : forall n n' : N,
      convert (add n n') = CanonicalNat.add (convert n) (convert n').
    auto.
  Defined.

  Lemma sub_commutes : forall n n' : N,
      convert (sub n n') = CanonicalNat.sub (convert n) (convert n').
    auto.
  Defined.

  Lemma comp_commutes : forall n n' : N,
      comp n n' = CanonicalNat.comp (convert n) (convert n').
    auto.
  Defined.
End CommutingCanonicalNat.
