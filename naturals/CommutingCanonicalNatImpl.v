Require Import CanonicalNatImpl CommutingNatIntf.

Module CommutingCanonicalNaturalImpl <: CommutingNaturalInterface.
  Definition N := CanonicalNaturalImpl.N.
  Definition zero := CanonicalNaturalImpl.zero.
  Definition succ := CanonicalNaturalImpl.succ.
  Definition pred := CanonicalNaturalImpl.pred.
  Definition add := CanonicalNaturalImpl.add.
  Definition sub := CanonicalNaturalImpl.sub.
  Definition comp := CanonicalNaturalImpl.comp.

  Definition inject (n:N) := n.
  Lemma injective : forall n n' : N, inject n = inject n' -> n = n'.
    auto.
  Defined.

  Lemma zero_commutes : inject zero = CanonicalNaturalImpl.zero.
    auto.
  Defined.

  Lemma succ_commutes : forall n : N,
      inject (succ n) = CanonicalNaturalImpl.succ (inject n).
    auto.
  Defined.

  Lemma pred_commutes : forall n : N,
      inject (pred n) = CanonicalNaturalImpl.pred (inject n).
    auto.
  Defined.

  Lemma add_commutes : forall n n' : N,
      inject (add n n') = CanonicalNaturalImpl.add (inject n) (inject n').
    auto.
  Defined.

  Lemma sub_commutes : forall n n' : N,
      inject (sub n n') = CanonicalNaturalImpl.sub (inject n) (inject n').
    auto.
  Defined.

  Lemma comp_commutes : forall n n' : N,
      comp n n' = CanonicalNaturalImpl.comp (inject n) (inject n').
    auto.
  Defined.
End CommutingCanonicalNaturalImpl.
