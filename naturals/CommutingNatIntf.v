Require Import NatIntf CanonicalNatImpl.

Module Type CommutingNaturalInterface <: NaturalInterface.
  Parameter N : Type.

  Parameter zero : N.
  Parameter succ : N -> N.
  Parameter pred : N -> N.
  Parameter add : N -> N -> N.
  Parameter sub : N -> N -> N.
  Parameter comp : N -> N -> comparison.

  Parameter inject : N -> CanonicalNaturalImpl.N.

  Axiom injective : forall n n' : N, inject n = inject n' -> n = n'.
  
  Axiom zero_commutes : inject zero = CanonicalNaturalImpl.zero.
  Axiom succ_commutes : forall n : N, 
    inject (succ n) = CanonicalNaturalImpl.succ (inject n).
  Axiom pred_commutes : forall n : N,
    inject (pred n) = CanonicalNaturalImpl.pred (inject n).
  Axiom add_commutes : forall n n' : N,
    inject (add n n') = CanonicalNaturalImpl.add (inject n) (inject n'). 
  Axiom sub_commutes : forall n n' : N,
    inject (sub n n') = CanonicalNaturalImpl.sub (inject n) (inject n'). 
  Axiom comp_commutes : forall n n' : N,
    comp n n' = CanonicalNaturalImpl.comp (inject n) (inject n').
End CommutingNaturalInterface.

