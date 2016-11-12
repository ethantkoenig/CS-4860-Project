Require Import NatIntf CanonicalNatImpl.


Module Type VerifiedNaturalInterface <: NaturalInterface.
  Parameter N : Type.

  Parameter zero : N.
  Parameter succ : N -> N.
  Parameter pred : N -> N.
(*
  Parameter add : N -> N -> N.
  Parameter sub : N -> N -> N.
*)
  Parameter inject : N -> CanonicalNaturalImpl.N.
  
  Axiom zero_commutes : inject zero = CanonicalNaturalImpl.zero.
  Axiom succ_commutes : forall n : N, 
                          inject (succ n) = CanonicalNaturalImpl.succ (inject n).
  Axiom pred_commutes : forall n : N,
                          inject (pred n) = CanonicalNaturalImpl.pred (inject n).
End VerifiedNaturalInterface. (* TODO more axioms *)
