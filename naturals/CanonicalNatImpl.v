Require Import NatIntf.

Module CanonicalNaturalImpl <: NaturalInterface.
  Definition N := nat.
  Definition zero := 0.
  Definition succ := S.
  Definition pred := pred.
(*
  Definition add := plus.
  Definition sub := minus.
*)
End CanonicalNaturalImpl.