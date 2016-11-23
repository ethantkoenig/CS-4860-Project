Require Import VerifiedNatIntf.


Module Type ArrayInterface (N : VerifiedNaturalInterface).

  Parameter M : Type -> Type.

  Parameter make : forall A : Type, nat -> A -> M A.
  Parameter len : forall A : Type, M A -> N.N.
  Parameter get : forall A : Type, M A -> N.N -> option A.
  Parameter set : forall A : Type, M A -> N.N -> A -> M A.
  Parameter concat : forall A : Type, M A -> M A -> M A.
End ArrayInterface.