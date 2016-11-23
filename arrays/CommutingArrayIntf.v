Require Import VerifiedNatIntf ArrayIntf CanonicalArrImpl.

Set Implicit Arguments.

Module Type CommutingArrayInterface (N : VerifiedNaturalInterface) <: ArrayInterface N.

  Module Canon := CanonicalArrayImpl N.

  Parameter M : Type -> Type.

  Parameter make : forall A, nat -> A -> M A.
  Parameter len : forall A, M A -> N.N.
  Parameter get : forall A, M A -> N.N -> option A.
  Parameter set : forall A, M A -> N.N -> A -> M A.
  Parameter concat : forall A, M A -> M A -> M A.

  Parameter inject : forall A : Type, M A -> Canon.M A.

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
End CommutingArrayInterface.