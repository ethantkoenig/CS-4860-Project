Require Import VerifiedNatIntf.

(* An interface for arrays indexed by natural numbers. The indices are not
 * tied to any specific implementation of the natural numbers, but can instead
 * be any implementation of VerifiedNatInterface *)
Module Type ArrayInterface (N : VerifiedNatInterface).

  Parameter M : Type -> Type.

  (* `make n x` creates an array of length n, where each index is
   * occupied by x. We use nat as the type of n, instead of N.N,
   * so that we can recurse well-foundedly. *)
  Parameter make : forall A : Type, nat -> A -> M A.

  (* Compute the length of an array *)
  Parameter len : forall A : Type, M A -> N.N.

  (* `get n l` computes the element in index n of array l, or None
   * if n is not a valid index *)
  Parameter get : forall A : Type, M A -> N.N -> option A.

  (* `set n x l` computes an array identical to l, except that the
   * n^th index is occupied by x. *)
  Parameter set : forall A : Type, M A -> N.N -> A -> M A.

  (* Compute the concatentation of two arrays *)
  Parameter concat : forall A : Type, M A -> M A -> M A.
End ArrayInterface.
