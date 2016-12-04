Require Import NatIntf CanonicalNatImpl.

(* An extension of NatInterface for implementations that commute with
 * CanonicalNat *)
Module Type CommutingNatInterface <: NatInterface.
  Parameter N : Type.

  Parameter zero : N.
  Parameter succ : N -> N.
  Parameter pred : N -> N.
  Parameter add : N -> N -> N.
  Parameter sub : N -> N -> N.
  Parameter comp : N -> N -> comparison.

  Parameter convert : N -> CanonicalNat.N.

  (* We require convert to be injective, because it makes a lot of subsequent
   * proofs a lot simpler. This requirement is not necessary, however. *)
  Axiom convert_injective : forall n n' : N, convert n = convert n' -> n = n'.

  Axiom zero_commutes : convert zero = CanonicalNat.zero.
  Axiom succ_commutes : forall n : N,
    convert (succ n) = CanonicalNat.succ (convert n).
  Axiom pred_commutes : forall n : N,
    convert (pred n) = CanonicalNat.pred (convert n).
  Axiom add_commutes : forall n n' : N,
    convert (add n n') = CanonicalNat.add (convert n) (convert n').
  Axiom sub_commutes : forall n n' : N,
    convert (sub n n') = CanonicalNat.sub (convert n) (convert n').
  Axiom comp_commutes : forall n n' : N,
    comp n n' = CanonicalNat.comp (convert n) (convert n').
End CommutingNatInterface.
