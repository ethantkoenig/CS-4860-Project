Require Import NatIntf CanonicalNatImpl.

(* An extension of NaturalInterface for implementations that commute with
 * CanonicalNatImpl *)
Module Type CommutingNaturalInterface <: NaturalInterface.
  Parameter N : Type.

  Parameter zero : N.
  Parameter succ : N -> N.
  Parameter pred : N -> N.
  Parameter add : N -> N -> N.
  Parameter sub : N -> N -> N.
  Parameter comp : N -> N -> comparison.

  Parameter convert : N -> CanonicalNaturalImpl.N.

  (* We require convert to be injective, because it makes a lot of subsequent
   * proofs a lot simpler. This requirement is not necessary, however. *)
  Axiom convert_injective : forall n n' : N, convert n = convert n' -> n = n'.

  Axiom zero_commutes : convert zero = CanonicalNaturalImpl.zero.
  Axiom succ_commutes : forall n : N,
    convert (succ n) = CanonicalNaturalImpl.succ (convert n).
  Axiom pred_commutes : forall n : N,
    convert (pred n) = CanonicalNaturalImpl.pred (convert n).
  Axiom add_commutes : forall n n' : N,
    convert (add n n') = CanonicalNaturalImpl.add (convert n) (convert n').
  Axiom sub_commutes : forall n n' : N,
    convert (sub n n') = CanonicalNaturalImpl.sub (convert n) (convert n').
  Axiom comp_commutes : forall n n' : N,
    comp n n' = CanonicalNaturalImpl.comp (convert n) (convert n').
End CommutingNaturalInterface.
