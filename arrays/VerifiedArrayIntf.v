Require Import List.
Require Import VerifiedNatIntf.
Require Import ArrayIntf CanonicalArrImpl CommutingArrayIntf.

Set Implicit Arguments.

(* An extension of CommutingArrayInterface that include various correctness
 * properties that correct implementations of the array interface should
 * satisfy. *)
Module Type VerifiedArrayInterface (N:VerifiedNatInterface)
    <: CommutingArrayInterface N.
  Parameter M : Type -> Type.

  Parameter make : forall A : Type, nat -> A -> M A.
  Parameter len : forall A : Type, M A -> N.N.
  Parameter get : forall A : Type, M A -> N.N -> option A.
  Parameter set : forall A : Type, M A -> N.N -> A -> M A.
  Parameter concat : forall A : Type, M A -> M A -> M A.

  Parameter convert : forall A : Type, M A -> list A.

  Module Canon := CanonicalArrayImpl N.

  Axiom make_commutes : forall (A : Type) n (x : A),
    convert (make n x) = Canon.make n x.
  Axiom len_commutes : forall (A : Type) (l : M A),
    len l =  Canon.len (convert l).
  Axiom get_commutes : forall A (l : M A) index,
    get l index = Canon.get (convert l) index.
  Axiom set_commutes : forall A (l : M A) index x,
    convert (set l index x) = Canon.set (convert l) index x.
  Axiom concat_commutes : forall A (l : M A) (l' : M A),
    convert (concat l l') = Canon.concat (convert l) (convert l').

  (* Correctness properties for array implementations *)
  Axiom len_make : forall A n (x:A),
    len (make (N.convert n) x) = n.

  Axiom get_set : forall A (l : M A) (n : N.N) (x : A),
    match get (set l n x) n with
    | None => True
    | Some x' => x' = x
    end.

  Axiom len_set : forall A (l : M A) n x,
    len (set l n x) = len l.

  Axiom len_concat : forall A (l1 l2 : M A),
    len (concat l1 l2) = N.add (len l1) (len l2).    

  Axiom concat_assoc : forall A (l1 l2 l3 : M A),
    convert (concat (concat l1 l2) l3) = convert (concat l1 (concat l2 l3)).
End VerifiedArrayInterface.

(* A functor which produces an implementation of VerifiedArrayInterface from
 * an implementation of CommutingArrayInterface. *) 
Module VerifiedCommutingArrayInterface (N:VerifiedNatInterface)
                                       (C:CommutingArrayInterface N)
    : VerifiedArrayInterface N.
  Definition M := C.M.
  Definition make := C.make.
  Definition len := C.len.
  Definition get := C.get.
  Definition set := C.set.
  Definition concat := C.concat.
  Definition convert := C.convert.

  Module Canon := C.Canon.

  Definition make_commutes := C.make_commutes.
  Definition len_commutes := C.len_commutes.
  Definition get_commutes := C.get_commutes.
  Definition set_commutes := C.set_commutes.
  Definition concat_commutes := C.concat_commutes.

  Lemma len_make : forall A n (x:A),
      len (make (N.convert n) x) = n.
    intros A n x.
    apply N.convert_injective.
    rewrite len_commutes.
    rewrite make_commutes.
    rewrite C.Canon.len_make.
    reflexivity.
  Defined.

  Lemma len_concat : forall A (l1 l2 : M A),
      len (concat l1 l2) = N.add (len l1) (len l2).
    intros A l1 l2.
    repeat (rewrite C.len_commutes).
    rewrite C.concat_commutes.
    rewrite C.Canon.len_concat.
    reflexivity.
  Defined.

  Lemma get_set : forall A (l : M A) (n : N.N) (x : A),
      match get (set l n x) n with
      | None => True
      | Some x' => x' = x
      end.
    intros A l n x.
    rewrite C.get_commutes.
    rewrite C.set_commutes.
    apply C.Canon.get_set.
  Defined.

  Lemma len_set : forall A (l : M A) n x,
      len (set l n x) = len l.
    intros A l n x.
    repeat rewrite C.len_commutes.
    rewrite C.set_commutes.
    apply C.Canon.len_set.
  Defined.

  Lemma concat_assoc : forall A (l1 l2 l3 : M A),
      convert (concat (concat l1 l2) l3) = convert (concat l1 (concat l2 l3)).
    intros A l1 l2 l3.
    repeat rewrite C.concat_commutes.
    repeat rewrite C.Canon.concat_def.
    symmetry; apply app_assoc.
  Defined.
End VerifiedCommutingArrayInterface.
