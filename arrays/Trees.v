(* Various definitions and lemmas involving binary trees *)

Require Import Arith List.
Require Import VerifiedNatIntf ArrayIntf CanonicalArrImpl.
Require Import Cpdt.CpdtTactics.

Import ListNotations.
Set Implicit Arguments.

Module TreeDefns (Natl : VerifiedNaturalInterface).

  Definition one := Natl.succ Natl.zero.

  Inductive tree (A : Type) : Type :=
    | Empty : tree A
    | Leaf : A -> tree A
    | Node : Natl.N -> Natl.N -> tree A -> tree A -> tree A.

  Definition T := tree.

  Fixpoint add A (x : A) (t : tree A) : tree A :=
    match t with
    | Empty => Leaf x
    | Leaf y => Node one one (Leaf x) (Leaf y)
    | Node nl nr l r =>
        match Natl.comp nl nr with
        | Lt => Node (Natl.succ nl) nr (add x l) r
        | Eq
        | Gt => Node nl (Natl.succ nr) l (add x r)
        end
    end.

  Fixpoint make A (m : nat) (x : A) : tree A :=
    match m with
    | O => Empty A
    | S m' => add x (make m' x)
    end.

  Definition len A (t : tree A) : Natl.N :=
    match t with
    | Empty => Natl.zero
    | Leaf _ => Natl.succ Natl.zero
    | Node nl nr _ _ => Natl.add nl nr
    end.

  Fixpoint get A (t : tree A) (index : Natl.N) : option A :=
    match t, index with
    | Empty, _ => None
    | Leaf x, _ =>
        match Natl.comp index Natl.zero with
        | Lt
        | Eq => Some x
        | Gt => None
        end
    | Node nl nr l r, i =>
        match Natl.comp i nl with
        | Lt => get l i
        | Eq
        | Gt => get r (Natl.sub i nl)
        end
    end.

  Fixpoint set A (t : tree A) (index : Natl.N) (x : A) : tree A :=
    match t, index with
    | Empty, _ => Empty A
    | Leaf y, _ =>
        match Natl.comp index Natl.zero with
        | Lt
        | Eq => Leaf x
        | Gt => Leaf y
        end
    | Node nl nr l r, i =>
        match Natl.comp i nl with
        | Lt => Node nl nr (set l i x) r
        | Eq
        | Gt => Node nl nr l (set r (Natl.sub i nl) x)
        end
    end.

  Definition concat A (t1 t2 : tree A) : tree A :=
    match t1, t2 with
    | Empty, _ => t2
    | _, Empty => t1
    | _, _ => Node (len t1) (len t2) t1 t2
    end.

  (** Properties and lemmas **)

  Fixpoint count A (t : tree A) : Natl.N :=
    match t with
    | Empty => Natl.zero
    | Leaf _ => Natl.succ (Natl.zero)
    | Node _ _ l r => Natl.add (count l) (count r)
    end.

  Fixpoint well_formed A (t : tree A) :=
    match t with
    | Empty => True
    | Leaf _ => True
    | Node nl nr l r => (count l = nl) /\ (count r = nr) /\ well_formed l /\ well_formed r
    end.

  Lemma add_inc : forall A (x:A) (t:tree A),
      count (add x t) = Natl.succ (count t).
    intros A x t.
    induction t as [| | nl nr l IHl r IHr ]; simpl; auto.
      (* Leaf *)
      rewrite Natl.add_succ; rewrite Natl.add_zero; reflexivity.
      (* Node *)
      remember (Natl.comp nl nr) as clr.
      Hint Resolve Natl.add_succ_right.
      destruct clr; simpl; rewrite <- Natl.add_succ; crush.
  Defined.

  Lemma add_preserves : forall A (x : A) (t : tree A),
      well_formed t -> well_formed (add x t).
    intros A x t.
    induction t as [| |nl nr l IHl r IHr]; simpl; auto.
      (* Node *)
      intros Hwf.
      Hint Resolve add_inc.
      destruct (Natl.comp nl nr); crush.
  Defined.

  Lemma make_wf : forall A n (x:A), well_formed (make n x).
    intros A m x.
    Hint Resolve add_preserves.
    induction m; crush.
  Defined.

  Lemma len_wf : forall A (t:tree A), well_formed t -> len t = count t.
    intros A t.
    destruct t; crush.
  Defined.

  Lemma set_count : forall A (t:tree A) i x,
      count (set t i x) = count t.
    intros A t.
    induction t as [| | nl nr l IHl r IHr ];
        intros i x; auto; simpl.
      (* Leaf _ *)
      destruct (Natl.comp i Natl.zero); auto.
      (* Node *)
      destruct (Natl.comp i nl); simpl.
        rewrite (IHr (Natl.sub i nl) x); reflexivity.
        rewrite (IHl i x); reflexivity.
        rewrite (IHr (Natl.sub i nl) x); reflexivity.
  Defined.

  Lemma set_wf : forall A (t:tree A) i x,
      well_formed t -> well_formed (set t i x).
    intros A t.
    induction t as [| | nl nr l IHl r IHr ];
        intros i x; simpl.
      (* Empty *)
      auto.
      (* Leaf *)
      destruct (Natl.comp i Natl.zero); auto.
      (* Node *)
      intros Hwf.
      destruct Hwf as (Hcr & Hcl & Hwfl & Hwfr).
      destruct (Natl.comp i nl);
          simpl;
          rewrite (set_count _ _ _).
        pose (IHr (Natl.sub i nl) x); auto.
        pose (IHl i x Hwfl); auto.
        pose (IHr (Natl.sub i nl) x); auto.
  Defined.

  Lemma concat_wf : forall A (t1 t2 : tree A),
      well_formed t1 -> well_formed t2 -> well_formed (concat t1 t2).
    intros A t1 t2.
    destruct t1; destruct t2; crush.
  Defined.

End TreeDefns.
