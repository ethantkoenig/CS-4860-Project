Require Import Arith Cpdt.CpdtTactics List Omega.
Require Import VerifiedNatIntf CanonicalArrImpl CommutingArrayIntf Trees.

Set Implicit Arguments.
Import ListNotations.

(* An implementation of CommutingArrayInterface using binary trees. *) 
Module TreeArrayImpl (Natl : VerifiedNatInterface)
    : CommutingArrayInterface Natl.

  Module T := TreeDefns Natl.
  Module Canon := CanonicalArrayImpl Natl.

  Inductive tree (A : Type) : Type :=
    | Verified : forall (t:T.tree A), T.well_formed t -> tree A.

  Definition M := tree.

  Definition make A (n:nat) (x:A) : tree A :=
    Verified (T.make n x) (T.make_wf n x).

  Definition len A (t:tree A) : Natl.N :=
    match t with
    | Verified t' _ => T.len t'
    end.

  Definition get A (t:tree A) (n:Natl.N) : option A :=
    match t with
    | Verified t' _ => T.get t' n
    end.

  Definition set A (t:tree A) (n:Natl.N) (x:A) : tree A :=
    match t with
    | Verified t' Hwf => Verified (T.set t' n x) (T.set_wf _ _ _ Hwf)
    end.

  Definition concat A (t1 t2:tree A) : tree A :=
    match t1, t2 with
    | Verified t1' H1, Verified t2' H2 =>
        Verified (T.concat t1' t2') (T.concat_wf _ _ H1 H2)
    end.

  Fixpoint convert' A (t:T.tree A ) : list A :=
    match t with
    | T.Empty => []
    | T.Leaf x => [x]
    | T.Node _ _ l r => Canon.concat (convert' l) (convert' r)
    end.

  Definition convert A (t:tree A) : list A :=
    match t with
    | Verified t' _ => convert' t'
    end.

  (** Commutativity lemmas **)

  Lemma Tmake_add : forall A (t:T.tree A) (n:nat) (x:A),
      convert' t = Canon.make n x ->
        convert' (T.add x t) = Canon.make (S n) x.
    intros A t.
    induction t as [| | nl nr l IHl r IHr];
        intros n x; simpl; intros Heq.
      (* Empty *)
      rewrite Canon.make_def; rewrite <- Heq; auto.
      (* Leaf a *)
      rewrite Canon.make_def.
      rewrite Canon.concat_def.
      rewrite Heq; auto.
      (* Node nl nr l IHl r IHr *)
      destruct (Canon.make_concat Heq) as (m & m' & Hl & Hr & Hsum).
      destruct (Natl.comp nl nr); simpl;
          [ (* Eq *) rewrite Hl; rewrite (IHr _ _ Hr) |
            (* Lt *) rewrite (IHl _ _ Hl); rewrite Hr |
            (* Gt *) rewrite Hl; rewrite (IHr _ _ Hr)];
          rewrite Canon.concat_make;
          [ (* Eq *) rewrite <- plus_n_Sm |
            (* Lt *) simpl |
            (* Gt *) rewrite <- plus_n_Sm];
          rewrite Hsum; auto.
  Defined.

  Lemma Tmake_commutes : forall A (n:nat) (x:A),
      convert' (T.make n x) = Canon.make n x.
    intros A n x.
    induction n;
        rewrite Canon.make_def; auto.
      (* S n *)
      pose (Tmake_add (T.make n x) IHn) as IHn'.
      rewrite Canon.make_def in IHn'.
      exact IHn'.
  Defined.

  Lemma make_commutes : forall A (n:nat) (x:A),
      convert (make n x) = Canon.make n x.
    intros; simpl; apply Tmake_commutes.
  Defined.

  Lemma Tlen_commutes : forall A (t:T.tree A),
      T.well_formed t -> T.len t = Canon.len (convert' t).
    intros A t.
    induction t as [|a| nl nr l IHl r IHr];
        simpl; intros Hwf.
      (* Empty *)
      symmetry; apply Canon.len_def.
      (* Leaf *)
      rewrite (Canon.len_def [a]); rewrite (Canon.len_def []); auto.
      (* Node *)
      destruct Hwf as (Hl & Hr & Hwfl & Hwfr).
      rewrite (Canon.len_concat _ _).
      simpl in IHl; rewrite <- (IHl Hwfl).
      simpl in IHr; rewrite <- (IHr Hwfr).
      rewrite <- Hl; rewrite <- Hr.
      rewrite (T.len_wf _ Hwfl); rewrite (T.len_wf _ Hwfr).
      reflexivity.
  Defined.

  Lemma len_commutes : forall A (t:tree A), len t = Canon.len (convert t).
    intros.
    destruct t as [t' Hwf].
    simpl; apply (Tlen_commutes _ Hwf).
  Defined.

  Lemma Tget_commutes : forall A (t:T.tree A) n,
      T.well_formed t -> T.get t n = Canon.get (convert' t) n.
    intros A t.
    induction t as [| | nl nr l IHl r IHr];
        intros n; simpl; intros Hwf.
      (* Empty *)
      rewrite (Canon.get_def _); reflexivity.
      (* Leaf a *)
      rewrite (Canon.get_def _).
      rewrite (Canon.get_def _); reflexivity.
      (* Node nl nr l r *)
      simpl in IHl; simpl in IHr.
      destruct Hwf as (Hnl & Hnr & Hl & Hr).
      rewrite (Canon.get_concat _ _).
      rewrite <- Hnl.
      rewrite <- (T.len_wf _ Hl).
      rewrite <- (Tlen_commutes _ Hl).
      rewrite (IHl n Hl).
      rewrite (IHr (Natl.sub n (T.len l)) Hr); auto.
  Defined.

  Lemma get_commutes : forall A (t:tree A) n,
      get t n = Canon.get (convert t) n.
    intros A t n.
    destruct t as [t' Hwf]; simpl.
    apply (Tget_commutes _ n Hwf).
  Defined.

  Lemma Tset_commutes : forall A (t:T.tree A) n x,
      T.well_formed t -> convert' (T.set t n x) = Canon.set (convert' t) n x.
    intros A t.
    induction t as [| | nl nr l IHl r IHr];
        intros n x Hwf; simpl.
      (* Empty *)
      rewrite Canon.set_def; reflexivity.
      (* Leaf a *)
      rewrite Canon.set_def.
      destruct (Natl.comp n Natl.zero); auto.
        (* Gt *)
        rewrite Canon.set_def; auto.
      (* Node nl nr l r *)
      destruct Hwf as (Hnl & Hnr & Hwfl & Hwfr).
      rewrite Canon.set_concat.
      rewrite <- Hnl.
      rewrite <- (T.len_wf _ Hwfl).
      rewrite <- (Tlen_commutes _ Hwfl).
      rewrite <- (IHl n x Hwfl).
      rewrite <- (IHr (Natl.sub n (T.len l)) x Hwfr).
      destruct (Natl.comp n (T.len l)); auto.
  Defined.

  Lemma set_commutes : forall A (t:tree A) n x,
      convert (set t n x) = Canon.set (convert t) n x.
    intros.
    destruct t as [t' Hwf]; simpl.
    apply (Tset_commutes _ n x Hwf).
  Defined.

  Lemma Tconcat_commutes : forall A (t t':T.tree A),
      convert' (T.concat t t') = Canon.concat (convert' t) (convert' t').
    intros A t t'.
    destruct t as [|a|nl nr l r];
        rewrite Canon.concat_def; auto; simpl.
      (* Leaf a *)
      destruct t' as [|a'| nl' nr' l' r'];
          auto; simpl.
        (* Leaf a' *)
        rewrite Canon.concat_def; auto.
        (* Node nl' nr' l' r' *)
        rewrite Canon.concat_def; rewrite Canon.concat_def; auto.
      (* Node nl nr l r *)
      destruct t' as [|a'| nl' nr' l' r'];
          simpl;
          [ rewrite app_nil_r (* Empty *)
          | rewrite Canon.concat_def (* Leaf *)
          | rewrite Canon.concat_def ]; (* Node *)
          auto.
  Defined.

  Lemma concat_commutes : forall A (t t':tree A),
      convert (concat t t') = Canon.concat (convert t) (convert t').
    intros A t1 t2.
    destruct t1 as [t1 H1]; destruct t2 as [t2 H2].
    simpl.
    apply Tconcat_commutes.
  Defined.
End TreeArrayImpl.
