Require Import Lia.
Require Import Bool.
Require Import List.
Import PeanoNat.Nat.
Import ListNotations.
Require Extraction.
Require Import Program.Wf.
Require Import Arith.Wf_nat.

Require Import Definitions.

Fixpoint decode_nat (x : message) : nat := match x with
  | [] => 0
  | x :: xs => (if x then 1 else 0) + 2 * decode_nat xs
  end.

Fixpoint div2 (n acc : nat) : nat * bool := match n with
  | 0       => (0,false)
  | 1       => (0,true)
  | S (S n) => div2 n (S acc)
  end.

Lemma div2_nk : forall n k,
   fst (div2 n (S k)) <= S (fst (div2 n k)) /\
   fst (div2 (S n) (S k)) <= S (fst (div2 (S n) k)).
Proof.
  induction n; intros.
  simpl. lia.
  split. destruct (IHn k). auto. 
  simpl. destruct (IHn (S k)). lia.
Qed.

Lemma div2_le : forall n k, n <> 0 -> 
  fst (div2 n k) < n + k /\
  fst (div2 (S n) k) < S n + k.
Proof.
  intros.
  generalize dependent k.
  induction n; intros. exfalso; apply H; auto.
  destruct n. simpl. lia.
  simpl. specialize IHn with k. destruct IHn as [IH1 IH2]. auto.
  split. change (div2 n (S k)) with (div2 (S (S n)) k). lia.
  destruct n. simpl. lia.
  simpl. change (div2 n (S (S k))) with (div2 (S (S n)) (S k)). 
  pose proof (div2_nk (S (S n)) k). lia.
Qed.

Lemma div2_le_0 : forall n, n <> 0 ->
  fst (div2 n 0) < n.
Proof. intros. destruct (div2_le n 0); auto. lia.
Qed.

(*
Definition encode_nat (n : nat) : message.
Proof.
  Check lt_wf_rec.
  apply (lt_wf_rec). auto.
  intros n' H.
  destruct (div2 n' 0) eqn:?.
  destruct n0, b eqn:?; simpl in *.
  - (*0, true *) exact [B1].
  - (*0, false *) exact [].
  - assert (fst (div2 n' 0) = S n0). rewrite Heqp; auto. 
    apply (cons B1). apply H with (S n0). rewrite <- H0. apply div2_le_0. destruct n'; discriminate.
  - assert (fst (div2 n' 0) = S n0). rewrite Heqp; auto. 
    apply (cons B0). apply H with (S n0). rewrite <- H0. apply div2_le_0. destruct n'; discriminate.
Defined.
Print encode_nat.
*)

Program Fixpoint encode_nat (n : nat) {measure n}: message := match div2 n 0 with
  | (0, false) => []
  | (0, true)  => [B1]
  | (m, false) => B0 :: encode_nat m
  | (m, true)  => B1 :: encode_nat m
  end.
Next Obligation.
  destruct n. inversion Heq_anonymous. subst. unfold "<>" in H.
  exfalso; apply H; auto.
  pose proof (div2_le_0 (S n)). 
  assert (fst (div2 (S n) 0) = m). rewrite <- Heq_anonymous. auto. lia.
Defined.
Next Obligation. 
  destruct n. inversion Heq_anonymous. 
  destruct (div2_le (S n) 0). auto.
  assert (fst (div2 (S n) 0) = m). rewrite <- Heq_anonymous. auto. lia.
Defined.

(** Reduction lemma. Still don't know how to properly work with Program Fixpoints... *)

Lemma encode_nat_recurse : forall n m b,
  n > 1 ->
  div2 n 0 = (m, b) ->
  encode_nat n = match b with
    | false => B0 :: encode_nat m
    | true  => B1 :: encode_nat m
  end.
Proof.
  intros.
  unfold encode_nat; simpl. rewrite fix_sub_eq. simpl. fold encode_nat. remember (div2 n 0) as A. rewrite H0. 
  destruct m. simpl. subst. admit.
  Admitted.

(** The main theorem relating encoding and decoding: encode_nat and decode_nat are inverses. This is the lemma that is needed for the final proof. *)
Lemma encode_inv : forall X,
  X = decode_nat (encode_nat X).
Proof.
  intros.
  induction X using lt_wf_ind. 
  destruct (div2 X 0) eqn:?. destruct X. auto. 
  assert (n < S X). { assert (n = fst (div2 (S X) 0)). rewrite Heqp. auto. rewrite H0. apply div2_le_0; auto. }
  specialize H with n.
  pose proof (encode_nat_recurse (S X) n b).
  (*
  destruct (n0, b0).
  rewrite H1; auto. simpl. destruct b; simpl; rewrite <- H; auto.
  admit.
  admit. *)
Admitted.

