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
  | 0       => (acc,false)
  | 1       => (acc,true)
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

Theorem nat_two_induction (P : nat -> Prop) :
  P 0 -> 
  P 1 -> 
  (forall n, P n -> P (S n) -> P (S (S n))) ->
  (forall n, P n).
Proof.
  intros H0 H1 IH n.
  enough (P n /\ P (S n)) by easy.
  induction n; intuition. 
Qed.

Lemma div2_eq : forall n k q b,
  div2 n k = (q, b) ->
  match b with
  | true  => 2 * q + 1 = n + 2 * k
  | false => 2 * q     = n + 2 * k
  end.
Proof.
  induction n using nat_two_induction; intros.
  - simpl in *. inversion H; subst. auto.
  - simpl in *. inversion H; subst. lia. 
  - simpl in H.
    specialize IHn with (S k) q b. 
    assert (S (S n) + 2 * k = n + 2 * S k). lia. rewrite H0.
    apply IHn; auto.
Qed.

Fixpoint encode_nat' (n n_meas : nat) :message := match n with
  | 0 => []
  | 1 => [B1]
  | S (S _) => (match n_meas with
    | 0 => [] (* Unreachable from encode_nat *)
    | S n_meas' => (match div2 n 0 with
      | (q,true)  => B1 :: encode_nat' q n_meas'
      | (q,false) => B0 :: encode_nat' q n_meas'
      end)
    end)
  end.
Definition encode_nat (n : nat) := encode_nat' n n.

Lemma encode_nat'_reduce : forall n X,
  n <= X ->
  encode_nat' n X = encode_nat' n n.
Proof.
  induction n using lt_wf_ind; intros.
  destruct n. destruct X; simpl; auto. 
  destruct n. destruct X; simpl; auto. 
  destruct X. inversion H0.
  destruct X. lia.
  destruct (div2 n 1) eqn:?. 
  remember (encode_nat' (S (S n)) (S (S X))) as E.
  assert (E = match div2 (S (S n)) 0 with | (q,true) => B1 :: encode_nat' q (S X) | (q,false) => B0 :: encode_nat' q (S X) end).
  simpl. subst. auto.
  rewrite H1.
  remember (encode_nat' (S (S n)) (S (S n))) as F.
  assert (F= match div2 (S (S n)) 0 with | (q,true) => B1 :: encode_nat' q (S n) | (q,false) => B0 :: encode_nat' q (S n) end).
  simpl; subst; auto.
  rewrite H2.
  destruct (div2 (S (S n)) 0) as [q b'] eqn:?.
  clear H1. clear H2. clear HeqF. clear HeqE. clear E. clear F.
  assert (fst (div2 (S (S n)) 0) = q). rewrite Heqp0. auto. 
  assert (q < S (S n)). rewrite <- H1. apply div2_le_0. auto.
  destruct b'.
  - rewrite H; try lia. assert (encode_nat' q (S n) = encode_nat' q q). rewrite H; try lia; auto. rewrite H3. auto. 
  - rewrite H; try lia. assert (encode_nat' q (S n) = encode_nat' q q). rewrite H; try lia; auto. rewrite H3. auto. 
Qed.
  
(** The main theorem relating encoding and decoding: encode_nat and decode_nat are inverses. This is the lemma that is needed for the final proof. *)
Lemma encode_inv : forall X,
  X = decode_nat (encode_nat X).
Proof.
  intros.
  induction X using lt_wf_ind. 
  destruct (div2 X 0) eqn:?. destruct X. auto. 
  assert (n < S X). { assert (n = fst (div2 (S X) 0)). rewrite Heqp. auto. rewrite H0. apply div2_le_0; auto. }
  specialize H with n.
  unfold encode_nat, encode_nat'; simpl; fold encode_nat'.
  destruct X; auto.
  simpl in Heqp. rewrite Heqp.
  destruct b.
  - assert (encode_nat' n (S X) = encode_nat n). { rewrite encode_nat'_reduce; auto; lia. } rewrite H1. simpl. rewrite <- H; auto. 
    pose proof (div2_eq X 1 n true Heqp). simpl in H2. lia.
  - assert (encode_nat' n (S X) = encode_nat n). apply encode_nat'_reduce; try lia. rewrite H1. simpl. rewrite <- H; auto. 
    pose proof (div2_eq X 1 n false Heqp). simpl in H2. lia.
Qed.
