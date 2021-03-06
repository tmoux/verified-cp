Require Import Lia.
Require Import Bool.
Require Import List.
Import PeanoNat.Nat.
Import ListNotations.
Require Extraction.

Require Import VerifiedCP.BrokenDevice.Definitions.
Require Import VerifiedCP.BrokenDevice.EncodeNat.

Section Examples.
Definition falses := [false; false; false; false; false; false; false; false; false].
Compute anna [B1; B0; B1] falses.
Compute bruno (anna [B1; B0; B1] falses).
End Examples.

(** ** Verification *)
Section Verification.
Inductive matches_broken_list : message -> broken_list -> Prop :=
  | matches_nil  : forall p,
      matches_broken_list [] p
  | matches_true : forall x p,
      matches_broken_list x p ->
      matches_broken_list (B0 :: x) (true :: p)
  | matches_false : forall x p b,
      matches_broken_list x p ->
      matches_broken_list (b :: x) (false :: p).
Hint Constructors matches_broken_list : core.

(** A modified induction principle for lists *)
Theorem list_two_induction {A} (P : list A -> Prop) :
  P [] -> 
  (forall a, P [a]) -> 
  (forall a b l, P l -> 
                   (forall c, P (c :: l)) -> 
                   P (a :: b :: l)) ->
  (forall l, P l).
Proof.
  intros H0 H1 IH l.
  enough (P l /\ (forall a, P (a :: l))) by easy.
  induction l; intuition. 
Qed.

Theorem list_three_induction {A} (P : list A -> Prop) :
  P [] -> 
  (forall a, P [a]) -> 
  (forall a b, P [a; b]) -> 
  (forall a b c l, P l -> 
                   P (a :: l) -> 
                   P (a :: b :: l) -> 
                   P (a :: b :: c :: l)) ->
  (forall l, P l).
Proof.
  intros H0 H1 H2 IH l.
  enough (P l /\ (forall a, P (a :: l)) /\ (forall a b, P (a :: b :: l))) by easy.
  induction l; intuition. 
Qed.

(** Anna's encoding respects the list of broken bits. This can basically be shown by the above induction principle (inducting on groups of threes) and casework. *)
Theorem anna_respects_broken : forall x p,
  matches_broken_list (anna x p) p.
Proof.
  intros x p.
  unfold anna.
  generalize dependent x.
  induction p as [| | | a b c p IH1 _ _] using list_three_induction; intros; auto.
  simpl.
  destruct x as [| x1 x]. 
    { unfold encode_packet. destruct a, b, c; simpl; auto. } 
  destruct x as [| x2 x].
    { destruct x1; unfold encode_packet; destruct a, b, c; simpl; auto. } 
    { destruct x1, x2, a, b, c; simpl; auto. }
Qed.


(** Two message are equal if they are the same elements, ignoring tailing zeros*)
(** This definition is still kind of stupid, may adjust it to make the proofs easier *)
Inductive equal_message : message -> message -> Prop :=
  | equal_cons : forall xs ys x,
      equal_message xs ys ->
      equal_message (x :: xs) (x :: ys)
  | equal_tail_0 : forall xs,
      Forall (fun x => x = B0) xs ->
      equal_message xs [].
Hint Constructors equal_message : core.

Inductive prefix : message -> message -> Prop :=
  | prefix_nil : forall ys,
      length ys > 0 ->
      prefix [] ys
  | prefix_cons : forall xs ys x,
      prefix xs ys ->
      prefix (x::xs) (x::ys).
Hint Constructors prefix : core.

Definition prefix_or_equal m1 m2:=
  prefix m1 m2 \/ equal_message m1 m2.

Lemma equal_empty_zeros : forall msg,
  equal_message msg [] ->
 Forall (fun x => x = B0) msg.
Proof.
  intros.
  induction msg; auto.
  inversion H; subst.
  inversion H0; subst.
  auto.
Qed.

Lemma equal_nil_cons : forall msg,
  equal_message msg [] ->
  equal_message (B0 :: msg) [].
Proof.
  intros.
  destruct msg; auto.
  constructor. constructor; auto.
  inversion H. auto.
Qed.

Lemma empty_message_prefix : forall p,
  equal_message (decode (encode [] p)) [].
Proof.
  intros.
  induction p.
  simpl. auto.
  destruct a as [[a b] c]. destruct a, b, c; simpl; try apply IHp; try (repeat apply equal_nil_cons); auto.
Qed.

Lemma one_message_prefix : forall p a,
  prefix_or_equal (decode (encode [a] p)) [a].
Proof.
  intros.
  induction p as [| [[a' b'] c'] p IH].
  simpl; left; auto.
  remember (decode (encode [] p)) as l.
  assert (Hz : Forall (fun x => x = B0) l). { apply equal_empty_zeros. subst. apply empty_message_prefix. }
  destruct a, a', b', c'; simpl; auto; rewrite <- Heql; right; repeat constructor; auto.
Qed.

Theorem decoding_encoding_preserves_order : forall msg p,
  prefix_or_equal (decode (encode msg p)) msg.
Proof.
  induction msg using list_two_induction; intros.
  - right. apply empty_message_prefix.
  - apply one_message_prefix.
  - generalize dependent b. generalize dependent a. 
    induction p as [| [[a' b'] c'] p IHp]; intros.
    + left; constructor; simpl; lia. 
    + destruct a', b', c', a, b; simpl;
      solve [ apply IHp
            | destruct (H B0 p) as [H1 | H2];
              [left | right]; constructor; auto
            | destruct (H B1 p) as [H1 | H2];
              [left | right]; constructor; auto
            | destruct (IHmsg p) as [H1 | H2];
              [left | right]; constructor; auto].
            
Qed.

Lemma prefix_len_less : forall m1 m2,
  prefix m1 m2 -> length m1 < length m2.
Proof.
  intros. induction H; simpl; lia.
Qed.

Theorem decoding_length_equal : forall msg p,
  prefix_or_equal (decode (encode msg p)) msg ->
  length (decode (encode msg p)) >= length msg ->
  equal_message (decode (encode msg p)) msg.
Proof.
  intros msg p H_pre H_len.
  pose proof (prefix_len_less (decode (encode msg p)) msg).
  destruct H_pre.
  - apply H in H0. lia.
  - auto.
Qed.

Example equal_ex : equal_message [B1; B0; B1; B0; B0; B0] [B1; B0; B1].
Proof.
  repeat constructor.
Qed.

Fixpoint count_broken (p : list chunk) := match p with
  | c :: rest => sum_chunk c + count_broken rest
  | _ => 0
  end.

(** The number of bits transmitted in a packet depends on the number of true (broken) bits in the chunk. *)
Lemma number_of_bits_in_packet: forall c msg,
  length (decode_packet (encode_packet c msg)) >= 2 - (sum_chunk c).
Proof.
  intros [[a b] c] [| [|] [| [|] x]]; destruct a, b, c; simpl; auto.
Qed.
  
(** chunk_count records the number of chunks in a list with count 0, 1, 2/3*)
Inductive chunk_count : list chunk -> nat -> nat -> nat -> Prop :=
  | cc_nil : chunk_count [] 0 0 0
  | cc_0   : forall l x y z c,
      sum_chunk c = 0 ->
      chunk_count l x y z ->
      chunk_count (c::l) (S x) y z
  | cc_1   : forall l x y z c,
      sum_chunk c = 1 ->
      chunk_count l x y z ->
      chunk_count (c::l) x (S y) z
  | cc_2_or_3   : forall l x y z c,
      sum_chunk c = 2 \/ sum_chunk c = 3 ->
      chunk_count l x y z ->
      chunk_count (c::l) x y (S z).
Hint Constructors chunk_count : core.

Lemma list_to_chunk_count : forall (l : list chunk),
    exists x y z, chunk_count l x y z.
Proof.
  intros.
  induction l; eauto.
  remember (sum_chunk a) as sum.
  destruct IHl as [x [y [z IHl]]].
  destruct a as [[a b] c].
  destruct a, b, c; pose proof Heqsum as H; simpl in H;
  repeat eexists; match goal with 
    | [ _ : sum = 0 |- _] => apply cc_0
    | [ _ : sum = 1 |- _] => apply cc_1
    | [ _ : sum = 2 |- _] => apply cc_2_or_3
    | [ _ : sum = 3 |- _] => apply cc_2_or_3
  end; simpl; try lia; apply IHl.
Qed.

Lemma chunk_count_total : forall l x y z,
  chunk_count l x y z ->
  x + y + z = length l.
Proof.
  intros. induction H; simpl; lia.
Qed.

Lemma chunk_count_sumsto_count_broken : forall l x y z,
  chunk_count l x y z -> 
  y + 2*z <= count_broken l.
Proof.
  intros. induction H; simpl; try rewrite H; lia.
Qed.  

Lemma chunk_count_decoded_length : forall msg l x y z,
  chunk_count l x y z ->
  length (decode (encode msg l)) >= 2*x + y.
Proof.
  intros.
  generalize dependent msg.
  induction H; intros; try (simpl; lia); simpl;
    rewrite app_length;
    remember (encode_packet c msg) as ep;
    pose proof (number_of_bits_in_packet c msg); rewrite <- Heqep in H1;
    specialize IHchunk_count with (drop (length (decode_packet ep)) msg); lia.
Qed.

Definition message_preserved (N K L : nat) := forall x p, 
  length p = N ->
  count_broken (bools_to_chunks p) = K ->
  length x <= L ->
  equal_message (bruno (anna x p)) x.


Fixpoint div3 (n : nat) := match n with
  | S (S (S n')) => 1 + div3 n'
  | _ => 0
  end.

Lemma bools_to_chunks_length : forall p (n : nat),
  length p = n ->
  length (bools_to_chunks p) = div3 n.
Proof.
  intros.
  generalize dependent n.
  induction p using list_three_induction; unfold div3; intros; subst; simpl; auto.
Qed.

Theorem correct_message_for_given_constraints :
  message_preserved 150 40 60.
Proof.
  unfold message_preserved.
  intros msg p H1 H2 H3.
  unfold bruno, anna. rewrite packets_message_inverses.
  remember (bools_to_chunks p) as l.
  destruct (list_to_chunk_count l) as [x [y [z Hcnt]]].
  assert (xy_lb : 2*x + y >= 60). { 
    assert (Hp_length : length l = 50). { subst. apply bools_to_chunks_length with (n := 150); auto. }
    pose proof (chunk_count_total l x y z Hcnt).
    pose proof (chunk_count_sumsto_count_broken l x y z Hcnt).
    lia. }
  pose proof (chunk_count_decoded_length msg l x y z Hcnt) as H_decoded_length.
  apply decoding_length_equal. apply decoding_encoding_preserves_order. lia.
  (* Now we know that the length of the decoded message is at least 60 (the length of the original message). *)
  (* Next, we must show that any decoded message is either a prefix of the original message, or it is equal (possibly with tailing zeros). 
     Since we know that it cannot be a strict prefix since its length is >= 60, it must indeed be equal. *)
Qed.



End Verification.

(** Verification for working with nats (instead of lists of bits) *)
Section VerificationNat.

Definition anna_nat (X : nat) (p : broken_list) :=
  anna (encode_nat X) p.
Definition bruno_nat (msg : message) : nat :=
  decode_nat (bruno msg).

(* maybe change the hypothesis to a bound on X, rather than a bound on length (encode_nat X) *)
Definition message_preserved_nat (N K L : nat) := forall X p, 
  length p = N ->
  count_broken (bools_to_chunks p) = K ->
  length (encode_nat X) <= L ->
  bruno_nat (anna_nat X p) = X.

Lemma equal_message_decoding : forall m1 m2,
  equal_message m1 m2 ->
  decode_nat m1 = decode_nat m2.
Proof.
  intros.
  induction H.
  - destruct x; simpl; auto.
  - simpl. induction xs; auto. inversion H; subst. simpl. rewrite IHxs; auto.
Qed.

Theorem correct_message_for_given_constraints_nat :
  message_preserved_nat 150 40 60.
  unfold message_preserved_nat.
  intros.
  unfold bruno_nat, anna_nat.
  rewrite encode_inv.
  apply equal_message_decoding.
  apply correct_message_for_given_constraints; auto.
Qed.

End VerificationNat.
