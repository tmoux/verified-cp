Require Import Lia.
Require Import Bool.
Require Import List.
Import PeanoNat.Nat.
Import ListNotations.
Require Extraction.
Require Import Program.Wf.
Require Import Arith.Wf_nat.

Inductive bit := B1 | B0.

Definition broken_list := list bool.
Definition message := list bit.
Definition packet : Set := bit * bit * bit.
Definition chunk : Set := bool * bool * bool.


Fixpoint bools_to_chunks (p : broken_list) : list chunk :=  match p with
  | a :: b :: c :: rest => (a,b,c) :: bools_to_chunks rest
  | _ => []
  end.

Definition sum_chunk '((a,b,c) : chunk) := b2n a + b2n b + b2n c.

Fixpoint packets_to_message (ps : list packet) := match ps with
  | [] => []
  | (a,b,c) :: rest => a :: b :: c :: packets_to_message rest
  end.

Fixpoint message_to_packets (x : message) := match x with
  | a :: b :: c :: rest => (a,b,c) :: message_to_packets rest
  | _ => []
  end.

(** Converting a list of packets to a message and back to packets is the identity. *)
Lemma packets_message_inverses : forall ps,
  message_to_packets (packets_to_message ps) = ps.
Proof.
  intros.
  induction ps as [| p ps IH].
  - reflexivity.
  - destruct p as [[a b] c]. simpl. rewrite IH. reflexivity.
Qed.

Definition encode_packet '((a,b,c) : chunk) (x : message) : packet := 
    let '(b1, b2) := (match x with
      | []                => (B0 , B0)
      | [b1']             => (b1', B0)
      | b1' :: b2' :: bs' => (b1', b2')
    end) in
    match sum_chunk (a,b,c) with
    | 0 => (match b1, b2 with
        | B0, B0 => (B0, B1, B1)
        | B0, B1 => (B1, B1, B1)
        | B1, B0 => (B1, B0, B0)
        | B1, B1 => (B1, B0, B1)
        end)
    | 1 => if a then (match b1 with
        | B0 => (B0, B0, B1)
        | B1 => (B0, B1, B0)
        end)
        else if c then (match b1 with
        | B0 => (B1, B1, B0)
        | B1 => (B0, B1, B0)
        end)
        else (match b1, b2 with
        | B0, _  => (B0, B0, B1)
        | B1, B0 => (B1, B0, B0)
        | B1, B1 => (B1, B0, B1)
        end)
    | _ => (B0, B0, B0)
    end.

Definition decode_packet (p : packet) : message := match p with
    | (B0, B0, B0) => []
    | (B0, B0, B1) => [B0]
    | (B0, B1, B0) => [B1]
    | (B0, B1, B1) => [B0; B0]
    | (B1, B0, B0) => [B1; B0]
    | (B1, B0, B1) => [B1; B1]
    | (B1, B1, B0) => [B0]
    | (B1, B1, B1) => [B0; B1]
    end.

Fixpoint drop {A} (n : nat) (l : list A) : list A := match n, l with
  | 0  , l       => l
  | n  , []      => l
  | S n, x :: ls => drop n ls
  end.

Fixpoint encode (x : message) (p : list chunk) : list packet := match p with
  | c :: rest => let pack := encode_packet c x in
    pack :: encode (drop (length (decode_packet pack)) x) rest
  | _ => []
  end.

Fixpoint decode (x : list packet) : message := match x with
  | p :: rest => decode_packet p ++ decode rest
  | _ => []
  end.      

Definition anna (x : message) (p : broken_list) : message :=
  packets_to_message (encode x (bools_to_chunks p)).

Definition bruno (x : message) : message :=
  decode (message_to_packets x).
