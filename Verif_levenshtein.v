Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Peano.
Require Import Omega.
Require Import Coq.Program.Equality.

Definition insert (i : nat) (c : ascii) (s : string) : string :=
  substring 0 i s ++ String c EmptyString ++ substring i (length s) s.
Definition delete (i : nat) (s : string) : string :=
  substring 0 i s ++ substring (S i) (length s) s.
Definition update (i : nat) (c : ascii) (s : string) : string :=
  substring 0 i s ++ String c EmptyString ++ substring (S i) (length s) s.

Eval compute in (substring 1 2 "a").
Eval compute in (insert 1 "!" "joomy").
Eval compute in (delete 6 "joomy").
Eval compute in (update 0 "J" "joomy").

Inductive edit : string -> string -> Type :=
| insertion (i : nat) (c : ascii) (s : string) : edit s (insert i c s)
| deletion (i : nat) (s : string) : edit s (delete i s)
| substitution (i : nat) (c : ascii) (s : string) : edit s (update i c s).

Inductive chain : string -> string -> Type :=
| same : forall s, chain s s
| change : forall s s' t, edit s s' -> chain s' t -> chain s t.

Fixpoint chain_length {s t : string} (c : chain s t) : nat :=
  match c with
  | same _ => 0
  | change _ _ _ _ c' => chain_length c'
  end.

Lemma substring_same : forall i s, substring i i s = EmptyString.
(* intros i s. *)
(* induction s. *)
(* simpl in *. destruct i; auto. *)
(* generalize dependent s. *)
Admitted.


Lemma substring_more : forall i s, i >= length s -> substring 0 i s = s.
Admitted.

Lemma substring_all : forall s, substring 0 (length s) s = s.
Proof. intros. apply substring_more. auto. Qed.

Lemma substring_append : forall s i j k, substring i k = substring i j ++ substring j k.

Lemma weaken_edit (a : ascii) (s1 s2 : string) (e : edit s1 s2) : edit (String a s1) (String a s2).
Proof.
inversion e.
* subst.
  pose (insertion (S i) c (String a s1)) as e'.
  unfold insert in *.
  simpl in *.
  rewrite (substring_more (S (length s1)) s1) in e'.



Lemma insert_chain : forall c s1 s2, chain s1 s2 -> chain s1 (String c s2).
intros.
apply (change _ (String c s1)).
pose (insertion 0 c s1) as e.
unfold insert in e.
rewrite (substring_same 0 s1) in e.
rewrite (substring_all s1) in e.
auto.
constructor.
Defined.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2).
intros.
induction s1; simpl.
constructor.

apply insert_chain.

Admitted.

Lemma delete_chain : forall c s, chain (String c s) s.
intros.
apply (change _ s).
pose (deletion 0 (String c s)) as e.
unfold delete in *.
simpl in e.
Admitted.


Fixpoint levenshtein_chain (s t : string) : chain s t.
Admitted.
