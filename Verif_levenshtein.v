Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Lists.List.
Require Import Coq.Init.Peano.
Require Import Omega.
Require Import Coq.Program.Equality.

Definition lstring := list ascii.

Section Isomorphism.

Fixpoint to_string (l : lstring) : string :=
  match l with
  | nil => EmptyString
  | cons x xs => String x (to_string xs)
  end.
Fixpoint to_lstring (s : string) : lstring :=
  match s with
  | EmptyString => nil
  | String x xs => cons x (to_lstring xs)
  end.
Lemma lstring_same : forall l, to_lstring (to_string l) = l.
Proof. intro l; induction l; simpl; f_equal; auto. Defined.

Lemma string_same : forall s, to_string (to_lstring s) = s.
Proof. intro s; induction s; simpl; f_equal; auto. Defined.

Definition on_string (f : lstring -> lstring) (s : string) : string :=
  to_string (f (to_lstring s)).
Definition on_lstring (f : string -> string) (l : lstring) : lstring :=
  to_lstring (f (to_string l)).

End Isomorphism.

Open Scope list_scope.
Import ListNotations.

Definition insert (i : nat) (c : ascii) (s : lstring) : lstring :=
  firstn i s ++ [c] ++ skipn i s.
Definition delete (i : nat) (s : lstring) : lstring :=
  firstn i s ++ skipn (S i) s.
Definition update (i : nat) (c : ascii) (s : lstring) : lstring :=
  firstn i s ++ [c] ++ skipn (S i) s.

Eval compute in (on_string (insert 1 "!") "joomy").
Eval compute in (on_string (delete 1) "joomy").
Eval compute in (on_string (update 0 "J") "joomy").

Inductive edit : lstring -> lstring -> Type :=
| insertion (i : nat) (c : ascii) (s : lstring) : edit s (insert i c s)
| deletion (i : nat) (s : lstring) : edit s (delete i s)
| substitution (i : nat) (c : ascii) (s : lstring) : edit s (update i c s).

Inductive chain : lstring -> lstring -> Type :=
| same : forall s, chain s s
| change : forall s s' t, edit s s' -> chain s' t -> chain s t.

Fixpoint chain_length {s t : lstring} (c : chain s t) : nat :=
  match c with
  | same _ => 0
  | change _ _ _ _ c' => chain_length c'
  end.

Lemma weaken_edit (a : ascii) (s1 s2 : lstring) (e : edit s1 s2) : edit (cons a s1) (cons a s2).
inversion e.
* pose (insertion (S i) c (cons a s1)). auto.
* pose (deletion (S i) (cons a s1)). auto.
* pose (substitution (S i) c (cons a s1)). auto.
Qed.

Lemma insert_chain : forall c s1 s2, chain s1 s2 -> chain s1 (cons c s2).
intros.
apply (change _ (cons c s1)).
pose (insertion 0 c s1) as e.
auto.
induction H.
constructor.
pose (weaken_edit c s s' e) as e'.
apply (change _ _ _ e' IHchain).
Qed.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2).
intros.
induction s1; simpl.
constructor.
apply insert_chain.
auto.
Qed.

Lemma delete_chain : forall c s, chain (cons c s) s.
intros.
apply (change _ s).
pose (deletion 0 (cons c s)) as e.
unfold delete in *.
simpl in e.
auto.
constructor.
Qed.

Fixpoint levenshtein_chain (s t : lstring) : chain s t.
Admitted.
