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

Inductive edit : lstring -> lstring -> Type :=
| insertion (a : ascii) {s : lstring} : edit s (a :: s)
| deletion (a : ascii) {s : lstring} : edit (a :: s) s
| update (a' : ascii) (a : ascii) {s : lstring} : edit (a' :: s) (a :: s).

Inductive chain : lstring -> lstring -> Type :=
| empty : chain [] []
| skip {a : ascii} {s t : lstring} : chain s t -> chain (a :: s) (a :: t)
| change {s t u : lstring} : edit s t -> chain t u -> chain s u.

Fixpoint chain_changes {s t : lstring} (c : chain s t) : nat :=
  match c with
  | empty => 0
  | skip c' => chain_changes c'
  | change _ c' => S (chain_changes c')
  end.

Lemma same_chain : forall s, chain s s.
intros s. induction s; constructor. auto.
Defined.

Lemma ch1 : chain (to_lstring "h") (to_lstring "ah").
simpl.
apply (@change _ ["a"%char;"h"%char]).
constructor.
apply same_chain.
Defined.
Eval compute in ch1.

Lemma insert_chain : forall c s1 s2, chain s1 s2 -> chain s1 (c :: s2).
intros c s1 s2 C.
apply (@change _ (c :: s1)); constructor. auto.
Defined.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2).
intros.
induction s1; simpl.
induction s2; constructor; auto.
apply insert_chain; auto.
Defined.

(* transparent version of app_nil_r *)
Lemma tr_app_nil_r : forall {A : Type} (l : list A), l ++ [] = l.
intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.

Lemma inserts_chain_nil : forall s, chain [] s.
intros s; pose (inserts_chain s nil); rewrite (tr_app_nil_r s) in *; auto.
Defined.

Lemma delete_chain : forall c s1 s2, chain s1 s2 -> chain (c :: s1) s2.
intros c s1 s2 C.
apply (@change _ s1). constructor. auto.
Defined.

Lemma deletes_chain : forall s1 s2, chain (s1 ++ s2) s2.
intros.
induction s1; simpl.
apply same_chain.
apply delete_chain.
auto.
Defined.

Lemma deletes_chain_nil : forall s, chain s [].
intros s; pose (deletes_chain s nil); rewrite (tr_app_nil_r s) in *; auto.
Defined.

Lemma update_chain : forall c c' s1 s2, chain s1 s2 -> chain (c :: s1) (c' :: s2).
intros c c' s1 s2 C.
apply (@change _ (c' :: s1)). constructor. apply skip. auto.
Defined.

(* These aux lemmas are needed because Coq wants to use the fixpoint
   we are defining as a higher order function otherwise. *)
Lemma aux1 : forall s t x xs y ys, s = x :: xs -> t = y :: ys -> chain s ys -> chain s t.
intros s t x xs y ys eq1 eq2 r1. subst. apply (insert_chain y (x :: xs) ys r1).
Defined.

Lemma aux2 : forall s t x xs y ys,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys -> chain s t.
intros s t x xs y ys eq1 eq2 ceq C.
subst. apply skip. auto.
Defined.

Fixpoint levenshtein_chain (s : lstring) :=
  fix levenshtein_chain1 (t : lstring) : chain s t :=
    (match s as s', t as t' return s = s' -> t = t' -> chain s t with
    | nil , _ =>
        fun eq1 eq2 =>
          ltac:(rewrite eq1; apply (inserts_chain_nil t))
    | cons y ys , nil =>
        fun eq1 eq2 =>
          ltac:(rewrite eq1; rewrite eq2; apply (deletes_chain_nil (y :: ys)))
    | cons x xs, cons y ys =>
      fun eq1 eq2 =>
        match ascii_dec x y with
        | left ceq =>
          aux2 s t x xs y ys eq1 eq2 ceq (levenshtein_chain xs ys)
        | right neq =>
            let r1 := levenshtein_chain1 ys in
            let r2 := levenshtein_chain xs (y :: ys) in
            let r3 := levenshtein_chain xs ys in
            let n1 := chain_changes r1 in
            let n2 := chain_changes r2 in
            let n3 := chain_changes r3 in
            match (Nat.leb n1 n2) return chain s t with
            | true => aux1 s t x xs y ys eq1 eq2 r1
            | false =>
              match (Nat.leb n2 n3) with
              | true =>
                ltac:(rewrite eq1; rewrite eq2; apply (delete_chain x _ _ r2))
              | false =>
                ltac:(rewrite eq1; rewrite eq2; apply (update_chain x y xs ys r3))
              end
            end
        end
    end) (eq_refl s) (eq_refl t).

Eval compute in (levenshtein_chain (to_lstring "joomy") (to_lstring "Joomy")).
Eval compute in (chain_changes (levenshtein_chain (to_lstring "joomy") (to_lstring "Joomy"))).

(* still buggy about updates *)

(* My original intent was to write it using Ltac but then
   there are multiple decreasing arguments. *)
(*
Fixpoint levenshtein_chain (s : lstring) (t : lstring) : chain s t.
induction s as [| x xs].
apply inserts_chain_nil.
induction t as [| y ys].
apply deletes_chain_nil.
pose (levenshtein_chain ((x :: xs), ys)) as r1.
pose (levenshtein_chain (xs, (y :: ys))) as r2.
pose (levenshtein_chain (xs, ys)) as r3.
pose (chain_changes r1) as n1.
pose (chain_changes r2) as n2.
pose (chain_changes r3) as n3.
destruct (Nat.leb n1 n2) eqn: comp.
* (* n1 <= n2 *)
  apply (insert_chain _ _ _ r1).
* (* n1 > n2 *)
  destruct (Nat.leb n2 n3) eqn: comp2.
  - (* n2 <= n3 *)
    apply (delete_chain _ _ _ r2).
  - (* n2 > n3 *)
    apply (insert_chain y (x :: xs) ys (delete_chain x xs ys r3)).
Defined.
*)
