Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Peano.
Require Import Omega.
Require Import Coq.Program.Equality.

Open Scope string_scope.
Print string.
Infix "::" := String (at level 60, right associativity) : string_scope.

Inductive edit : string -> string -> Type :=
| insertion (a : ascii) {s : string} : edit s (a :: s)
| deletion (a : ascii) {s : string} : edit (a :: s) s
| update (a' : ascii) (a : ascii) {s : string} : edit (a' :: s) (a :: s).

Inductive chain : string -> string -> Type :=
| empty : chain "" ""
| skip {a : ascii} {s t : string} : chain s t -> chain (a :: s) (a :: t)
| change {s t u : string} : edit s t -> chain t u -> chain s u.

Fixpoint chain_changes {s t : string} (c : chain s t) : nat :=
  match c with
  | empty => 0
  | skip c' => chain_changes c'
  | change _ c' => S (chain_changes c')
  end.

Lemma same_chain : forall s, chain s s.
intros s. induction s; constructor. auto.
Defined.

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

(* transparent string version of app_nil_r *)
Lemma tr_app_empty_r : forall {A : Type} (l : string), l ++ "" = l.
intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.

Lemma inserts_chain_empty : forall s, chain "" s.
intros s.
induction s; simpl.
constructor.
apply insert_chain. auto.
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

Lemma deletes_chain_empty : forall s, chain s "".
intros s.
induction s; simpl.
constructor. apply delete_chain. auto.
Defined.

Lemma update_chain : forall c c' s1 s2, chain s1 s2 -> chain (c :: s1) (c' :: s2).
intros c c' s1 s2 C.
apply (@change _ (c' :: s1)). constructor. apply skip. auto.
Defined.

(* These aux lemmas are needed because Coq wants to use the fixpoint
   we are defining as a higher order function otherwise. *)
Lemma aux_insert : forall s t x xs y ys, s = x :: xs -> t = y :: ys -> chain s ys -> chain s t.
intros s t x xs y ys eq1 eq2 r1. subst. apply (insert_chain y (x :: xs) ys r1).
Defined.

Lemma aux_eq_char : forall s t x xs y ys,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys -> chain s t.
intros s t x xs y ys eq1 eq2 ceq C.
subst. apply skip. auto.
Defined.

Lemma aux_both_empty : forall s t, s = "" -> t = "" -> chain s t.
intros s t eq1 eq2. subst. constructor.
Defined.

Definition min_app {t : Type} (x y z : t) (f : t -> nat) : t :=
  let n1 := f x in let n2 := f y in let n3 := f z in
  match (Nat.leb n1 n2) with
  | true => match (Nat.leb n1 n3) with | true => x | false => z end
  | false => match (Nat.leb n2 n3) with | true => y | false => z end
  end.

Fixpoint levenshtein_chain (s : string) :=
  fix levenshtein_chain1 (t : string) : chain s t :=
    (match s as s', t as t' return s = s' -> t = t' -> chain s t with
    | "" , "" => (* redundant but whatever *)
        fun eq1 eq2 => aux_both_empty s t eq1 eq2
    | "" , _ =>
        fun eq1 eq2 =>
          ltac:(rewrite eq1; apply (inserts_chain_empty t))
    | y :: ys , "" =>
        fun eq1 eq2 =>
          ltac:(rewrite eq1, eq2; apply (deletes_chain_empty (y :: ys)))
    | x :: xs, y :: ys =>
      fun eq1 eq2 =>
        match ascii_dec x y with
        | left ceq => aux_eq_char s t x xs y ys eq1 eq2 ceq (levenshtein_chain xs ys)
        | right neq =>
          let r1 := levenshtein_chain1 ys in
          let r2 := levenshtein_chain xs (y :: ys) in
          let r3 := levenshtein_chain xs ys in
          let r1' : chain s t :=
              aux_insert s t x xs y ys eq1 eq2 r1 in
          let r2' : chain s t :=
              ltac:(rewrite eq1, eq2;
                    apply (delete_chain x xs (y :: ys) r2)) in
          let r3' : chain s t :=
              ltac:(rewrite eq1, eq2;
                    apply (update_chain x y xs ys r3)) in
          min_app r1' r2' r3' chain_changes
        end
    end) (eq_refl s) (eq_refl t).

Eval compute in (levenshtein_chain "x" "X").
Eval compute in (chain_changes (levenshtein_chain "joomy" "Joomy")).
