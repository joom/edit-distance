Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Init.Peano.
Require Import Omega.
Require Import Coq.Program.Equality.

Open Scope string_scope.
Infix "::" := String (at level 60, right associativity) : string_scope.
Notation "[ x ]" := (String x EmptyString) : string_scope.
Notation "[ x ; y ; .. ; z ]" := (String x (String y .. (String z EmptyString) ..)) : string_scope.

Theorem app_empty_end : forall (s : string), s = s ++ "".
Proof.
  induction s; simpl in |- *; auto.
  rewrite <- IHs; auto.
Qed.

Theorem app_ass : forall l m n:string, (l ++ m) ++ n = l ++ m ++ n.
Proof.
  intros. induction l; simpl in |- *; auto.
  now_show (a :: (l ++ m) ++ n = a :: l ++ m ++ n).
  rewrite <- IHl; auto.
Qed.

Fixpoint rev (s: string) : string :=
  match s with
    | EmptyString => EmptyString
    | String a s' => rev s' ++ String a EmptyString
  end.

Lemma distr_rev : forall x y:string, rev (x ++ y) = rev y ++ rev x.
Proof.
  induction x as [| a l IHl].
  destruct y as [| a l].
  simpl in |- *.
  auto.

  simpl in |- *.
  apply app_empty_end; auto.

  intro y.
  simpl in |- *.
  rewrite (IHl y).
  apply (app_ass (rev y) (rev l) [a]).
Qed.

Remark rev_unit : forall (l:string) (a:ascii), rev (l ++ [a]) = a :: rev l.
Proof.
  intros.
  apply (distr_rev l [a]); simpl in |- *; auto.
Qed.

Lemma rev_involutive : forall l:string, rev (rev l) = l.
Proof.
  induction l as [| a l IHl].
  simpl in |- *; auto.

  simpl in |- *.
  rewrite (rev_unit (rev l) a).
  rewrite IHl; auto.
Qed.

Unset Implicit Arguments.
Lemma rev_string_ind :
  forall P:string-> Prop,
    P "" ->
    (forall (a:ascii) (l:string), P (rev l) -> P (rev (a :: l))) ->
    forall l:string, P (rev l).
Proof.
  induction l; auto.
Qed.

Lemma rev_string_rec :
  forall P:string-> Set,
    P "" ->
    (forall (a:ascii) (l:string), P (rev l) -> P (rev (a :: l))) ->
    forall l:string, P (rev l).
Proof.
  induction l; auto.
Defined.
Set Implicit Arguments.

Theorem rev_ind :
  forall P:string -> Prop,
    P "" ->
    (forall (x:ascii) (l:string), P l -> P (l ++ [x])) -> forall l:string, P l.
Proof.
  intros.
  generalize (rev_involutive l).
  intros E; rewrite <- E.
  apply (rev_string_ind P).
  auto.

  simpl in |- *.
  intros.
  apply (H0 a (rev l0)).
  auto.
Qed.

Theorem rev_rec :
  forall P:string -> Set,
    P "" ->
    (forall (x:ascii) (l:string), P l -> P (l ++ [x])) -> forall l:string, P l.
Proof.
  intros.
  generalize (rev_involutive l).
  intros E; rewrite <- E.
  apply (rev_string_rec P).
  auto.

  simpl in |- *.
  intros.
  apply (H0 a (rev l0)).
  auto.
Defined.

Lemma length_app_last : forall x xs, length (xs ++ [x]) = S (length xs).
Proof.
intros x xs.
induction xs.
* auto.
* simpl. f_equal. auto.
Qed.

Fixpoint firstn (n:nat)(l:string) : string :=
  match n with
    | 0 => ""
    | S n => match l with
                | "" => ""
                | a::l => a::(firstn n l)
              end
  end.

Fixpoint skipn (n:nat)(l:string) : string :=
  match n with
    | 0 => l
    | S n => match l with
                | "" => ""
                | a::l => skipn n l
              end
  end.


Ltac now_show c := change c in |- *.

Theorem app_ass' : forall l m n:string, (l ++ m) ++ n = l ++ m ++ n.
Proof.
intros. induction l; simpl in |- *; auto.
now_show (a :: (l ++ m) ++ n = a :: l ++ m ++ n).
rewrite <- IHl; auto.
Defined.
