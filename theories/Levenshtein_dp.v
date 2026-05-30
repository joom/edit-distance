(** * Dynamic-programming Levenshtein model

    This file defines a Wagner-Fischer-style dynamic-programming model over
    [string] and proves that it computes the same value as the intrinsic
    recursive [levenshtein_recursive] model.  The DP scans
    left-to-right while the intrinsic model consumes string heads, so the main
    bridge first proves a reversed-string specification and then removes the
    reversal using [levenshtein_recursive_rev]. *)

From Stdlib Require Import String Ascii Nat Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import List.

Local Open Scope string_scope.
Local Infix "::" := String (at level 60, right associativity) : string_scope.
Local Notation "[ x ]" := (String x EmptyString) : string_scope.
Local Notation "[ x ; y ; .. ; z ]" := (String x (String y .. (String z EmptyString) ..)) : string_scope.

Require Import EditDistance.Levenshtein_recursive.
Import Levenshtein.
Import ListNotations.

Open Scope nat_scope.
Local Open Scope list_scope.

(** C-style minimum for one DP cell.  [result] is the west cell, [distance] is
    the north cell, and [bDistance] is the north-west substitution candidate. *)
Definition dp_min (result distance bDistance : nat) : nat :=
  if Nat.ltb result distance then
    if Nat.ltb result bDistance then S result else bDistance
  else
    if Nat.ltb distance bDistance then S distance else bDistance.

(** One row update of the C-style DP.  [old_cache] contains the previous row,
    [distance] is the north-west cell, and [result] is the west cell. *)
Fixpoint inner_loop (a_chars : list ascii) (b_char : ascii) (old_cache : list nat)
    (distance result : nat) : list nat * nat * nat :=
  match a_chars, old_cache with
  | a_i :: a_rest, c_i :: c_rest =>
      let bDistance := if ascii_dec b_char a_i then distance else S distance in
      let new_result := dp_min result c_i bDistance in
      let '(rest_cache, fd, fr) :=
          inner_loop a_rest b_char c_rest c_i new_result in
      (new_result :: rest_cache, fd, fr)
  | _, _ => ([], distance, result)
  end.

(** String-level row update with the same state convention as [inner_loop].
    It avoids converting strings to lists inside the executable DP path. *)
Fixpoint inner_loop_string (a_str : string) (b_char : ascii) (old_cache : list nat)
    (distance result : nat) : list nat * nat * nat :=
  match a_str, old_cache with
  | String a_i a_rest, c_i :: c_rest =>
      let bDistance := if ascii_dec b_char a_i then distance else S distance in
      let new_result := dp_min result c_i bDistance in
      let '(rest_cache, fd, fr) :=
          inner_loop_string a_rest b_char c_rest c_i new_result in
      (new_result :: rest_cache, fd, fr)
  | _, _ => ([], distance, result)
  end.

(** Relates the string row update to the list row update after character
    extraction, so list-oriented VST facts can be reused. *)
Lemma inner_loop_string_eq :
  forall a_str b_char old_cache distance result,
    inner_loop_string a_str b_char old_cache distance result =
    inner_loop (list_ascii_of_string a_str) b_char old_cache distance result.
Proof.
  induction a_str as [|a_i a_rest IH]; intros b_char old_cache distance result.
  - destruct old_cache; reflexivity.
  - destruct old_cache as [|c_i c_rest]; [reflexivity|].
    cbn [inner_loop_string list_ascii_of_string inner_loop].
    rewrite IH. reflexivity.
Qed.

(** Process one target character against a full source row.  The returned list
    is the new cache row and the returned natural is the final cell of that
    row. *)
Definition process_row (a_chars : list ascii) (b_char : ascii)
    (old_cache : list nat) (bIndex : nat) : list nat * nat :=
  let '(new_cache, _, final_result) :=
      inner_loop a_chars b_char old_cache bIndex bIndex in
  (new_cache, final_result).

(** String-level row wrapper for one target character.  It returns only the
    rewritten cache row and the final cell for the row. *)
Definition process_row_string (a_str : string) (b_char : ascii)
    (old_cache : list nat) (bIndex : nat) : list nat * nat :=
  let '(new_cache, _, final_result) :=
      inner_loop_string a_str b_char old_cache bIndex bIndex in
  (new_cache, final_result).

(** Relates the string row wrapper to the list row wrapper after converting the
    source string to characters. *)
Lemma process_row_string_eq :
  forall a_str b_char old_cache bIndex,
    process_row_string a_str b_char old_cache bIndex =
    process_row (list_ascii_of_string a_str) b_char old_cache bIndex.
Proof.
  intros a_str b_char old_cache bIndex.
  unfold process_row_string, process_row.
  rewrite inner_loop_string_eq.
  reflexivity.
Qed.

(** Index-based views of the outer loop.  These definitions mirror the C loop
    closely and are used by the VST proof. *)
(** Cache contents after [k] target characters have been processed by the
    index-based outer loop. *)
Fixpoint outer_cache (a_chars b_chars : list ascii) (init : list nat)
    (k : nat) : list nat :=
  match k with
  | O => init
  | S k' =>
      let prev := outer_cache a_chars b_chars init k' in
      let b_j := nth k' b_chars Ascii.zero in
      fst (process_row a_chars b_j prev k')
  end.

(** Final row value produced at index [k] by the index-based outer loop.  At
    zero rows the C loop has not produced a row result, so the value is [0]. *)
Definition outer_result (a_chars b_chars : list ascii) (init : list nat)
    (k : nat) : nat :=
  match k with
  | O => 0
  | S k' =>
      let prev := outer_cache a_chars b_chars init k' in
      let b_j := nth k' b_chars Ascii.zero in
      snd (process_row a_chars b_j prev k')
  end.

(** Executable list-character outer loop that threads the cache through target
    characters and returns the last row result. *)
Fixpoint outer_result_run (a_chars b_chars : list ascii)
    (cache : list nat) (bIndex : nat) : nat :=
  match b_chars with
  | [] => 0
  | ch :: bs =>
      let '(cache', row_res) := process_row a_chars ch cache bIndex in
      match bs with
      | [] => row_res
      | _ :: _ => outer_result_run a_chars bs cache' (S bIndex)
      end
  end.

(** Executable string outer loop used by [levenshtein_dp].  It mirrors
    [outer_result_run] without pre-converting target characters to a list. *)
Fixpoint outer_result_run_string (a_str b_str : string)
    (cache : list nat) (bIndex : nat) : nat :=
  match b_str with
  | EmptyString => 0
  | String ch bs =>
      let '(cache', row_res) := process_row_string a_str ch cache bIndex in
      match bs with
      | EmptyString => row_res
      | String _ _ => outer_result_run_string a_str bs cache' (S bIndex)
      end
  end.

(** Relates the string outer loop to the list outer loop after converting both
    input strings to character lists. *)
Lemma outer_result_run_string_eq :
  forall a_str b_str cache bIndex,
    outer_result_run_string a_str b_str cache bIndex =
    outer_result_run (list_ascii_of_string a_str) (list_ascii_of_string b_str) cache bIndex.
Proof.
  intros a_str b_str.
  induction b_str as [|b_ch b_rest IH]; intros cache bIndex.
  - reflexivity.
  - cbn [outer_result_run_string list_ascii_of_string outer_result_run].
    rewrite process_row_string_eq.
    destruct (process_row (list_ascii_of_string a_str) b_ch cache bIndex) as [cache' row_res].
    destruct b_rest as [|b1 b_rest'].
    + reflexivity.
    + apply IH.
Qed.

(** Initial cache row for a non-empty source.  It contains the costs of
    deleting each prefix of the source before any target characters have been
    processed. *)
Definition init_cache (la : nat) : list nat :=
  map S (seq 0 la).

(** Dynamic-programming Levenshtein distance over Rocq strings.  Empty-input
    cases are handled directly, and non-empty cases run the row DP. *)
Definition levenshtein_dp (s t : string) : nat :=
  let la := String.length s in
  let lb := String.length t in
  if la =? 0 then lb
  else if lb =? 0 then la
  else outer_result_run_string s t (init_cache la) 0.

(** Converts string-to-list length preservation into the form needed by cache
    length and VST loop invariants. *)
Lemma list_ascii_of_string_length :
  forall s, length (list_ascii_of_string s) = String.length s.
Proof.
  intros s.
  induction s as [|a s' IH]; cbn; [reflexivity |].
  now rewrite IH.
Qed.

(** Converts list-to-string length preservation into the form needed by
    reversal and conversion bridge lemmas. *)
Lemma string_of_list_ascii_length :
  forall l, String.length (string_of_list_ascii l) = length l.
Proof.
  intros l.
  induction l as [|a l IH]; cbn; [reflexivity|].
  now rewrite IH.
Qed.

(** Characterizes the C-style branchy minimum as the mathematical minimum of
    insertion, deletion, and substitution candidates. *)
Lemma dp_min_spec : forall r d bd,
  dp_min r d bd = Nat.min (S r) (Nat.min (S d) bd).
Proof.
  intros r d bd.
  unfold dp_min.
  destruct (Nat.ltb r d) eqn:Hrd.
  - destruct (Nat.ltb r bd) eqn:Hrb.
    + apply PeanoNat.Nat.ltb_lt in Hrd.
      apply PeanoNat.Nat.ltb_lt in Hrb.
      rewrite (PeanoNat.Nat.min_l (S r) (Nat.min (S d) bd)).
      2:{
        apply PeanoNat.Nat.min_glb.
        lia.
        apply PeanoNat.Nat.le_trans with (m := S r); lia.
      }
      reflexivity.
    + apply PeanoNat.Nat.ltb_lt in Hrd.
      apply PeanoNat.Nat.ltb_ge in Hrb.
      rewrite (PeanoNat.Nat.min_r (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) bd) by lia.
      reflexivity.
  - destruct (Nat.ltb d bd) eqn:Hdb.
    + apply PeanoNat.Nat.ltb_ge in Hrd.
      apply PeanoNat.Nat.ltb_lt in Hdb.
      rewrite (PeanoNat.Nat.min_l (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) (S d)) by lia.
      reflexivity.
    + apply PeanoNat.Nat.ltb_ge in Hrd.
      apply PeanoNat.Nat.ltb_ge in Hdb.
      rewrite (PeanoNat.Nat.min_r (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) bd) by lia.
      reflexivity.
Qed.

(** Row specification where [pre_rev] is the reverse of the already-processed
    prefix of [a], and [brow] is the reverse of the current [b]-prefix. *)
(** Computes all DP cells for remaining source suffixes against the current
    reversed target prefix. *)
Fixpoint row_values (pre_rev a_rest brow : string) : list nat :=
  match a_rest with
  | EmptyString => []
  | String a_i a_tail =>
      levenshtein_recursive (String a_i pre_rev) brow
      :: row_values (String a_i pre_rev) a_tail brow
  end.

(** Computes the last DP cell for a row by moving the whole remaining source
    suffix into the processed prefix. *)
Fixpoint row_last (pre_rev a_rest brow : string) : nat :=
  match a_rest with
  | EmptyString => levenshtein_recursive pre_rev brow
  | String a_i a_tail => row_last (String a_i pre_rev) a_tail brow
  end.

(** The row against an empty target consists of source-prefix deletion costs. *)
Lemma row_values_empty_b :
  forall pre_rev a_rest,
    row_values pre_rev a_rest EmptyString =
    map S (seq (String.length pre_rev) (String.length a_rest)).
Proof.
  intros pre_rev a_rest.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev;
    cbn [row_values String.length].
  - reflexivity.
  - rewrite levenshtein_recursive_nil_r.
    rewrite IH.
    reflexivity.
Qed.

(** The initial cache row is exactly the row specification for an empty target
    prefix. *)
Lemma init_cache_row_values :
  forall a_rest,
    init_cache (String.length a_rest) = row_values EmptyString a_rest EmptyString.
Proof.
  intros a_rest.
  unfold init_cache.
  rewrite row_values_empty_b.
  cbn [String.length].
  reflexivity.
Qed.

(** DP cell equation for matching source and target characters after at least
    one source character has already been processed. *)
Lemma dp_cell_eq_cont :
  forall x pre_rev bpre_rev,
    dp_min (levenshtein_recursive pre_rev (x :: bpre_rev))
           (levenshtein_recursive (x :: pre_rev) bpre_rev)
           (levenshtein_recursive pre_rev bpre_rev)
    = levenshtein_recursive (x :: pre_rev) (x :: bpre_rev).
Proof.
  intros x pre_rev bpre_rev.
  rewrite dp_min_spec.
  rewrite levenshtein_recursive_skip_eq.
  rewrite (PeanoNat.Nat.min_r
             (S (levenshtein_recursive (x :: pre_rev) bpre_rev))
             (levenshtein_recursive pre_rev bpre_rev)).
  2:{ apply levenshtein_recursive_insert_lower. }
  rewrite (PeanoNat.Nat.min_r
             (S (levenshtein_recursive pre_rev (x :: bpre_rev)))
             (levenshtein_recursive pre_rev bpre_rev)).
  2:{ apply levenshtein_recursive_insert_lower_r. }
  reflexivity.
Qed.

(** DP cell equation for non-matching source and target characters in the
    continuing part of a row. *)
Lemma dp_cell_neq_cont :
  forall x y pre_rev bpre_rev,
    x <> y ->
    dp_min (levenshtein_recursive pre_rev (y :: bpre_rev))
           (levenshtein_recursive (x :: pre_rev) bpre_rev)
           (S (levenshtein_recursive pre_rev bpre_rev))
    = levenshtein_recursive (x :: pre_rev) (y :: bpre_rev).
Proof.
  intros x y pre_rev bpre_rev Hxy.
  rewrite dp_min_spec.
  rewrite levenshtein_recursive_cons_neq by exact Hxy.
  rewrite min3_comm12.
  reflexivity.
Qed.

(** First-cell equation for matching source and target characters.  This is the
    boundary case where the processed source prefix is empty. *)
Lemma dp_cell_first_eq :
  forall x bpre_rev,
    dp_min (levenshtein_recursive EmptyString bpre_rev)
           (levenshtein_recursive (String x EmptyString) bpre_rev)
           (levenshtein_recursive EmptyString bpre_rev)
    = levenshtein_recursive (String x EmptyString) (x :: bpre_rev).
Proof.
  intros x bpre_rev.
  rewrite dp_min_spec.
  rewrite levenshtein_recursive_skip_eq.
  rewrite PeanoNat.Nat.min_r by lia.
  rewrite PeanoNat.Nat.min_r.
  2:{ apply (levenshtein_recursive_insert_lower x EmptyString bpre_rev). }
  reflexivity.
Qed.

(** First-cell equation for non-matching source and target characters.  This is
    the boundary case before any source character has been processed. *)
Lemma dp_cell_first_neq :
  forall x y bpre_rev,
    x <> y ->
    dp_min (levenshtein_recursive EmptyString bpre_rev)
           (levenshtein_recursive (String x EmptyString) bpre_rev)
           (S (levenshtein_recursive EmptyString bpre_rev))
    = levenshtein_recursive (String x EmptyString) (y :: bpre_rev).
Proof.
  intros x y bpre_rev Hxy.
  set (d := levenshtein_recursive EmptyString bpre_rev).
  set (c := levenshtein_recursive (String x EmptyString) bpre_rev).
  rewrite dp_min_spec.
  rewrite levenshtein_recursive_cons_neq by exact Hxy.
  assert (Hd : levenshtein_recursive EmptyString (y :: bpre_rev) = S d).
  {
    unfold d.
    rewrite !levenshtein_recursive_nil_l.
    reflexivity.
  }
  rewrite Hd.
  fold c d.
  rewrite min3_comm12.
  rewrite PeanoNat.Nat.min_id.
  replace (Nat.min (S (S d)) (S d)) with (S d).
  2:{ symmetry. apply PeanoNat.Nat.min_r. lia. }
  reflexivity.
Qed.

(** Correctness of the string inner loop against the row specification.  The
    returned tuple contains the new row and the old/new final cells. *)
Lemma inner_loop_cont_correct :
  forall pre_rev a_rest b_char bpre_rev,
    inner_loop_string a_rest b_char (row_values pre_rev a_rest bpre_rev)
      (levenshtein_recursive pre_rev bpre_rev)
      (levenshtein_recursive pre_rev (b_char :: bpre_rev))
    =
    (row_values pre_rev a_rest (b_char :: bpre_rev),
     row_last pre_rev a_rest bpre_rev,
     row_last pre_rev a_rest (b_char :: bpre_rev)).
Proof.
  intros pre_rev a_rest.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev b_char bpre_rev; cbn.
  - reflexivity.
  - destruct (ascii_dec b_char a_i) as [Heq|Hneq].
    + subst a_i.
      rewrite dp_cell_eq_cont.
      rewrite (IH (String b_char pre_rev) b_char bpre_rev).
      reflexivity.
    + rewrite dp_cell_neq_cont.
      2:{ intro Hc. apply Hneq. symmetry. exact Hc. }
      rewrite (IH (String a_i pre_rev) b_char bpre_rev).
    reflexivity.
Qed.

(** Correctness of processing one target character for a non-empty source row.
    The result is the next row specification and its final cell. *)
Lemma process_row_correct_nonempty :
  forall a0 a_tail b_char bpre_rev,
    process_row_string (a0 :: a_tail) b_char
      (row_values EmptyString (a0 :: a_tail) bpre_rev)
      (String.length bpre_rev)
    =
    (row_values EmptyString (a0 :: a_tail) (b_char :: bpre_rev),
     row_last EmptyString (a0 :: a_tail) (b_char :: bpre_rev)).
Proof.
  intros a0 a_tail b_char bpre_rev.
  unfold process_row_string.
  cbn [row_values].
  replace (String.length bpre_rev) with (levenshtein_recursive EmptyString bpre_rev).
  2:{ apply levenshtein_recursive_nil_l. }
  destruct (ascii_dec b_char a0) as [Heq|Hneq].
  - subst a0.
    cbn [inner_loop_string].
    destruct (ascii_dec b_char b_char) as [Hbb|Hbb].
    2:{ exfalso. apply Hbb. reflexivity. }
    rewrite dp_cell_first_eq.
    rewrite inner_loop_cont_correct with
      (pre_rev := String b_char EmptyString) (a_rest := a_tail)
      (b_char := b_char) (bpre_rev := bpre_rev).
    reflexivity.
  - remember (if ascii_dec b_char a0
              then levenshtein_recursive EmptyString bpre_rev
              else S (levenshtein_recursive EmptyString bpre_rev)) as bd0 eqn:Hbd0.
    assert (Hbd0' : bd0 = S (levenshtein_recursive EmptyString bpre_rev)).
    {
      rewrite Hbd0.
      destruct (ascii_dec b_char a0) as [Hc|Hc].
      - exfalso. apply Hneq. exact Hc.
      - reflexivity.
    }
    rewrite Hbd0' in *.
    cbn [inner_loop_string].
    destruct (ascii_dec b_char a0) as [Hc|Hc].
    + exfalso. apply Hneq. exact Hc.
    + cbn.
    rewrite (dp_cell_first_neq a0 b_char bpre_rev).
    2:{ intro Heq'. apply Hneq. symmetry. exact Heq'. }
    rewrite inner_loop_cont_correct with
      (pre_rev := String a0 EmptyString) (a_rest := a_tail)
      (b_char := b_char) (bpre_rev := bpre_rev).
    reflexivity.
Qed.

(** Appends the same suffix to both endpoints of an edit chain without
    changing its cost. *)
Lemma chain_append_right :
  forall s t n (c : chain s t n) u,
    chain (s ++ u) (t ++ u) n.
Proof.
  intros s t n c.
  induction c as [|a s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH]; intros u.
  - exact (same_chain u).
  - cbn [String.append].
    apply skip.
    exact (IH u).
  - destruct e.
    + cbn [String.append].
      eapply change.
      * exact (insertion a).
      * exact (IH u).
    + cbn [String.append].
      eapply change.
      * exact (deletion a).
      * exact (IH u).
    + cbn [String.append].
      eapply change.
      * exact (update a' a (neq := neq)).
      * exact (IH u).
Qed.

(** Adds one character at the end of the source endpoint by one deletion step,
    preserving the rest of the edit chain. *)
Lemma chain_add_last_source :
  forall s t n (c : chain s t n) a,
    chain (s ++ String a EmptyString) t (S n).
Proof.
  intros s t n c.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH]; intros a.
  - cbn [String.append].
    exact (delete_chain a EmptyString EmptyString 0 empty).
  - cbn [String.append].
    apply skip.
    exact (IH a).
  - destruct e.
    + cbn [String.append].
      eapply change.
      * exact (insertion a0).
      * exact (IH a).
    + cbn [String.append].
      eapply change.
      * exact (deletion a0).
      * exact (IH a).
    + cbn [String.append].
      eapply change.
      * exact (update a' a0 (neq := neq)).
      * exact (IH a).
Qed.

(** Removes a final source character from an edit-chain endpoint by paying one
    extra edit step in the transformed chain. *)
Lemma chain_strip_last_source :
  forall s a t n,
    chain (s ++ String a EmptyString) t n ->
    chain s t (S n).
Proof.
  intros s a t n c.
  remember (String.append s (String a EmptyString)) as src eqn:Hsrc.
  revert s a Hsrc.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH];
    intros s0 a0 Hsrc.
  - destruct s0; cbn in Hsrc; discriminate.
  - destruct s0 as [|y s0']; cbn in Hsrc.
    + inversion Hsrc; subst.
      eapply change.
      * constructor.
      * apply skip.
        exact c1.
    + inversion Hsrc; subst.
      apply skip.
      apply IH with (a := a0).
      reflexivity.
  - destruct e as [ch s2|ch s2|ch' ch Hneq s2].
    + eapply change.
      * constructor.
      * apply IH with (s := String ch s0) (a := a0).
        cbn [String.append].
        now rewrite Hsrc.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (insertion a0).
        -- eapply change.
           ++ exact (deletion a0).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (deletion y).
        -- apply IH with (s := s0') (a := a0).
           reflexivity.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (insertion a0).
        -- eapply change.
           ++ exact (update a0 ch (neq := Hneq)).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update y ch (neq := Hneq)).
        -- apply IH with (s := String ch s0') (a := a0).
           cbn [String.append].
           reflexivity.
Qed.

(** Changes the final source character in an edit-chain endpoint by paying one
    extra update step. *)
Lemma chain_update_last_source :
  forall s a a' t n,
    a' <> a ->
    chain (s ++ String a EmptyString) t n ->
    chain (s ++ String a' EmptyString) t (S n).
Proof.
  intros s a a' t n Hneq_sa c.
  remember (String.append s (String a EmptyString)) as src eqn:Hsrc.
  revert s a Hneq_sa Hsrc.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH];
    intros s0 a0 Hneq0 Hsrc.
  - destruct s0; cbn in Hsrc; discriminate.
  - destruct s0 as [|y s0']; cbn in Hsrc.
    + inversion Hsrc; subst.
      eapply change.
      * exact (update a' a0 (neq := Hneq0)).
      * apply skip.
        exact c1.
    + inversion Hsrc; subst.
      apply skip.
      apply IH with (a := a0).
      * exact Hneq0.
      * reflexivity.
  - destruct e as [ch s2|ch s2|ch' ch Hneq_e s2].
    + eapply change.
      * exact (insertion ch).
      * apply IH with (s := String ch s0) (a := a0).
        -- exact Hneq0.
        -- cbn [String.append].
           now rewrite Hsrc.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update a' a0 (neq := Hneq0)).
        -- eapply change.
           ++ exact (deletion a0).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (deletion y).
        -- apply IH with (s := s0') (a := a0).
           ++ exact Hneq0.
           ++ reflexivity.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update a' a0 (neq := Hneq0)).
        -- eapply change.
           ++ exact (update a0 ch (neq := Hneq_e)).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update y ch (neq := Hneq_e)).
        -- apply IH with (s := String ch s0') (a := a0).
           ++ exact Hneq0.
           ++ cbn [String.append].
              reflexivity.
Qed.

(** String append is associative.  This local form avoids depending on the
    exact exported name used by different Rocq standard-library versions. *)
Lemma string_append_assoc :
  forall s t u,
    String.append s (String.append t u) =
    String.append (String.append s t) u.
Proof.
  intros s t u.
  induction s as [|a s IH]; cbn [String.append].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Converts list append into string append for ASCII character conversions. *)
Lemma string_of_list_ascii_app :
  forall l1 l2,
    string_of_list_ascii (l1 ++ l2) =
    String.append (string_of_list_ascii l1) (string_of_list_ascii l2).
Proof.
  intros l1 l2.
  induction l1 as [|x xs IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

(** Reverses a Rocq string by converting to a character list, reversing the
    list, and converting back. *)
Definition rev_string (s : string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string s)).

(** Reversing a non-empty string moves its head to the final character. *)
Lemma rev_string_cons :
  forall a s,
    rev_string (String a s) =
    String.append (rev_string s) (String a EmptyString).
Proof.
  intros a s.
  unfold rev_string.
  cbn [list_ascii_of_string rev].
  rewrite string_of_list_ascii_app.
  cbn [string_of_list_ascii String.append].
  reflexivity.
Qed.

(** Reversal commutes with converting an ASCII list to a string. *)
Lemma rev_string_of_list :
  forall l,
    rev_string (string_of_list_ascii l) = string_of_list_ascii (rev l).
Proof.
  intros l.
  unfold rev_string.
  rewrite list_ascii_of_string_of_list_ascii.
  reflexivity.
Qed.

(** String reversal is an involution. *)
Lemma rev_string_involutive :
  forall s, rev_string (rev_string s) = s.
Proof.
  intros s.
  unfold rev_string.
  rewrite list_ascii_of_string_of_list_ascii.
  rewrite rev_involutive.
  rewrite string_of_list_ascii_of_string.
  reflexivity.
Qed.

(** Reversing both endpoints preserves the existence and cost of an edit
    chain. *)
Lemma chain_rev_string :
  forall s t n (c : chain s t n),
    chain (rev_string s) (rev_string t) n.
Proof.
  intros s t n c.
  induction c as [|a s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH].
  - unfold rev_string.
    cbn [list_ascii_of_string rev string_of_list_ascii].
    constructor.
  - rewrite !rev_string_cons.
    exact (chain_append_right _ _ _ IH (String a EmptyString)).
  - destruct e as [ch s2|ch s2|ch' ch Hneq s2].
    + rewrite rev_string_cons in IH.
      exact (chain_strip_last_source (rev_string s2) ch (rev_string u1) n1 IH).
    + rewrite rev_string_cons.
      exact (chain_add_last_source (rev_string s2) (rev_string u1) n1 IH ch).
    + rewrite rev_string_cons.
      rewrite rev_string_cons in IH.
      exact (chain_update_last_source (rev_string s2) ch ch' (rev_string u1) n1 Hneq IH).
Qed.

(** Levenshtein distance is invariant under reversing both input strings. *)
Lemma levenshtein_recursive_rev :
  forall s t,
    levenshtein_recursive (rev_string s) (rev_string t) =
    levenshtein_recursive s t.
Proof.
  intros s t.
  apply PeanoNat.Nat.le_antisymm.
  - destruct (levenshtein_chain s t) as [n c] eqn:Hchain.
    pose proof
      (levenshtein_recursive_of_chain s t n c Hchain)
      as Hn.
    pose proof
      (chain_rev_string s t n c)
      as Hrev.
    pose proof
      (levenshtein_recursive_is_minimal (rev_string s) (rev_string t) n Hrev)
      as Hmin.
    rewrite <- Hn in Hmin.
    exact Hmin.
  - destruct (levenshtein_chain (rev_string s) (rev_string t)) as [n c] eqn:Hchain.
    pose proof
      (levenshtein_recursive_of_chain (rev_string s) (rev_string t) n c Hchain)
      as Hn.
    pose proof
      (chain_rev_string (rev_string s) (rev_string t) n c)
      as Hrev.
    pose proof
      (levenshtein_recursive_is_minimal
         (rev_string (rev_string s)) (rev_string (rev_string t)) n Hrev)
      as Hmin.
    rewrite !rev_string_involutive in Hmin.
    rewrite Hn.
    exact Hmin.
Qed.

(** Reversing a string preserves its length. *)
Lemma rev_string_length :
  forall s, String.length (rev_string s) = String.length s.
Proof.
  intros s.
  unfold rev_string.
  rewrite string_of_list_ascii_length.
  rewrite length_rev.
  apply list_ascii_of_string_length.
Qed.

(** The last row-specification cell equals the recursive distance from the
    reversed remaining source plus the processed prefix. *)
Lemma row_last_rev :
  forall pre_rev a_rest brow,
    row_last pre_rev a_rest brow =
    levenshtein_recursive (String.append (rev_string a_rest) pre_rev) brow.
Proof.
  intros pre_rev a_rest brow.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev; cbn [row_last].
  - unfold rev_string. cbn [list_ascii_of_string rev string_of_list_ascii].
    reflexivity.
  - rewrite (IH (String a_i pre_rev)).
    rewrite rev_string_cons.
    rewrite <- string_append_assoc.
    cbn [String.append].
    reflexivity.
Qed.

(** Correctness of the executable string outer loop for non-empty inputs.  It
    connects the loop result to the final row specification. *)
Lemma outer_result_run_correct :
  forall a b bpre_rev,
    a <> EmptyString ->
    b <> EmptyString ->
    outer_result_run_string a b
      (row_values EmptyString a bpre_rev)
      (String.length bpre_rev)
    = row_last EmptyString a (String.append (rev_string b) bpre_rev).
Proof.
  intros a b bpre_rev Ha Hb.
  revert bpre_rev Hb.
  induction b as [|b0 b_tail IH]; intros bpre_rev Hb; [contradiction|].
  destruct a as [|a0 a_tail]; [contradiction|].
  cbn [outer_result_run_string].
  rewrite process_row_correct_nonempty.
  destruct b_tail as [|b1 b_tail'].
  - cbn [outer_result_run_string].
    rewrite rev_string_cons.
    unfold rev_string at 1.
    cbn [list_ascii_of_string rev string_of_list_ascii String.append].
    reflexivity.
  - specialize (IH (String b0 bpre_rev) ltac:(discriminate)).
    replace (S (String.length bpre_rev))
      with (String.length (b0 :: bpre_rev)) by reflexivity.
    rewrite IH.
    rewrite !rev_string_cons.
    rewrite <- !string_append_assoc.
    cbn [String.append].
    reflexivity.
Qed.

(** Reversed-string specification for the DP implementation.  The executable
    scan order computes the recursive model over reversed inputs. *)
Theorem levenshtein_dp_rev_spec :
  forall s t,
    levenshtein_dp s t = levenshtein_recursive (rev_string s) (rev_string t).
Proof.
  intros s t.
  destruct s as [|a0 s_tail].
  - unfold levenshtein_dp. cbn [String.length Nat.eqb].
    unfold rev_string at 1.
    cbn [list_ascii_of_string rev string_of_list_ascii].
    rewrite levenshtein_recursive_nil_l.
    rewrite rev_string_length. reflexivity.
  - destruct t as [|b0 t_tail].
    + unfold levenshtein_dp. cbn [String.length Nat.eqb].
      unfold rev_string at 2.
      cbn [list_ascii_of_string rev string_of_list_ascii].
      rewrite levenshtein_recursive_nil_r.
      rewrite rev_string_length. reflexivity.
    + unfold levenshtein_dp.
      cbn [String.length Nat.eqb].
      change (init_cache (S (String.length s_tail)))
        with (init_cache (String.length (a0 :: s_tail))).
      rewrite init_cache_row_values.
      change 0 with (String.length EmptyString).
      rewrite (outer_result_run_correct
                 (String a0 s_tail) (String b0 t_tail) EmptyString
                 ltac:(discriminate) ltac:(discriminate)).
      rewrite (@tr_app_empty_r ascii).
      rewrite row_last_rev with (pre_rev := EmptyString).
      rewrite (@tr_app_empty_r ascii).
      reflexivity.
Qed.

(** Main correctness theorem relating the DP implementation to the recursive
    string model. *)
Theorem levenshtein_dp_eq_levenshtein_recursive :
  forall s t, levenshtein_dp s t = levenshtein_recursive s t.
Proof.
  intros s t.
  rewrite levenshtein_dp_rev_spec.
  rewrite levenshtein_recursive_rev.
  unfold levenshtein_recursive.
  reflexivity.
Qed.

(** * VST proof helpers

    The VST proof needs loop invariants for partially executed loops.  The
    step-indexed definitions below expose the prefix written so far and connect
    the executable [inner_loop] functions to index-based loop states. *)

(** Executes only the first [n] iterations of the inner loop.  The prefix in
    the result is the part of the cache written so far. *)
Fixpoint inner_steps (n : nat) (a_chars : list ascii) (b_char : ascii)
    (old_cache : list nat) (distance result : nat)
    : list nat * nat * nat :=
  match n, a_chars, old_cache with
  | O, _, _ => ([], distance, result)
  | S n', a_i :: a_rest, c_i :: c_rest =>
      let bDistance := if ascii_dec b_char a_i then distance else S distance in
      let new_result := dp_min result c_i bDistance in
      let '(rest_cache, fd, fr) :=
          inner_steps n' a_rest b_char c_rest c_i new_result in
      (new_result :: rest_cache, fd, fr)
  | S _, _, _ => ([], distance, result)
  end.

(** Zero inner-loop steps leave the cache prefix empty and preserve the carried
    north-west and west cells. *)
Lemma inner_steps_O :
  forall a_chars b_char old_cache distance result,
    inner_steps 0 a_chars b_char old_cache distance result =
    ([], distance, result).
Proof. reflexivity. Qed.

(** Running [inner_steps] for the full source length agrees with the executable
    inner loop when the old cache is long enough. *)
Lemma inner_steps_full :
  forall a_chars b_char old_cache distance result,
    length a_chars <= length old_cache ->
    inner_steps (length a_chars) a_chars b_char old_cache distance result
    = inner_loop a_chars b_char old_cache distance result.
Proof.
  intros a_chars.
  induction a_chars as [|a0 a_rest IH];
    intros b_char old_cache distance result Hlen.
  - reflexivity.
  - destruct old_cache as [|c0 c_rest]; [simpl in Hlen; lia|].
    simpl in Hlen.
    cbn [length inner_steps inner_loop].
    rewrite IH by lia.
    reflexivity.
Qed.

(** One-step unfolding lemma used to control [simpl] and [cbn] behavior. *)
Lemma inner_steps_cons_S :
  forall n a0 a_rest b_char c0 c_rest distance result,
    inner_steps (S n) (a0 :: a_rest) b_char (c0 :: c_rest) distance result =
    let bDistance := if ascii_dec b_char a0 then distance else S distance in
    let new_result := dp_min result c0 bDistance in
    let '(rest_cache, fd, fr) :=
        inner_steps n a_rest b_char c_rest c0 new_result in
    (new_result :: rest_cache, fd, fr).
Proof. reflexivity. Qed.

(** Per-component equations for [inner_steps_extend].  Splitting them avoids
    destructuring-let unification issues in later VST obligations. *)

(** After [S n] inner steps, the carried north-west cell is the [n]th old-cache
    cell. *)
Lemma inner_steps_S_dist :
  forall n a_chars b_char old_cache distance result,
    n < length a_chars ->
    n < length old_cache ->
    snd (fst (inner_steps (S n) a_chars b_char old_cache distance result)) =
    nth n old_cache 0.
Proof.
  intros n a_chars.
  revert n.
  induction a_chars as [|a0 a_rest IHa];
    intros n b_char old_cache distance result Hlen_a Hlen_c.
  - simpl in Hlen_a; lia.
  - destruct old_cache as [|c0 c_rest]; [simpl in Hlen_c; lia|].
    simpl in Hlen_a, Hlen_c.
    destruct n as [|n].
    + reflexivity.
    + rewrite inner_steps_cons_S.
      cbv zeta.
      set (new_res0 := dp_min result c0
                         (if ascii_dec b_char a0 then distance else S distance)).
      destruct (inner_steps (S n) a_rest b_char c_rest c0 new_res0)
        as [[prefix d] r] eqn:Hstep.
      cbn [fst snd].
      pose proof (IHa n b_char c_rest c0 new_res0
                    ltac:(lia) ltac:(lia)) as IH'.
      rewrite Hstep in IH'.
      cbn in IH'.
      exact IH'.
Qed.

(** The result cell after [S n] inner steps is the DP minimum computed from the
    previous partial-step state. *)
Lemma inner_steps_S_result :
  forall n a_chars b_char old_cache distance result,
    n < length a_chars ->
    n < length old_cache ->
    snd (inner_steps (S n) a_chars b_char old_cache distance result) =
    dp_min (snd (inner_steps n a_chars b_char old_cache distance result))
           (nth n old_cache 0)
           (if ascii_dec b_char (nth n a_chars Ascii.zero)
            then snd (fst (inner_steps n a_chars b_char old_cache distance result))
            else S (snd (fst (inner_steps n a_chars b_char old_cache distance result)))).
Proof.
  intros n a_chars.
  revert n.
  induction a_chars as [|a0 a_rest IHa];
    intros n b_char old_cache distance result Hlen_a Hlen_c.
  - simpl in Hlen_a; lia.
  - destruct old_cache as [|c0 c_rest]; [simpl in Hlen_c; lia|].
    simpl in Hlen_a, Hlen_c.
    destruct n as [|n].
    + reflexivity.
    + rewrite !inner_steps_cons_S.
      cbv zeta.
      set (new_res0 := dp_min result c0
                         (if ascii_dec b_char a0 then distance else S distance)).
      destruct (inner_steps n a_rest b_char c_rest c0 new_res0)
        as [[prefix_n d_n] r_n] eqn:Hstep_n.
      destruct (inner_steps (S n) a_rest b_char c_rest c0 new_res0)
        as [[prefix_Sn d_Sn] r_Sn] eqn:Hstep_Sn.
      cbn [fst snd].
      pose proof (IHa n b_char c_rest c0 new_res0
                    ltac:(lia) ltac:(lia)) as IH'.
      rewrite Hstep_n in IH'.
      rewrite Hstep_Sn in IH'.
      cbn in IH'.
      exact IH'.
Qed.

(** The cache prefix after [S n] inner steps appends the newest result cell to
    the prefix after [n] steps. *)
Lemma inner_steps_S_prefix :
  forall n a_chars b_char old_cache distance result,
    n < length a_chars ->
    n < length old_cache ->
    fst (fst (inner_steps (S n) a_chars b_char old_cache distance result)) =
    fst (fst (inner_steps n a_chars b_char old_cache distance result)) ++
    [snd (inner_steps (S n) a_chars b_char old_cache distance result)].
Proof.
  intros n a_chars.
  revert n.
  induction a_chars as [|a0 a_rest IHa];
    intros n b_char old_cache distance result Hlen_a Hlen_c.
  - simpl in Hlen_a; lia.
  - destruct old_cache as [|c0 c_rest]; [simpl in Hlen_c; lia|].
    simpl in Hlen_a, Hlen_c.
    destruct n as [|n].
    + reflexivity.
    + rewrite !inner_steps_cons_S.
      cbv zeta.
      set (new_res0 := dp_min result c0
                         (if ascii_dec b_char a0 then distance else S distance)).
      destruct (inner_steps n a_rest b_char c_rest c0 new_res0)
        as [[prefix_n d_n] r_n] eqn:Hstep_n.
      destruct (inner_steps (S n) a_rest b_char c_rest c0 new_res0)
        as [[prefix_Sn d_Sn] r_Sn] eqn:Hstep_Sn.
      cbn [fst snd app].
      f_equal.
      pose proof (IHa n b_char c_rest c0 new_res0
                    ltac:(lia) ltac:(lia)) as IH'.
      rewrite Hstep_n in IH'.
      rewrite Hstep_Sn in IH'.
      cbn in IH'.
      exact IH'.
Qed.

(** A single-step extension law for partial inner-loop execution.  It packages
    the prefix, carried old-cache cell, and new result cell together. *)
Lemma inner_steps_extend :
  forall n a_chars b_char old_cache distance result,
    n < length a_chars ->
    n < length old_cache ->
    inner_steps (S n) a_chars b_char old_cache distance result =
    let '(prefix, d, r) :=
        inner_steps n a_chars b_char old_cache distance result in
    let a_n := nth n a_chars Ascii.zero in
    let c_n := nth n old_cache 0 in
    let bDistance := if ascii_dec b_char a_n then d else S d in
    let new_result := dp_min r c_n bDistance in
    (prefix ++ [new_result], c_n, new_result).
Proof.
  intros n a_chars b_char old_cache distance result Hlen_a Hlen_c.
  destruct (inner_steps n a_chars b_char old_cache distance result)
    as [[prefix_n d_n] r_n] eqn:Hstep_n.
  cbv zeta.
  destruct (inner_steps (S n) a_chars b_char old_cache distance result)
    as [[prefix_Sn d_Sn] r_Sn] eqn:Hstep_Sn.
  pose proof (inner_steps_S_dist n a_chars b_char old_cache distance result
                Hlen_a Hlen_c) as Hd.
  pose proof (inner_steps_S_prefix n a_chars b_char old_cache distance result
                Hlen_a Hlen_c) as Hp.
  pose proof (inner_steps_S_result n a_chars b_char old_cache distance result
                Hlen_a Hlen_c) as Hr.
  rewrite Hstep_Sn in Hd, Hp, Hr. cbn [fst snd] in Hd, Hp, Hr.
  rewrite Hstep_n in Hp, Hr. cbn [fst snd] in Hp, Hr.
  subst d_Sn r_Sn prefix_Sn.
  reflexivity.
Qed.

(** The written cache prefix produced by [inner_steps n] has length [n] when
    both input sequences are long enough. *)
Lemma inner_steps_length :
  forall n a_chars b_char old_cache distance result,
    n <= length a_chars ->
    n <= length old_cache ->
    length (fst (fst (inner_steps n a_chars b_char old_cache distance result))) = n.
Proof.
  intros n.
  induction n as [|n IH];
    intros a_chars b_char old_cache distance result Hlen_a Hlen_c.
  - reflexivity.
  - destruct a_chars as [|a0 a_rest]; [simpl in Hlen_a; lia|].
    destruct old_cache as [|c0 c_rest]; [simpl in Hlen_c; lia|].
    simpl in Hlen_a, Hlen_c.
    cbn [inner_steps].
    destruct (inner_steps n a_rest b_char c_rest _ _) as [[prefix d] r] eqn:Hstep.
    cbn [fst snd length].
    f_equal.
    pose proof (IH a_rest b_char c_rest c0
                 (dp_min result c0
                   (if ascii_dec b_char a0 then distance else S distance))
                 ltac:(lia) ltac:(lia)) as Hl.
    rewrite Hstep in Hl. cbn in Hl. exact Hl.
Qed.

(** Bridge [outer_result_run] to the index-based
    [outer_result] view used in loop invariants. *)

(** Executable outer-loop state that returns both the final cache and the final
    row result after scanning a target-character list. *)
Fixpoint outer_run_state (a_chars : list ascii) (b_chars : list ascii)
    (cache : list nat) (bIndex : nat) : list nat * nat :=
  match b_chars with
  | [] => (cache, 0)
  | ch :: bs =>
      let '(cache', row_res) := process_row a_chars ch cache bIndex in
      match bs with
      | [] => (cache', row_res)
      | _ :: _ => outer_run_state a_chars bs cache' (S bIndex)
      end
  end.

(** The executable outer-loop result is the second component of
    [outer_run_state]. *)
Lemma outer_result_run_via_state :
  forall b_chars a_chars cache bIndex,
    outer_result_run a_chars b_chars cache bIndex =
    snd (outer_run_state a_chars b_chars cache bIndex).
Proof.
  intros b_chars.
  induction b_chars as [|b0 bs IH]; intros a_chars cache bIndex.
  - reflexivity.
  - cbn [outer_result_run outer_run_state].
    destruct (process_row a_chars b0 cache bIndex) as [cache' row_res] eqn:Hpr.
    destruct bs as [|b1 bs'].
    + reflexivity.
    + cbn [snd]. apply IH.
Qed.

(** Index-based outer-loop iterator starting at an arbitrary cache and target
    index, used to align partial C loop states. *)
Fixpoint outer_iter_from (a_chars : list ascii) (b_chars : list ascii)
    (cache0 : list nat) (bIndex0 : nat) (k : nat) : list nat * nat :=
  match k with
  | O => (cache0, 0)
  | S k' =>
      let '(prev, _) := outer_iter_from a_chars b_chars cache0 bIndex0 k' in
      let b_k := nth k' b_chars Ascii.zero in
      process_row a_chars b_k prev (bIndex0 + k')
  end.

(** Starting [outer_iter_from] at index zero reproduces [outer_cache] and
    [outer_result] after [k] rows. *)
Lemma outer_iter_from_zero_eq_outer :
  forall k a_chars b_chars init,
    outer_iter_from a_chars b_chars init 0 k =
    (outer_cache a_chars b_chars init k, outer_result a_chars b_chars init k).
Proof.
  intros k.
  induction k as [|k IH]; intros a_chars b_chars init.
  - reflexivity.
  - cbn [outer_iter_from outer_cache outer_result].
    rewrite IH.
    cbn [fst].
    replace (0 + k)%nat with k by lia.
    destruct (process_row a_chars (nth k b_chars Ascii.zero)
               (outer_cache a_chars b_chars init k) k) as [c r] eqn:Hpr.
    cbn [fst snd]. reflexivity.
Qed.

(** Iterating only through [b1] is unaffected by extra target characters
    appended after [b1]. *)
Lemma outer_iter_from_app_irrelevant :
  forall k a b1 b2 cache bIndex,
    k <= length b1 ->
    outer_iter_from a (b1 ++ b2) cache bIndex k =
    outer_iter_from a b1 cache bIndex k.
Proof.
  intros k.
  induction k as [|k IH]; intros a b1 b2 cache bIndex Hk.
  - reflexivity.
  - cbn [outer_iter_from].
    rewrite IH by lia.
    rewrite app_nth1 by lia.
    reflexivity.
Qed.

(** Running [outer_run_state] over a list with one appended final character is
    equivalent to processing that final character after the prefix run. *)
Lemma outer_run_state_app_last :
  forall bs bn a cache bIndex,
    outer_run_state a (bs ++ [bn]) cache bIndex =
    let '(prev, _) := outer_run_state a bs cache bIndex in
    process_row a bn prev (bIndex + length bs).
Proof.
  intros bs.
  induction bs as [|b0 bs' IH]; intros bn a cache bIndex.
  - cbn [outer_run_state app length].
    replace (bIndex + 0)%nat with bIndex by lia.
    destruct (process_row a bn cache bIndex) as [c r] eqn:Hpr.
    reflexivity.
  - cbn [outer_run_state app].
    destruct (process_row a b0 cache bIndex) as [c0 r0] eqn:Hpr0.
    destruct bs' as [|b1 bs''].
    + cbn [app length].
      cbn [outer_run_state].
      destruct (process_row a bn c0 (S bIndex)) as [c1 r1] eqn:Hpr1.
      replace (bIndex + 1)%nat with (S bIndex) by lia.
      rewrite Hpr1. reflexivity.
    + change ((b1 :: bs'') ++ [bn]) with (b1 :: (bs'' ++ [bn])).
      cbv iota.
      change (b1 :: (bs'' ++ [bn])) with ((b1 :: bs'') ++ [bn]).
      rewrite (IH bn a c0 (S bIndex)).
      destruct (outer_run_state a (b1 :: bs'') c0 (S bIndex)) as [prev res] eqn:Hrun.
      cbn [length].
      replace (bIndex + S (S (length bs'')))%nat
         with (S bIndex + S (length bs''))%nat by lia.
      reflexivity.
Qed.

(** The index-based iterator has the same append-last behavior as
    [outer_run_state]. *)
Lemma outer_iter_from_app_last :
  forall bs bn a cache bIndex,
    outer_iter_from a (bs ++ [bn]) cache bIndex (S (length bs)) =
    let '(prev, _) := outer_iter_from a bs cache bIndex (length bs) in
    process_row a bn prev (bIndex + length bs).
Proof.
  intros bs bn a cache bIndex.
  cbn [outer_iter_from].
  rewrite outer_iter_from_app_irrelevant by lia.
  rewrite app_nth2 by lia.
  replace (length bs - length bs)%nat with 0%nat by lia.
  cbn [nth].
  destruct (outer_iter_from a bs cache bIndex (length bs)) as [prev res] eqn:Hpr.
  reflexivity.
Qed.

(** The executable outer-loop state agrees with the index-based iterator after
    the full target length. *)
Lemma outer_run_state_eq_iter_from :
  forall b_chars a_chars cache bIndex,
    outer_run_state a_chars b_chars cache bIndex =
    outer_iter_from a_chars b_chars cache bIndex (length b_chars).
Proof.
  intros b_chars.
  induction b_chars as [|bn bs IH] using rev_ind; intros a_chars cache bIndex.
  - reflexivity.
  - rewrite outer_run_state_app_last.
    rewrite length_app. cbn [length].
    replace (length bs + 1)%nat with (S (length bs)) by lia.
    rewrite outer_iter_from_app_last.
    rewrite IH.
    destruct (outer_iter_from a_chars bs cache bIndex (length bs)) as [prev res] eqn:Hi.
    reflexivity.
Qed.

(** The executable outer-loop result agrees with [outer_result] for non-empty
    list inputs. *)
Lemma outer_result_run_eq_outer_result :
  forall a b init,
    a <> [] ->
    b <> [] ->
    outer_result_run a b init 0 = outer_result a b init (length b).
Proof.
  intros a b init Ha Hb.
  rewrite outer_result_run_via_state.
  rewrite outer_run_state_eq_iter_from.
  rewrite outer_iter_from_zero_eq_outer.
  reflexivity.
Qed.

(** Rewrites the string DP into the index-based [outer_result] form used by the
    VST proof for non-empty strings. *)
Lemma levenshtein_dp_via_outer_result :
  forall s t,
    s <> EmptyString -> t <> EmptyString ->
    levenshtein_dp s t =
    outer_result (list_ascii_of_string s) (list_ascii_of_string t)
                 (init_cache (String.length s)) (String.length t).
Proof.
  intros s t Hs Ht.
  unfold levenshtein_dp.
  destruct s as [|a0 s_tail]; [contradiction|].
  destruct t as [|b0 t_tail]; [contradiction|].
  cbn [String.length Nat.eqb].
  rewrite outer_result_run_string_eq.
  rewrite outer_result_run_eq_outer_result by (cbn; discriminate).
  rewrite list_ascii_of_string_length.
  reflexivity.
Qed.

(** Length invariants for the DP cache. *)

(** The inner loop writes exactly one cache cell per source character when the
    previous cache row is long enough. *)
Lemma inner_loop_length :
  forall a_chars b_char old_cache distance result,
    length a_chars <= length old_cache ->
    length (fst (fst (inner_loop a_chars b_char old_cache distance result)))
    = length a_chars.
Proof.
  intros a_chars.
  induction a_chars as [|a0 a_rest IH];
    intros b_char old_cache distance result Hlen.
  - reflexivity.
  - destruct old_cache as [|c0 c_rest]; [simpl in Hlen; lia|].
    simpl in Hlen.
    cbn [inner_loop length].
    destruct (inner_loop a_rest b_char c_rest c0 _)
      as [[prefix d] r] eqn:Hstep.
    cbn [fst snd length].
    f_equal.
    pose proof (IH b_char c_rest c0
                 (dp_min result c0
                   (if ascii_dec b_char a0 then distance else S distance))
                 ltac:(lia)) as Hlen'.
    rewrite Hstep in Hlen'.
    cbn in Hlen'.
    exact Hlen'.
Qed.

(** Processing a row preserves the source-length cache invariant. *)
Lemma process_row_length :
  forall a_chars b_char cache bIndex,
    length a_chars <= length cache ->
    length (fst (process_row a_chars b_char cache bIndex)) = length a_chars.
Proof.
  intros a_chars b_char cache bIndex Hlen.
  unfold process_row.
  destruct (inner_loop a_chars b_char cache bIndex bIndex) as [[c d] r] eqn:Hil.
  cbn [fst].
  pose proof (inner_loop_length a_chars b_char cache bIndex bIndex Hlen) as H.
  rewrite Hil in H. cbn in H. exact H.
Qed.

(** Every index-based outer-loop cache has the same length as the initial cache
    when the initial cache matches the source length. *)
Lemma outer_cache_length :
  forall k a_chars b_chars init,
    length a_chars = length init ->
    length (outer_cache a_chars b_chars init k) = length init.
Proof.
  intros k.
  induction k as [|k IH]; intros a_chars b_chars init Hlen.
  - reflexivity.
  - cbn [outer_cache].
    rewrite process_row_length;
      [exact Hlen | rewrite IH by assumption; lia].
Qed.
