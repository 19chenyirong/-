Require Import Coq.Strings.String.
Require Import Coq.Init.Datatypes.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Coq.Sorting.Permutation.
From AUXLib Require Import int_auto Axioms Feq Idents List_lemma VMap ListLib.
From compcert.lib Require Import Integers.
Require Import SetsClass.SetsClass. Import SetsNotation.
From SimpleC.SL Require Import Mem CommonAssertion StoreAux.
Require Import Logic.LogicGenerator.demo932.Interface.
Local Open Scope Z_scope.
Local Open Scope sets.
Local Open Scope string.
Import ListNotations.
Local Open Scope list.

Module Type ArrayLibSig (CRules: SeparationLogicSig) (DePredSig : DerivedPredSig CRules) (SLibSig : StoreLibSig CRules DePredSig).

Import CRules.
Import DePredSig.
Import SLibSig.
Local Open Scope sac.  

Module Type ELEMENT_STORE.
  Parameter Inline A : Type.
  Parameter Inline sizeA : Z.
  Parameter Inline storeA : addr -> Z -> A -> Assertion.
  Parameter Inline undefstoreA : addr -> Z -> Assertion.
  Axiom store_to_undefstore : forall x lo a, storeA x lo a |-- undefstoreA x lo.
  Axiom storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Axiom undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
End ELEMENT_STORE.

Section GeneralArrayLib.
  Variable (A : Type).
  Variable (storeA : addr -> Z -> A -> Assertion).

  Lemma store_array_rec_length: forall x lo hi (l : list A),
  store_array_rec storeA x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
  Proof.
    intros.
    revert lo; induction l; simpl store_array_rec ; intros.
    + entailer!. simpl in *; lia.
    + prop_apply IHl.
      entailer!. simpl in * ; lia.
  Qed.

  Lemma store_array_rec_nil : forall x lo (l : list A),
    store_array_rec storeA x lo lo l |-- [| l = nil |] && emp.
  Proof.
    intros.
    prop_apply (store_array_rec_length x lo lo l).
    Intros.
    destruct l ; simpl in * ; try entailer!.
  Qed.

  Lemma store_array_length: forall x n (l : list A),
    store_array storeA x n l |-- [| Z.of_nat (length l) = n |].
  Proof.
    intros.
    unfold store_array.
    prop_apply store_array_rec_length.
    entailer!. 
  Qed.

  Lemma store_array_Zlength: forall x n (l : list A),
    store_array storeA x n l |-- [| Zlength l = n |].
  Proof.
    intros. rewrite Zlength_correct.
    apply store_array_length.
  Qed.

  Lemma store_array_rec_split_to_missing_i : forall x lo n m (l : list A) a,
    lo <= n < m ->
    store_array_rec storeA x lo m l |-- storeA x n (Znth (n - lo) l a) ** store_array_missing_i_rec storeA x n lo m l.
  Proof.
    intros.
    revert H.
    rename m into hi.
    revert lo; induction l; intros; simpl; intros.
    + entailer!.
    + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
      - Right.
        sep_apply IHl; [ | lia ].
        rewrite Znth_cons by lia.
        replace (n - (lo + 1)) with (n - lo - 1) by lia.
        entailer!.
      - rewrite <- derivable1_orp_intros1.
        subst n.
        replace (lo - lo) with 0 by lia.
        entailer!.
  Qed. 

  Lemma store_array_split_to_missing_i : forall x n m (l : list A) a,
    0 <= n < m ->
    store_array storeA x m l |-- storeA x n (Znth n l a) ** store_array_missing_i_rec storeA x n 0 m l.
  Proof.
    intros.
    revert H.
    unfold store_array.
    replace n with (n - 0) at 4 by lia.
    eapply store_array_rec_split_to_missing_i.
  Qed. 

  Lemma store_array_missing_i_merge_to_rec: forall x lo n m a (l: list A),
    lo <= n < m -> 
    storeA x n a ** store_array_missing_i_rec storeA x n lo m l |-- store_array_rec storeA x lo m (replace_Znth (n - lo) a l).
  Proof.
    intros.
    revert H.
    revert lo; induction l; intros; simpl.
    + entailer!.
    + rewrite derivable1_sepcon_comm.
      apply derivable1s_wand_sepcon_adjoint.
      Split;
      apply derivable1s_wand_sepcon_adjoint.
      - Intros.
        subst n.
        replace (lo - lo) with 0 by lia.
        simpl.
        entailer!.
      - Intros.
        sep_apply IHl; [ | lia ].
        entailer!.
        rewrite replace_Znth_cons by lia.
        replace (n - (lo + 1)) with (n - lo - 1) by lia.
        simpl.
        entailer!.
  Qed.

  Lemma store_array_missing_i_merge_to_array: forall x n m a (l: list A),
    0 <= n < m -> 
    storeA x n a ** store_array_missing_i_rec storeA x n 0 m l |-- store_array storeA x m (replace_Znth n a l).
  Proof.
    intros.
    unfold store_array.
    replace n with (n - 0) at 3 by lia.
    eapply store_array_missing_i_merge_to_rec;auto.
  Qed.

End GeneralArrayLib.

Module ArrayLib (ES: ELEMENT_STORE).

Import ES.

Definition ceil x lo hi (l : list A): Assertion :=
  store_array_rec storeA x lo hi l.

Definition missing_i x i lo hi (l : list A): Assertion :=
  store_array_missing_i_rec storeA x i lo hi l.

Definition full x n (l : list A): Assertion :=
  store_array storeA x n l.

Definition undef_ceil x lo hi : Assertion :=
  store_undef_array_rec undefstoreA x lo hi (Z.to_nat (hi - lo)).

Definition undef_missing_i x i lo hi : Assertion :=
  store_undef_array_missing_i_rec undefstoreA x i lo hi (Z.to_nat (hi - lo)).

Definition undef_full x n : Assertion :=
  store_undef_array undefstoreA x n.

Definition ceil_shape x lo hi : Assertion :=
  store_undef_array_rec (fun x lo => EX a, storeA x lo a) x lo hi (Z.to_nat (hi - lo)).

Definition missing_i_shape x i lo hi : Assertion :=
  store_undef_array_missing_i_rec (fun x lo => EX a, storeA x lo a) x i lo hi (Z.to_nat (hi - lo)).

Definition full_shape x n : Assertion :=
  store_undef_array (fun x lo => EX a, storeA x lo a) x n.

(** length Lemmas *)

Lemma ceil_length: forall x lo hi (l : list A),
  ceil x lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  revert lo; induction l; unfold ceil ; simpl ; intros.
  + entailer!.
  + prop_apply IHl.
    entailer!. 
Qed.

Lemma ceil_nil : forall x lo (l : list A),
  ceil x lo lo l |-- [| l = nil |] && emp.
Proof.
  intros.
  prop_apply ceil_length.
  Intros.
  destruct l ; simpl in * ; try entailer!.
Qed.

Lemma ceil_single : forall x lo a, 
  storeA x lo a |-- ceil x lo (lo + 1) (a :: nil).
Proof.
  intros.
  unfold ceil.
  simpl.
  entailer!.
Qed.

Lemma undef_ceil_single: forall x lo,
  undefstoreA x lo |-- undef_ceil x lo (lo + 1).
Proof.
  intros.
  unfold undef_ceil.
  replace (Z.to_nat (lo + 1 - lo)) with 1%nat by lia.
  simpl.
  entailer!.
Qed.

Lemma ceil_shape_single : forall x lo a,
  storeA x lo a |-- ceil_shape x lo (lo + 1).
Proof.
  intros.
  unfold ceil_shape.
  replace (Z.to_nat (lo + 1 - lo)) with 1%nat by lia.
  simpl.
  Exists a.
  entailer!.
Qed.

Lemma full_length: forall x n (l : list A),
  full x n l |-- [| Z.of_nat (length l) = n |].
Proof.
  intros.
  unfold full.
  prop_apply ceil_length.
  entailer!. 
Qed.

Lemma full_Zlength: forall x n (l : list A),
  full x n l |-- [| Zlength l = n |].
Proof.
  intros. rewrite Zlength_correct.
  apply full_length.
Qed.

Lemma missing_i_length: forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- [| Z.of_nat (length l) = hi - lo |].
Proof.
  intros.
  revert i lo hi; induction l; unfold missing_i ; simpl ; intros.
  - entailer!.
  - Split ; Intros.
    + prop_apply ceil_length.
      Intros. simpl length.
      entailer!. 
    + prop_apply IHl. simpl length.
      entailer!.
Qed.

(* Basic Properties *)

Lemma ceil_valid : forall x lo hi l,
  ceil x lo hi l |-- [| lo <= hi |].
Proof.
  intros.
  unfold ceil.
  prop_apply store_array_rec_length.
  entailer!.
Qed.

Lemma undef_ceil_valid : forall x lo hi,
  undef_ceil x lo hi |-- [| lo <= hi |].
Proof.
  intros.
  unfold undef_ceil.
  destruct (Z_le_gt_dec lo hi) as [H | H].
  - entailer!.
  - replace (Z.to_nat (hi - lo)) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

Lemma ceil_shape_valid : forall x lo hi,
  ceil_shape x lo hi |-- [| lo <= hi |].
Proof.
  intros.
  unfold ceil_shape.
  destruct (Z_le_gt_dec lo hi) as [H | H].
  - entailer!.
  - replace (Z.to_nat (hi - lo)) with 0%nat by lia.
    simpl.
    entailer!.
Qed.

Lemma ceil_empty : forall x lo hi,
  ceil x lo hi nil --||-- [| hi = lo |] && emp.
Proof.
  intros.
  unfold ceil.
  simpl.
  split ; entailer!.
Qed.

Lemma undef_ceil_empty : forall x lo,
  undef_ceil x lo lo --||-- emp.
Proof.
  intros.
  unfold undef_ceil.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  split ; entailer!.
Qed.

Lemma ceil_shape_empty : forall x lo,
  ceil_shape x lo lo --||-- emp.
Proof.
  intros.
  unfold ceil_shape.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  split ; entailer!.
Qed.

Lemma ceil_unfold : forall x lo hi (l : list A) a,
  ceil x lo hi (a :: l) --||-- storeA x lo a ** ceil x (lo + 1) hi l.
Proof.
  intros.
  unfold ceil.
  simpl.
  entailer!.
Qed.

Lemma undef_ceil_unfold : forall x lo hi,
  lo < hi ->
  undef_ceil x lo hi --||-- undefstoreA x lo ** undef_ceil x (lo + 1) hi.
Proof.
  intros.
  unfold undef_ceil.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  entailer!.
Qed.

Lemma ceil_shape_unfold : forall x lo hi,
  lo < hi ->
  ceil_shape x lo hi --||-- EX a, storeA x lo a ** ceil_shape x (lo + 1) hi.
Proof.
  intros.
  unfold ceil_shape.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  split ; 
  entailer!.
Qed.

Lemma missing_i_empty : forall x i lo hi,
  missing_i x i lo hi nil --||-- [| False |] .
Proof.
  intros.
  unfold missing_i.
  simpl.
  entailer!.
Qed.

Lemma undef_missing_i_empty : forall x i lo,
  undef_missing_i x i lo lo |-- [| False |] .
Proof.
  intros.
  unfold undef_missing_i.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  entailer!.
Qed.

Lemma missing_i_shape_empty : forall x i lo,
  missing_i_shape x i lo lo --||-- [| False |] .
Proof.
  intros.
  unfold missing_i_shape.
  replace (Z.to_nat (lo - lo)) with O by lia.
  simpl.
  entailer!.
Qed.

Lemma missing_i_unfold : forall x i lo hi (l : list A) a,
  missing_i x i lo hi (a :: l) --||--
   [|i = lo|] && ceil x (lo + 1) hi l || 
   [|i > lo|] && storeA x lo a ** missing_i x i (lo + 1) hi l.
Proof.
  intros.
  unfold missing_i.
  simpl.
  entailer!.
Qed.

Lemma undef_missing_i_unfold : forall x i lo hi,
  lo < hi ->
  undef_missing_i x i lo hi --||--
   [|i = lo|] && undef_ceil x (lo + 1) hi || 
   [|i > lo|] && undefstoreA x lo ** undef_missing_i x i (lo + 1) hi.
Proof.
  intros.
  unfold undef_missing_i.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  entailer!.
Qed.

Lemma missing_i_shape_unfold : forall x i lo hi,
  lo < hi ->
  missing_i_shape x i lo hi --||--
   [|i = lo|] && ceil_shape x (lo + 1) hi || 
   [|i > lo|] && (EX a, storeA x lo a) ** missing_i_shape x i (lo + 1) hi.
Proof.
  intros.
  unfold missing_i_shape.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  simpl.
  split ; entailer!.
Qed.

Lemma full_empty : forall x n,
  full x n nil --||-- [| n = 0 |] && emp.
Proof.
  intros.
  unfold full, store_array.
  simpl.
  split; entailer!.
Qed.

Lemma undef_full_empty : forall x,
  undef_full x 0 --||-- emp.
Proof.
  intros.
  unfold undef_full, store_undef_array.
  simpl.
  split; entailer!.
Qed.

Lemma full_shape_empty : forall x,
  full_shape x 0 --||-- emp.
Proof.
  intros.
  unfold full_shape, store_undef_array.
  simpl.
  split; entailer!.
Qed.

Lemma full_unfold : forall x n (l : list A) a,
  full x n (a :: l) --||-- storeA x 0 a ** ceil x 1 n l.
Proof.
  intros.
  unfold full, store_array.
  simpl.
  entailer!.
Qed.

Lemma undef_full_unfold : forall x n (l : list A),
  n >= 0 -> 
  undef_full x (n + 1) --||-- undefstoreA x 0 ** undef_ceil x 1 (n + 1).
Proof.
  intros.
  unfold undef_full, store_undef_array, undef_ceil.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  simpl.
  replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma full_shape_unfold : forall x n (l : list A),
  n >= 0 -> 
  full_shape x (n + 1) --||-- EX a, storeA x 0 a ** ceil_shape x 1 (n + 1).
Proof.
  intros.
  unfold full_shape, ceil_shape, store_undef_array.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  simpl.
  replace (Z.to_nat (n + 1 - 1)) with (Z.to_nat n) by lia.
  split ; entailer!.
Qed.

Ltac ArraySimplify :=
  repeat progress (
    match goal with
      | |- context [ceil ?x ?lo ?hi nil] => rewrite (ceil_empty x lo hi)
      | |- context [undef_ceil ?x ?lo ?lo] => rewrite (undef_ceil_empty x lo)
      | |- context [ceil_shape ?x ?lo ?lo] => rewrite (ceil_shape_empty x lo)
      | |- context [ceil ?x ?lo ?hi (?a :: ?l)] => rewrite (ceil_unfold x lo hi l a)
      | |- context [missing_i ?x ?i ?lo ?hi nil] => rewrite (missing_i_empty x i lo hi)
      | |- context [undef_missing_i ?x ?i ?lo ?lo] => rewrite (undef_missing_i_empty x i lo)
      | |- context [missing_i_shape ?x ?i ?lo ?lo] => rewrite (missing_i_shape_empty x i lo)
      | |- context [missing_i ?x ?i ?lo ?hi (?a :: ?l)] => rewrite (missing_i_unfold x i lo hi l a)
      | |- context [full ?x ?n nil] => rewrite (full_empty x n)
      | |- context [undef_full ?x 0] => rewrite (undef_full_empty x)
      | |- context [full_shape ?x 0] => rewrite (full_shape_empty x)
      | |- context [full ?x ?n (?a :: ?l)] => rewrite (full_unfold x n l a)
      | |- context [undef_full ?x (?n + 1)] => rewrite (undef_full_unfold x n)
      | |- context [full_shape ?x (?n + 1)] => rewrite (full_shape_unfold x n)
    end).

(* Transition Lemmas *)

Lemma full_to_ceil : forall x n (l : list A),
  full x n l |-- ceil x 0 n l.
Proof.
  intros.
  unfold full, ceil.
  unfold store_array.
  entailer!.
Qed.

Lemma undef_full_to_undef_ceil : forall x n,
  undef_full x n |-- undef_ceil x 0 n.
Proof.
  intros.
  unfold undef_full, undef_ceil.
  unfold store_undef_array.
  replace (Z.to_nat (n - 0)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma full_shape_to_ceil_shape : forall x n,
  full_shape x n |-- ceil_shape x 0 n.
Proof.
  intros.
  unfold full_shape, ceil_shape.
  unfold store_undef_array.
  replace (Z.to_nat (n - 0)) with (Z.to_nat n) by lia.
  entailer!.
Qed.

Lemma ceil_shift : forall x lo mid hi (l : list A),
  ceil x (lo + mid) (lo + hi) l --||-- ceil (x + lo * sizeA) mid hi l.
Proof.
  intros.
  revert lo mid hi ; induction l; intros ; ArraySimplify.
  - split ; entailer!.
  - rewrite (storeA_shift x lo mid a).
    replace (mid + lo) with (lo + mid) by lia.
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia.
    rewrite (IHl lo (mid + 1) hi).
    entailer!.
Qed.

Lemma ceil_0_shift : forall x lo hi (l : list A),
  ceil x lo hi l --||-- ceil (x + lo * sizeA) 0 (hi - lo) l.
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite ceil_shift.
  entailer!.
Qed.

Lemma undef_ceil_shift : forall x lo mid hi,
  undef_ceil x (lo + mid) (lo + hi) --||-- undef_ceil (x + lo * sizeA) mid hi.
Proof.
  intros.
  unfold undef_ceil.
  replace (lo + hi - (lo + mid)) with (hi - mid) by lia.
  set (len := Z.to_nat (hi - mid)).
  assert (len = Z.to_nat (hi - mid)) by lia.
  clearbody len. 
  revert H. revert lo mid hi ; induction len; intros ; simpl.
  - split ; entailer!.
  - rewrite (undefstoreA_shift x lo mid).
    replace (mid + lo) with (lo + mid) by lia.
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia.
    rewrite (IHlen lo (mid + 1) hi).
    entailer!.
    lia.
Qed.

Lemma undef_ceil_0_shift : forall x lo hi,
  undef_ceil x lo hi --||-- undef_ceil (x + lo * sizeA) 0 (hi - lo).
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite undef_ceil_shift.
  entailer!.
Qed.

Lemma ceil_shape_shift : forall x lo mid hi,
  ceil_shape x (lo + mid) (lo + hi) --||-- ceil_shape (x + lo * sizeA) mid hi.
Proof.
  intros.
  unfold ceil_shape.
  replace (lo + hi - (lo + mid)) with (hi - mid) by lia.
  set (len := Z.to_nat (hi - mid)).
  assert (len = Z.to_nat (hi - mid)) by lia.
  clearbody len. 
  revert H. revert lo mid hi ; induction len; intros ; simpl.
  - split ; entailer!.
  - split ; Intros a ; Exists a ;
    rewrite (storeA_shift x lo mid);
    replace (mid + lo) with (lo + mid) by lia;
    replace (lo + mid + 1) with (lo + (mid + 1)) by lia;
    rewrite (IHlen lo (mid + 1) hi);
    entailer!.
Qed.

Lemma ceil_shape_0_shift : forall x lo hi,
  ceil_shape x lo hi --||-- ceil_shape (x + lo * sizeA) 0 (hi - lo).
Proof.
  intros.
  replace lo with (lo + 0) at 1 by lia.
  replace hi with (lo + (hi - lo)) at 1 by lia.
  rewrite ceil_shape_shift.
  entailer!.
Qed.

Lemma ceil_to_full : forall x lo hi (l : list A),
  ceil x lo hi l |-- full (x + lo * sizeA) (hi - 
  lo) l.
Proof.
  intros.
  rewrite ceil_0_shift.
  unfold ceil, full, store_array. 
  entailer!.
Qed.

Lemma ceil_to_undef_ceil : forall x lo hi (l : list A),
  ceil x lo hi l |-- undef_ceil x lo hi.
Proof.
  intros.
  prop_apply ceil_length. Intros.
  revert H ; revert lo; induction l ; intros ; simpl ; ArraySimplify.
  + Intros. subst. ArraySimplify. entailer!.
  + simpl length in H.
    sep_apply IHl ; try lia.
    sep_apply store_to_undefstore.
    rewrite (undef_ceil_unfold x lo hi) ; try lia.
    entailer!.
Qed.

Lemma ceil_to_ceil_shape : forall x lo hi (l : list A),
  ceil x lo hi l |-- ceil_shape x lo hi.
Proof.
  intros.
  prop_apply ceil_length. Intros.
  revert H ; revert lo; induction l ; intros ; simpl ; ArraySimplify.
  + Intros. subst. ArraySimplify. entailer!.
  + simpl length in H.
    sep_apply IHl ; try lia.
    rewrite (ceil_shape_unfold x lo hi) ; try lia.
    Exists a. entailer!.
Qed.

Lemma undef_ceil_to_undef_full : forall x lo hi,
  undef_ceil x lo hi |-- undef_full (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  rewrite undef_ceil_0_shift.
  unfold undef_ceil, undef_full, store_undef_array.
  replace (Z.to_nat (hi - lo - 0)) with (Z.to_nat (hi - lo)) by lia.
  entailer!.
Qed.

Lemma ceil_shape_to_full_shape : forall x lo hi,
  ceil_shape x lo hi |-- full_shape (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  rewrite ceil_shape_0_shift.
  unfold ceil_shape, full_shape, store_undef_array.
  replace (Z.to_nat (hi - lo - 0)) with (Z.to_nat (hi - lo)) by lia.
  entailer!.
Qed.

Lemma missing_i_to_ceil_head : forall x lo hi a (l : list A),
  missing_i x lo lo hi (a :: l) |-- ceil x (lo + 1) hi l.
Proof.
  intros.
  rewrite missing_i_unfold.
  Split ; try entailer!.
Qed.

Lemma undef_missing_i_to_undef_ceil_head : forall x lo hi,
  lo < hi ->
  undef_missing_i x lo lo hi |-- undef_ceil x (lo + 1) hi.
Proof.
  intros.
  rewrite undef_missing_i_unfold ; try lia.
  Split ; try entailer!.
Qed.

Lemma missing_i_shape_to_ceil_shape_head : forall x lo hi,
  lo < hi ->
  missing_i_shape x lo lo hi |-- ceil_shape x (lo + 1) hi.
Proof.
  intros.
  rewrite missing_i_shape_unfold ; try lia.
  Split ; try entailer!.
  Intros x0. entailer!.
Qed.

Lemma missing_i_to_ceil_tail : forall x lo hi a (l : list A),
  missing_i x hi lo hi (l ++ a :: nil) |-- ceil x lo (hi - 1) l.
Proof.
  intros.
  revert lo hi.
  induction l ; simpl ; intros ; ArraySimplify ; Split ; try entailer!.
  prop_apply ceil_length. 
  Intros.
  rewrite length_app in H0. simpl in H0. 
  lia.
Qed.

Lemma undef_missing_i_to_undef_ceil_tail : forall x lo hi,
  lo < hi -> 
  undef_missing_i x hi lo hi |-- undef_ceil x lo (hi - 1).
Proof.
  intros.
  unfold undef_missing_i, undef_ceil.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  replace (hi - 1 - lo) with (hi - (lo + 1)) by lia.
  simpl. 
  Split ; try entailer!.
  set (len := Z.to_nat (hi - (lo + 1))).
  assert (len = Z.to_nat (hi - (lo + 1))) by lia.
  clearbody len.
  generalize dependent lo. revert hi.
  induction len ; simpl ; intros ; ArraySimplify.
  - entailer!. 
  - Split ; try entailer!.
    sep_apply IHlen ; try lia.
    entailer!. 
Qed.

Lemma missing_i_shape_to_ceil_shape_tail : forall x lo hi,
  lo < hi -> 
  missing_i_shape x hi lo hi |-- ceil_shape x lo (hi - 1).
Proof.
  intros.
  unfold missing_i_shape, ceil_shape.
  replace (Z.to_nat (hi - lo)) with (S (Z.to_nat (hi - (lo + 1)))) by lia.
  replace (hi - 1 - lo) with (hi - (lo + 1)) by lia.
  simpl.  
  Split ; try entailer!. Intros x0.
  set (len := Z.to_nat (hi - (lo + 1))).
  assert (len = Z.to_nat (hi - (lo + 1))) by lia.
  clearbody len.
  generalize dependent lo. revert hi x0.
  induction len ; simpl ; intros ; ArraySimplify.
  - entailer!.
  - Split ; try entailer!. Intros x1.
    Exists x0.
    sep_apply IHlen ; try lia.
    entailer!.
Qed.

Lemma missing_i_to_undef_missing_i : forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- undef_missing_i x i lo hi.
Proof.
  intros.
  prop_apply missing_i_length. Intros.
  revert H.
  revert i lo hi.
  induction l ; simpl ; intros ; ArraySimplify. 
  + entailer!.
  + Split ; Intros ; rewrite undef_missing_i_unfold ; try lia ; [Left | Right].
    * sep_apply ceil_to_undef_ceil.
      entailer!. 
    * sep_apply IHl.
      sep_apply store_to_undefstore.
      entailer!.
      lia.
Qed.

Lemma missing_i_to_missing_i_shape : forall x i lo hi (l : list A),
  missing_i x i lo hi l |-- missing_i_shape x i lo hi.
Proof.
  intros.
  prop_apply missing_i_length. Intros.
  revert H.
  revert i lo hi.
  induction l ; simpl ; intros ; ArraySimplify.
  + entailer!.
  + Split ; Intros ; rewrite missing_i_shape_unfold ; try lia ; [Left | Right].
    * sep_apply ceil_to_ceil_shape.
      entailer!.
    * sep_apply IHl.
      Exists a.
      entailer!.
      lia.
Qed.

Lemma full_to_undef_full : forall x n (l : list A),
  full x n l |-- undef_full x n.
Proof.
  intros.
  sep_apply full_to_ceil.
  sep_apply ceil_to_undef_ceil.
  sep_apply undef_ceil_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!. 
Qed.

Lemma full_to_full_shape : forall x n (l : list A),
  full x n l |-- full_shape x n.
Proof.
  intros.
  sep_apply full_to_ceil.
  sep_apply ceil_to_ceil_shape.
  sep_apply ceil_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.  
Qed.

(* Split & Merge Lemmas  *)

Lemma ceil_split_to_missing_i : forall x lo n m (l : list A) a,
  lo <= n < m ->
  ceil x lo m l |-- storeA x n (Znth (n - lo) l a) ** missing_i x n lo m l.
Proof.
  intros.
  revert H.
  rename m into hi.
  revert lo; induction l; intros; simpl; ArraySimplify.
  + entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - Right.
      sep_apply IHl; [ | lia ].
      rewrite Znth_cons by lia.
      replace (n - (lo + 1)) with (n - lo - 1) by lia.
      entailer!.
    - Left.
      subst n.
      replace (lo - lo) with 0 by lia.
      entailer!.
Qed. 

Lemma full_split_to_missing_i : forall x n m (l : list A) a,
  0 <= n < m ->
  full x m l |-- storeA x n (Znth n l a) ** missing_i x n 0 m l.
Proof.
  intros.
  sep_apply full_to_ceil.
  sep_apply (ceil_split_to_missing_i x 0 n m l a) ; eauto.
  replace (n - 0) with n by lia.
  entailer!.
Qed. 

Lemma missing_i_merge_to_ceil: forall x lo n m a (l: list A),
  lo <= n < m -> 
  storeA x n a ** missing_i x n lo m l |-- ceil x lo m (replace_Znth (n - lo) a l).
Proof.
  intros.
  revert H.
  revert lo n m.
  induction l; intros; simpl ; ArraySimplify ; try entailer!.
  Split ; try entailer!.
  - subst n.
    replace (lo - lo) with 0 by lia.
    simpl.
    entailer!.
  - sep_apply IHl; [ | lia ].
    rewrite replace_Znth_cons by lia.
    replace (n - (lo + 1)) with (n - lo - 1) by lia.
    ArraySimplify.
    entailer!.
Qed.

Lemma missing_i_merge_to_full: forall x n m a (l: list A),
  0 <= n < m -> 
  storeA x n a ** missing_i x n 0 m l |-- full x m (replace_Znth n a l).
Proof.
  intros.
  sep_apply (missing_i_merge_to_ceil x 0 n m a l) ; eauto.
  sep_apply ceil_to_full.
  replace (n - 0) with n by lia.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.


Lemma undef_ceil_split_to_undef_missing_i : forall x lo n m,
  lo <= n < m ->
  undef_ceil x lo m |-- undefstoreA x n ** undef_missing_i x n lo m.
Proof.
  intros.
  unfold undef_ceil, undef_missing_i.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi; induction len; intros; simpl.
  + entailer!.
  + pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - Right. entailer!.
      sep_apply (IHlen (lo + 1) n hi) ; eauto ; try lia.
      entailer!.
    - Left.
      subst n. entailer!.
Qed.

Lemma undef_full_split_to_undef_missing_i : forall x n m,
  0 <= n < m ->
  undef_full x m |-- undefstoreA x n ** undef_missing_i x n 0 m.
Proof.
  intros.
  sep_apply undef_full_to_undef_ceil.
  sep_apply (undef_ceil_split_to_undef_missing_i x 0 n m) ; eauto.
  entailer!.
Qed. 

Lemma undef_missing_i_merge_to_undef_ceil: forall x lo n m,
  lo <= n < m -> 
  undefstoreA x n ** undef_missing_i x n lo m |-- undef_ceil x lo m.
Proof.
  intros.
  unfold undef_ceil, undef_missing_i.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi.
  induction len; intros; simpl ; try entailer!.
  Split ; try entailer!.
  - subst n.
    replace (lo - lo) with 0 by lia.
    simpl.
    entailer!.
  - sep_apply (IHlen (lo + 1) n hi) ; try lia.
    entailer!.
Qed.

Lemma undef_missing_i_merge_to_undef_full: forall x n m,
  0 <= n < m -> 
  undefstoreA x n ** undef_missing_i x n 0 m |-- undef_full x m.
Proof.
  intros.
  sep_apply (undef_missing_i_merge_to_undef_ceil x 0 n m) ; eauto.
  sep_apply undef_ceil_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma ceil_shape_split_to_missing_i_shape : forall x lo n m,
  lo <= n < m ->
  ceil_shape x lo m |-- EX a, storeA x n a ** missing_i_shape x n lo m.
Proof.
  intros.
  unfold ceil_shape, missing_i_shape.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi; induction len; intros; simpl.
  + entailer!.
  + Intros a.
    pose proof Z_le_lt_eq_dec lo n ltac:(lia) as [? | ?].
    - sep_apply (IHlen (lo + 1) n hi) ; eauto ; try lia.
      Intros a0. Exists a0.
      Right. entailer!. Exists a.
      entailer!.
    - Exists a. Left.
      subst n.
       entailer!.
Qed.

Lemma full_shape_split_to_missing_i_shape : forall x n m,
  0 <= n < m ->
  full_shape x m |-- EX a, storeA x n a ** missing_i_shape x n 0 m.
Proof.
  intros.
  sep_apply full_shape_to_ceil_shape.
  sep_apply (ceil_shape_split_to_missing_i_shape x 0 n m) ; eauto.
  entailer!.
Qed. 

Lemma missing_i_shape_merge_to_ceil_shape: forall x lo n m a,
  lo <= n < m -> 
  storeA x n a ** missing_i_shape x n lo m |-- ceil_shape x lo m.
Proof.
  intros.
  unfold ceil_shape, missing_i_shape.
  revert H.
  rename m into hi.
  set (len := Z.to_nat (hi - lo)).
  assert (len = Z.to_nat (hi - lo)) by lia.
  clearbody len.
  revert H.
  revert lo n hi.
  induction len; intros; simpl ; try entailer!.
  Split ; try entailer!.
  - subst n. Exists a. entailer!.
  - Intros x0.
    sep_apply (IHlen (lo + 1) n hi) ; try lia.
    Exists x0.
    entailer!.
Qed.

Lemma missing_i_shape_merge_to_full_shape: forall x n m a,
  0 <= n < m -> 
  storeA x n a ** missing_i_shape x n 0 m |-- full_shape x m.
Proof.
  intros.
  sep_apply (missing_i_shape_merge_to_ceil_shape x 0 n m) ; eauto.
  sep_apply ceil_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma ceil_split_to_ceil : forall x lo mid hi (l : list A),
  lo <= mid <= hi ->
  ceil x lo hi l |-- ceil x lo mid (sublist 0 (mid - lo) l) ** ceil x mid hi (sublist (mid - lo) (hi - lo) l).
Proof.
  intros.
  generalize dependent lo. revert mid hi.
  induction l; intros ; ArraySimplify.
  - do 2 rewrite sublist_of_nil. 
    ArraySimplify.
    entailer!. 
  - prop_apply ceil_length. Intros.
    destruct (Z_lt_ge_dec mid (lo + 1)).
    + assert (mid = lo) by lia; subst mid.
      rewrite sublist_nil by lia. 
      replace (lo - lo) with 0 by lia.
      rewrite sublist_cons1 ; try lia.
      ArraySimplify.
      rewrite sublist_self.
      entailer!.
      rewrite Zlength_correct. lia.
    + rewrite sublist_cons1 by lia.
      rewrite sublist_cons2; try lia.
      2 :{
        rewrite Zlength_correct. simpl. lia. 
      }
      replace (mid - lo - 1) with (mid - (lo + 1)) by lia.
      replace (hi - lo - 1) with (hi - (lo + 1)) by lia.
      sep_apply (IHl mid) ; try lia.
      ArraySimplify.
      entailer!.
Qed.

Lemma undef_ceil_split_to_undef_ceil : forall x lo mid hi,
  lo <= mid <= hi ->
  undef_ceil x lo hi |-- undef_ceil x lo mid ** undef_ceil x mid hi.
Proof.
  intros.
  unfold undef_ceil.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!.
  - assert (mid = lo) by lia. 
    subst. 
    entailer!.
  - apply IHlen1; lia.
Qed.

Lemma ceil_shape_split_to_ceil_shape : forall x lo mid hi,
  lo <= mid <= hi ->
  ceil_shape x lo hi |-- ceil_shape x lo mid ** ceil_shape x mid hi.
Proof.
  intros.
  unfold ceil_shape.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!.
  - assert (mid = lo) by lia. 
    subst. 
    entailer!.
  - Intros x0. Exists x0.
    sep_apply IHlen1 ; eauto ; try lia.
    entailer!.
Qed.

Lemma full_split_to_ceil : forall x n m (l : list A),
  0 <= n <= m ->
  full x m l |--  
  ceil x 0 n (sublist 0 n l) ** ceil x n m (sublist n m l).
Proof.
  intros.
  sep_apply full_to_ceil.
  sep_apply (ceil_split_to_ceil x 0 n m l) ; try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma full_split_to_full : forall x n m (l : list A),
  0 <= n <= m ->
  full x m l |--  
  full x n (sublist 0 n l) ** full (x + n * sizeA) (m - n) (sublist n m l).
Proof.
  intros.
  sep_apply full_split_to_ceil ; eauto.
  sep_apply ceil_to_full. 
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply ceil_to_full.
Qed.

Lemma undef_full_split_to_undef_ceil : forall x n m,
  0 <= n <= m ->
  undef_full x m |--  
  undef_ceil x 0 n ** undef_ceil x n m.
Proof.
  intros.
  sep_apply undef_full_to_undef_ceil.
  sep_apply (undef_ceil_split_to_undef_ceil x 0 n m) ; try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma undef_full_split_to_undef_full : forall x n m,
  0 <= n <= m ->
  undef_full x m |--  
  undef_full x n ** undef_full (x + n * sizeA) (m - n).
Proof.
  intros.
  sep_apply undef_full_split_to_undef_ceil ; eauto.
  sep_apply undef_ceil_to_undef_full. 
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply undef_ceil_to_undef_full.
Qed.

Lemma full_shape_split_to_ceil_shape : forall x n m,
  0 <= n <= m ->
  full_shape x m |--  
  ceil_shape x 0 n ** ceil_shape x n m.
Proof.
  intros.
  sep_apply full_shape_to_ceil_shape.
  sep_apply (ceil_shape_split_to_ceil_shape x 0 n m) ; try lia.
  replace (n - 0) with n by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma full_shape_split_to_full_shape : forall x n m,
  0 <= n <= m ->
  full_shape x m |--  
  full_shape x n ** full_shape (x + n * sizeA) (m - n).
Proof.
  intros.
  sep_apply full_shape_split_to_ceil_shape ; eauto.
  sep_apply ceil_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (n - 0) with n by lia.
  entailer!.
  apply ceil_shape_to_full_shape.
Qed.

Lemma ceil_merge_to_ceil : forall x lo mid hi (l1 l2 : list A),
  lo <= mid <= hi ->
  ceil x lo mid l1 ** ceil x mid hi l2 |-- ceil x lo hi (l1 ++ l2).
Proof.
  intros.
  generalize dependent lo. revert mid hi l2.
  induction l1; intros ; ArraySimplify. 
  - rewrite app_nil_l.
    Intros. subst.
    entailer!.
  - simpl. ArraySimplify.
    entailer!.
    prop_apply ceil_length. Intros.
    apply IHl1. lia. 
Qed. 

Lemma undef_ceil_merge_to_undef_ceil : forall x lo mid hi,
  lo <= mid <= hi ->
  undef_ceil x lo mid ** undef_ceil x mid hi |-- undef_ceil x lo hi.
Proof.
  intros.
   unfold undef_ceil.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!. 
  - subst.
    entailer!.
  - apply IHlen1; lia.
Qed.

Lemma ceil_shape_merge_to_ceil_shape : forall x lo mid hi,
  lo <= mid <= hi ->
  ceil_shape x lo mid ** ceil_shape x mid hi |-- ceil_shape x lo hi.
Proof.
  intros.
  unfold ceil_shape.
  set (len1 := Z.to_nat (mid - lo)).
  set (len2 := Z.to_nat (hi - mid)).
  replace (Z.to_nat (hi - lo)) with (len1 + len2)%nat by lia.
  assert (len1 = Z.to_nat (mid - lo)) by lia.
  assert (len2 = Z.to_nat (hi - mid)) by lia.
  clearbody len1. clearbody len2.
  generalize dependent mid. revert lo hi len2.
  induction len1; intros ; simpl ; try entailer!.
  - subst. 
    entailer!.
  - Intros x0. Exists x0.
    sep_apply IHlen1 ; eauto ; try lia.
    entailer!.
Qed.

Lemma ceil_merge_to_full : forall x lo mid hi (l1 l2 : list A),
  lo <= mid <= hi ->
  ceil x lo mid l1 ** ceil x mid hi l2 |-- full (x + lo * sizeA) (hi - lo) (l1 ++ l2).
Proof.
  intros.
  sep_apply ceil_merge_to_ceil ; eauto.
  sep_apply ceil_to_full.
  entailer!.
Qed.

Lemma full_merge_to_full : forall x n m (l1 l2 : list A),
  0 <= n <= m ->
  full x n l1 ** full (x + n * sizeA) (m - n) l2 |-- full x m (l1 ++ l2).
Proof.
  intros.
  sep_apply full_to_ceil.
  sep_apply (full_to_ceil (x + n * sizeA)).
  rewrite <- ceil_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (ceil_merge_to_full x 0 n m) ; eauto.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma undef_ceil_merge_to_undef_full : forall x lo mid hi,
  lo <= mid <= hi ->
  undef_ceil x lo mid ** undef_ceil x mid hi |-- undef_full (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  sep_apply undef_ceil_merge_to_undef_ceil ; eauto.
  sep_apply undef_ceil_to_undef_full.
  entailer!.
Qed.

Lemma undef_full_merge_to_undef_full : forall x n m,
  0 <= n <= m ->
  undef_full x n ** undef_full (x + n * sizeA) (m - n) |-- undef_full x m.
Proof.
  intros.
  sep_apply undef_full_to_undef_ceil.
  sep_apply (undef_full_to_undef_ceil (x + n * sizeA)).
  rewrite <- undef_ceil_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (undef_ceil_merge_to_undef_ceil x 0 n m) ; eauto.
  replace (Z.to_nat n + Z.to_nat (m - n))%nat with (Z.to_nat m) by lia.
  sep_apply undef_ceil_to_undef_full.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

Lemma ceil_shape_merge_to_full_shape : forall x lo mid hi,
  lo <= mid <= hi ->
  ceil_shape x lo mid ** ceil_shape x mid hi |-- full_shape (x + lo * sizeA) (hi - lo).
Proof.
  intros.
  sep_apply ceil_shape_merge_to_ceil_shape ; eauto.
  sep_apply ceil_shape_to_full_shape.
  entailer!.
Qed.

Lemma full_shape_merge_to_full_shape : forall x n m,
  0 <= n <= m ->
  full_shape x n ** full_shape (x + n * sizeA) (m - n) |-- full_shape x m.
Proof.
  intros.
  sep_apply full_shape_to_ceil_shape.
  sep_apply (full_shape_to_ceil_shape (x + n * sizeA)).
  rewrite <- ceil_shape_shift.
  replace (n + 0) with n by lia.
  replace (n + (m - n)) with m by lia.
  sep_apply (ceil_shape_merge_to_ceil_shape x 0 n m) ; eauto.
  replace (Z.to_nat n + Z.to_nat (m - n))%nat with (Z.to_nat m) by lia.
  sep_apply ceil_shape_to_full_shape.
  replace (x + 0 * sizeA) with x by lia.
  replace (m - 0) with m by lia.
  entailer!.
Qed.

End ArrayLib. 

Module StoreIntAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(INT)) # Int |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(INT)) # Int |->_ .
  Definition sizeA := sizeof(INT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_int_undef_store_int.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(INT) + lo * sizeof(INT)) with (x + (lo + n) * sizeof(INT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(INT) + lo * sizeof(INT)) with (x + (lo + n) * sizeof(INT)) by lia.
    entailer!.
  Qed.

End StoreIntAsElement.

Module IntArray := ArrayLib (StoreIntAsElement).

Module StoreUIntAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UINT)) # UInt |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UINT)) # UInt |->_ .
  Definition sizeA := sizeof(UINT).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uint_undef_store_uint.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UINT) + lo * sizeof(UINT)) with (x + (lo + n) * sizeof(UINT)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UINT) + lo * sizeof(UINT)) with (x + (lo + n) * sizeof(UINT)) by lia.
    entailer!.
  Qed.

End StoreUIntAsElement.

Module UIntArray := ArrayLib (StoreUIntAsElement).

Module StoreCharAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(CHAR)) # Char |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(CHAR)) # Char |->_ .
  Definition sizeA := sizeof(CHAR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_char_undef_store_char.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(CHAR) + lo * sizeof(CHAR)) with (x + (lo + n) * sizeof(CHAR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(CHAR) + lo * sizeof(CHAR)) with (x + (lo + n) * sizeof(CHAR)) by lia.
    entailer!.
  Qed.

End StoreCharAsElement.

Module CharArray := ArrayLib (StoreCharAsElement).

Module StoreUCharAsElement <: ELEMENT_STORE.
  Definition A := Z.
  Definition storeA (x: addr) (lo: Z) (a: Z): Assertion :=
    (x + lo * sizeof(UCHAR)) # UChar |-> a.
  Definition undefstoreA (x: addr) (lo: Z): Assertion :=
    (x + lo * sizeof(UCHAR)) # UChar |->_ .
  Definition sizeA := sizeof(UCHAR).

  Lemma store_to_undefstore : forall x lo a,
    storeA x lo a |-- undefstoreA x lo.
  Proof.
    intros.
    apply store_uchar_undef_store_uchar.
  Qed.

  Lemma storeA_shift : forall x n lo a,
    storeA (x + n * sizeA) lo a --||-- storeA x (lo + n) a.
  Proof.
    intros.
    unfold storeA, sizeA.
    replace (x + n * sizeof(UCHAR) + lo * sizeof(UCHAR)) with (x + (lo + n) * sizeof(UCHAR)) by lia.
    entailer!.
  Qed.

  Lemma undefstoreA_shift : forall x n lo,
    undefstoreA (x + n * sizeA) lo --||-- undefstoreA x (lo + n).
  Proof.
    intros.
    unfold undefstoreA, sizeA.
    replace (x + n * sizeof(UCHAR) + lo * sizeof(UCHAR)) with (x + (lo + n) * sizeof(UCHAR)) by lia.
    entailer!.
  Qed.

End StoreUCharAsElement.

Module UCharArray := ArrayLib (StoreUCharAsElement).

Definition repeat_Z {A: Type} (a: A) (n: Z): list A :=
  repeat a (Z.to_nat n).

Lemma repeat_Z_tail : forall {A: Type} (a: A) n,
  n >= 0 ->
  repeat_Z a (n + 1) = repeat_Z a n ++ a :: nil.
Proof.
  intros.
  unfold repeat_Z.
  replace (Z.to_nat (n + 1)) with (S (Z.to_nat n)) by lia.
  set (Z.to_nat n) as m.
  clearbody m. clear H n. 
  rename m into n. 
  induction n ; simpl in *; auto. 
  rewrite IHn. auto. 
Qed.

End ArrayLibSig.