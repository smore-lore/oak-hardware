(****************************************************************************)
(* Copyright 2021 The Project Oak Authors                                   *)
(*                                                                          *)
(* Licensed under the Apache License, Version 2.0 (the "License")           *)
(* you may not use this file except in compliance with the License.         *)
(* You may obtain a copy of the License at                                  *)
(*                                                                          *)
(*     http://www.apache.org/licenses/LICENSE-2.0                           *)
(*                                                                          *)
(* Unless required by applicable law or agreed to in writing, software      *)
(* distributed under the License is distributed on an "AS IS" BASIS,        *)
(* WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. *)
(* See the License for the specific language governing permissions and      *)
(* limitations under the License.                                           *)
(****************************************************************************)

Require Import Coq.Init.Nat.
Require Import Coq.micromega.Lia.
Require Import Cava.Cava.
Local Open Scope vector_scope.
Require Import Examples.TwoSorter.

Section WithCava.
  Context {signal} `{Cava signal}.

  (* simpler definition for 2^n to make types easier to work with *)
  Fixpoint two_pow (n : nat) : nat :=
    match n with
    | O => 1
    | S n => let r := two_pow n in r + r
    end.

  Lemma two_pow_pow : forall n : nat, two_pow n = pow 2 n.
  Proof.
    intros.
    induction n.
    - reflexivity.
    - simpl.
      rewrite IHn.
      lia.
  Qed.

  Definition parl {A m n}
    (default : signal A)
    (f : signal (Vec A m) -> cava (signal (Vec A m)))
    (g : signal (Vec A n) -> cava (signal (Vec A n)))
    (input : signal (Vec A (m + n)))
    : cava (signal (Vec A (m + n))) :=
    inputV <- unpackV input ;;
    let (ifst, isnd) := Vector.splitat m inputV in
    ifst' <- (packV >=> f >=> unpackV) ifst ;;
    isnd' <- (packV >=> g >=> unpackV) isnd ;;
    packV (ifst' ++ isnd').

  Fixpoint vec_alternate {A n m}
    (default : A)
    (a : Vector.t A n)
    (b : Vector.t A m)
    : Vector.t A (n + m) :=
    match a, b with
    | ahd :: atl, bhd :: btl =>
        resize_default default (n + m) (ahd :: bhd :: vec_alternate default atl btl)
    | _, _ => a ++ b
    end.

  Definition vec_riffle {A n}
    (default : A)
    (input : Vector.t A (two_pow (S n)))
    : Vector.t A (two_pow (S n)) :=
    let (fst_halve, snd_halve) := Vector.splitat (two_pow n) input in
    vec_alternate default fst_halve snd_halve.

  Fixpoint list_odds {A} (a : list A) :=
    match a with
    | a1 :: a2 :: atl => a1 :: list_odds atl
    | empty_or_single => empty_or_single
    end%list.
  Definition vec_odds {A n} (default : A) (a : Vector.t A (n + n)) : Vector.t A n :=
    resize_default default n (Vector.of_list (list_odds (Vector.to_list a))).

  Fixpoint list_evens {A} (a : list A) :=
    match a with
    | a1 :: a2 :: atl => a2 :: list_evens atl
    | empty_or_single => []
    end%list.
  Definition vec_evens {A n} (default : A) (a : Vector.t A (n + n)) : Vector.t A n :=
    resize_default default n (Vector.of_list (list_evens (Vector.to_list a))).

  Definition vec_unriffle {A n}
    (default : A)
    (input : Vector.t A (two_pow (S n)))
    : Vector.t A (two_pow (S n)) :=
    vec_odds default input ++ vec_evens default input.

  Definition riffle {A n}
    (default : signal A)
    : signal (Vec A (two_pow (S n))) -> cava (signal (Vec A (two_pow (S n)))) :=
    unpackV >=> vec_riffle default >=> packV.

  Definition unriffle {A n}
    (default : signal A)
    : signal (Vec A (two_pow (S n))) -> cava (signal (Vec A (two_pow (S n)))) :=
    unpackV >=> vec_unriffle default >=> packV.

  Definition interleave {A n}
    (default : signal A)
    (f : signal (Vec A (two_pow n)) -> cava (signal (Vec A (two_pow n))))
    : signal (Vec A (two_pow (S n))) -> cava (signal (Vec A (two_pow (S n)))) :=
    unriffle default >=> parl default f f >=> riffle default.

  Fixpoint evens {A n}
    (default : signal A)
    (f : signal (Vec A 2) -> cava (signal (Vec A 2)))
    : signal (Vec A n) -> cava (signal (Vec A n)) :=
    match n with
    | O => ret
    | S n' => match n' with
              | O => ret
              | S n'' => parl default f (evens default f)
              end
    end.

  Fixpoint butterfly {A n}
    (default : signal A)
    (f : signal (Vec A 2) -> cava (signal (Vec A 2)))
    : signal (Vec A (two_pow (S n))) -> cava (signal (Vec A (two_pow (S n)))) :=
    match n with
    | O => f
    | S n' => interleave default (butterfly default f) >=> evens default f
    end.

  Fixpoint bitonicSorter {bw n}
    (default : signal (Vec Bit bw))
    : signal (Vec (Vec Bit bw) (two_pow n)) -> cava (signal (Vec (Vec Bit bw) (two_pow n))) :=
    match n with
    | O => ret
    | S n' => (parl default (bitonicSorter default) (bitonicSorter default >=> Vec.rev))
              >=> butterfly default twoSorter
    end.

End WithCava.

Section Test.
  Definition run_sort (n : nat) (v : Vector.t N (two_pow n)) : Vector.t N (two_pow n) :=
    let bw := 8 in
    Vector.map Bv2N (@bitonicSorter combType _ _ n
                       (N2Bv_sized bw 0)
                       (Vector.map (N2Bv_sized bw) v)).

  Open Scope N.
  Lemma testSort0_1 : [1] = run_sort 0 [1]. reflexivity. Qed.
  Lemma testSort1_1 : [1; 2] = run_sort 1 [1; 2]. reflexivity. Qed.
  Lemma testSort1_2 : [1; 2] = run_sort 1 [2; 1]. reflexivity. Qed.
  Lemma testSort2_1 : [1; 2; 3; 4] = run_sort 2 [1; 2; 3; 4]. reflexivity. Qed.
  Lemma testSort2_2 : [1; 2; 3; 4] = run_sort 2 [3; 2; 1; 4]. reflexivity. Qed.
  Lemma testSortBig : [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16] =
           run_sort 4 [12; 2; 11; 10; 16; 14; 6; 3; 5; 1; 7; 15; 9; 13; 4; 8].
  Proof. reflexivity. Qed.
  Close Scope N.
End Test.

Section Properties.
  Fixpoint inorder {bw n} (v : Vector.t (Bvector bw) n) : Prop :=
    match v with
    | a :: v' =>
        match v' with
        | b :: v'' => (Bv2N a <=? Bv2N b = true)%N /\ inorder v'
        | [] => True
        end
    | _ => True
    end.

  Lemma butterflySortedReverseInOrder :
    forall n bw : nat,
    forall d : Bvector bw,
    forall v1 v2 : Vector.t (Bvector bw) (two_pow n),
    inorder v1 -> inorder v2 ->
    inorder (@butterfly combType _ (Vec Bit bw) _ d (@twoSorter combType _ _) (v1 ++ (reverse v2))).
  Proof.
    induction n; intros.
    { simpl in v1, v2.
      constant_vector_simpl v1.
      constant_vector_simpl v2.
      simpl.

      unfold N.leb.
      destruct (Bv2N x0 ?= Bv2N x)%N eqn:e.
      { simpl. rewrite e. tauto. }
      { simpl. rewrite e. tauto. }
      { simpl.
        rewrite N.compare_antisym.
        rewrite e.
        tauto. } }
    { simpl.
      cbv [interleave
           parl
           packV
           unpackV
           Combinational.CombinationalSemantics
           unriffle
           riffle
           vec_riffle
           vec_unriffle].
      simpl.
      do 2 rewrite VectorSpec.splitat_append.
  Admitted.

  Theorem bitonicSorterInOrder :
    forall n bw : nat,
    forall d : Bvector bw,
    forall v : Vector.t (Bvector bw) (two_pow n),
    inorder (@bitonicSorter combType _ _ _ d v).
  Proof.
    induction n.
    { simpl.
      intros.
      constant_vector_simpl v.
      simpl.
      trivial. }
    { simpl.
      intros.
      cbv [parl
           packV
           unpackV
           Combinational.CombinationalSemantics
           Vec.rev].
      simpl.
      destruct (@Vector.splitat (Vector.t bool bw) (two_pow n) (two_pow n) v) as [ifst isnd] eqn:e.
      apply butterflySortedReverseInOrder.
      { apply IHn. }
      { apply IHn. } }
  Qed.

  (* TODO: proof that the sorter is a permutation *)
End Properties.
