(* Copyright 2020 The Project Oak Authors                                   *)
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

Require Import Coq.Arith.Arith Coq.Bool.Bvector Coq.Init.Nat Coq.Vectors.VectorDef.

Section Spec.
  (* FIPS 197, 2.1: Word A group of 32 bits that is treated either as a single
     entity or as an array of 4 bytes. *)
  Variable bits_per_byte : nat.
  Variable bytes_per_word : nat.
  Definition byte := Bvector bits_per_byte.
  Definition word := t byte bytes_per_word.

  (* FIPS 197, 2.2: Number of columns (32-bit words) comprising the State.
     For this standard, Nb = 4. *)
  Variable nb : nat.

  Definition state := t word nb.

  (* FIXME: better way to work with conditionals like this *)
  Theorem sub_sub_1_l x : x - 1 <= x.
  Proof. induction x. auto with arith. rewrite <- Nat.add_1_r. rewrite PeanoNat.Nat.add_sub. auto with arith. Qed.
  Theorem sub_succ x y : x - S y <= x - y.
  Proof.
    rewrite <- (Nat.add_1_r y).
    rewrite PeanoNat.Nat.sub_add_distr.
    rewrite sub_sub_1_l.
    reflexivity.
  Qed.
  Theorem sub_0_smaller (x : nat) : x - 0 < S x.
  Proof. rewrite Nat.sub_0_r. auto with arith. Qed. 
  Theorem sub_1_smaller (x : nat) : x - 1 < S x.
  Proof. induction x; auto with arith. Qed.
  Theorem lt_s a b : S a <= b -> a <= b.
  Proof. intros. auto with arith. Qed.
  Theorem le_lt_lt a b c : a <= b -> b < c -> a < c.
  Proof. intros. unfold lt in *. induction H. assumption. apply IHle. apply lt_s. assumption. Qed.
  Theorem le_le_le a b c : a <= b -> b <= c -> a <= c.
  Proof. intros. induction H. assumption. apply IHle. apply lt_s. assumption. Qed.
  Theorem sub_smaller (x : nat) (y : nat) : x - y < S x.
  Proof.
    induction y.
    { exact (sub_0_smaller x). }
    refine (le_lt_lt (x - S y) (x - y) (S x) _ _).
    rewrite sub_succ. auto with arith.
    assumption.
  Qed.

  Theorem mod_lt (x : nat) (m : nat) : (m > 0) -> (modulo x m) < m.
  Proof.
    intros.
    destruct m.
    inversion H.
    simpl.
    induction x.
    simpl.
    rewrite Nat.sub_diag.
    auto with arith.
    exact (sub_smaller _ _).
  Qed.

  Fixpoint iota' n max (p : n <= max) : t (Fin.t max) n.
    Proof.
    induction n.
    exact (nil (Fin.t max)).
    refine (cons (Fin.t max) (@Fin.of_nat_lt (max - n - 1) max _) _ _).
    induction max.
    { inversion p. }
    { rewrite <- Nat.sub_add_distr.
      rewrite <- Nat.add_comm.
      rewrite Nat.sub_add_distr.
      simpl. rewrite Nat.sub_0_r.
      exact (sub_smaller max n). }
    apply IHn.
    auto with arith.
   Defined.
  Theorem le_refl n : n <= n. Proof. auto with arith. Defined.
  Definition iota n := iota' n n (le_refl n).

  Eval compute in iota(3).
  (* [Fin.FS (Fin.FS Fin.F1); Fin.FS Fin.F1; Fin.F1] *)
  (* 2, 1, 0 *)

  Definition fin_rot {n} (a : Fin.t n) (rot_by : nat) : Fin.t n.
    Proof.
      refine (@Fin.of_nat_lt (modulo (rot_by + proj1_sig (Fin.to_nat a)) n) n _).
      apply mod_lt.
      induction a; auto with arith.
    Qed.

  Definition shift_rows (x : state) : state :=
    map2 (fun column => fun col_i => 
      map2 (fun row => fun row_i => 
        nth (nth x (fin_rot col_i (proj1_sig (Fin.to_nat row_i)))) row_i
      ) column (iota bytes_per_word)
    ) x (iota nb).

  Definition inv_shift_rows (x : state) : state :=
    map2 (fun column => fun col_i => 
      map2 (fun row => fun row_i => 
        nth (nth x (fin_rot col_i (bytes_per_word * (proj1_sig (Fin.to_nat row_i))))) row_i
      ) column (iota bytes_per_word)
    ) x (iota nb).

  Section Properties.
    Theorem inverse_shift_rows (x : state) : inv_shift_rows (shift_rows x) = x.
    Proof.
      unfold shift_rows, inv_shift_rows.
      cbv [state word] in *.
      induction x.
      reflexivity.
    Abort.
  End Properties.
End Spec.
