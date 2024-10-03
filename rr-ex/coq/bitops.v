Require Import ZArith.
From stdpp Require Import numbers.
From refinedrust Require Import typing.
From QuickChick Require Import QuickChick.
Require Import FunInd Recdef.

Open Scope Z.
(*Definition type_of_ptr_add `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=*)
  (*fn(∀ () : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (l, offset) : loc * Z, (λ ϝ, []); l :@: alias_ptr_t, (offset) :@: int usize_t; λ π,*)
    (*⌜l `has_layout_loc` (use_layout_alg' T_st)⌝ ∗*)
    (*⌜(offset * size_of_st T_st)%Z ∈ isize_t⌝ ∗*)
    (*loc_in_bounds l 0 ((Z.to_nat offset) * size_of_st T_st)*)
  (*) →*)
  (*∃ () : unit, (l, offset) @ offset_ptr_t T_st; λ π, £ (S (num_laters_per_step 1)) ∗ atime 1.*)

(*Definition saturating_add_spec `{!LayoutAlg} (T_st : syn_type) : function := {|*)
  (*f_args := [("lhs", usize_t : layout); ("rhs", usize_t : layout)];*)
  (*[>f_local_vars<]*)
  (*f_code :=*)
    (*<["_bb0" :=*)
      (*return zst_val*)
    (*]>%E $*)
    (*∅;*)
  (*f_init := "_bb0";*)
(*|}.*)

Definition int_bitwidth (it: int_type) := 8*2^it_byte_size_log it.
(* `ws` is the bitwidth of the target
   `x` is the target integer
   `n` is the shift amount
   ref. https://stackoverflow.com/questions/776508/best-practices-for-circular-shift-rotate-operations-in-c/776523#776523
 *)
(*Definition Zrotate_right ws x n :=*)
  (*let mask := Z.land (ws-1) in*)
  (*let count := mask n in*)
  (*mask $ Z.lor (Z.shiftr x count) (Z.shiftl x (mask (-count))).*)

(*Definition Zrotate_right ws x n := Z.land (Z.ones ws)*)
  (*$ Z.lor (Z.shiftr x n) (Z.shiftl x (ws - n)).*)

(** * Rotate shift
  We don't going general.
  Use this function like [Zrotate_right (int_bitwidth _)] for each integer type.
 *)
Check (_ && _).
Check Z.succ_pred_induction 0.
Definition Zrotate_right (ws: Z) (x n: Z) :=
  let sa := n `mod` ws in
    Z.land (Z.ones ws) $
      (Z.lor (Z.shiftr x sa) (Z.shiftl x (ws - sa))).

Definition rotate_right_usize x n := Zrotate_right (int_bitwidth usize_t) x n.

(* FIXME: corner cases to fix *)
(*Compute Zrotate_right 1 1 (-1). [> must be 1 <]*)
(*Compute Zrotate_right 1 1 (1). [> must be 1 <]*)
(*Compute Zrotate_right 2 1 1. [> ? <]*)

Definition rotate_itP (ws x n m: Z) : bool := 
  orb (negb (bool_decide (0 ≤  x < 2^ws)%Z)) $
  bool_decide (orb (negb $ Z.testbit x m)
    (Z.testbit (Zrotate_right ws x n) ((m - n + ws) `mod` ws))).
Compute N.ldiff 7 2.
Compute Z.land (2^64) (-1).

QuickChick (rotate_itP (int_bitwidth usize_t)).
Example rotr_rot :
  rotate_right_usize 1 (1) = (1 ≪  (int_bitwidth usize_t - 1)) := ltac:(reflexivity).
Example rotr_sa_neg :
  rotate_right_usize 1 (-(int_bitwidth usize_t - 1)) = (1 ≪  (int_bitwidth usize_t - 1)) := ltac:(reflexivity).

(* TODO: Leave proving this for general int for future work *)
(* similar formalization? stdpp.numbers.rotate_nat_add *)
(* `m` is 0-indexed bit position *)
Definition Zrotate_right_spec := fun ws => forall x n m,
  0 < ws ->
  0 ≤  x < 2^ws ->
  0 ≤ m < ws ->
  Z.testbit x m = Z.testbit (Zrotate_right ws x n) ((m - n + ws) `mod` ws).

(*Lemma Zrotate_right_spec_succ := fun ws => forall x n m,*)
  (*0 < ws ->*)
  (*0 ≤  x < 2^ws-1 ->*)
  (*0 ≤ m < ws ->*)
  (*Z.testbit x m = Z.testbit (Zrotate_right ws x n) ((m - n + ws) `mod` ws).*)

Check forall a b, 0 ≤ a < b -> a `mod` b = a.
Search (0 ≤ _ < _ -> _ `mod` _ = _).

Definition Zrotate_right_in_range (ws: Z) := forall (x n: Z),
  0 ≤ x < 2^ws -> 0 ≤  Zrotate_right ws x n < 2^ws.

Lemma Zrotate_right_in_range_usize: Zrotate_right_in_range (int_bitwidth usize_t).
Proof.
  unfold Zrotate_right_in_range.
  intros x n H.
  unfold Zrotate_right.
  rewrite Z.land_comm Z.land_ones; [lia |done].
Qed.

Check Z.lor_spec.

Definition lor_nbits (ws: Z) := forall x y,
  0 ≤ x < 2^ws -> 0 ≤ y < 2^ws -> Z.lor x y = (Z.lor x y) `mod` 2^ws.

Lemma lor_nbits_usize: lor_nbits (int_bitwidth usize_t).
Proof.
  intros x y Hx Hy.
  rewrite <- Z.land_ones; [..| done].
  rewrite Z.land_lor_distr_l !Z.land_ones; [..|done|done].
  rewrite !Z.mod_small;[reflexivity|assumption|assumption].
Qed.

  (*symmetry.*)
  (*apply (Z.mod_small (Z.lor x y) (2^int_bitwidth usize_t)).*)
  (*split.*)
  (*- rewrite Z.lor_nonneg; lia.*)
  (*-*)
    (*[>Check Z.log2_le_mono (Z.lor x y) (2^int_bitwidth usize_t).<]*)
    (*Search Z.lor. Search (_ < _ -> _ _< _ _).  *)

Lemma Zrotate_right_usize_spec: Zrotate_right_spec (int_bitwidth usize_t).
Proof.
  unfold Zrotate_right_spec.
  intros x n m Hws_pos Hx_ran Hm_ws.
  unfold Zrotate_right.
  rewrite Z.land_comm.
  (*rewrite Z.land_ones.*)
  rewrite Z.land_lor_distr_l !Z.land_ones; [..|done|done].
  rewrite (
    Z.lor_spec
      ((x ≫ (n `mod` int_bitwidth usize_t)) `mod` 2 ^ int_bitwidth usize_t)
      ((x ≪ (int_bitwidth usize_t - n `mod` int_bitwidth usize_t))
        `mod` 2 ^ int_bitwidth usize_t)
    )
  .
  (*-*)
  (*generalize dependent x.*)
    (*[>assert (Hws_is: int_bitwidth usize_t = 64). { reflexivity. }<]*)
    (*[>rewrite Hws_is.<]*)
    (*Search Z.lor.*)
    (*induction x using (Z.succ_pred_induction 0); intros Hx_ran; [..|lia].*)
    (*[> NOTE: ref. theories/Numbers/Abstract/ZBits.v <]*)
    (*Search Z.testbit.*)
    (*+ rewrite Z.land_ones; [..|lia].*)
      (*rewrite Z.shiftr_0_l Z.lor_0_l Z.shiftl_0_l Zmod_0_l !Z.bits_0.*)
      (*reflexivity.*)
    (*+ Check Z.mod_add.*)
      (*Check Z.bits_inj. Check Z.mul_pow2_bits.*)
      (*Search (Z.testbit (Z.lor _ _) _).*)
      (*[>Search Z.land<]*)
      (*Search Z.modulo.*)
      (*Check Z.lor_spec (Z.succ x ≫ (n `mod` 64)) (Z.succ x ≪ (64 - n `mod` 64)) m.*)
      (*(* NOTE: JUST USE [Z.land_lor_distr_l]:*)
         (*~~we cannot eliminate the mask/`mod` out of [Z.lor] here*)
         (*we have to specialize [Z.lor_spec] for fixed-bitwidth~~*)
      (**)*)
      (*[>Check Z.shiftl_spec (Z.succ x ≫ (n `mod` int_bitwidth usize_t))<]*)
      (*[>(Z.succ x ≪ (int_bitwidth usize_t - n `mod` int_bitwidth usize_t)).<]*)
      (*rewrite Z.land_lor_distr_l !Z.land_ones.*)

  (** rewrite (Z.lor_spec*)
        (*((Z.succ x ≫ (n `mod` int_bitwidth usize_t)) `mod` 2 ^ int_bitwidth usize_t)*)
        (*((Z.succ x ≪ (int_bitwidth usize_t - n `mod` int_bitwidth usize_t)) `mod` 2 ^ int_bitwidth usize_t)*)
        (*)*)
      (*.*)
Admitted.


Search Z.testbit.
  - done.
  Search Z.ones.
  Check Z.land_ones.
  Check Z.ones_mod_pow2 _ (int_bitwidth usize_t).
  Check Z.testbit_neg_r.
Admitted.
(*Compute Zrotate_right 8 1 1.*)
Compute Z.shiftl 1 3.
Check Z.to_nat.
(*Function msb_enabled (n: Z) {measure Z.to_nat} : Z :=*)
  (*if decide (n ≤ 0) then 0 else 1+(msb_enabled (Z.shiftr n 1)).*)
(*Proof.*)
  (*intros. rewrite Z.shiftr_div_pow2; lia.*)
(*Defined.*)

Lemma Zinduction: forall  (P: Z -> Prop),
  P 0 ->
  (forall i, 0 < i -> P (i-1) -> P i) ->
  forall n, 0 <= n -> P n.
Proof.
intros.
rewrite <- (Z2Nat.id n) in * by lia.
set (j := Z.to_nat n) in *. clearbody j.
induction j.
- simpl. apply H.
- apply (H0 (Z.of_nat (S j))).
  + rewrite inj_S. unfold Z.succ. lia.
  + rewrite inj_S. unfold Z.succ. rewrite Z.add_simpl_r.
    apply IHj. lia.
Qed.

(*Lemma ZinductionSucc: forall  (P: Z -> Prop),*)
  (*P 0 ->*)
  (*(forall i, 0 < i -> P i -> P (i + 1)) ->*)
  (*forall n, 0 <= n -> P n.*)
(*Proof.*)
(*intros.*)
(*rewrite <- (Z2Nat.id n) in * by lia.*)
(*set (j := Z.to_nat n) in *. clearbody j.*)
(*induction j.*)
(*- simpl. apply H.*)
(*- apply (H0 (S $ Z.of_nat j)).*)
  (*+ rewrite inj_S. unfold Z.succ. lia.*)
  (*+ rewrite inj_S. unfold Z.succ. rewrite Z.add_simpl_r.*)
    (*apply IHj. lia.*)
(*Qed.*)


Compute Z.testbit 4 3.
 Print positive.
 Check (xI xH).
Print Pos.size.

(* Searching for enabled bit bitween [msb_idx, 0] bits.
 * Returns 1-indexed position from LSB for the highest bit which is 1.
 * Returns 0 for input 0b0.
 * i.e. clz b = bitwidth - msb_enabled bitwidth b
 *
 * Example 1:
     n = 0b00010000
     msb_enabled 8 n = 5
*)
Fixpoint msb_enabled (msb_idx: nat) (n: Z) : Z :=
  match msb_idx with
  | O => if Z.testbit n 0 then 1 else 0
  | S x => if Z.testbit n msb_idx
           then msb_idx + 1 (* convert to 1-indexed result *)
           else msb_enabled x n
  end.


Lemma msb_enabled_0: forall idx, msb_enabled idx 0 = 0.
Proof.
  intros.
  induction idx.
  - reflexivity.
  - unfold msb_enabled.
    rewrite Z.bits_0.
    fold msb_enabled.
    assumption.
Qed.

Definition count_leading_zeros (it: int_type) (i: Z) :=
  bits_per_int it - msb_enabled (Z.to_nat $ bits_per_int it - 1) i.

Compute msb_enabled 63 4.

Definition msb_enabled_64bitP (n: Z) :=
  orb (negb (bool_decide (0 < n)%Z)) $
  bool_decide (0 ≤  msb_enabled 63 n < 64).

QuickChick msb_enabled_64bitP.

Definition clz_itP (n m: Z) : bool := 
  orb (negb (bool_decide (0 < n < 2^m)%Z)) $
  bool_decide (Z.log2 n = msb_enabled (Z.to_nat m) n - 1).

QuickChick clz_itP.

Search "Odd".
(* TODO *)
Lemma msb_enabled_log2_nbits_odd: forall m ws,
  0 < ws ->
  0 < m < 2^ws ->
  Z.log2 m = msb_enabled (Z.to_nat (ws - 1)) m - 1.
Proof.
  intros m ws Hws.
  pattern m ; apply Zinduction ; intros.
  - inversion H. inversion H0.
  - destruct (Z.Even_or_Odd i).
    + admit.
    Search (Z.log2 (_ + _)).
    Search Nat.Odd_Even_ind.
    + Search Z.Odd. unfold Z.Odd in H2. Check Z.log2_succ_double.

Abort.

(* TODO *)
Lemma count_leading_zeros_spec: forall it m,
  it_signed it = false -> m∈  it
  (* to avoid log2 0 = -1 *)
   -> 0 < m
   -> Z.log2 m = (bits_per_int it) - count_leading_zeros it m - 1.
Proof.
  intros it m Hsigned Hit_range.
  unfold count_leading_zeros.
  pattern m ; apply Zinduction ; intros ; ring_simplify.
  - inversion H.
  - 
Abort.
