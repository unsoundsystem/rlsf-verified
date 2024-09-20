From refinedrust Require Import typing.
Require Import FunInd Recdef.

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
Definition Zrotate_right ws x n := Z.lor (Z.shiftr x n) (Z.shiftl x (ws - n)).
Definition rotate_right_usize x n := Zrotate_right (int_bitwidth usize_t) x n.
(*Compute Zrotate_right 8 1 1.*)
Compute Z.shiftl 1 3.
Check Z.to_nat.
Function msb_enabled (n: Z) {measure Z.to_nat} : Z :=
  if decide (n ≤ 0) then 0 else 1+(msb_enabled (Z.shiftr n 1)).
Proof.
  intros. rewrite Z.shiftr_div_pow2; lia.
Defined.

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

Compute Z.testbit 4 3.
(* returns index of most significant bits which is 1 (1-indexed)*)
(* msb_idx is 0-indexed msb posision e.g. 63 when using fo 64 bits *)
Function msb_enabled2 (msb_idx: Z) (n: Z) {measure Z.to_nat msb_idx} : Z :=
  if Z.testbit n msb_idx then 1+msb_idx else
  if decide (msb_idx ≤ 0) then 0 else msb_enabled2 (msb_idx-1) n.
Proof.
  intros. lia.
Defined.

Lemma msb_enabled2_0: forall idx, 0 ≤ idx -> msb_enabled2 idx 0 = 0.
Proof.
  intros.
  pattern idx; apply Zinduction.
  - reflexivity.
  - intros. 
    rewrite msb_enabled2_equation.
    rewrite Z.bits_0. 
    destruct (decide (i ≤ 0)).
    + reflexivity.
    + assumption.
  - assumption.
Qed.

(*Lemma msb_enabled2_spec: forall idx n,*)
  (*0 ≤ n -> 0 ≤ idx -> msb_enabled idx n ->*)
  (*forall m, 0 ≤ m -> idx < m -> Z.testbit n m = false.*)

Definition count_leading_zeros (it: int_type) (i: Z) := bits_per_int it - msb_enabled2 (bits_per_int it-1) i.

Compute msb_enabled2 63 2.
Compute count_leading_zeros usize_t 1.
Compute (count_leading_zeros usize_t (max_int usize_t)).
Compute Z.log2 1.

Lemma count_leading_zeros_spec: forall it m,
  it_signed it = false -> m∈  it
  (* to avoid log2 0 = -1 *)
   -> 0 < m
   -> Z.log2 (m) = (bits_per_int it) - count_leading_zeros it m - 1.
Proof.
  intros it m Hsigned Hit_range.
  unfold count_leading_zeros.
  pattern m ; apply Zinduction ; intros ; ring_simplify.
  - inversion H.
  - Search Z.log2.
  rewrite msb_enabled2_equation.
Abort.
