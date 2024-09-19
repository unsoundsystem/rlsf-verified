From refinedrust Require Import typing.

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
