From refinedrust Require Import typing.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex.

(** * Axiomization of `ptr_read` *)

Definition ptr_read_ax `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* )];
  f_local_vars := [("tmp", use_layout_alg' T_st)];
  f_code :=
    <["_bb0" :=
      "tmp" <-{use_op_alg' T_st} use{use_op_alg' T_st} (!{PtrOp} "src");
      return (use{use_op_alg' T_st} "tmp")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Definition type_of_ptr_read_ax `{!typeGS Σ} (T_rt : Type) (T_st : syn_type) :=
  fn(∀ () : 0 | ( *[T_ty]) : [(T_rt, T_st)] | (l, r) : (loc * T_rt), (λ ϝ, []);
      l :@: alias_ptr_t; λ π, ∃ vs, 
      (l ◁ₗ[π, Owned false] PlaceIn vs @ (◁ value_t (T_ty.(ty_syn_type))))
  )
    → ∃ vs : val, vs @ value_t (T_ty.(ty_syn_type)); λ π,
      (l ◁ₗ[π, Owned false] PlaceIn vs @ (◁ value_t (T_ty.(ty_syn_type)))) ∗
      vs ◁ᵥ{π} r @ T_ty
.

Lemma ptr_read_ax_typed `{!typeGS Σ} π T_rt T_st T_ly :
  syn_type_has_layout T_st T_ly →
  ⊢ typed_function π [T_rt] (ptr_read_ax T_st) [T_st] (type_of_ptr_read_ax T_rt T_st).
Proof.
Admitted.
