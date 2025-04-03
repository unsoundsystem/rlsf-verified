From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex generated_specs_rr_ex generated_template_utils_examples_wrap_sub_max.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma utils_examples_wrap_sub_max_proof (π : thread_id) :
  utils_examples_wrap_sub_max_lemma π.
Proof.
  utils_examples_wrap_sub_max_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
