From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rlsf_verif_core.generated Require Import generated_code_rlsf_verif_core generated_specs_rlsf_verif_core generated_template_add_42.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma add_42_proof (π : thread_id) :
  add_42_lemma π.
Proof.
  add_42_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
