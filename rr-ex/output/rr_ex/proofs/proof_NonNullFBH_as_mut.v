From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex generated_specs_rr_ex generated_template_NonNullFBH_as_mut.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma NonNullFBH_as_mut_proof (π : thread_id) :
  NonNullFBH_as_mut_lemma π.
Proof.
  NonNullFBH_as_mut_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
