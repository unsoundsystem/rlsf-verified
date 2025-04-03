From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex generated_specs_rr_ex generated_template_silly.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma silly_proof (π : thread_id) :
  silly_lemma π.
Proof.
  silly_prelude.

  repeat liRStep; liShow.
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
  (*Compute type Silly_inv_t_rt.*)
Qed.
End proof.
