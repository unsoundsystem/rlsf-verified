From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex generated_specs_rr_ex generated_template_mutate_struct.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma mutate_struct_proof (π : thread_id) :
  mutate_struct_lemma π.
Proof.
  mutate_struct_prelude.

  (*unfold mutate_struct_lemma;*)
  (*set (FN_NAME := FUNCTION_NAME "mutate_struct");*)
  (*intros;*)
  (*iStartProof.*)

  (*Print mutate_struct_lemma.*)
  (*start_function "mutate_struct" ( [] ) ( [] ) ( [  l fbh ] );*)
  (*set (loop_map := BB_INV_MAP (PolyNil));*)
  (*intros arg_x local___0 local___2;*)
  (*prepare_parameters ( l fbh );*)
  (*init_lfts (∅ );*)
  (*init_tyvars ( ∅ ).*)

  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.
  liRStep.


  repeat liRStep; liShow.
  (*About trigger_tc.*)
  (*unfold trigger_tc.*)
  About uninit.
  Check interpret_rust_type_goal.
  Print rust_type.
  Print typed_stmt.
  About typed_write.
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
