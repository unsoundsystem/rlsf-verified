From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex generated_specs_rr_ex generated_template_silly_deref.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma silly_deref_proof (π : thread_id) :
  silly_deref_lemma π.
Proof.
  (*silly_deref_prelude.*)
  unfold silly_deref_lemma;
  set (FN_NAME := FUNCTION_NAME "silly_deref");
  intros;
  iStartProof;
  start_function "silly_deref" ( [] ) ( [] ) ( [ [  l vs ] z ] );
  set (loop_map := BB_INV_MAP (PolyNil)).
  (* TODO: is this x really related to l that we specified in the annotation?*)
  intros arg_x;
  prepare_parameters ( l vs z );
  init_lfts (∅ );
  init_tyvars ( ∅ ).

  About typed_place.
  repeat liRStep; liShow.
  Check arg_x.
  Search typed_place.
  Check typed_place.
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
