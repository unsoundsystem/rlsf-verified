From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.rr_ex.generated Require Import generated_code_rr_ex generated_specs_rr_ex generated_template_utils_examples_map_floor.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma utils_examples_map_floor_proof (π : thread_id) :
  utils_examples_map_floor_lemma π.
Proof.
  Print utils_examples_map_floor_lemma.

  unfold utils_examples_map_floor_lemma.
  (* Copied from the template tactic *)
  set (FN_NAME := FUNCTION_NAME "utils_examples_map_floor");
  intros;
  iStartProof;
  start_function "utils_examples_map_floor" ( [] ) ( [] ) ( ? );
  set (loop_map := BB_INV_MAP (PolyNil)).
  (* FIXME: Fails to intro *)
  intros arg_size local___0 local___2 local___3 local___4 local___5 local___6 local___7 local___8 local___9 local___10 local___11 local___12 local___13 local___14 local___15 local_fl local___17 local___18 local___19 local___20 local___21 local___22 local___23 local_sl local___25 local___26.
  prepare_parameters ( );
  init_lfts (∅ );
  init_tyvars ( ∅ ).
  (*utils_examples_map_floor_prelude.*)
  (* Copied from the template tactic *)

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
  Abort.
End proof.
