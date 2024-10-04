Require Import ZArith.
From stdpp Require Import base numbers finite decidable gmap.
From QuickChick Require Import QuickChick.

(** * Formalization of index calculation in TLSF
 *)
Section index.
  Open Scope Z.
  (** NOTE: We don't think about 2^0 granularity allocation
     [GRANULARITY_LOG2] corresponds to `GRANULARITY_LOG2` in rlsf codebase.
   *)
  Variable FLLEN SLLEN GRANULARITY_LOG2: Z.
  Hypothesis FLLEN_pos: FLLEN > 0.
  Hypothesis SLLEN_pos: SLLEN > 0.
  Hypothesis GRANULARITY_LOG2_pos: GRANULARITY_LOG2 > 0.
  Hypothesis valid_freelist_size: FLLEN > GRANULARITY_LOG2.

  (** * Block index
     Following Zhang et.al., we formalize bitmap index by tuple of positive
     integer (restriction on [Z]).

     This [block_index] has order defined by calculating next bigger index
     as ordinary TLSF algorithm do.
   *)
  Definition block_index := (Z * Z)%type.
  Definition block_index_valid (blk_idx: block_index) :=
    let '(i, j) := blk_idx in
    0 ≤ i < FLLEN /\ 0 ≤ j < SLLEN. 


  Definition size_of_flb (i : Z) := 2^i `div` 2^SLLEN.
  Definition block_size_range x blk_sz :=
    let '(i, j) := x in
      2^i + size_of_flb i * j ≤  blk_sz < 2^i + size_of_flb i * (j + 1)
      .
 
  Definition block_index_gt (x y: block_index) : Prop := 
    let '(i, j) := x in
    let '(k, l) := y in
    i > k \/ (i = k /\ j > l)
  .

  Definition block_index_suc (x: block_index) : block_index :=
    let '(i, j) := x in
    if decide (j + 1 < SLLEN) then (i, j + 1) else (i + 1, 0).

  Definition block_size_range_not_overwrapP x y z :=
    negb (bool_decide (block_index_valid x)
      && bool_decide (block_index_valid y)
      && bool_decide (block_index_gt x y))
      || negb (bool_decide (block_size_range x z)
        && bool_decide (block_size_range y z)).

  (** This states all free block managed by TSLF allocator
      falls into exactly one free list. (`self.first_free[fl][sl]` in rlsf)
  *)
  Lemma block_size_range_not_overwrap: forall x y,
    block_index_valid x
    -> block_index_valid y
    -> block_index_gt x y
    -> forall z, ~(block_size_range x z /\ block_size_range y z).
  Proof.
    intros (i, j) (k, l) Hvalid_x Hvalid_y H z.
    unfold block_size_range, size_of_flb.
    destruct Hvalid_x as [Hx_fl Hx_sl].
    destruct Hvalid_y as [Hy_fl Hy_sl].
    destruct H as [Higtk | [Hieqk Hjgtl]].
    (* First Level Index is different *)
    - admit.
    (* Second Level Index is different *)
    -
  Admitted.
End index.

(** * System state *)
Section system_state.
  (* TODO: consider which we should use there,
           maybe location types used in RefinedRust *)
  Variable loc : Type.
  Variable loc_add: loc -> Z -> loc.

  Record block := Block {
    start : loc;
    size : positive;
  }.

  (* this assumptions are needed to use gmap/gset
   TODO: Once we decide how to treat about locations
         there be actual instance
   *)
  Context `{Countable block} `{EqDecision block}.

  Record tlsf := Tlsf {
    allocated_block : list block;
    free_blocks : list (list block);
  }.
  Definition end_addr b: loc := loc_add (start b) (Z.pos $ size b).

  (** * Abstract freelist
     correspinds to `self.first_free` in rlsf.
    TODO: there would be more sophisticated way using stdpp constructs.
   *)
  Definition block_matrix :=  nat -> nat -> gset block.

End system_state.

QuickChick (block_size_range_not_overwrapP 8 4).
