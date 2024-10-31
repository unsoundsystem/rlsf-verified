Require Import ZArith.
From stdpp Require Import base numbers finite decidable gmap list.
From refinedrust Require Import typing shims.
From QuickChick Require Import QuickChick.
Require Import Psatz. 

Section abstract_spec.

Open Scope Z.
(** NOTE: We don't think about 2^0 granularity allocation
   [GRANULARITY_LOG2] corresponds to `GRANULARITY_LOG2` in rlsf codebase.
 *)
Variable FLLEN SLLEN GRANULARITY_LOG2: Z.
Hypothesis FLLEN_pos: FLLEN > 0.
Hypothesis SLLEN_pos: SLLEN > 0.
Hypothesis GRANULARITY_LOG2_pos: GRANULARITY_LOG2 > 0.
Hypothesis valid_freelist_size: FLLEN > GRANULARITY_LOG2.


(** * Formalization of index calculation in TLSF
 *)
Section index.
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


  (* NOTE: SLLEN is not SLI!!! SLLEN = 2^SLI *)
  Definition size_of_slb (i : Z) := 2^i `div` SLLEN.

  (** Calculating the size range of block allowed for given freelist index
      - will be used in spec of `Tlsf::map_floor` / `Tlsf::map_ceil`
   *)
  Definition block_size_range x blk_sz :=
    let '(i, j) := x in
      2^i + size_of_slb i * j ≤  blk_sz < 2^i + size_of_slb i * (j + 1)
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

  Lemma silly: forall x y x' y' z,
    y < x' ->
   ¬( x ≤ z < y ∧ x' ≤ z <y').
  Proof.
    intros x y x' y' z Hyx'.
    unfold not. intros [[Hxz Hzy] [Hx'z Hzy']]. nia.
  Qed.
  Lemma fl_range_not_overwrap: forall x y,
    block_index_valid x
    -> block_index_valid y
    -> x.1 > y.1
    -> forall z: Z, ¬(block_size_range x z ∧  block_size_range y z).
  Proof.
    intros (i, j) (k, l) [Hvalid_x Hvalid_x'] [Hvalid_y Hvalid_y'] Hik z.
    simpl in Hik.
    unfold block_size_range, size_of_slb, not.
    assert (2 ^ i + 2 ^ i `div` SLLEN * (j + 1)
      < 2 ^ k + 2 ^ k `div` SLLEN * l). {
        (* TODO *)
        admit.
    }
    intros [[? ?] [? ?]]. 
    nia.

    Admitted.

  (** This states all free block managed by TSLF allocator
      falls into exactly one free list. (`self.first_free[fl][sl]` in rlsf)
  *)
  Lemma block_size_range_not_overwrap: forall x y, block_index_valid x -> block_index_valid y
    -> block_index_gt x y
    -> forall z,
      2^GRANULARITY_LOG2 ≤  z ->
      ~(block_size_range x z /\ block_size_range y z).
  Proof.
    intros (i, j) (k, l) Hvalid_x Hvalid_y H z Hz.
    unfold block_size_range, size_of_slb.
    destruct Hvalid_x as [Hx_fl Hx_sl].
    destruct Hvalid_y as [Hy_fl Hy_sl].
    destruct H as [Higtk | [Hieqk Hjgtl]].
    (* First Level Index is different i > k *)
    -
      Search (_≤ _ -> _ - _ ≤  _ - _ ). 
      Search (_^_ `div` _^_).
      Check Z.sub_le_mono.
      Check Z.sub_lt_mono.
      (*rewrite <- (Z.pow_sub_r 2 i SLLEN).*)
      admit.
    (* Second Level Index is different *)
    -
  Admitted.
End index.

(** * System state *)
Section system_state.

  (** Representation of block
     - loc is RefinedRust a construct
     - [block] doesn't directly correspoinds to `BlockHdr`
        `BlockHdr` embedded at the start of the managed region,
        thus [start] is the pointer to that header and [size] is
        the field [BlockHdr::size] of the header.
   *)
  Record block := Block {
    start : loc;
    size : positive;
  }.

  Global Instance block_eq_dec: EqDecision block.
  Proof. solve_decision. Qed.

  Check prov_countable.(encode).
  Check prov_countable.(decode).

  Check prod_countable (A:=prov) (B:=Z).
  Global Instance loc_countable: Countable loc := prod_countable (A:=prov) (B:=Z).

  Global Instance block_countable: Countable block.
  Proof.
    refine (inj_countable' (λ b, (start b, size b))
      (λ b, Block b.1 b.2)
      _
    ).
    intros [].
    reflexivity.
  Qed.

  Record tlsf := Tlsf {
    allocated_block : list block;
    free_blocks : list (list block);
  }.
  Definition end_addr b: loc := (start b) +ₗ (Z.pos $ size b).

  (** * Abstract freelist
     correspinds to `self.first_free` in rlsf.

     - here developing lemmas about operations on this list.
     - lemmas proved here will used in the annotations on rlsf and proofs under `./output/proofs`.
   *)
  (* TODO: Lookup instance to ease access? e.g. m !! (fl, sl) *)
  (* TODO: conversion between idealistic block_matrix & block_matrix use for refinement?
     e.g. without place_rfn
   *)
  Definition block_matrix :=  list $ place_rfn $ list $ place_rfn (option (place_rfn loc)).
  (*Definition block_matrix :=  list $ list $ option (place_rfn loc).*)
  Print place_rfn.

  Definition f := 
    fun (idx: (Z * Z)%type) (m: block_matrix) =>
      x ←  m !! Z.to_nat idx.1;
      x' ←  (match x with PlaceIn xs => Some xs | _ => None end);
      y ←  x' !! Z.to_nat idx.2;
      y' ←  (match y with PlaceIn xs => Some xs | _ => None end);

      y'.
  Check f.
      (*y ←  x' !! Z.to_nat idx.2;*)
      (*y' ←  (match y with PlaceIn xs => Some xs | _ => None end);*)
      (*y : option (place_rfn loc) .*)

  Check NULL_loc.
  Check PlaceIn NULL_loc.
  (*Compute f (0,0) [[ Some (PlaceIn NULL_loc) ]; [None;None]; []].*)
  (*Check list $ place_rfn $ list $ place_rfn (option (place_rfn loc));*)

  (** This lookup instance allows access to [block_matrix] with [block_index].
     The implemetation doesn't distinguish between out of bounds aceess and
     access to empty list.
     The client must ensure the validity of the [block_index] to identify empty freeslist.
   *)
  Global Instance block_matrix_lookup :
    Lookup (Z * Z)%type (place_rfn loc) block_matrix :=
    fix f (idx: (Z * Z)%type) (m: block_matrix)
      : option (place_rfn loc) := let _ : Lookup _ _ _ := @f  in
      x ←  m !! Z.to_nat idx.1;
      x' ←  (match x with PlaceIn xs => Some xs | _ => None end);
      y ←  x' !! Z.to_nat idx.2;
      y' ←  (match y with PlaceIn xs => Some xs | _ => None end);

      y' : option (place_rfn loc).

  Example silly_ac : option (place_rfn loc) :=
    let m : block_matrix := [PlaceIn [ PlaceIn $ Some (PlaceIn NULL_loc) ]; PlaceIn [PlaceIn $ None;PlaceIn $ None]; PlaceIn []] in
      m !! (0, 0).
  Compute silly_ac.

  (** Consistency bitween bitmaps and freelist
     - [fl_bitmap]/[sl_bitmap] are correspind to the same names in rlsf.
        - `fl_bitmap`/`sl_bitmap` in rlsf will refined by same types.
     - leaving this as function due to the convinience for positioning quantifiers.
  *)
  Definition block_matrix_inv (m: block_matrix) (fl_bitmap: Z) (sl_bitmap: list Z) :=
    λ (fl_idx sl_idx: Z) fb,
      block_index_valid (fl_idx, sl_idx) ->
      m !! (fl_idx, sl_idx) = Some fb
      ↔  exists slb, Z.testbit fl_bitmap fl_idx = true ∧
          sl_bitmap !! (Z.to_nat fl_idx) = Some slb
          ∧ Z.testbit slb sl_idx
  .

  Context `{refinedrustGS Σ}. 

  Check (_ ↦ _)%I. 
  Check val_to_bytes.
  Check _ `has_layout_val` _.
  Check struct_t.
  About type.
  Check mem_cast_compat_loc.
  About _ty_has_op_type.
  (*Check (λ l node np, l ↦ node )%I.*)
  (* list rep possibly ...

    l ↦ v * v @ struct_t ... field ...
       * l' ↦ v' * to_val_or_somthing l' @ field
  *)

End system_state.

End abstract_spec.

QuickChick (block_size_range_not_overwrapP 8 4).
