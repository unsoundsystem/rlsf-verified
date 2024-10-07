Require Import ZArith.
From stdpp Require Import base numbers finite decidable gmap.
From refinedrust Require Import typing.
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

  (** Representation of block
     - loc is RefinedRust a construct
   *)
  Record block := Block {
    start : loc;
    size : positive;
  }.

  (* this assumptions are needed to use gmap/gset
   TODO: Once we decide how to treat about locations
         there be actual instance
   *)
  Context `{Countable block} `{EqDecision block}.

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
    intros.
    simpl.
    destruct x.
    reflexivity.
  Qed.

  Record tlsf := Tlsf {
    allocated_block : list block;
    free_blocks : list (list block);
  }.
  Definition end_addr b: loc := (start b) +ₗ (Z.pos $ size b).

  (** * Abstract freelist
     correspinds to `self.first_free` in rlsf.
   *)
  Definition block_matrix :=  gmap (nat * nat) $ gset block.


  Context `{!refinedrustGS Σ}.

  (** Representation of abstract [block_matrix] in physical memory.
   *)
  Fixpoint free_list_repr (m: block_matrix): iProp Σ.
  Admitted.

End system_state.

QuickChick (block_size_range_not_overwrapP 8 4).
