Require Import ZArith.
From stdpp Require Import numbers.

Parameter loc : Type.

Record block := Block {
  start : loc;
  size : positive;
}.

Record tlsf := Tlsf {
  allocated_block : list block;
  free_blocks : list (list block);
}.

Section index.
  Parameter FLLEN SLLEN : positive.
  Open Scope Z.
  Definition block_index := (Z * Z)%type.

  Definition size_of_flb (i : Z) := 2^i `div` 2^(Z.pos SLLEN).
  Definition block_size_range x: Z -> Prop :=
    let '(i, j) := x in
    fun b =>
      2^i + size_of_flb i * j ≤  b
      < 2^i + size_of_flb i * (j + 1)
      .
 
  Definition block_index_gt (x y: block_index) : Prop := 
    let '(i, j) := x in
    let '(k, l) := y in
    i > k \/ (i = k /\ j > l)
  .

  Definition block_index_suc (x: block_index) : block_index :=
    let '(i, j) := x in
    if decide (j + 1 < (Z.pos SLLEN)) then (i, j + 1) else (i + 1, 0).

  Lemma block_size_range_not_overwrap: forall x y,
    block_index_gt x y
    -> forall z, ~(block_size_range x z /\ block_size_range y z).
  Proof. Admitted.
End index.
