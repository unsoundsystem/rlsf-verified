#!/bin/bash
set -e

VERUS_PATH=$(realpath $(dirname "$0")/../../verus/source/target-verus/release/verus)
PROJ=$(realpath $(dirname "$0")/..)
VERUS_SINGULAR_PATH=/usr/bin/Singular

funcs=(
    # ========== Main entry points ==========
    "linked_list lib::Tlsf::link_free_block"
    "linked_list lib::Tlsf::unlink_free_block"
    "mapping lib::Tlsf::map_floor"
    "mapping lib::Tlsf::map_ceil"
    "allocate lib::Tlsf::allocate"
    "search_block lib::Tlsf::search_suitable_free_block_list_for_allocation"
    "deallocate lib::Tlsf::deallocate"
    "deallocate lib::Tlsf::deallocate_block"
    "initialize lib::Tlsf::insert_free_block_ptr_aligned"

    # ========== Root module (lib.rs) ==========
    "ROOT Tlsf::lemma_wf_components"
    "ROOT Tlsf::max_pool_size"
    "ROOT Tlsf::lemma_max_pool_size_spec_value"

    # ========== bitmap ==========
    "bitmap lib::Tlsf::set_bit_for_index"
    "bitmap lib::Tlsf::clear_bit_for_sl"

    # ========== linked_list helpers ==========
    "linked_list lib::Tlsf::set_freelist"
    "linked_list lib::Tlsf::freelist_nonempty"
    "linked_list lib::Tlsf::wf_index_in_freelist"
    "linked_list lib::Tlsf::wf_weak_index_in_freelist"
    "linked_list lib::Tlsf::lemma_size_class_at"
    "linked_list lib::Tlsf::lemma_freelist_wf_extract_wf_free_node"
    "linked_list lib::Tlsf::lemma_free_blocks_in_freelist_except_perms_frame"
    "linked_list lib::Tlsf::lemma_wf_free_node_preserve_if_not_touched"
    "linked_list lib::Tlsf::lemma_wf_free_node_preserve_remove_head"
    "linked_list lib::Tlsf::lemma_wf_free_node_head_from_addr_form"
    "linked_list lib::Tlsf::lemma_freelist_len_gt1_from_nonnull_next"
    "linked_list lib::Tlsf::lemma_wf_free_node_next_addr"
    "linked_list lib::Tlsf::lemma_free_block_allblock_contains"
    "linked_list lib::Tlsf::lemma_shadow_list_no_duplicates"
    "linked_list lib::Tlsf::lemma_shadow_list_contains_unique"
    "linked_list lib::Tlsf::lemma_nodup_get"
    "linked_list lib::Tlsf::lemma_ii_push_for_index_ensures"
    "linked_list lib::Tlsf::lemma_ii_remove_for_index_ensures"
    "linked_list lib::Tlsf::lemma_shadow_ptrs_nonnull_frame"
    "linked_list lib::Tlsf::lemma_shadow_ptrs_nonnull_after_push"

    # ========== deallocate helpers ==========
    "deallocate lib::Tlsf::used_block_hdr_for_allocation"

    # ========== all_blocks ==========
    "all_blocks AllBlocks::lemma_block_wf"
    "all_blocks AllBlocks::lemma_node_is_wf"
    "all_blocks AllBlocks::lemma_wf_node_ptr"
    "all_blocks AllBlocks::lemma_wf_node_ptr_from_facts"
    "all_blocks AllBlocks::lemma_wf_free_ptr_hdr_bound"
    "all_blocks AllBlocks::lemma_wf_nodup"
    "all_blocks AllBlocks::lemma_wf_extract_node"
    "all_blocks AllBlocks::lemma_wf_perm_wf"
    "all_blocks AllBlocks::lemma_wf_glue_facts"
    "all_blocks AllBlocks::lemma_wf_structural_facts"
    "all_blocks AllBlocks::lemma_construct_wf_node_glue"
    "all_blocks AllBlocks::lemma_construct_wf_node_structural"
    "all_blocks AllBlocks::lemma_transfer_wf_node"
    "all_blocks AllBlocks::lemma_wf_from_nodes"
    "all_blocks AllBlocks::lemma_pool_size_bounded_transfer"
    "all_blocks AllBlocks::lemma_contains"
    "all_blocks AllBlocks::lemma_phys_next_matches_intro"
    "all_blocks AllBlocks::lemma_phys_next_matches_elim"

    # ========== parameters ==========
    "parameters lib::Tlsf::sli_pow2_is_sllen"
    "parameters lib::Tlsf::granularity_basics"
    "parameters lib::Tlsf::lemma_parameter_validity_implies_block_index_parameter_validity"

    # ========== mapping helpers ==========
    "mapping lib::Tlsf::fl_not_underflow"
    "mapping lib::Tlsf::lemma_floor_index_contains_size"
    "mapping lib::Tlsf::lemma_fl_fllen_le_iff_valid_size"
    "mapping lib::Tlsf::lemma_size_within_max_is_valid_block_size"

    # ========== block_index ==========
    "block_index BlockIndex::lemma_bsr_wf"
    "block_index BlockIndex::lemma_block_size_range_mono"
    "block_index BlockIndex::lemma_block_size_range_start_mono_same_fl"

    # ========== bits ==========
    "bits lemma_pow2_values"
    "bits lemma_log2_values"
    "bits lemma_round_down_pow2"
    "bits lemma_round_up_pow2"
    "bits lemma_usize_rotr_mask_lower"
    "bits lemma_duplicate_low_mask_usize"
    "bits lemma_low_mask_u64_values"
    "bits granularity_is_power_of_two"
    "bits mask_higher_bits_leq_mask"
    "bits log2_using_leading_zeros_usize"
    "bits bit_mask_is_mod_for_pow2"
    "bits lemma_log2_distributes"
    "bits lemma_usize_shr_is_div"
    "bits lemma_pow2_div_sub"

    # ========== utils ==========
    "utils lib::Tlsf::lemma_checked_add_eq"
)

cd $PROJ

run() {
    echo "Checking for regression"
    for item in "${funcs[@]}"; do
        set -- $item
        local module=$1
        local func=$2
        if [ "$module" = "ROOT" ]; then
            echo "=== Verifying $func at root ==="
            VERUS_SINGULAR_PATH=$VERUS_SINGULAR_PATH $VERUS_PATH src/lib.rs \
                --verify-root \
                --verify-function $func \
                --crate-type=lib \
                --expand-errors \
                --multiple-errors=10 \
                --triggers-mode silent \
                --rlimit=1000
        else
            echo "=== Verifying $func at $module ==="
            VERUS_SINGULAR_PATH=$VERUS_SINGULAR_PATH $VERUS_PATH src/lib.rs \
                --verify-only-module $module \
                --verify-function $func \
                --crate-type=lib \
                --expand-errors \
                --multiple-errors=10 \
                --triggers-mode silent \
                --rlimit=1000
        fi
    done
}

run
