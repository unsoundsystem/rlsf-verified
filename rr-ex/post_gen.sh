sed -i \
    -e 's/Definition BlockHdr_ty.*/Definition BlockHdr_ty : type (plist place_rfn [Z : Type; option (place_rfn loc) : Type])./' \
    -e 's/Definition FreeBlockHdr_ty.*/Definition FreeBlockHdr_ty : type (plist place_rfn [BlockHdr_inv_t_rt : Type; option (place_rfn loc) : Type; option (place_rfn loc) : Type])./' \
    -e 's/Definition Silly_ty.*/Definition Silly_ty : type (plist place_rfn [loc : Type; Z : Type])./' \
    /home/shinaikakishita/projects/tlsf-verif/tlsf-allocator-verification-progress-report/rr-ex/output/rr_ex/generated/generated_specs_rr_ex.v

