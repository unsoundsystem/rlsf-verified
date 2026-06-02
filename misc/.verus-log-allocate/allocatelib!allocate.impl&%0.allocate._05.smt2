(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun R (Real) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %R (Poly) Real)
(declare-fun %F (Poly) fndef)
(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const REAL Type)
(declare-const CHAR Type)
(declare-const USIZE Type)
(declare-const ISIZE Type)
(declare-const TYPE%tuple%0. Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun FLOAT (Int) Type)
(declare-fun CONST_INT (Int) Type)
(declare-fun CONST_BOOL (Bool) Type)
(declare-sort Dcr 0)
(declare-const $ Dcr)
(declare-const $slice Dcr)
(declare-const $dyn Dcr)
(declare-fun DST (Dcr) Dcr)
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr Type Dcr) Dcr)
(declare-fun RC (Dcr Type Dcr) Dcr)
(declare-fun ARC (Dcr Type Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun CONST_PTR (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun MUTREF (Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)
(declare-const STRSLICE Type)
(declare-const ALLOCATOR_GLOBAL Type)
(declare-fun PTR (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun sized (Dcr) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)
(declare-fun const_bool (Type) Bool)
(declare-fun mut_ref_current% (Poly) Poly)
(declare-fun mut_ref_future% (Poly) Poly)
(declare-fun mut_ref_update_current% (Poly Poly) Poly)
(assert
 (forall ((m Poly) (arg Poly)) (!
   (= (mut_ref_current% (mut_ref_update_current% m arg)) arg)
   :pattern ((mut_ref_update_current% m arg))
   :qid prelude_mut_ref_update_current_current
   :skolemid skolem_prelude_mut_ref_update_current_current
)))
(assert
 (forall ((m Poly) (arg Poly)) (!
   (= (mut_ref_future% (mut_ref_update_current% m arg)) (mut_ref_future% m))
   :pattern ((mut_ref_update_current% m arg))
   :qid prelude_mut_ref_update_current_future
   :skolemid skolem_prelude_mut_ref_update_current_future
)))
(assert
 (forall ((m Poly) (d Dcr) (t Type)) (!
   (=>
    (has_type m (MUTREF d t))
    (has_type (mut_ref_current% m) t)
   )
   :pattern ((has_type m (MUTREF d t)) (mut_ref_current% m))
   :qid prelude_mut_ref_current_has_type
   :skolemid skolem_prelude_mut_ref_current_has_type
)))
(assert
 (forall ((m Poly) (d Dcr) (t Type)) (!
   (=>
    (has_type m (MUTREF d t))
    (has_type (mut_ref_future% m) t)
   )
   :pattern ((has_type m (MUTREF d t)) (mut_ref_future% m))
   :qid prelude_mut_ref_current_has_type
   :skolemid skolem_prelude_mut_ref_current_has_type
)))
(assert
 (forall ((m Poly) (d Dcr) (t Type) (arg Poly)) (!
   (=>
    (and
     (has_type m (MUTREF d t))
     (has_type arg t)
    )
    (has_type (mut_ref_update_current% m arg) (MUTREF d t))
   )
   :pattern ((has_type m (MUTREF d t)) (mut_ref_update_current% m arg))
   :qid prelude_mut_ref_update_has_type
   :skolemid skolem_prelude_mut_ref_update_has_type
)))
(assert
 (forall ((d Dcr)) (!
   (=>
    (sized d)
    (sized (DST d))
   )
   :pattern ((sized (DST d)))
   :qid prelude_sized_decorate_struct_inherit
   :skolemid skolem_prelude_sized_decorate_struct_inherit
)))
(assert
 (forall ((d Dcr)) (!
   (sized (REF d))
   :pattern ((sized (REF d)))
   :qid prelude_sized_decorate_ref
   :skolemid skolem_prelude_sized_decorate_ref
)))
(assert
 (forall ((d Dcr)) (!
   (sized (MUT_REF d))
   :pattern ((sized (MUT_REF d)))
   :qid prelude_sized_decorate_mut_ref
   :skolemid skolem_prelude_sized_decorate_mut_ref
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (BOX d t d2))
   :pattern ((sized (BOX d t d2)))
   :qid prelude_sized_decorate_box
   :skolemid skolem_prelude_sized_decorate_box
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (RC d t d2))
   :pattern ((sized (RC d t d2)))
   :qid prelude_sized_decorate_rc
   :skolemid skolem_prelude_sized_decorate_rc
)))
(assert
 (forall ((d Dcr) (t Type) (d2 Dcr)) (!
   (sized (ARC d t d2))
   :pattern ((sized (ARC d t d2)))
   :qid prelude_sized_decorate_arc
   :skolemid skolem_prelude_sized_decorate_arc
)))
(assert
 (forall ((d Dcr)) (!
   (sized (GHOST d))
   :pattern ((sized (GHOST d)))
   :qid prelude_sized_decorate_ghost
   :skolemid skolem_prelude_sized_decorate_ghost
)))
(assert
 (forall ((d Dcr)) (!
   (sized (TRACKED d))
   :pattern ((sized (TRACKED d)))
   :qid prelude_sized_decorate_tracked
   :skolemid skolem_prelude_sized_decorate_tracked
)))
(assert
 (forall ((d Dcr)) (!
   (sized (NEVER d))
   :pattern ((sized (NEVER d)))
   :qid prelude_sized_decorate_never
   :skolemid skolem_prelude_sized_decorate_never
)))
(assert
 (forall ((d Dcr)) (!
   (sized (CONST_PTR d))
   :pattern ((sized (CONST_PTR d)))
   :qid prelude_sized_decorate_const_ptr
   :skolemid skolem_prelude_sized_decorate_const_ptr
)))
(assert
 (sized $)
)
(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))
(assert
 (forall ((b Bool)) (!
   (= b (const_bool (CONST_BOOL b)))
   :pattern ((CONST_BOOL b))
   :qid prelude_type_id_const_bool
   :skolemid skolem_prelude_type_id_const_bool
)))
(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))
(assert
 (forall ((r Real)) (!
   (has_type (R r) REAL)
   :pattern ((has_type (R r) REAL))
   :qid prelude_has_type_real
   :skolemid skolem_prelude_has_type_real
)))
(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))
(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))
(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))
(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))
(assert
 (forall ((x Real)) (!
   (= x (%R (R x)))
   :pattern ((R x))
   :qid prelude_unbox_box_real
   :skolemid skolem_prelude_unbox_box_real
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x USIZE)
    (= x (I (%I x)))
   )
   :pattern ((has_type x USIZE))
   :qid prelude_box_unbox_usize
   :skolemid skolem_prelude_box_unbox_usize
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ISIZE)
    (= x (I (%I x)))
   )
   :pattern ((has_type x ISIZE))
   :qid prelude_box_unbox_isize
   :skolemid skolem_prelude_box_unbox_isize
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (FLOAT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (FLOAT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (I (%I x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x REAL)
    (= x (R (%R x)))
   )
   :pattern ((has_type x REAL))
   :qid prelude_box_unbox_real
   :skolemid skolem_prelude_box_unbox_real
)))
(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (= SZ 64)
)
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(declare-fun charClip (Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(assert
 (forall ((i Int)) (!
   (and
    (or
     (and
      (<= 0 (charClip i))
      (<= (charClip i) 55295)
     )
     (and
      (<= 57344 (charClip i))
      (<= (charClip i) 1114111)
    ))
    (=>
     (or
      (and
       (<= 0 i)
       (<= i 55295)
      )
      (and
       (<= 57344 i)
       (<= i 1114111)
     ))
     (= i (charClip i))
   ))
   :pattern ((charClip i))
   :qid prelude_char_clip
   :skolemid skolem_prelude_char_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((i Int)) (!
   (= (charInv i) (or
     (and
      (<= 0 i)
      (<= i 55295)
     )
     (and
      (<= 57344 i)
      (<= i 1114111)
   )))
   :pattern ((charInv i))
   :qid prelude_char_inv
   :skolemid skolem_prelude_char_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((x Int)) (!
   (=>
    (uInv SZ x)
    (has_type (I x) USIZE)
   )
   :pattern ((has_type (I x) USIZE))
   :qid prelude_has_type_usize
   :skolemid skolem_prelude_has_type_usize
)))
(assert
 (forall ((x Int)) (!
   (=>
    (iInv SZ x)
    (has_type (I x) ISIZE)
   )
   :pattern ((has_type (I x) ISIZE))
   :qid prelude_has_type_isize
   :skolemid skolem_prelude_has_type_isize
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (FLOAT bits))
   )
   :pattern ((has_type (I x) (FLOAT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Int)) (!
   (=>
    (charInv x)
    (has_type (I x) CHAR)
   )
   :pattern ((has_type (I x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x USIZE)
    (uInv SZ (%I x))
   )
   :pattern ((has_type x USIZE))
   :qid prelude_unbox_usize
   :skolemid skolem_prelude_unbox_usize
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x ISIZE)
    (iInv SZ (%I x))
   )
   :pattern ((has_type x ISIZE))
   :qid prelude_unbox_isize
   :skolemid skolem_prelude_unbox_isize
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (FLOAT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (FLOAT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(declare-fun RAdd (Real Real) Real)
(declare-fun RSub (Real Real) Real)
(declare-fun RMul (Real Real) Real)
(declare-fun RDiv (Real Real) Real)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Real) (y Real)) (!
   (= (RAdd x y) (+ x y))
   :pattern ((RAdd x y))
   :qid prelude_radd
   :skolemid skolem_prelude_radd
)))
(assert
 (forall ((x Real) (y Real)) (!
   (= (RSub x y) (- x y))
   :pattern ((RSub x y))
   :qid prelude_rsub
   :skolemid skolem_prelude_rsub
)))
(assert
 (forall ((x Real) (y Real)) (!
   (= (RMul x y) (* x y))
   :pattern ((RMul x y))
   :qid prelude_rmul
   :skolemid skolem_prelude_rmul
)))
(assert
 (forall ((x Real) (y Real)) (!
   (= (RDiv x y) (/ x y))
   :pattern ((RDiv x y))
   :qid prelude_rdiv
   :skolemid skolem_prelude_rdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
   :skolemid skolem_prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
   :skolemid skolem_prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
   :skolemid skolem_prelude_mod_unsigned_in_bounds
)))
(declare-fun bitxor (Poly Poly) Int)
(declare-fun bitand (Poly Poly) Int)
(declare-fun bitor (Poly Poly) Int)
(declare-fun bitshr (Poly Poly) Int)
(declare-fun bitshl (Poly Poly) Int)
(declare-fun bitnot (Poly) Int)
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitxor x y))
   )
   :pattern ((uClip bits (bitxor x y)))
   :qid prelude_bit_xor_u_inv
   :skolemid skolem_prelude_bit_xor_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitxor x y))
   )
   :pattern ((iClip bits (bitxor x y)))
   :qid prelude_bit_xor_i_inv
   :skolemid skolem_prelude_bit_xor_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitor x y))
   )
   :pattern ((uClip bits (bitor x y)))
   :qid prelude_bit_or_u_inv
   :skolemid skolem_prelude_bit_or_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitor x y))
   )
   :pattern ((iClip bits (bitor x y)))
   :qid prelude_bit_or_i_inv
   :skolemid skolem_prelude_bit_or_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitand x y))
   )
   :pattern ((uClip bits (bitand x y)))
   :qid prelude_bit_and_u_inv
   :skolemid skolem_prelude_bit_and_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitand x y))
   )
   :pattern ((iClip bits (bitand x y)))
   :qid prelude_bit_and_i_inv
   :skolemid skolem_prelude_bit_and_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (<= 0 (%I y))
    )
    (uInv bits (bitshr x y))
   )
   :pattern ((uClip bits (bitshr x y)))
   :qid prelude_bit_shr_u_inv
   :skolemid skolem_prelude_bit_shr_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (<= 0 (%I y))
    )
    (iInv bits (bitshr x y))
   )
   :pattern ((iClip bits (bitshr x y)))
   :qid prelude_bit_shr_i_inv
   :skolemid skolem_prelude_bit_shr_i_inv
)))
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun has_resolved (Dcr Type Poly) Bool)
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun default_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))

;; MODULE 'module allocate'
;; src/allocate.rs:525:25: 525:31 (#0)

;; query spun off because: bitvector

;; Fuel
(declare-const fuel%vstd!std_specs.num.usize_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.usize_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.
 FuelId
)
(declare-const fuel%vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.
 FuelId
)
(declare-const fuel%vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.
 FuelId
)
(declare-const fuel%vstd!std_specs.num.isize_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.isize_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u128_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u128_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i128_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i128_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u64_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u64_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i64_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i64_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u32_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u32_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i32_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i32_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u16_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u16_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i16_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i16_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u8_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.u8_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i8_specs.impl&%0.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.num.i8_specs.impl&%0.eq_spec. FuelId)
(declare-const fuel%vstd!arithmetic.div_mod.lemma_basic_div. FuelId)
(declare-const fuel%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. FuelId)
(declare-const fuel%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. FuelId)
(declare-const fuel%vstd!arithmetic.div_mod.lemma_mod_equivalence. FuelId)
(declare-const fuel%vstd!arithmetic.power2.pow2. FuelId)
(declare-const fuel%vstd!std_specs.bits.u64_trailing_zeros. FuelId)
(declare-const fuel%vstd!std_specs.bits.axiom_u64_trailing_zeros. FuelId)
(declare-const fuel%vstd!std_specs.cmp.impl&%2.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.cmp.impl&%2.eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.option.impl&%0.is_Some. FuelId)
(declare-const fuel%vstd!std_specs.option.impl&%0.arrow_0. FuelId)
(declare-const fuel%vstd!std_specs.option.is_none. FuelId)
(declare-const fuel%vstd!std_specs.option.spec_unwrap. FuelId)
(declare-const fuel%vstd!std_specs.option.impl&%1.obeys_eq_spec. FuelId)
(declare-const fuel%vstd!std_specs.option.impl&%1.eq_spec. FuelId)
(declare-const fuel%vstd!raw_ptr.ptr_mut_specs.spec_addr. FuelId)
(declare-const fuel%vstd!array.array_view. FuelId)
(declare-const fuel%vstd!array.impl&%0.view. FuelId)
(declare-const fuel%vstd!array.impl&%2.spec_index. FuelId)
(declare-const fuel%vstd!array.lemma_array_index. FuelId)
(declare-const fuel%vstd!array.array_len_matches_n. FuelId)
(declare-const fuel%vstd!array.axiom_array_ext_equal. FuelId)
(declare-const fuel%vstd!array.axiom_array_has_resolved. FuelId)
(declare-const fuel%vstd!layout.valid_layout. FuelId)
(declare-const fuel%vstd!layout.size_of_as_usize. FuelId)
(declare-const fuel%vstd!layout.layout_of_primitives. FuelId)
(declare-const fuel%vstd!layout.layout_of_unit_tuple. FuelId)
(declare-const fuel%vstd!layout.layout_of_references_and_pointers. FuelId)
(declare-const fuel%vstd!layout.layout_of_references_and_pointers_for_sized_types.
 FuelId
)
(declare-const fuel%vstd!layout.layout_of_references_and_pointers_for_unsized_types.
 FuelId
)
(declare-const fuel%vstd!layout.align_properties. FuelId)
(declare-const fuel%vstd!layout.align_nonzero. FuelId)
(declare-const fuel%vstd!map.impl&%0.new. FuelId)
(declare-const fuel%vstd!map.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!map.axiom_map_index_decreases_finite. FuelId)
(declare-const fuel%vstd!map.axiom_map_index_decreases_infinite. FuelId)
(declare-const fuel%vstd!map.axiom_map_insert_domain. FuelId)
(declare-const fuel%vstd!map.axiom_map_insert_same. FuelId)
(declare-const fuel%vstd!map.axiom_map_insert_different. FuelId)
(declare-const fuel%vstd!map.axiom_map_remove_domain. FuelId)
(declare-const fuel%vstd!map.axiom_map_remove_different. FuelId)
(declare-const fuel%vstd!map.axiom_map_ext_equal. FuelId)
(declare-const fuel%vstd!map.axiom_map_ext_equal_deep. FuelId)
(declare-const fuel%vstd!map_lib.impl&%0.contains_key. FuelId)
(declare-const fuel%vstd!map_lib.impl&%0.map_entries. FuelId)
(declare-const fuel%vstd!map_lib.impl&%0.map_values. FuelId)
(declare-const fuel%vstd!map_lib.impl&%0.is_injective. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%1.arrow_0. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%3.view. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%5.ptr. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%5.opt_value. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%5.is_init. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%5.is_uninit. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%5.value. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%6.is_init. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%6.is_uninit. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%6.value. FuelId)
(declare-const fuel%vstd!raw_ptr.axiom_ptr_mut_from_data. FuelId)
(declare-const fuel%vstd!raw_ptr.ptrs_mut_eq. FuelId)
(declare-const fuel%vstd!raw_ptr.ptrs_mut_eq_sized. FuelId)
(declare-const fuel%vstd!raw_ptr.spec_cast_ptr_to_usize. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%9.view. FuelId)
(declare-const fuel%vstd!raw_ptr.impl&%10.is_range. FuelId)
(declare-const fuel%vstd!seq.impl&%0.spec_index. FuelId)
(declare-const fuel%vstd!seq.impl&%0.spec_add. FuelId)
(declare-const fuel%vstd!seq.Seq.last. FuelId)
(declare-const fuel%vstd!seq.impl&%0.first. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_index_decreases. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_subrange_decreases. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_empty. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_new_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_new_index. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_push_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_push_index_same. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_push_index_different. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_ext_equal. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_ext_equal_deep. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_subrange_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_subrange_index. FuelId)
(declare-const fuel%vstd!seq.lemma_seq_two_subranges_index. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_add_len. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_add_index1. FuelId)
(declare-const fuel%vstd!seq.axiom_seq_add_index2. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.add_empty_left. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.add_empty_right. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.push_distributes_over_add. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.contains. FuelId)
(declare-const fuel%vstd!seq_lib.impl&%0.remove. FuelId)
(declare-const fuel%vstd!set.Set.subset_of. FuelId)
(declare-const fuel%vstd!set.axiom_set_empty. FuelId)
(declare-const fuel%vstd!set.axiom_set_new. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_same. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_different. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_same. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_insert. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_different. FuelId)
(declare-const fuel%vstd!set.axiom_set_difference. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal. FuelId)
(declare-const fuel%vstd!set.axiom_set_ext_equal_deep. FuelId)
(declare-const fuel%vstd!set.axiom_mk_map_domain. FuelId)
(declare-const fuel%vstd!set.axiom_mk_map_index. FuelId)
(declare-const fuel%vstd!set.axiom_set_empty_finite. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_finite. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_finite. FuelId)
(declare-const fuel%vstd!set.axiom_set_difference_finite. FuelId)
(declare-const fuel%vstd!set.axiom_set_empty_len. FuelId)
(declare-const fuel%vstd!set.axiom_set_insert_len. FuelId)
(declare-const fuel%vstd!set.axiom_set_remove_len. FuelId)
(declare-const fuel%vstd!set.axiom_set_contains_len. FuelId)
(declare-const fuel%vstd!set_lib.impl&%0.is_empty. FuelId)
(declare-const fuel%vstd!set_lib.lemma_set_subset_finite. FuelId)
(declare-const fuel%vstd!set_lib.set_int_range. FuelId)
(declare-const fuel%vstd!set_lib.axiom_is_empty. FuelId)
(declare-const fuel%vstd!set_lib.axiom_is_empty_len0. FuelId)
(declare-const fuel%vstd!slice.impl&%2.spec_index. FuelId)
(declare-const fuel%vstd!slice.axiom_spec_len. FuelId)
(declare-const fuel%vstd!slice.len%returns_clause_autospec. FuelId)
(declare-const fuel%vstd!slice.axiom_slice_ext_equal. FuelId)
(declare-const fuel%vstd!slice.axiom_slice_has_resolved. FuelId)
(declare-const fuel%vstd!view.impl&%0.view. FuelId)
(declare-const fuel%vstd!view.impl&%2.view. FuelId)
(declare-const fuel%vstd!view.impl&%4.view. FuelId)
(declare-const fuel%vstd!view.impl&%6.view. FuelId)
(declare-const fuel%vstd!view.impl&%14.view. FuelId)
(declare-const fuel%vstd!view.impl&%16.view. FuelId)
(declare-const fuel%vstd!view.impl&%18.view. FuelId)
(declare-const fuel%vstd!view.impl&%20.view. FuelId)
(declare-const fuel%vstd!view.impl&%22.view. FuelId)
(declare-const fuel%vstd!view.impl&%24.view. FuelId)
(declare-const fuel%vstd!view.impl&%26.view. FuelId)
(declare-const fuel%vstd!view.impl&%28.view. FuelId)
(declare-const fuel%vstd!view.impl&%30.view. FuelId)
(declare-const fuel%vstd!view.impl&%32.view. FuelId)
(declare-const fuel%vstd!view.impl&%34.view. FuelId)
(declare-const fuel%vstd!view.impl&%36.view. FuelId)
(declare-const fuel%vstd!view.impl&%38.view. FuelId)
(declare-const fuel%vstd!view.impl&%40.view. FuelId)
(declare-const fuel%vstd!view.impl&%42.view. FuelId)
(declare-const fuel%vstd!view.impl&%44.view. FuelId)
(declare-const fuel%vstd!view.impl&%48.view. FuelId)
(declare-const fuel%vstd!view.impl&%50.view. FuelId)
(declare-const fuel%lib!bits.usize_trailing_zeros. FuelId)
(declare-const fuel%lib!bits.is_power_of_two. FuelId)
(declare-const fuel%lib!block_index.GRANULARITY. FuelId)
(declare-const fuel%lib!block_index.impl&%7.view. FuelId)
(declare-const fuel%lib!block_index.impl&%7.granularity_log2_spec. FuelId)
(declare-const fuel%lib!block_index.impl&%7.parameter_validity. FuelId)
(declare-const fuel%lib!block_index.impl&%7.valid_block_index. FuelId)
(declare-const fuel%lib!block_index.impl&%7.wf. FuelId)
(declare-const fuel%lib!block_index.impl&%7.block_size_range. FuelId)
(declare-const fuel%lib!block_index.impl&%7.valid_block_size. FuelId)
(declare-const fuel%lib!half_open_range.impl&%0.wf. FuelId)
(declare-const fuel%lib!half_open_range.impl&%0.contains. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.all_freelist_wf_weak. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.all_freelist_wf. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.wf_shadow. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.shadow_freelist_popped_at. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.perms_size_unchanged_for_freelist. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.wf_free_node. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.free_next_of. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.free_prev_of. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.free_blocks_in_freelist_except. FuelId)
(declare-const fuel%lib!linked_list.impl&%0.free_blocks_in_freelist. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.value_at. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.contains. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.wf_node. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.phys_next_of. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.phys_prev_of. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.wf. FuelId)
(declare-const fuel%lib!all_blocks.impl&%0.get_ptr_internal_index. FuelId)
(declare-const fuel%lib!all_blocks.impl&%1.ii_remove_for_index. FuelId)
(declare-const fuel%lib!all_blocks.impl&%1.ii_shift_after_insert. FuelId)
(declare-const fuel%lib!all_blocks.impl&%1.contains. FuelId)
(declare-const fuel%lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index. FuelId)
(declare-const fuel%lib!all_blocks.is_identity_injection. FuelId)
(declare-const fuel%lib!bitmap.impl&%0.bitmap_wf. FuelId)
(declare-const fuel%lib!bitmap.impl&%0.bitmap_sync. FuelId)
(declare-const fuel%lib!block.impl&%1.is_sentinel. FuelId)
(declare-const fuel%lib!block.impl&%1.is_free. FuelId)
(declare-const fuel%lib!block.impl&%2.wf. FuelId)
(declare-const fuel%lib!parameters.GRANULARITY. FuelId)
(declare-const fuel%lib!parameters.SIZE_USED. FuelId)
(declare-const fuel%lib!parameters.SIZE_SENTINEL. FuelId)
(declare-const fuel%lib!parameters.SPEC_SIZE_SIZE_MASK. FuelId)
(declare-const fuel%lib!parameters.impl&%0.granularity_log2_spec. FuelId)
(declare-const fuel%lib!parameters.impl&%0.parameter_validity. FuelId)
(declare-const fuel%lib!parameters.impl&%0.max_block_size. FuelId)
(declare-const fuel%lib!parameters.impl&%0.max_allocatable_size. FuelId)
(declare-const fuel%lib!VERUS_layout_of_usize. FuelId)
(declare-const fuel%lib!VERUS_layout_of_BlockHdr. FuelId)
(declare-const fuel%lib!VERUS_layout_of_FreeLink. FuelId)
(declare-const fuel%lib!VERUS_layout_of_UsedBlockPad. FuelId)
(declare-const fuel%lib!impl&%0.wf. FuelId)
(declare-const fuel%lib!impl&%0.is_ii. FuelId)
(declare-const fuel%lib!impl&%0.is_root_provenance. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!function.group_function_axioms. FuelId)
(declare-const fuel%vstd!laws_cmp.group_laws_cmp. FuelId)
(declare-const fuel%vstd!laws_eq.bool_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u8_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i8_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u16_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i16_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u32_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i32_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u64_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i64_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.u128_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.i128_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.usize_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.isize_laws.group_laws_eq. FuelId)
(declare-const fuel%vstd!laws_eq.group_laws_eq. FuelId)
(declare-const fuel%vstd!layout.group_align_properties. FuelId)
(declare-const fuel%vstd!layout.group_layout_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_filter_ensures. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_default. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms. FuelId)
(declare-const fuel%vstd!std_specs.btree.group_btree_axioms. FuelId)
(declare-const fuel%vstd!std_specs.hash.group_hash_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)
(assert
 (distinct fuel%vstd!std_specs.num.usize_specs.impl&%0.obeys_eq_spec. fuel%vstd!std_specs.num.usize_specs.impl&%0.eq_spec.
  fuel%vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec. fuel%vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.
  fuel%vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec. fuel%vstd!std_specs.num.isize_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.isize_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.u128_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.u128_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.i128_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.i128_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.u64_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.u64_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.i64_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.i64_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.u32_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.u32_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.i32_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.i32_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.u16_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.u16_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.i16_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.i16_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.u8_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.u8_specs.impl&%0.eq_spec. fuel%vstd!std_specs.num.i8_specs.impl&%0.obeys_eq_spec.
  fuel%vstd!std_specs.num.i8_specs.impl&%0.eq_spec. fuel%vstd!arithmetic.div_mod.lemma_basic_div.
  fuel%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. fuel%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish.
  fuel%vstd!arithmetic.div_mod.lemma_mod_equivalence. fuel%vstd!arithmetic.power2.pow2.
  fuel%vstd!std_specs.bits.u64_trailing_zeros. fuel%vstd!std_specs.bits.axiom_u64_trailing_zeros.
  fuel%vstd!std_specs.cmp.impl&%2.obeys_eq_spec. fuel%vstd!std_specs.cmp.impl&%2.eq_spec.
  fuel%vstd!std_specs.option.impl&%0.is_Some. fuel%vstd!std_specs.option.impl&%0.arrow_0.
  fuel%vstd!std_specs.option.is_none. fuel%vstd!std_specs.option.spec_unwrap. fuel%vstd!std_specs.option.impl&%1.obeys_eq_spec.
  fuel%vstd!std_specs.option.impl&%1.eq_spec. fuel%vstd!raw_ptr.ptr_mut_specs.spec_addr.
  fuel%vstd!array.array_view. fuel%vstd!array.impl&%0.view. fuel%vstd!array.impl&%2.spec_index.
  fuel%vstd!array.lemma_array_index. fuel%vstd!array.array_len_matches_n. fuel%vstd!array.axiom_array_ext_equal.
  fuel%vstd!array.axiom_array_has_resolved. fuel%vstd!layout.valid_layout. fuel%vstd!layout.size_of_as_usize.
  fuel%vstd!layout.layout_of_primitives. fuel%vstd!layout.layout_of_unit_tuple. fuel%vstd!layout.layout_of_references_and_pointers.
  fuel%vstd!layout.layout_of_references_and_pointers_for_sized_types. fuel%vstd!layout.layout_of_references_and_pointers_for_unsized_types.
  fuel%vstd!layout.align_properties. fuel%vstd!layout.align_nonzero. fuel%vstd!map.impl&%0.new.
  fuel%vstd!map.impl&%0.spec_index. fuel%vstd!map.axiom_map_index_decreases_finite.
  fuel%vstd!map.axiom_map_index_decreases_infinite. fuel%vstd!map.axiom_map_insert_domain.
  fuel%vstd!map.axiom_map_insert_same. fuel%vstd!map.axiom_map_insert_different. fuel%vstd!map.axiom_map_remove_domain.
  fuel%vstd!map.axiom_map_remove_different. fuel%vstd!map.axiom_map_ext_equal. fuel%vstd!map.axiom_map_ext_equal_deep.
  fuel%vstd!map_lib.impl&%0.contains_key. fuel%vstd!map_lib.impl&%0.map_entries. fuel%vstd!map_lib.impl&%0.map_values.
  fuel%vstd!map_lib.impl&%0.is_injective. fuel%vstd!raw_ptr.impl&%1.arrow_0. fuel%vstd!raw_ptr.impl&%3.view.
  fuel%vstd!raw_ptr.impl&%5.ptr. fuel%vstd!raw_ptr.impl&%5.opt_value. fuel%vstd!raw_ptr.impl&%5.is_init.
  fuel%vstd!raw_ptr.impl&%5.is_uninit. fuel%vstd!raw_ptr.impl&%5.value. fuel%vstd!raw_ptr.impl&%6.is_init.
  fuel%vstd!raw_ptr.impl&%6.is_uninit. fuel%vstd!raw_ptr.impl&%6.value. fuel%vstd!raw_ptr.axiom_ptr_mut_from_data.
  fuel%vstd!raw_ptr.ptrs_mut_eq. fuel%vstd!raw_ptr.ptrs_mut_eq_sized. fuel%vstd!raw_ptr.spec_cast_ptr_to_usize.
  fuel%vstd!raw_ptr.impl&%9.view. fuel%vstd!raw_ptr.impl&%10.is_range. fuel%vstd!seq.impl&%0.spec_index.
  fuel%vstd!seq.impl&%0.spec_add. fuel%vstd!seq.Seq.last. fuel%vstd!seq.impl&%0.first.
  fuel%vstd!seq.axiom_seq_index_decreases. fuel%vstd!seq.axiom_seq_subrange_decreases.
  fuel%vstd!seq.axiom_seq_empty. fuel%vstd!seq.axiom_seq_new_len. fuel%vstd!seq.axiom_seq_new_index.
  fuel%vstd!seq.axiom_seq_push_len. fuel%vstd!seq.axiom_seq_push_index_same. fuel%vstd!seq.axiom_seq_push_index_different.
  fuel%vstd!seq.axiom_seq_ext_equal. fuel%vstd!seq.axiom_seq_ext_equal_deep. fuel%vstd!seq.axiom_seq_subrange_len.
  fuel%vstd!seq.axiom_seq_subrange_index. fuel%vstd!seq.lemma_seq_two_subranges_index.
  fuel%vstd!seq.axiom_seq_add_len. fuel%vstd!seq.axiom_seq_add_index1. fuel%vstd!seq.axiom_seq_add_index2.
  fuel%vstd!seq_lib.impl&%0.add_empty_left. fuel%vstd!seq_lib.impl&%0.add_empty_right.
  fuel%vstd!seq_lib.impl&%0.push_distributes_over_add. fuel%vstd!seq_lib.impl&%0.contains.
  fuel%vstd!seq_lib.impl&%0.remove. fuel%vstd!set.Set.subset_of. fuel%vstd!set.axiom_set_empty.
  fuel%vstd!set.axiom_set_new. fuel%vstd!set.axiom_set_insert_same. fuel%vstd!set.axiom_set_insert_different.
  fuel%vstd!set.axiom_set_remove_same. fuel%vstd!set.axiom_set_remove_insert. fuel%vstd!set.axiom_set_remove_different.
  fuel%vstd!set.axiom_set_difference. fuel%vstd!set.axiom_set_ext_equal. fuel%vstd!set.axiom_set_ext_equal_deep.
  fuel%vstd!set.axiom_mk_map_domain. fuel%vstd!set.axiom_mk_map_index. fuel%vstd!set.axiom_set_empty_finite.
  fuel%vstd!set.axiom_set_insert_finite. fuel%vstd!set.axiom_set_remove_finite. fuel%vstd!set.axiom_set_difference_finite.
  fuel%vstd!set.axiom_set_empty_len. fuel%vstd!set.axiom_set_insert_len. fuel%vstd!set.axiom_set_remove_len.
  fuel%vstd!set.axiom_set_contains_len. fuel%vstd!set_lib.impl&%0.is_empty. fuel%vstd!set_lib.lemma_set_subset_finite.
  fuel%vstd!set_lib.set_int_range. fuel%vstd!set_lib.axiom_is_empty. fuel%vstd!set_lib.axiom_is_empty_len0.
  fuel%vstd!slice.impl&%2.spec_index. fuel%vstd!slice.axiom_spec_len. fuel%vstd!slice.len%returns_clause_autospec.
  fuel%vstd!slice.axiom_slice_ext_equal. fuel%vstd!slice.axiom_slice_has_resolved.
  fuel%vstd!view.impl&%0.view. fuel%vstd!view.impl&%2.view. fuel%vstd!view.impl&%4.view.
  fuel%vstd!view.impl&%6.view. fuel%vstd!view.impl&%14.view. fuel%vstd!view.impl&%16.view.
  fuel%vstd!view.impl&%18.view. fuel%vstd!view.impl&%20.view. fuel%vstd!view.impl&%22.view.
  fuel%vstd!view.impl&%24.view. fuel%vstd!view.impl&%26.view. fuel%vstd!view.impl&%28.view.
  fuel%vstd!view.impl&%30.view. fuel%vstd!view.impl&%32.view. fuel%vstd!view.impl&%34.view.
  fuel%vstd!view.impl&%36.view. fuel%vstd!view.impl&%38.view. fuel%vstd!view.impl&%40.view.
  fuel%vstd!view.impl&%42.view. fuel%vstd!view.impl&%44.view. fuel%vstd!view.impl&%48.view.
  fuel%vstd!view.impl&%50.view. fuel%lib!bits.usize_trailing_zeros. fuel%lib!bits.is_power_of_two.
  fuel%lib!block_index.GRANULARITY. fuel%lib!block_index.impl&%7.view. fuel%lib!block_index.impl&%7.granularity_log2_spec.
  fuel%lib!block_index.impl&%7.parameter_validity. fuel%lib!block_index.impl&%7.valid_block_index.
  fuel%lib!block_index.impl&%7.wf. fuel%lib!block_index.impl&%7.block_size_range. fuel%lib!block_index.impl&%7.valid_block_size.
  fuel%lib!half_open_range.impl&%0.wf. fuel%lib!half_open_range.impl&%0.contains. fuel%lib!linked_list.impl&%0.all_freelist_wf_weak.
  fuel%lib!linked_list.impl&%0.all_freelist_wf. fuel%lib!linked_list.impl&%0.wf_shadow.
  fuel%lib!linked_list.impl&%0.shadow_freelist_popped_at. fuel%lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.
  fuel%lib!linked_list.impl&%0.wf_free_node. fuel%lib!linked_list.impl&%0.free_next_of.
  fuel%lib!linked_list.impl&%0.free_prev_of. fuel%lib!linked_list.impl&%0.free_blocks_in_freelist_except.
  fuel%lib!linked_list.impl&%0.free_blocks_in_freelist. fuel%lib!all_blocks.impl&%0.value_at.
  fuel%lib!all_blocks.impl&%0.contains. fuel%lib!all_blocks.impl&%0.wf_node. fuel%lib!all_blocks.impl&%0.phys_next_of.
  fuel%lib!all_blocks.impl&%0.phys_prev_of. fuel%lib!all_blocks.impl&%0.wf. fuel%lib!all_blocks.impl&%0.get_ptr_internal_index.
  fuel%lib!all_blocks.impl&%1.ii_remove_for_index. fuel%lib!all_blocks.impl&%1.ii_shift_after_insert.
  fuel%lib!all_blocks.impl&%1.contains. fuel%lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.
  fuel%lib!all_blocks.is_identity_injection. fuel%lib!bitmap.impl&%0.bitmap_wf. fuel%lib!bitmap.impl&%0.bitmap_sync.
  fuel%lib!block.impl&%1.is_sentinel. fuel%lib!block.impl&%1.is_free. fuel%lib!block.impl&%2.wf.
  fuel%lib!parameters.GRANULARITY. fuel%lib!parameters.SIZE_USED. fuel%lib!parameters.SIZE_SENTINEL.
  fuel%lib!parameters.SPEC_SIZE_SIZE_MASK. fuel%lib!parameters.impl&%0.granularity_log2_spec.
  fuel%lib!parameters.impl&%0.parameter_validity. fuel%lib!parameters.impl&%0.max_block_size.
  fuel%lib!parameters.impl&%0.max_allocatable_size. fuel%lib!VERUS_layout_of_usize.
  fuel%lib!VERUS_layout_of_BlockHdr. fuel%lib!VERUS_layout_of_FreeLink. fuel%lib!VERUS_layout_of_UsedBlockPad.
  fuel%lib!impl&%0.wf. fuel%lib!impl&%0.is_ii. fuel%lib!impl&%0.is_root_provenance.
  fuel%vstd!array.group_array_axioms. fuel%vstd!function.group_function_axioms. fuel%vstd!laws_cmp.group_laws_cmp.
  fuel%vstd!laws_eq.bool_laws.group_laws_eq. fuel%vstd!laws_eq.u8_laws.group_laws_eq.
  fuel%vstd!laws_eq.i8_laws.group_laws_eq. fuel%vstd!laws_eq.u16_laws.group_laws_eq.
  fuel%vstd!laws_eq.i16_laws.group_laws_eq. fuel%vstd!laws_eq.u32_laws.group_laws_eq.
  fuel%vstd!laws_eq.i32_laws.group_laws_eq. fuel%vstd!laws_eq.u64_laws.group_laws_eq.
  fuel%vstd!laws_eq.i64_laws.group_laws_eq. fuel%vstd!laws_eq.u128_laws.group_laws_eq.
  fuel%vstd!laws_eq.i128_laws.group_laws_eq. fuel%vstd!laws_eq.usize_laws.group_laws_eq.
  fuel%vstd!laws_eq.isize_laws.group_laws_eq. fuel%vstd!laws_eq.group_laws_eq. fuel%vstd!layout.group_align_properties.
  fuel%vstd!layout.group_layout_axioms. fuel%vstd!map.group_map_axioms. fuel%vstd!multiset.group_multiset_axioms.
  fuel%vstd!raw_ptr.group_raw_ptr_axioms. fuel%vstd!seq.group_seq_axioms. fuel%vstd!seq_lib.group_filter_ensures.
  fuel%vstd!seq_lib.group_seq_lib_default. fuel%vstd!set.group_set_axioms. fuel%vstd!set_lib.group_set_lib_default.
  fuel%vstd!slice.group_slice_axioms. fuel%vstd!string.group_string_axioms. fuel%vstd!std_specs.bits.group_bits_axioms.
  fuel%vstd!std_specs.control_flow.group_control_flow_axioms. fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms.
  fuel%vstd!std_specs.btree.group_btree_axioms. fuel%vstd!std_specs.hash.group_hash_axioms.
  fuel%vstd!std_specs.range.group_range_axioms. fuel%vstd!std_specs.slice.group_slice_axioms.
  fuel%vstd!std_specs.vec.group_vec_axioms. fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.
  fuel%vstd!group_vstd_default.
))
(assert
 (=>
  (fuel_bool_default fuel%vstd!array.group_array_axioms.)
  (and
   (fuel_bool_default fuel%vstd!array.array_len_matches_n.)
   (fuel_bool_default fuel%vstd!array.lemma_array_index.)
   (fuel_bool_default fuel%vstd!array.axiom_array_ext_equal.)
   (fuel_bool_default fuel%vstd!array.axiom_array_has_resolved.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!laws_eq.group_laws_eq.)
  (and
   (fuel_bool_default fuel%vstd!laws_eq.bool_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u8_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i8_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u16_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i16_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u32_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i32_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u64_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i64_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.u128_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.i128_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.usize_laws.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_eq.isize_laws.group_laws_eq.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!layout.group_align_properties.)
  (and
   (fuel_bool_default fuel%vstd!layout.align_properties.)
   (fuel_bool_default fuel%vstd!layout.align_nonzero.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!layout.group_layout_axioms.)
  (and
   (fuel_bool_default fuel%vstd!layout.layout_of_primitives.)
   (fuel_bool_default fuel%vstd!layout.layout_of_unit_tuple.)
   (fuel_bool_default fuel%vstd!layout.layout_of_references_and_pointers.)
   (fuel_bool_default fuel%vstd!layout.layout_of_references_and_pointers_for_sized_types.)
   (fuel_bool_default fuel%vstd!layout.layout_of_references_and_pointers_for_unsized_types.)
   (fuel_bool_default fuel%vstd!layout.group_align_properties.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!map.group_map_axioms.)
  (and
   (fuel_bool_default fuel%vstd!map.axiom_map_index_decreases_finite.)
   (fuel_bool_default fuel%vstd!map.axiom_map_index_decreases_infinite.)
   (fuel_bool_default fuel%vstd!map.axiom_map_insert_domain.)
   (fuel_bool_default fuel%vstd!map.axiom_map_insert_same.)
   (fuel_bool_default fuel%vstd!map.axiom_map_insert_different.)
   (fuel_bool_default fuel%vstd!map.axiom_map_remove_domain.)
   (fuel_bool_default fuel%vstd!map.axiom_map_remove_different.)
   (fuel_bool_default fuel%vstd!map.axiom_map_ext_equal.)
   (fuel_bool_default fuel%vstd!map.axiom_map_ext_equal_deep.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
  (and
   (fuel_bool_default fuel%vstd!raw_ptr.axiom_ptr_mut_from_data.)
   (fuel_bool_default fuel%vstd!raw_ptr.ptrs_mut_eq.)
   (fuel_bool_default fuel%vstd!raw_ptr.ptrs_mut_eq_sized.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
  (and
   (fuel_bool_default fuel%vstd!seq.axiom_seq_index_decreases.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_subrange_decreases.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_empty.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_new_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_new_index.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_push_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_push_index_same.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_push_index_different.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_ext_equal.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_ext_equal_deep.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_subrange_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_subrange_index.)
   (fuel_bool_default fuel%vstd!seq.lemma_seq_two_subranges_index.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_add_len.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_add_index1.)
   (fuel_bool_default fuel%vstd!seq.axiom_seq_add_index2.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
  (and
   (fuel_bool_default fuel%vstd!seq_lib.group_filter_ensures.)
   (fuel_bool_default fuel%vstd!seq_lib.impl&%0.add_empty_left.)
   (fuel_bool_default fuel%vstd!seq_lib.impl&%0.add_empty_right.)
   (fuel_bool_default fuel%vstd!seq_lib.impl&%0.push_distributes_over_add.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!set.group_set_axioms.)
  (and
   (fuel_bool_default fuel%vstd!set.axiom_set_empty.)
   (fuel_bool_default fuel%vstd!set.axiom_set_new.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_same.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_different.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_same.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_insert.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_different.)
   (fuel_bool_default fuel%vstd!set.axiom_set_difference.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal.)
   (fuel_bool_default fuel%vstd!set.axiom_set_ext_equal_deep.)
   (fuel_bool_default fuel%vstd!set.axiom_mk_map_domain.)
   (fuel_bool_default fuel%vstd!set.axiom_mk_map_index.)
   (fuel_bool_default fuel%vstd!set.axiom_set_empty_finite.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_finite.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_finite.)
   (fuel_bool_default fuel%vstd!set.axiom_set_difference_finite.)
   (fuel_bool_default fuel%vstd!set.axiom_set_empty_len.)
   (fuel_bool_default fuel%vstd!set.axiom_set_insert_len.)
   (fuel_bool_default fuel%vstd!set.axiom_set_remove_len.)
   (fuel_bool_default fuel%vstd!set.axiom_set_contains_len.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!set_lib.group_set_lib_default.)
  (and
   (fuel_bool_default fuel%vstd!set_lib.axiom_is_empty.)
   (fuel_bool_default fuel%vstd!set_lib.axiom_is_empty_len0.)
   (fuel_bool_default fuel%vstd!set_lib.lemma_set_subset_finite.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
  (and
   (fuel_bool_default fuel%vstd!slice.axiom_spec_len.)
   (fuel_bool_default fuel%vstd!slice.axiom_slice_ext_equal.)
   (fuel_bool_default fuel%vstd!slice.axiom_slice_has_resolved.)
)))
(assert
 (=>
  (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
  (fuel_bool_default fuel%vstd!std_specs.bits.axiom_u64_trailing_zeros.)
))
(assert
 (fuel_bool_default fuel%vstd!group_vstd_default.)
)
(assert
 (=>
  (fuel_bool_default fuel%vstd!group_vstd_default.)
  (and
   (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
   (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
   (fuel_bool_default fuel%vstd!map.group_map_axioms.)
   (fuel_bool_default fuel%vstd!set.group_set_axioms.)
   (fuel_bool_default fuel%vstd!set_lib.group_set_lib_default.)
   (fuel_bool_default fuel%vstd!multiset.group_multiset_axioms.)
   (fuel_bool_default fuel%vstd!function.group_function_axioms.)
   (fuel_bool_default fuel%vstd!laws_eq.group_laws_eq.)
   (fuel_bool_default fuel%vstd!laws_cmp.group_laws_cmp.)
   (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!array.group_array_axioms.)
   (fuel_bool_default fuel%vstd!string.group_string_axioms.)
   (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
   (fuel_bool_default fuel%vstd!layout.group_layout_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.range.group_range_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.control_flow.group_control_flow_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.manually_drop.group_manually_drop_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vecdeque.group_vec_dequeue_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.hash.group_hash_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.btree.group_btree_axioms.)
)))

;; Trait-Decls
(declare-fun tr_bound%vstd!array.ArrayAdditionalSpecFns. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%vstd!slice.SliceAdditionalSpecFns. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%vstd!view.View. (Dcr Type) Bool)
(declare-fun tr_bound%core!cmp.PartialEq. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%vstd!std_specs.cmp.PartialEqSpec. (Dcr Type Dcr Type) Bool)
(declare-fun tr_bound%core!alloc.Allocator. (Dcr Type) Bool)
(declare-fun tr_bound%vstd!std_specs.option.OptionAdditionalFns. (Dcr Type Dcr Type)
 Bool
)

;; Associated-Type-Decls
(declare-fun proj%%vstd!view.View./V (Dcr Type) Dcr)
(declare-fun proj%vstd!view.View./V (Dcr Type) Type)

;; Datatypes
(declare-fun pointee_metadata% (Dcr) Type)
(declare-fun pointee_metadata%% (Dcr) Dcr)
(assert
 (forall ((d Dcr)) (!
   (=>
    (sized d)
    (= (pointee_metadata% d) TYPE%tuple%0.)
   )
   :pattern ((pointee_metadata% d))
   :qid prelude_project_pointee_metadata_sized
   :skolemid skolem_prelude_project_pointee_metadata_sized
)))
(assert
 (forall ((d Dcr)) (!
   (=>
    (sized d)
    (= (pointee_metadata%% d) $)
   )
   :pattern ((pointee_metadata%% d))
   :qid prelude_project_pointee_metadata_decoration_sized
   :skolemid skolem_prelude_project_pointee_metadata_decoration_sized
)))
(assert
 (= (pointee_metadata% $slice) USIZE)
)
(assert
 (= (pointee_metadata%% $slice) $)
)
(assert
 (forall ((d Dcr)) (!
   (= (pointee_metadata% (DST d)) (pointee_metadata% d))
   :pattern ((pointee_metadata% (DST d)))
   :qid prelude_project_pointee_metadata_decorate_struct_inherit
   :skolemid skolem_prelude_project_pointee_metadata_decorate_struct_inherit
)))
(assert
 (forall ((d Dcr)) (!
   (= (pointee_metadata%% (DST d)) (pointee_metadata%% d))
   :pattern ((pointee_metadata%% (DST d)))
   :qid prelude_project_pointee_metadata_decoration_decorate_struct_inherit
   :skolemid skolem_prelude_project_pointee_metadata_decoration_decorate_struct_inherit
)))
(declare-sort alloc!alloc.Global. 0)
(declare-sort core!convert.Infallible. 0)
(declare-sort lib!half_open_range.HalfOpenRange. 0)
(declare-sort vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. 0)
(declare-sort vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. 0)
(declare-sort vstd!raw_ptr.IsExposed. 0)
(declare-sort vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. 0)
(declare-sort vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. 0)
(declare-sort vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. 0)
(declare-sort vstd!raw_ptr.PointsToRaw. 0)
(declare-sort vstd!raw_ptr.Provenance. 0)
(declare-sort vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. 0)
(declare-sort vstd!set.Set<int.>. 0)
(declare-sort vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. 0)
(declare-sort ptr_mut%<u8.>. 0)
(declare-sort ptr_mut%<lib!block.BlockHdr.>. 0)
(declare-sort ptr_mut%<lib!block.FreeLink.>. 0)
(declare-sort ptr_mut%<lib!block.UsedBlockPad.>. 0)
(declare-datatypes ((core!ops.control_flow.ControlFlow. 0) (core!option.Option. 0)
  (core!marker.PhantomData. 0) (vstd!raw_ptr.PtrData. 0) (vstd!raw_ptr.MemContents.
   0
  ) (vstd!raw_ptr.PointsToData. 0) (lib!block_index.BlockIndex. 0) (lib!all_blocks.AllBlocks.
   0
  ) (lib!all_blocks.ShadowFreelist. 0) (lib!block.BlockHdr. 0) (lib!block.FreeLink.
   0
  ) (lib!block.BlockPerm. 0) (lib!block.UsedBlockPad. 0) (lib!Tlsf. 0) (lib!DeallocToken.
   0
  ) (tuple%0. 0) (tuple%2. 0) (tuple%3. 0)
 ) (((core!ops.control_flow.ControlFlow./Continue (core!ops.control_flow.ControlFlow./Continue/?0
     Poly
    )
   ) (core!ops.control_flow.ControlFlow./Break (core!ops.control_flow.ControlFlow./Break/?0
     Poly
   ))
  ) ((core!option.Option./None) (core!option.Option./Some (core!option.Option./Some/?0
     Poly
   ))
  ) ((core!marker.PhantomData./PhantomData)) ((vstd!raw_ptr.PtrData./PtrData (vstd!raw_ptr.PtrData./PtrData/?addr
     Int
    ) (vstd!raw_ptr.PtrData./PtrData/?provenance vstd!raw_ptr.Provenance.) (vstd!raw_ptr.PtrData./PtrData/?metadata
     Poly
   ))
  ) ((vstd!raw_ptr.MemContents./Uninit) (vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.MemContents./Init/?0
     Poly
   ))
  ) ((vstd!raw_ptr.PointsToData./PointsToData (vstd!raw_ptr.PointsToData./PointsToData/?ptr
     Poly
    ) (vstd!raw_ptr.PointsToData./PointsToData/?opt_value vstd!raw_ptr.MemContents.)
   )
  ) ((lib!block_index.BlockIndex./BlockIndex (lib!block_index.BlockIndex./BlockIndex/?0
     Int
    ) (lib!block_index.BlockIndex./BlockIndex/?1 Int)
   )
  ) ((lib!all_blocks.AllBlocks./AllBlocks (lib!all_blocks.AllBlocks./AllBlocks/?ptrs vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.)
    (lib!all_blocks.AllBlocks./AllBlocks/?perms vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.)
   )
  ) ((lib!all_blocks.ShadowFreelist./ShadowFreelist (lib!all_blocks.ShadowFreelist./ShadowFreelist/?m
     Poly
    ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/?pi Poly)
   )
  ) ((lib!block.BlockHdr./BlockHdr (lib!block.BlockHdr./BlockHdr/?size Int) (lib!block.BlockHdr./BlockHdr/?prev_phys_block
     ptr_mut%<lib!block.BlockHdr.>.
   ))
  ) ((lib!block.FreeLink./FreeLink (lib!block.FreeLink./FreeLink/?next_free ptr_mut%<lib!block.BlockHdr.>.)
    (lib!block.FreeLink./FreeLink/?prev_free ptr_mut%<lib!block.BlockHdr.>.)
   )
  ) ((lib!block.BlockPerm./BlockPerm (lib!block.BlockPerm./BlockPerm/?points_to vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.)
    (lib!block.BlockPerm./BlockPerm/?free_link_perm core!option.Option.) (lib!block.BlockPerm./BlockPerm/?mem
     vstd!raw_ptr.PointsToRaw.
    ) (lib!block.BlockPerm./BlockPerm/?overhead_mem vstd!raw_ptr.PointsToRaw.) (lib!block.BlockPerm./BlockPerm/?pad_perm
     core!option.Option.
   ))
  ) ((lib!block.UsedBlockPad./UsedBlockPad (lib!block.UsedBlockPad./UsedBlockPad/?block_hdr
     ptr_mut%<lib!block.BlockHdr.>.
   ))
  ) ((lib!Tlsf./Tlsf (lib!Tlsf./Tlsf/?fl_bitmap Int) (lib!Tlsf./Tlsf/?sl_bitmap %%Function%%)
    (lib!Tlsf./Tlsf/?first_free %%Function%%) (lib!Tlsf./Tlsf/?_phantom core!marker.PhantomData.)
    (lib!Tlsf./Tlsf/?valid_range vstd!set.Set<int.>.) (lib!Tlsf./Tlsf/?all_blocks lib!all_blocks.AllBlocks.)
    (lib!Tlsf./Tlsf/?root_provenances core!option.Option.) (lib!Tlsf./Tlsf/?shadow_freelist
     lib!all_blocks.ShadowFreelist.
    ) (lib!Tlsf./Tlsf/?user_block_map vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.)
   )
  ) ((lib!DeallocToken./DeallocToken (lib!DeallocToken./DeallocToken/?ptr ptr_mut%<u8.>.)
    (lib!DeallocToken./DeallocToken/?user_size Int) (lib!DeallocToken./DeallocToken/?align
     Int
   ))
  ) ((tuple%0./tuple%0)) ((tuple%2./tuple%2 (tuple%2./tuple%2/?0 Poly) (tuple%2./tuple%2/?1
     Poly
   ))
  ) ((tuple%3./tuple%3 (tuple%3./tuple%3/?0 Poly) (tuple%3./tuple%3/?1 Poly) (tuple%3./tuple%3/?2
     Poly
)))))
(declare-fun core!ops.control_flow.ControlFlow./Continue/0 (Dcr Type Dcr Type core!ops.control_flow.ControlFlow.)
 Poly
)
(declare-fun core!ops.control_flow.ControlFlow./Break/0 (Dcr Type Dcr Type core!ops.control_flow.ControlFlow.)
 Poly
)
(declare-fun core!option.Option./Some/0 (Dcr Type core!option.Option.) Poly)
(declare-fun vstd!raw_ptr.PtrData./PtrData/addr (vstd!raw_ptr.PtrData.) Int)
(declare-fun vstd!raw_ptr.PtrData./PtrData/provenance (vstd!raw_ptr.PtrData.) vstd!raw_ptr.Provenance.)
(declare-fun vstd!raw_ptr.PtrData./PtrData/metadata (vstd!raw_ptr.PtrData.) Poly)
(declare-fun vstd!raw_ptr.MemContents./Init/0 (Dcr Type vstd!raw_ptr.MemContents.)
 Poly
)
(declare-fun vstd!raw_ptr.PointsToData./PointsToData/ptr (vstd!raw_ptr.PointsToData.)
 Poly
)
(declare-fun vstd!raw_ptr.PointsToData./PointsToData/opt_value (vstd!raw_ptr.PointsToData.)
 vstd!raw_ptr.MemContents.
)
(declare-fun lib!block_index.BlockIndex./BlockIndex/0 (lib!block_index.BlockIndex.)
 Int
)
(declare-fun lib!block_index.BlockIndex./BlockIndex/1 (lib!block_index.BlockIndex.)
 Int
)
(declare-fun lib!all_blocks.AllBlocks./AllBlocks/ptrs (lib!all_blocks.AllBlocks.)
 vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
)
(declare-fun lib!all_blocks.AllBlocks./AllBlocks/perms (lib!all_blocks.AllBlocks.)
 vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
)
(declare-fun lib!all_blocks.ShadowFreelist./ShadowFreelist/m (lib!all_blocks.ShadowFreelist.)
 Poly
)
(declare-fun lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (lib!all_blocks.ShadowFreelist.)
 Poly
)
(declare-fun lib!block.BlockHdr./BlockHdr/size (lib!block.BlockHdr.) Int)
(declare-fun lib!block.BlockHdr./BlockHdr/prev_phys_block (lib!block.BlockHdr.) ptr_mut%<lib!block.BlockHdr.>.)
(declare-fun lib!block.FreeLink./FreeLink/next_free (lib!block.FreeLink.) ptr_mut%<lib!block.BlockHdr.>.)
(declare-fun lib!block.FreeLink./FreeLink/prev_free (lib!block.FreeLink.) ptr_mut%<lib!block.BlockHdr.>.)
(declare-fun lib!block.BlockPerm./BlockPerm/points_to (lib!block.BlockPerm.) vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.)
(declare-fun lib!block.BlockPerm./BlockPerm/free_link_perm (lib!block.BlockPerm.)
 core!option.Option.
)
(declare-fun lib!block.BlockPerm./BlockPerm/mem (lib!block.BlockPerm.) vstd!raw_ptr.PointsToRaw.)
(declare-fun lib!block.BlockPerm./BlockPerm/overhead_mem (lib!block.BlockPerm.) vstd!raw_ptr.PointsToRaw.)
(declare-fun lib!block.BlockPerm./BlockPerm/pad_perm (lib!block.BlockPerm.) core!option.Option.)
(declare-fun lib!block.UsedBlockPad./UsedBlockPad/block_hdr (lib!block.UsedBlockPad.)
 ptr_mut%<lib!block.BlockHdr.>.
)
(declare-fun lib!Tlsf./Tlsf/fl_bitmap (lib!Tlsf.) Int)
(declare-fun lib!Tlsf./Tlsf/sl_bitmap (lib!Tlsf.) %%Function%%)
(declare-fun lib!Tlsf./Tlsf/first_free (lib!Tlsf.) %%Function%%)
(declare-fun lib!Tlsf./Tlsf/_phantom (lib!Tlsf.) core!marker.PhantomData.)
(declare-fun lib!Tlsf./Tlsf/valid_range (lib!Tlsf.) vstd!set.Set<int.>.)
(declare-fun lib!Tlsf./Tlsf/all_blocks (lib!Tlsf.) lib!all_blocks.AllBlocks.)
(declare-fun lib!Tlsf./Tlsf/root_provenances (lib!Tlsf.) core!option.Option.)
(declare-fun lib!Tlsf./Tlsf/shadow_freelist (lib!Tlsf.) lib!all_blocks.ShadowFreelist.)
(declare-fun lib!Tlsf./Tlsf/user_block_map (lib!Tlsf.) vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.)
(declare-fun lib!DeallocToken./DeallocToken/ptr (lib!DeallocToken.) ptr_mut%<u8.>.)
(declare-fun lib!DeallocToken./DeallocToken/user_size (lib!DeallocToken.) Int)
(declare-fun lib!DeallocToken./DeallocToken/align (lib!DeallocToken.) Int)
(declare-fun tuple%2./tuple%2/0 (tuple%2.) Poly)
(declare-fun tuple%2./tuple%2/1 (tuple%2.) Poly)
(declare-fun tuple%3./tuple%3/0 (tuple%3.) Poly)
(declare-fun tuple%3./tuple%3/1 (tuple%3.) Poly)
(declare-fun tuple%3./tuple%3/2 (tuple%3.) Poly)
(declare-fun TYPE%fun%1. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%fun%2. (Dcr Type Dcr Type Dcr Type) Type)
(declare-const TYPE%alloc!alloc.Global. Type)
(declare-fun TYPE%core!ops.control_flow.ControlFlow. (Dcr Type Dcr Type) Type)
(declare-const TYPE%core!convert.Infallible. Type)
(declare-fun TYPE%core!option.Option. (Dcr Type) Type)
(declare-fun TYPE%core!marker.PhantomData. (Dcr Type) Type)
(declare-fun TYPE%vstd!map.Map. (Dcr Type Dcr Type) Type)
(declare-const TYPE%vstd!raw_ptr.Provenance. Type)
(declare-fun TYPE%vstd!raw_ptr.PtrData. (Dcr Type) Type)
(declare-fun TYPE%vstd!raw_ptr.PointsTo. (Dcr Type) Type)
(declare-fun TYPE%vstd!raw_ptr.MemContents. (Dcr Type) Type)
(declare-fun TYPE%vstd!raw_ptr.PointsToData. (Dcr Type) Type)
(declare-const TYPE%vstd!raw_ptr.IsExposed. Type)
(declare-const TYPE%vstd!raw_ptr.PointsToRaw. Type)
(declare-fun TYPE%vstd!seq.Seq. (Dcr Type) Type)
(declare-fun TYPE%vstd!set.Set. (Dcr Type) Type)
(declare-fun TYPE%lib!block_index.BlockIndex. (Dcr Type Dcr Type) Type)
(declare-const TYPE%lib!half_open_range.HalfOpenRange. Type)
(declare-fun TYPE%lib!all_blocks.AllBlocks. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%lib!all_blocks.ShadowFreelist. (Dcr Type Dcr Type) Type)
(declare-const TYPE%lib!block.BlockHdr. Type)
(declare-const TYPE%lib!block.FreeLink. Type)
(declare-const TYPE%lib!block.BlockPerm. Type)
(declare-const TYPE%lib!block.UsedBlockPad. Type)
(declare-fun TYPE%lib!Tlsf. (Dcr Type Dcr Type) Type)
(declare-const TYPE%lib!DeallocToken. Type)
(declare-fun TYPE%tuple%2. (Dcr Type Dcr Type) Type)
(declare-fun TYPE%tuple%3. (Dcr Type Dcr Type Dcr Type) Type)
(declare-fun FNDEF%core!cmp.PartialEq.eq. (Dcr Type Dcr Type) Type)
(declare-fun Poly%fun%1. (%%Function%%) Poly)
(declare-fun %Poly%fun%1. (Poly) %%Function%%)
(declare-fun Poly%fun%2. (%%Function%%) Poly)
(declare-fun %Poly%fun%2. (Poly) %%Function%%)
(declare-fun Poly%array%. (%%Function%%) Poly)
(declare-fun %Poly%array%. (Poly) %%Function%%)
(declare-fun Poly%alloc!alloc.Global. (alloc!alloc.Global.) Poly)
(declare-fun %Poly%alloc!alloc.Global. (Poly) alloc!alloc.Global.)
(declare-fun Poly%core!convert.Infallible. (core!convert.Infallible.) Poly)
(declare-fun %Poly%core!convert.Infallible. (Poly) core!convert.Infallible.)
(declare-fun Poly%lib!half_open_range.HalfOpenRange. (lib!half_open_range.HalfOpenRange.)
 Poly
)
(declare-fun %Poly%lib!half_open_range.HalfOpenRange. (Poly) lib!half_open_range.HalfOpenRange.)
(declare-fun Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.)
 Poly
)
(declare-fun %Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (Poly)
 vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
)
(declare-fun Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
 (vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.) Poly
)
(declare-fun %Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
 (Poly) vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
)
(declare-fun Poly%vstd!raw_ptr.IsExposed. (vstd!raw_ptr.IsExposed.) Poly)
(declare-fun %Poly%vstd!raw_ptr.IsExposed. (Poly) vstd!raw_ptr.IsExposed.)
(declare-fun Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.)
 Poly
)
(declare-fun %Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (Poly) vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.)
(declare-fun Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (vstd!raw_ptr.PointsTo<lib!block.FreeLink.>.)
 Poly
)
(declare-fun %Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (Poly) vstd!raw_ptr.PointsTo<lib!block.FreeLink.>.)
(declare-fun Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. (vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>.)
 Poly
)
(declare-fun %Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. (Poly) vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>.)
(declare-fun Poly%vstd!raw_ptr.PointsToRaw. (vstd!raw_ptr.PointsToRaw.) Poly)
(declare-fun %Poly%vstd!raw_ptr.PointsToRaw. (Poly) vstd!raw_ptr.PointsToRaw.)
(declare-fun Poly%vstd!raw_ptr.Provenance. (vstd!raw_ptr.Provenance.) Poly)
(declare-fun %Poly%vstd!raw_ptr.Provenance. (Poly) vstd!raw_ptr.Provenance.)
(declare-fun Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.)
 Poly
)
(declare-fun %Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (Poly) vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.)
(declare-fun Poly%vstd!set.Set<int.>. (vstd!set.Set<int.>.) Poly)
(declare-fun %Poly%vstd!set.Set<int.>. (Poly) vstd!set.Set<int.>.)
(declare-fun Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. (vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)
 Poly
)
(declare-fun %Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. (Poly) vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)
(declare-fun Poly%ptr_mut%<u8.>. (ptr_mut%<u8.>.) Poly)
(declare-fun %Poly%ptr_mut%<u8.>. (Poly) ptr_mut%<u8.>.)
(declare-fun Poly%ptr_mut%<lib!block.BlockHdr.>. (ptr_mut%<lib!block.BlockHdr.>.)
 Poly
)
(declare-fun %Poly%ptr_mut%<lib!block.BlockHdr.>. (Poly) ptr_mut%<lib!block.BlockHdr.>.)
(declare-fun Poly%ptr_mut%<lib!block.FreeLink.>. (ptr_mut%<lib!block.FreeLink.>.)
 Poly
)
(declare-fun %Poly%ptr_mut%<lib!block.FreeLink.>. (Poly) ptr_mut%<lib!block.FreeLink.>.)
(declare-fun Poly%ptr_mut%<lib!block.UsedBlockPad.>. (ptr_mut%<lib!block.UsedBlockPad.>.)
 Poly
)
(declare-fun %Poly%ptr_mut%<lib!block.UsedBlockPad.>. (Poly) ptr_mut%<lib!block.UsedBlockPad.>.)
(declare-fun Poly%core!ops.control_flow.ControlFlow. (core!ops.control_flow.ControlFlow.)
 Poly
)
(declare-fun %Poly%core!ops.control_flow.ControlFlow. (Poly) core!ops.control_flow.ControlFlow.)
(declare-fun Poly%core!option.Option. (core!option.Option.) Poly)
(declare-fun %Poly%core!option.Option. (Poly) core!option.Option.)
(declare-fun Poly%core!marker.PhantomData. (core!marker.PhantomData.) Poly)
(declare-fun %Poly%core!marker.PhantomData. (Poly) core!marker.PhantomData.)
(declare-fun Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData.) Poly)
(declare-fun %Poly%vstd!raw_ptr.PtrData. (Poly) vstd!raw_ptr.PtrData.)
(declare-fun Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents.) Poly)
(declare-fun %Poly%vstd!raw_ptr.MemContents. (Poly) vstd!raw_ptr.MemContents.)
(declare-fun Poly%vstd!raw_ptr.PointsToData. (vstd!raw_ptr.PointsToData.) Poly)
(declare-fun %Poly%vstd!raw_ptr.PointsToData. (Poly) vstd!raw_ptr.PointsToData.)
(declare-fun Poly%lib!block_index.BlockIndex. (lib!block_index.BlockIndex.) Poly)
(declare-fun %Poly%lib!block_index.BlockIndex. (Poly) lib!block_index.BlockIndex.)
(declare-fun Poly%lib!all_blocks.AllBlocks. (lib!all_blocks.AllBlocks.) Poly)
(declare-fun %Poly%lib!all_blocks.AllBlocks. (Poly) lib!all_blocks.AllBlocks.)
(declare-fun Poly%lib!all_blocks.ShadowFreelist. (lib!all_blocks.ShadowFreelist.)
 Poly
)
(declare-fun %Poly%lib!all_blocks.ShadowFreelist. (Poly) lib!all_blocks.ShadowFreelist.)
(declare-fun Poly%lib!block.BlockHdr. (lib!block.BlockHdr.) Poly)
(declare-fun %Poly%lib!block.BlockHdr. (Poly) lib!block.BlockHdr.)
(declare-fun Poly%lib!block.FreeLink. (lib!block.FreeLink.) Poly)
(declare-fun %Poly%lib!block.FreeLink. (Poly) lib!block.FreeLink.)
(declare-fun Poly%lib!block.BlockPerm. (lib!block.BlockPerm.) Poly)
(declare-fun %Poly%lib!block.BlockPerm. (Poly) lib!block.BlockPerm.)
(declare-fun Poly%lib!block.UsedBlockPad. (lib!block.UsedBlockPad.) Poly)
(declare-fun %Poly%lib!block.UsedBlockPad. (Poly) lib!block.UsedBlockPad.)
(declare-fun Poly%lib!Tlsf. (lib!Tlsf.) Poly)
(declare-fun %Poly%lib!Tlsf. (Poly) lib!Tlsf.)
(declare-fun Poly%lib!DeallocToken. (lib!DeallocToken.) Poly)
(declare-fun %Poly%lib!DeallocToken. (Poly) lib!DeallocToken.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)
(declare-fun Poly%tuple%2. (tuple%2.) Poly)
(declare-fun %Poly%tuple%2. (Poly) tuple%2.)
(declare-fun Poly%tuple%3. (tuple%3.) Poly)
(declare-fun %Poly%tuple%3. (Poly) tuple%3.)
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%1. (Poly%fun%1. x)))
   :pattern ((Poly%fun%1. x))
   :qid internal_crate__fun__1_box_axiom_definition
   :skolemid skolem_internal_crate__fun__1_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%fun%1. (%Poly%fun%1. x)))
   )
   :pattern ((has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_unbox_axiom_definition
   :skolemid skolem_internal_crate__fun__1_unbox_axiom_definition
)))
(declare-fun %%apply%%0 (%%Function%% Poly) Poly)
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x %%Function%%)) (!
   (=>
    (forall ((T%0 Poly)) (!
      (=>
       (has_type T%0 T%0&)
       (has_type (%%apply%%0 x T%0) T%1&)
      )
      :pattern ((has_type (%%apply%%0 x T%0) T%1&))
      :qid internal_crate__fun__1_constructor_inner_definition
      :skolemid skolem_internal_crate__fun__1_constructor_inner_definition
    ))
    (has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
   )
   :pattern ((has_type (Poly%fun%1. (mk_fun x)) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__fun__1_constructor_definition
   :skolemid skolem_internal_crate__fun__1_constructor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (has_type (%%apply%%0 x T%0) T%1&)
   )
   :pattern ((%%apply%%0 x T%0) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&.
      T%1&
   )))
   :qid internal_crate__fun__1_apply_definition
   :skolemid skolem_internal_crate__fun__1_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%0 Poly) (x %%Function%%))
  (!
   (=>
    (and
     (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type T%0 T%0&)
    )
    (height_lt (height (%%apply%%0 x T%0)) (height (fun_from_recursive_field (Poly%fun%1.
        (mk_fun x)
   )))))
   :pattern ((height (%%apply%%0 x T%0)) (has_type (Poly%fun%1. x) (TYPE%fun%1. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_crate__fun__1_height_apply_definition
   :skolemid skolem_internal_crate__fun__1_height_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%fun%1. T%0&. T%0& T%1&. T%1&))
     (forall ((T%0 Poly)) (!
       (=>
        (has_type T%0 T%0&)
        (ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1. y) T%0))
       )
       :pattern ((ext_eq deep T%1& (%%apply%%0 (%Poly%fun%1. x) T%0) (%%apply%%0 (%Poly%fun%1.
           y
          ) T%0
       )))
       :qid internal_crate__fun__1_inner_ext_equal_definition
       :skolemid skolem_internal_crate__fun__1_inner_ext_equal_definition
    )))
    (ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%fun%1. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_crate__fun__1_ext_equal_definition
   :skolemid skolem_internal_crate__fun__1_ext_equal_definition
)))
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%fun%2. (Poly%fun%2. x)))
   :pattern ((Poly%fun%2. x))
   :qid internal_crate__fun__2_box_axiom_definition
   :skolemid skolem_internal_crate__fun__2_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    Poly
   )
  ) (!
   (=>
    (has_type x (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
    (= x (Poly%fun%2. (%Poly%fun%2. x)))
   )
   :pattern ((has_type x (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&)))
   :qid internal_crate__fun__2_unbox_axiom_definition
   :skolemid skolem_internal_crate__fun__2_unbox_axiom_definition
)))
(declare-fun %%apply%%1 (%%Function%% Poly Poly) Poly)
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    %%Function%%
   )
  ) (!
   (=>
    (forall ((T%0 Poly) (T%1 Poly)) (!
      (=>
       (and
        (has_type T%0 T%0&)
        (has_type T%1 T%1&)
       )
       (has_type (%%apply%%1 x T%0 T%1) T%2&)
      )
      :pattern ((has_type (%%apply%%1 x T%0 T%1) T%2&))
      :qid internal_crate__fun__2_constructor_inner_definition
      :skolemid skolem_internal_crate__fun__2_constructor_inner_definition
    ))
    (has_type (Poly%fun%2. (mk_fun x)) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
   )
   :pattern ((has_type (Poly%fun%2. (mk_fun x)) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&.
      T%2&
   )))
   :qid internal_crate__fun__2_constructor_definition
   :skolemid skolem_internal_crate__fun__2_constructor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%0
    Poly
   ) (T%1 Poly) (x %%Function%%)
  ) (!
   (=>
    (and
     (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type T%0 T%0&)
     (has_type T%1 T%1&)
    )
    (has_type (%%apply%%1 x T%0 T%1) T%2&)
   )
   :pattern ((%%apply%%1 x T%0 T%1) (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&. T%0& T%1&.
      T%1& T%2&. T%2&
   )))
   :qid internal_crate__fun__2_apply_definition
   :skolemid skolem_internal_crate__fun__2_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (T%0
    Poly
   ) (T%1 Poly) (x %%Function%%)
  ) (!
   (=>
    (and
     (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type T%0 T%0&)
     (has_type T%1 T%1&)
    )
    (height_lt (height (%%apply%%1 x T%0 T%1)) (height (fun_from_recursive_field (Poly%fun%2.
        (mk_fun x)
   )))))
   :pattern ((height (%%apply%%1 x T%0 T%1)) (has_type (Poly%fun%2. x) (TYPE%fun%2. T%0&.
      T%0& T%1&. T%1& T%2&. T%2&
   )))
   :qid internal_crate__fun__2_height_apply_definition
   :skolemid skolem_internal_crate__fun__2_height_apply_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (deep
    Bool
   ) (x Poly) (y Poly)
  ) (!
   (=>
    (and
     (has_type x (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type y (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (forall ((T%0 Poly) (T%1 Poly)) (!
       (=>
        (and
         (has_type T%0 T%0&)
         (has_type T%1 T%1&)
        )
        (ext_eq deep T%2& (%%apply%%1 (%Poly%fun%2. x) T%0 T%1) (%%apply%%1 (%Poly%fun%2. y)
          T%0 T%1
       )))
       :pattern ((ext_eq deep T%2& (%%apply%%1 (%Poly%fun%2. x) T%0 T%1) (%%apply%%1 (%Poly%fun%2.
           y
          ) T%0 T%1
       )))
       :qid internal_crate__fun__2_inner_ext_equal_definition
       :skolemid skolem_internal_crate__fun__2_inner_ext_equal_definition
    )))
    (ext_eq deep (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&) x y)
   )
   :pattern ((ext_eq deep (TYPE%fun%2. T%0&. T%0& T%1&. T%1& T%2&. T%2&) x y))
   :qid internal_crate__fun__2_ext_equal_definition
   :skolemid skolem_internal_crate__fun__2_ext_equal_definition
)))
(assert
 (forall ((x %%Function%%)) (!
   (= x (%Poly%array%. (Poly%array%. x)))
   :pattern ((Poly%array%. x))
   :qid internal_crate__array___box_axiom_definition
   :skolemid skolem_internal_crate__array___box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (x Poly)) (!
   (=>
    (has_type x (ARRAY T&. T& N&. N&))
    (= x (Poly%array%. (%Poly%array%. x)))
   )
   :pattern ((has_type x (ARRAY T&. T& N&. N&)))
   :qid internal_crate__array___unbox_axiom_definition
   :skolemid skolem_internal_crate__array___unbox_axiom_definition
)))
(assert
 (forall ((x alloc!alloc.Global.)) (!
   (= x (%Poly%alloc!alloc.Global. (Poly%alloc!alloc.Global. x)))
   :pattern ((Poly%alloc!alloc.Global. x))
   :qid internal_alloc__alloc__Global_box_axiom_definition
   :skolemid skolem_internal_alloc__alloc__Global_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%alloc!alloc.Global.)
    (= x (Poly%alloc!alloc.Global. (%Poly%alloc!alloc.Global. x)))
   )
   :pattern ((has_type x TYPE%alloc!alloc.Global.))
   :qid internal_alloc__alloc__Global_unbox_axiom_definition
   :skolemid skolem_internal_alloc__alloc__Global_unbox_axiom_definition
)))
(assert
 (forall ((x alloc!alloc.Global.)) (!
   (has_type (Poly%alloc!alloc.Global. x) TYPE%alloc!alloc.Global.)
   :pattern ((has_type (Poly%alloc!alloc.Global. x) TYPE%alloc!alloc.Global.))
   :qid internal_alloc__alloc__Global_has_type_always_definition
   :skolemid skolem_internal_alloc__alloc__Global_has_type_always_definition
)))
(assert
 (forall ((x core!convert.Infallible.)) (!
   (= x (%Poly%core!convert.Infallible. (Poly%core!convert.Infallible. x)))
   :pattern ((Poly%core!convert.Infallible. x))
   :qid internal_core__convert__Infallible_box_axiom_definition
   :skolemid skolem_internal_core__convert__Infallible_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%core!convert.Infallible.)
    (= x (Poly%core!convert.Infallible. (%Poly%core!convert.Infallible. x)))
   )
   :pattern ((has_type x TYPE%core!convert.Infallible.))
   :qid internal_core__convert__Infallible_unbox_axiom_definition
   :skolemid skolem_internal_core__convert__Infallible_unbox_axiom_definition
)))
(assert
 (forall ((x core!convert.Infallible.)) (!
   (has_type (Poly%core!convert.Infallible. x) TYPE%core!convert.Infallible.)
   :pattern ((has_type (Poly%core!convert.Infallible. x) TYPE%core!convert.Infallible.))
   :qid internal_core__convert__Infallible_has_type_always_definition
   :skolemid skolem_internal_core__convert__Infallible_has_type_always_definition
)))
(assert
 (forall ((x lib!half_open_range.HalfOpenRange.)) (!
   (= x (%Poly%lib!half_open_range.HalfOpenRange. (Poly%lib!half_open_range.HalfOpenRange.
      x
   )))
   :pattern ((Poly%lib!half_open_range.HalfOpenRange. x))
   :qid internal_lib__half_open_range__HalfOpenRange_box_axiom_definition
   :skolemid skolem_internal_lib__half_open_range__HalfOpenRange_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!half_open_range.HalfOpenRange.)
    (= x (Poly%lib!half_open_range.HalfOpenRange. (%Poly%lib!half_open_range.HalfOpenRange.
       x
   ))))
   :pattern ((has_type x TYPE%lib!half_open_range.HalfOpenRange.))
   :qid internal_lib__half_open_range__HalfOpenRange_unbox_axiom_definition
   :skolemid skolem_internal_lib__half_open_range__HalfOpenRange_unbox_axiom_definition
)))
(assert
 (forall ((x lib!half_open_range.HalfOpenRange.)) (!
   (has_type (Poly%lib!half_open_range.HalfOpenRange. x) TYPE%lib!half_open_range.HalfOpenRange.)
   :pattern ((has_type (Poly%lib!half_open_range.HalfOpenRange. x) TYPE%lib!half_open_range.HalfOpenRange.))
   :qid internal_lib__half_open_range__HalfOpenRange_has_type_always_definition
   :skolemid skolem_internal_lib__half_open_range__HalfOpenRange_has_type_always_definition
)))
(assert
 (forall ((x vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.)) (!
   (= x (%Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
      x
   )))
   :pattern ((Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. x))
   :qid internal_vstd__map__Map<ptr_mut__<u8.>./ptr_mut__<lib!block.BlockHdr.>.>_box_axiom_definition
   :skolemid skolem_internal_vstd__map__Map<ptr_mut__<u8.>./ptr_mut__<lib!block.BlockHdr.>.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!map.Map. $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)))
    (= x (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (%Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!map.Map. $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.))))
   :qid internal_vstd__map__Map<ptr_mut__<u8.>./ptr_mut__<lib!block.BlockHdr.>.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__map__Map<ptr_mut__<u8.>./ptr_mut__<lib!block.BlockHdr.>.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.)) (!
   (has_type (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. x) (TYPE%vstd!map.Map.
     $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)
   ))
   :pattern ((has_type (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
      x
     ) (TYPE%vstd!map.Map. $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.))
   ))
   :qid internal_vstd__map__Map<ptr_mut__<u8.>./ptr_mut__<lib!block.BlockHdr.>.>_has_type_always_definition
   :skolemid skolem_internal_vstd__map__Map<ptr_mut__<u8.>./ptr_mut__<lib!block.BlockHdr.>.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.)) (
   !
   (= x (%Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
      x
   )))
   :pattern ((Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
     x
   ))
   :qid internal_vstd__map__Map<ptr_mut__<lib!block.BlockHdr.>./lib!block.BlockPerm.>_box_axiom_definition
   :skolemid skolem_internal_vstd__map__Map<ptr_mut__<lib!block.BlockHdr.>./lib!block.BlockPerm.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!map.Map. $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.))
    (= x (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (%Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!map.Map. $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.)))
   :qid internal_vstd__map__Map<ptr_mut__<lib!block.BlockHdr.>./lib!block.BlockPerm.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__map__Map<ptr_mut__<lib!block.BlockHdr.>./lib!block.BlockPerm.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.)) (
   !
   (has_type (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
     x
    ) (TYPE%vstd!map.Map. $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.)
   )
   :pattern ((has_type (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
      x
     ) (TYPE%vstd!map.Map. $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.)
   ))
   :qid internal_vstd__map__Map<ptr_mut__<lib!block.BlockHdr.>./lib!block.BlockPerm.>_has_type_always_definition
   :skolemid skolem_internal_vstd__map__Map<ptr_mut__<lib!block.BlockHdr.>./lib!block.BlockPerm.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.IsExposed.)) (!
   (= x (%Poly%vstd!raw_ptr.IsExposed. (Poly%vstd!raw_ptr.IsExposed. x)))
   :pattern ((Poly%vstd!raw_ptr.IsExposed. x))
   :qid internal_vstd__raw_ptr__IsExposed_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__IsExposed_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.IsExposed.)
    (= x (Poly%vstd!raw_ptr.IsExposed. (%Poly%vstd!raw_ptr.IsExposed. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.IsExposed.))
   :qid internal_vstd__raw_ptr__IsExposed_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__IsExposed_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.IsExposed.)) (!
   (has_type (Poly%vstd!raw_ptr.IsExposed. x) TYPE%vstd!raw_ptr.IsExposed.)
   :pattern ((has_type (Poly%vstd!raw_ptr.IsExposed. x) TYPE%vstd!raw_ptr.IsExposed.))
   :qid internal_vstd__raw_ptr__IsExposed_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__IsExposed_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.)) (!
   (= x (%Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.
      x
   )))
   :pattern ((Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. x))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.BlockHdr.>_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.BlockHdr.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.))
    (= x (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (%Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.BlockHdr.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.BlockHdr.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.)) (!
   (has_type (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. x) (TYPE%vstd!raw_ptr.PointsTo.
     $ TYPE%lib!block.BlockHdr.
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. x) (TYPE%vstd!raw_ptr.PointsTo.
      $ TYPE%lib!block.BlockHdr.
   )))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.BlockHdr.>_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.BlockHdr.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsTo<lib!block.FreeLink.>.)) (!
   (= x (%Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>.
      x
   )))
   :pattern ((Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. x))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.FreeLink.>_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.FreeLink.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.))
    (= x (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (%Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.FreeLink.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.FreeLink.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsTo<lib!block.FreeLink.>.)) (!
   (has_type (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. x) (TYPE%vstd!raw_ptr.PointsTo.
     $ TYPE%lib!block.FreeLink.
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. x) (TYPE%vstd!raw_ptr.PointsTo.
      $ TYPE%lib!block.FreeLink.
   )))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.FreeLink.>_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.FreeLink.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>.)) (!
   (= x (%Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>.
      x
   )))
   :pattern ((Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. x))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.UsedBlockPad.>_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.UsedBlockPad.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.UsedBlockPad.))
    (= x (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. (%Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.UsedBlockPad.)))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.UsedBlockPad.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.UsedBlockPad.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>.)) (!
   (has_type (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. x) (TYPE%vstd!raw_ptr.PointsTo.
     $ TYPE%lib!block.UsedBlockPad.
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. x) (TYPE%vstd!raw_ptr.PointsTo.
      $ TYPE%lib!block.UsedBlockPad.
   )))
   :qid internal_vstd__raw_ptr__PointsTo<lib!block.UsedBlockPad.>_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsTo<lib!block.UsedBlockPad.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToRaw.)) (!
   (= x (%Poly%vstd!raw_ptr.PointsToRaw. (Poly%vstd!raw_ptr.PointsToRaw. x)))
   :pattern ((Poly%vstd!raw_ptr.PointsToRaw. x))
   :qid internal_vstd__raw_ptr__PointsToRaw_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsToRaw_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.PointsToRaw.)
    (= x (Poly%vstd!raw_ptr.PointsToRaw. (%Poly%vstd!raw_ptr.PointsToRaw. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.PointsToRaw.))
   :qid internal_vstd__raw_ptr__PointsToRaw_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsToRaw_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToRaw.)) (!
   (has_type (Poly%vstd!raw_ptr.PointsToRaw. x) TYPE%vstd!raw_ptr.PointsToRaw.)
   :pattern ((has_type (Poly%vstd!raw_ptr.PointsToRaw. x) TYPE%vstd!raw_ptr.PointsToRaw.))
   :qid internal_vstd__raw_ptr__PointsToRaw_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsToRaw_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Provenance.)) (!
   (= x (%Poly%vstd!raw_ptr.Provenance. (Poly%vstd!raw_ptr.Provenance. x)))
   :pattern ((Poly%vstd!raw_ptr.Provenance. x))
   :qid internal_vstd__raw_ptr__Provenance_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__Provenance_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%vstd!raw_ptr.Provenance.)
    (= x (Poly%vstd!raw_ptr.Provenance. (%Poly%vstd!raw_ptr.Provenance. x)))
   )
   :pattern ((has_type x TYPE%vstd!raw_ptr.Provenance.))
   :qid internal_vstd__raw_ptr__Provenance_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__Provenance_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!raw_ptr.Provenance.)) (!
   (has_type (Poly%vstd!raw_ptr.Provenance. x) TYPE%vstd!raw_ptr.Provenance.)
   :pattern ((has_type (Poly%vstd!raw_ptr.Provenance. x) TYPE%vstd!raw_ptr.Provenance.))
   :qid internal_vstd__raw_ptr__Provenance_has_type_always_definition
   :skolemid skolem_internal_vstd__raw_ptr__Provenance_has_type_always_definition
)))
(assert
 (forall ((x vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.)) (!
   (= x (%Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
      x
   )))
   :pattern ((Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. x))
   :qid internal_vstd__seq__Seq<ptr_mut__<lib!block.BlockHdr.>.>_box_axiom_definition
   :skolemid skolem_internal_vstd__seq__Seq<ptr_mut__<lib!block.BlockHdr.>.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)))
    (= x (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (%Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.))))
   :qid internal_vstd__seq__Seq<ptr_mut__<lib!block.BlockHdr.>.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__seq__Seq<ptr_mut__<lib!block.BlockHdr.>.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.)) (!
   (has_type (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. x) (TYPE%vstd!seq.Seq.
     $ (PTR $ TYPE%lib!block.BlockHdr.)
   ))
   :pattern ((has_type (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. x) (TYPE%vstd!seq.Seq.
      $ (PTR $ TYPE%lib!block.BlockHdr.)
   )))
   :qid internal_vstd__seq__Seq<ptr_mut__<lib!block.BlockHdr.>.>_has_type_always_definition
   :skolemid skolem_internal_vstd__seq__Seq<ptr_mut__<lib!block.BlockHdr.>.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<int.>.)) (!
   (= x (%Poly%vstd!set.Set<int.>. (Poly%vstd!set.Set<int.>. x)))
   :pattern ((Poly%vstd!set.Set<int.>. x))
   :qid internal_vstd__set__Set<int.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<int.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ INT))
    (= x (Poly%vstd!set.Set<int.>. (%Poly%vstd!set.Set<int.>. x)))
   )
   :pattern ((has_type x (TYPE%vstd!set.Set. $ INT)))
   :qid internal_vstd__set__Set<int.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<int.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<int.>.)) (!
   (has_type (Poly%vstd!set.Set<int.>. x) (TYPE%vstd!set.Set. $ INT))
   :pattern ((has_type (Poly%vstd!set.Set<int.>. x) (TYPE%vstd!set.Set. $ INT)))
   :qid internal_vstd__set__Set<int.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<int.>_has_type_always_definition
)))
(assert
 (forall ((x vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)) (!
   (= x (%Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. (Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.
      x
   )))
   :pattern ((Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. x))
   :qid internal_vstd__set__Set<ptr_mut__<lib!block.BlockHdr.>.>_box_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<ptr_mut__<lib!block.BlockHdr.>.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!set.Set. $ (PTR $ TYPE%lib!block.BlockHdr.)))
    (= x (Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. (%Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.
       x
   ))))
   :pattern ((has_type x (TYPE%vstd!set.Set. $ (PTR $ TYPE%lib!block.BlockHdr.))))
   :qid internal_vstd__set__Set<ptr_mut__<lib!block.BlockHdr.>.>_unbox_axiom_definition
   :skolemid skolem_internal_vstd__set__Set<ptr_mut__<lib!block.BlockHdr.>.>_unbox_axiom_definition
)))
(assert
 (forall ((x vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)) (!
   (has_type (Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. x) (TYPE%vstd!set.Set.
     $ (PTR $ TYPE%lib!block.BlockHdr.)
   ))
   :pattern ((has_type (Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. x) (TYPE%vstd!set.Set.
      $ (PTR $ TYPE%lib!block.BlockHdr.)
   )))
   :qid internal_vstd__set__Set<ptr_mut__<lib!block.BlockHdr.>.>_has_type_always_definition
   :skolemid skolem_internal_vstd__set__Set<ptr_mut__<lib!block.BlockHdr.>.>_has_type_always_definition
)))
(assert
 (forall ((x ptr_mut%<u8.>.)) (!
   (= x (%Poly%ptr_mut%<u8.>. (Poly%ptr_mut%<u8.>. x)))
   :pattern ((Poly%ptr_mut%<u8.>. x))
   :qid internal_crate__ptr_mut__<u8.>_box_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<u8.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (PTR $ (UINT 8)))
    (= x (Poly%ptr_mut%<u8.>. (%Poly%ptr_mut%<u8.>. x)))
   )
   :pattern ((has_type x (PTR $ (UINT 8))))
   :qid internal_crate__ptr_mut__<u8.>_unbox_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<u8.>_unbox_axiom_definition
)))
(assert
 (forall ((x ptr_mut%<u8.>.)) (!
   (has_type (Poly%ptr_mut%<u8.>. x) (PTR $ (UINT 8)))
   :pattern ((has_type (Poly%ptr_mut%<u8.>. x) (PTR $ (UINT 8))))
   :qid internal_crate__ptr_mut__<u8.>_has_type_always_definition
   :skolemid skolem_internal_crate__ptr_mut__<u8.>_has_type_always_definition
)))
(assert
 (forall ((x ptr_mut%<lib!block.BlockHdr.>.)) (!
   (= x (%Poly%ptr_mut%<lib!block.BlockHdr.>. (Poly%ptr_mut%<lib!block.BlockHdr.>. x)))
   :pattern ((Poly%ptr_mut%<lib!block.BlockHdr.>. x))
   :qid internal_crate__ptr_mut__<lib!block.BlockHdr.>_box_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.BlockHdr.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (PTR $ TYPE%lib!block.BlockHdr.))
    (= x (Poly%ptr_mut%<lib!block.BlockHdr.>. (%Poly%ptr_mut%<lib!block.BlockHdr.>. x)))
   )
   :pattern ((has_type x (PTR $ TYPE%lib!block.BlockHdr.)))
   :qid internal_crate__ptr_mut__<lib!block.BlockHdr.>_unbox_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.BlockHdr.>_unbox_axiom_definition
)))
(assert
 (forall ((x ptr_mut%<lib!block.BlockHdr.>.)) (!
   (has_type (Poly%ptr_mut%<lib!block.BlockHdr.>. x) (PTR $ TYPE%lib!block.BlockHdr.))
   :pattern ((has_type (Poly%ptr_mut%<lib!block.BlockHdr.>. x) (PTR $ TYPE%lib!block.BlockHdr.)))
   :qid internal_crate__ptr_mut__<lib!block.BlockHdr.>_has_type_always_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.BlockHdr.>_has_type_always_definition
)))
(assert
 (forall ((x ptr_mut%<lib!block.FreeLink.>.)) (!
   (= x (%Poly%ptr_mut%<lib!block.FreeLink.>. (Poly%ptr_mut%<lib!block.FreeLink.>. x)))
   :pattern ((Poly%ptr_mut%<lib!block.FreeLink.>. x))
   :qid internal_crate__ptr_mut__<lib!block.FreeLink.>_box_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.FreeLink.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (PTR $ TYPE%lib!block.FreeLink.))
    (= x (Poly%ptr_mut%<lib!block.FreeLink.>. (%Poly%ptr_mut%<lib!block.FreeLink.>. x)))
   )
   :pattern ((has_type x (PTR $ TYPE%lib!block.FreeLink.)))
   :qid internal_crate__ptr_mut__<lib!block.FreeLink.>_unbox_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.FreeLink.>_unbox_axiom_definition
)))
(assert
 (forall ((x ptr_mut%<lib!block.FreeLink.>.)) (!
   (has_type (Poly%ptr_mut%<lib!block.FreeLink.>. x) (PTR $ TYPE%lib!block.FreeLink.))
   :pattern ((has_type (Poly%ptr_mut%<lib!block.FreeLink.>. x) (PTR $ TYPE%lib!block.FreeLink.)))
   :qid internal_crate__ptr_mut__<lib!block.FreeLink.>_has_type_always_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.FreeLink.>_has_type_always_definition
)))
(assert
 (forall ((x ptr_mut%<lib!block.UsedBlockPad.>.)) (!
   (= x (%Poly%ptr_mut%<lib!block.UsedBlockPad.>. (Poly%ptr_mut%<lib!block.UsedBlockPad.>.
      x
   )))
   :pattern ((Poly%ptr_mut%<lib!block.UsedBlockPad.>. x))
   :qid internal_crate__ptr_mut__<lib!block.UsedBlockPad.>_box_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.UsedBlockPad.>_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x (PTR $ TYPE%lib!block.UsedBlockPad.))
    (= x (Poly%ptr_mut%<lib!block.UsedBlockPad.>. (%Poly%ptr_mut%<lib!block.UsedBlockPad.>.
       x
   ))))
   :pattern ((has_type x (PTR $ TYPE%lib!block.UsedBlockPad.)))
   :qid internal_crate__ptr_mut__<lib!block.UsedBlockPad.>_unbox_axiom_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.UsedBlockPad.>_unbox_axiom_definition
)))
(assert
 (forall ((x ptr_mut%<lib!block.UsedBlockPad.>.)) (!
   (has_type (Poly%ptr_mut%<lib!block.UsedBlockPad.>. x) (PTR $ TYPE%lib!block.UsedBlockPad.))
   :pattern ((has_type (Poly%ptr_mut%<lib!block.UsedBlockPad.>. x) (PTR $ TYPE%lib!block.UsedBlockPad.)))
   :qid internal_crate__ptr_mut__<lib!block.UsedBlockPad.>_has_type_always_definition
   :skolemid skolem_internal_crate__ptr_mut__<lib!block.UsedBlockPad.>_has_type_always_definition
)))
(assert
 (forall ((x core!ops.control_flow.ControlFlow.)) (!
   (= x (%Poly%core!ops.control_flow.ControlFlow. (Poly%core!ops.control_flow.ControlFlow.
      x
   )))
   :pattern ((Poly%core!ops.control_flow.ControlFlow. x))
   :qid internal_core__ops__control_flow__ControlFlow_box_axiom_definition
   :skolemid skolem_internal_core__ops__control_flow__ControlFlow_box_axiom_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&))
    (= x (Poly%core!ops.control_flow.ControlFlow. (%Poly%core!ops.control_flow.ControlFlow.
       x
   ))))
   :pattern ((has_type x (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)))
   :qid internal_core__ops__control_flow__ControlFlow_unbox_axiom_definition
   :skolemid skolem_internal_core__ops__control_flow__ControlFlow_unbox_axiom_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (_0! Poly)) (!
   (=>
    (has_type _0! C&)
    (has_type (Poly%core!ops.control_flow.ControlFlow. (core!ops.control_flow.ControlFlow./Continue
       _0!
      )
     ) (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)
   ))
   :pattern ((has_type (Poly%core!ops.control_flow.ControlFlow. (core!ops.control_flow.ControlFlow./Continue
       _0!
      )
     ) (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)
   ))
   :qid internal_core!ops.control_flow.ControlFlow./Continue_constructor_definition
   :skolemid skolem_internal_core!ops.control_flow.ControlFlow./Continue_constructor_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x core!ops.control_flow.ControlFlow.))
  (!
   (=>
    (is-core!ops.control_flow.ControlFlow./Continue x)
    (= (core!ops.control_flow.ControlFlow./Continue/0 B&. B& C&. C& x) (core!ops.control_flow.ControlFlow./Continue/?0
      x
   )))
   :pattern ((core!ops.control_flow.ControlFlow./Continue/0 B&. B& C&. C& x))
   :qid internal_core!ops.control_flow.ControlFlow./Continue/0_accessor_definition
   :skolemid skolem_internal_core!ops.control_flow.ControlFlow./Continue/0_accessor_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&))
    (has_type (core!ops.control_flow.ControlFlow./Continue/0 B&. B& C&. C& (%Poly%core!ops.control_flow.ControlFlow.
       x
      )
     ) C&
   ))
   :pattern ((core!ops.control_flow.ControlFlow./Continue/0 B&. B& C&. C& (%Poly%core!ops.control_flow.ControlFlow.
      x
     )
    ) (has_type x (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&))
   )
   :qid internal_core!ops.control_flow.ControlFlow./Continue/0_invariant_definition
   :skolemid skolem_internal_core!ops.control_flow.ControlFlow./Continue/0_invariant_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (_0! Poly)) (!
   (=>
    (has_type _0! B&)
    (has_type (Poly%core!ops.control_flow.ControlFlow. (core!ops.control_flow.ControlFlow./Break
       _0!
      )
     ) (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)
   ))
   :pattern ((has_type (Poly%core!ops.control_flow.ControlFlow. (core!ops.control_flow.ControlFlow./Break
       _0!
      )
     ) (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)
   ))
   :qid internal_core!ops.control_flow.ControlFlow./Break_constructor_definition
   :skolemid skolem_internal_core!ops.control_flow.ControlFlow./Break_constructor_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x core!ops.control_flow.ControlFlow.))
  (!
   (=>
    (is-core!ops.control_flow.ControlFlow./Break x)
    (= (core!ops.control_flow.ControlFlow./Break/0 B&. B& C&. C& x) (core!ops.control_flow.ControlFlow./Break/?0
      x
   )))
   :pattern ((core!ops.control_flow.ControlFlow./Break/0 B&. B& C&. C& x))
   :qid internal_core!ops.control_flow.ControlFlow./Break/0_accessor_definition
   :skolemid skolem_internal_core!ops.control_flow.ControlFlow./Break/0_accessor_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&))
    (has_type (core!ops.control_flow.ControlFlow./Break/0 B&. B& C&. C& (%Poly%core!ops.control_flow.ControlFlow.
       x
      )
     ) B&
   ))
   :pattern ((core!ops.control_flow.ControlFlow./Break/0 B&. B& C&. C& (%Poly%core!ops.control_flow.ControlFlow.
      x
     )
    ) (has_type x (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&))
   )
   :qid internal_core!ops.control_flow.ControlFlow./Break/0_invariant_definition
   :skolemid skolem_internal_core!ops.control_flow.ControlFlow./Break/0_invariant_definition
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x core!ops.control_flow.ControlFlow.))
  (!
   (=>
    (is-core!ops.control_flow.ControlFlow./Continue x)
    (height_lt (height (core!ops.control_flow.ControlFlow./Continue/0 B&. B& C&. C& x))
     (height (Poly%core!ops.control_flow.ControlFlow. x))
   ))
   :pattern ((height (core!ops.control_flow.ControlFlow./Continue/0 B&. B& C&. C& x)))
   :qid prelude_datatype_height_core!ops.control_flow.ControlFlow./Continue/0
   :skolemid skolem_prelude_datatype_height_core!ops.control_flow.ControlFlow./Continue/0
)))
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type) (x core!ops.control_flow.ControlFlow.))
  (!
   (=>
    (is-core!ops.control_flow.ControlFlow./Break x)
    (height_lt (height (core!ops.control_flow.ControlFlow./Break/0 B&. B& C&. C& x)) (
      height (Poly%core!ops.control_flow.ControlFlow. x)
   )))
   :pattern ((height (core!ops.control_flow.ControlFlow./Break/0 B&. B& C&. C& x)))
   :qid prelude_datatype_height_core!ops.control_flow.ControlFlow./Break/0
   :skolemid skolem_prelude_datatype_height_core!ops.control_flow.ControlFlow./Break/0
)))
(assert
 (forall ((x core!option.Option.)) (!
   (= x (%Poly%core!option.Option. (Poly%core!option.Option. x)))
   :pattern ((Poly%core!option.Option. x))
   :qid internal_core__option__Option_box_axiom_definition
   :skolemid skolem_internal_core__option__Option_box_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (= x (Poly%core!option.Option. (%Poly%core!option.Option. x)))
   )
   :pattern ((has_type x (TYPE%core!option.Option. V&. V&)))
   :qid internal_core__option__Option_unbox_axiom_definition
   :skolemid skolem_internal_core__option__Option_unbox_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
     V&. V&
   ))
   :pattern ((has_type (Poly%core!option.Option. core!option.Option./None) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./None_constructor_definition
   :skolemid skolem_internal_core!option.Option./None_constructor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (_0! Poly)) (!
   (=>
    (has_type _0! V&)
    (has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :pattern ((has_type (Poly%core!option.Option. (core!option.Option./Some _0!)) (TYPE%core!option.Option.
      V&. V&
   )))
   :qid internal_core!option.Option./Some_constructor_definition
   :skolemid skolem_internal_core!option.Option./Some_constructor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x core!option.Option.)) (!
   (=>
    (is-core!option.Option./Some x)
    (= (core!option.Option./Some/0 V&. V& x) (core!option.Option./Some/?0 x))
   )
   :pattern ((core!option.Option./Some/0 V&. V& x))
   :qid internal_core!option.Option./Some/0_accessor_definition
   :skolemid skolem_internal_core!option.Option./Some/0_accessor_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!option.Option. V&. V&))
    (has_type (core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. x)) V&)
   )
   :pattern ((core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. x)) (has_type
     x (TYPE%core!option.Option. V&. V&)
   ))
   :qid internal_core!option.Option./Some/0_invariant_definition
   :skolemid skolem_internal_core!option.Option./Some/0_invariant_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x core!option.Option.)) (!
   (=>
    (is-core!option.Option./Some x)
    (height_lt (height (core!option.Option./Some/0 V&. V& x)) (height (Poly%core!option.Option.
       x
   ))))
   :pattern ((height (core!option.Option./Some/0 V&. V& x)))
   :qid prelude_datatype_height_core!option.Option./Some/0
   :skolemid skolem_prelude_datatype_height_core!option.Option./Some/0
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./None (%Poly%core!option.Option. x))
     (is-core!option.Option./None (%Poly%core!option.Option. y))
    )
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./None_ext_equal_definition
   :skolemid skolem_internal_core!option.Option./None_ext_equal_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (deep Bool) (x Poly) (y Poly)) (!
   (=>
    (and
     (has_type x (TYPE%core!option.Option. V&. V&))
     (has_type y (TYPE%core!option.Option. V&. V&))
     (is-core!option.Option./Some (%Poly%core!option.Option. x))
     (is-core!option.Option./Some (%Poly%core!option.Option. y))
     (ext_eq deep V& (core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. x))
      (core!option.Option./Some/0 V&. V& (%Poly%core!option.Option. y))
    ))
    (ext_eq deep (TYPE%core!option.Option. V&. V&) x y)
   )
   :pattern ((ext_eq deep (TYPE%core!option.Option. V&. V&) x y))
   :qid internal_core!option.Option./Some_ext_equal_definition
   :skolemid skolem_internal_core!option.Option./Some_ext_equal_definition
)))
(assert
 (forall ((x core!marker.PhantomData.)) (!
   (= x (%Poly%core!marker.PhantomData. (Poly%core!marker.PhantomData. x)))
   :pattern ((Poly%core!marker.PhantomData. x))
   :qid internal_core__marker__PhantomData_box_axiom_definition
   :skolemid skolem_internal_core__marker__PhantomData_box_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!marker.PhantomData. V&. V&))
    (= x (Poly%core!marker.PhantomData. (%Poly%core!marker.PhantomData. x)))
   )
   :pattern ((has_type x (TYPE%core!marker.PhantomData. V&. V&)))
   :qid internal_core__marker__PhantomData_unbox_axiom_definition
   :skolemid skolem_internal_core__marker__PhantomData_unbox_axiom_definition
)))
(assert
 (forall ((V&. Dcr) (V& Type) (x core!marker.PhantomData.)) (!
   (has_type (Poly%core!marker.PhantomData. x) (TYPE%core!marker.PhantomData. V&. V&))
   :pattern ((has_type (Poly%core!marker.PhantomData. x) (TYPE%core!marker.PhantomData.
      V&. V&
   )))
   :qid internal_core__marker__PhantomData_has_type_always_definition
   :skolemid skolem_internal_core__marker__PhantomData_has_type_always_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= x (%Poly%vstd!raw_ptr.PtrData. (Poly%vstd!raw_ptr.PtrData. x)))
   :pattern ((Poly%vstd!raw_ptr.PtrData. x))
   :qid internal_vstd__raw_ptr__PtrData_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PtrData_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PtrData. T&. T&))
    (= x (Poly%vstd!raw_ptr.PtrData. (%Poly%vstd!raw_ptr.PtrData. x)))
   )
   :pattern ((has_type x (TYPE%vstd!raw_ptr.PtrData. T&. T&)))
   :qid internal_vstd__raw_ptr__PtrData_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PtrData_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_addr! Int) (_provenance! vstd!raw_ptr.Provenance.) (
    _metadata! Poly
   )
  ) (!
   (=>
    (and
     (uInv SZ _addr!)
     (has_type _metadata! (pointee_metadata% T&.))
    )
    (has_type (Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData./PtrData _addr! _provenance!
       _metadata!
      )
     ) (TYPE%vstd!raw_ptr.PtrData. T&. T&)
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData./PtrData _addr!
       _provenance! _metadata!
      )
     ) (TYPE%vstd!raw_ptr.PtrData. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.PtrData./PtrData_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData_constructor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= (vstd!raw_ptr.PtrData./PtrData/addr x) (vstd!raw_ptr.PtrData./PtrData/?addr x))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/addr x))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/addr_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/addr_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PtrData. T&. T&))
    (uInv SZ (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. x)))
   )
   :pattern ((vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. x)) (has_type
     x (TYPE%vstd!raw_ptr.PtrData. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/addr_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/addr_invariant_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= (vstd!raw_ptr.PtrData./PtrData/provenance x) (vstd!raw_ptr.PtrData./PtrData/?provenance
     x
   ))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/provenance x))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/provenance_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/provenance_accessor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PtrData.)) (!
   (= (vstd!raw_ptr.PtrData./PtrData/metadata x) (vstd!raw_ptr.PtrData./PtrData/?metadata
     x
   ))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/metadata x))
   :qid internal_vstd!raw_ptr.PtrData./PtrData/metadata_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/metadata_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PtrData. T&. T&))
    (has_type (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. x))
     (pointee_metadata% T&.)
   ))
   :pattern ((vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. x))
    (has_type x (TYPE%vstd!raw_ptr.PtrData. T&. T&))
   )
   :qid internal_vstd!raw_ptr.PtrData./PtrData/metadata_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.PtrData./PtrData/metadata_invariant_definition
)))
(assert
 (forall ((x vstd!raw_ptr.MemContents.)) (!
   (= x (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. x)))
   :pattern ((Poly%vstd!raw_ptr.MemContents. x))
   :qid internal_vstd__raw_ptr__MemContents_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__MemContents_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&))
    (= x (Poly%vstd!raw_ptr.MemContents. (%Poly%vstd!raw_ptr.MemContents. x)))
   )
   :pattern ((has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&)))
   :qid internal_vstd__raw_ptr__MemContents_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__MemContents_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (has_type (Poly%vstd!raw_ptr.MemContents. vstd!raw_ptr.MemContents./Uninit) (TYPE%vstd!raw_ptr.MemContents.
     T&. T&
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.MemContents. vstd!raw_ptr.MemContents./Uninit)
     (TYPE%vstd!raw_ptr.MemContents. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.MemContents./Uninit_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Uninit_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_0! Poly)) (!
   (=>
    (has_type _0! T&)
    (has_type (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents./Init _0!)) (TYPE%vstd!raw_ptr.MemContents.
      T&. T&
   )))
   :pattern ((has_type (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.MemContents./Init _0!))
     (TYPE%vstd!raw_ptr.MemContents. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.MemContents./Init_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Init_constructor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x vstd!raw_ptr.MemContents.)) (!
   (=>
    (is-vstd!raw_ptr.MemContents./Init x)
    (= (vstd!raw_ptr.MemContents./Init/0 T&. T& x) (vstd!raw_ptr.MemContents./Init/?0 x))
   )
   :pattern ((vstd!raw_ptr.MemContents./Init/0 T&. T& x))
   :qid internal_vstd!raw_ptr.MemContents./Init/0_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Init/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&))
    (has_type (vstd!raw_ptr.MemContents./Init/0 T&. T& (%Poly%vstd!raw_ptr.MemContents.
       x
      )
     ) T&
   ))
   :pattern ((vstd!raw_ptr.MemContents./Init/0 T&. T& (%Poly%vstd!raw_ptr.MemContents.
      x
     )
    ) (has_type x (TYPE%vstd!raw_ptr.MemContents. T&. T&))
   )
   :qid internal_vstd!raw_ptr.MemContents./Init/0_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.MemContents./Init/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x vstd!raw_ptr.MemContents.)) (!
   (=>
    (is-vstd!raw_ptr.MemContents./Init x)
    (height_lt (height (vstd!raw_ptr.MemContents./Init/0 T&. T& x)) (height (Poly%vstd!raw_ptr.MemContents.
       x
   ))))
   :pattern ((height (vstd!raw_ptr.MemContents./Init/0 T&. T& x)))
   :qid prelude_datatype_height_vstd!raw_ptr.MemContents./Init/0
   :skolemid skolem_prelude_datatype_height_vstd!raw_ptr.MemContents./Init/0
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToData.)) (!
   (= x (%Poly%vstd!raw_ptr.PointsToData. (Poly%vstd!raw_ptr.PointsToData. x)))
   :pattern ((Poly%vstd!raw_ptr.PointsToData. x))
   :qid internal_vstd__raw_ptr__PointsToData_box_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsToData_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PointsToData. T&. T&))
    (= x (Poly%vstd!raw_ptr.PointsToData. (%Poly%vstd!raw_ptr.PointsToData. x)))
   )
   :pattern ((has_type x (TYPE%vstd!raw_ptr.PointsToData. T&. T&)))
   :qid internal_vstd__raw_ptr__PointsToData_unbox_axiom_definition
   :skolemid skolem_internal_vstd__raw_ptr__PointsToData_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (_ptr! Poly) (_opt_value! vstd!raw_ptr.MemContents.))
  (!
   (=>
    (and
     (has_type _ptr! (PTR T&. T&))
     (has_type (Poly%vstd!raw_ptr.MemContents. _opt_value!) (TYPE%vstd!raw_ptr.MemContents.
       T&. T&
    )))
    (has_type (Poly%vstd!raw_ptr.PointsToData. (vstd!raw_ptr.PointsToData./PointsToData
       _ptr! _opt_value!
      )
     ) (TYPE%vstd!raw_ptr.PointsToData. T&. T&)
   ))
   :pattern ((has_type (Poly%vstd!raw_ptr.PointsToData. (vstd!raw_ptr.PointsToData./PointsToData
       _ptr! _opt_value!
      )
     ) (TYPE%vstd!raw_ptr.PointsToData. T&. T&)
   ))
   :qid internal_vstd!raw_ptr.PointsToData./PointsToData_constructor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PointsToData./PointsToData_constructor_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToData.)) (!
   (= (vstd!raw_ptr.PointsToData./PointsToData/ptr x) (vstd!raw_ptr.PointsToData./PointsToData/?ptr
     x
   ))
   :pattern ((vstd!raw_ptr.PointsToData./PointsToData/ptr x))
   :qid internal_vstd!raw_ptr.PointsToData./PointsToData/ptr_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PointsToData./PointsToData/ptr_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PointsToData. T&. T&))
    (has_type (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData.
       x
      )
     ) (PTR T&. T&)
   ))
   :pattern ((vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData.
      x
     )
    ) (has_type x (TYPE%vstd!raw_ptr.PointsToData. T&. T&))
   )
   :qid internal_vstd!raw_ptr.PointsToData./PointsToData/ptr_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.PointsToData./PointsToData/ptr_invariant_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToData.)) (!
   (= (vstd!raw_ptr.PointsToData./PointsToData/opt_value x) (vstd!raw_ptr.PointsToData./PointsToData/?opt_value
     x
   ))
   :pattern ((vstd!raw_ptr.PointsToData./PointsToData/opt_value x))
   :qid internal_vstd!raw_ptr.PointsToData./PointsToData/opt_value_accessor_definition
   :skolemid skolem_internal_vstd!raw_ptr.PointsToData./PointsToData/opt_value_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%vstd!raw_ptr.PointsToData. T&. T&))
    (has_type (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
       (%Poly%vstd!raw_ptr.PointsToData. x)
      )
     ) (TYPE%vstd!raw_ptr.MemContents. T&. T&)
   ))
   :pattern ((vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
      x
     )
    ) (has_type x (TYPE%vstd!raw_ptr.PointsToData. T&. T&))
   )
   :qid internal_vstd!raw_ptr.PointsToData./PointsToData/opt_value_invariant_definition
   :skolemid skolem_internal_vstd!raw_ptr.PointsToData./PointsToData/opt_value_invariant_definition
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToData.)) (!
   (=>
    (is-vstd!raw_ptr.PointsToData./PointsToData x)
    (height_lt (height (vstd!raw_ptr.PointsToData./PointsToData/ptr x)) (height (Poly%vstd!raw_ptr.PointsToData.
       x
   ))))
   :pattern ((height (vstd!raw_ptr.PointsToData./PointsToData/ptr x)))
   :qid prelude_datatype_height_vstd!raw_ptr.PointsToData./PointsToData/ptr
   :skolemid skolem_prelude_datatype_height_vstd!raw_ptr.PointsToData./PointsToData/ptr
)))
(assert
 (forall ((x vstd!raw_ptr.PointsToData.)) (!
   (=>
    (is-vstd!raw_ptr.PointsToData./PointsToData x)
    (height_lt (height (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
        x
      ))
     ) (height (Poly%vstd!raw_ptr.PointsToData. x))
   ))
   :pattern ((height (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
       x
   ))))
   :qid prelude_datatype_height_vstd!raw_ptr.PointsToData./PointsToData/opt_value
   :skolemid skolem_prelude_datatype_height_vstd!raw_ptr.PointsToData./PointsToData/opt_value
)))
(assert
 (forall ((x lib!block_index.BlockIndex.)) (!
   (= x (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex. x)))
   :pattern ((Poly%lib!block_index.BlockIndex. x))
   :qid internal_lib__block_index__BlockIndex_box_axiom_definition
   :skolemid skolem_internal_lib__block_index__BlockIndex_box_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (= x (Poly%lib!block_index.BlockIndex. (%Poly%lib!block_index.BlockIndex. x)))
   )
   :pattern ((has_type x (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)))
   :qid internal_lib__block_index__BlockIndex_unbox_axiom_definition
   :skolemid skolem_internal_lib__block_index__BlockIndex_unbox_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (_0! Int) (_1! Int))
  (!
   (=>
    (and
     (uInv SZ _0!)
     (uInv SZ _1!)
    )
    (has_type (Poly%lib!block_index.BlockIndex. (lib!block_index.BlockIndex./BlockIndex
       _0! _1!
      )
     ) (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((has_type (Poly%lib!block_index.BlockIndex. (lib!block_index.BlockIndex./BlockIndex
       _0! _1!
      )
     ) (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :qid internal_lib!block_index.BlockIndex./BlockIndex_constructor_definition
   :skolemid skolem_internal_lib!block_index.BlockIndex./BlockIndex_constructor_definition
)))
(assert
 (forall ((x lib!block_index.BlockIndex.)) (!
   (= (lib!block_index.BlockIndex./BlockIndex/0 x) (lib!block_index.BlockIndex./BlockIndex/?0
     x
   ))
   :pattern ((lib!block_index.BlockIndex./BlockIndex/0 x))
   :qid internal_lib!block_index.BlockIndex./BlockIndex/0_accessor_definition
   :skolemid skolem_internal_lib!block_index.BlockIndex./BlockIndex/0_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (uInv SZ (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex.
       x
   ))))
   :pattern ((lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex.
      x
     )
    ) (has_type x (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
   )
   :qid internal_lib!block_index.BlockIndex./BlockIndex/0_invariant_definition
   :skolemid skolem_internal_lib!block_index.BlockIndex./BlockIndex/0_invariant_definition
)))
(assert
 (forall ((x lib!block_index.BlockIndex.)) (!
   (= (lib!block_index.BlockIndex./BlockIndex/1 x) (lib!block_index.BlockIndex./BlockIndex/?1
     x
   ))
   :pattern ((lib!block_index.BlockIndex./BlockIndex/1 x))
   :qid internal_lib!block_index.BlockIndex./BlockIndex/1_accessor_definition
   :skolemid skolem_internal_lib!block_index.BlockIndex./BlockIndex/1_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (uInv SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
       x
   ))))
   :pattern ((lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
      x
     )
    ) (has_type x (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
   )
   :qid internal_lib!block_index.BlockIndex./BlockIndex/1_invariant_definition
   :skolemid skolem_internal_lib!block_index.BlockIndex./BlockIndex/1_invariant_definition
)))
(assert
 (forall ((x lib!all_blocks.AllBlocks.)) (!
   (= x (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. x)))
   :pattern ((Poly%lib!all_blocks.AllBlocks. x))
   :qid internal_lib__all_blocks__AllBlocks_box_axiom_definition
   :skolemid skolem_internal_lib__all_blocks__AllBlocks_box_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!all_blocks.AllBlocks. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (= x (Poly%lib!all_blocks.AllBlocks. (%Poly%lib!all_blocks.AllBlocks. x)))
   )
   :pattern ((has_type x (TYPE%lib!all_blocks.AllBlocks. FLLEN&. FLLEN& SLLEN&. SLLEN&)))
   :qid internal_lib__all_blocks__AllBlocks_unbox_axiom_definition
   :skolemid skolem_internal_lib__all_blocks__AllBlocks_unbox_axiom_definition
)))
(assert
 (forall ((x lib!all_blocks.AllBlocks.)) (!
   (= (lib!all_blocks.AllBlocks./AllBlocks/ptrs x) (lib!all_blocks.AllBlocks./AllBlocks/?ptrs
     x
   ))
   :pattern ((lib!all_blocks.AllBlocks./AllBlocks/ptrs x))
   :qid internal_lib!all_blocks.AllBlocks./AllBlocks/ptrs_accessor_definition
   :skolemid skolem_internal_lib!all_blocks.AllBlocks./AllBlocks/ptrs_accessor_definition
)))
(assert
 (forall ((x lib!all_blocks.AllBlocks.)) (!
   (= (lib!all_blocks.AllBlocks./AllBlocks/perms x) (lib!all_blocks.AllBlocks./AllBlocks/?perms
     x
   ))
   :pattern ((lib!all_blocks.AllBlocks./AllBlocks/perms x))
   :qid internal_lib!all_blocks.AllBlocks./AllBlocks/perms_accessor_definition
   :skolemid skolem_internal_lib!all_blocks.AllBlocks./AllBlocks/perms_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x lib!all_blocks.AllBlocks.))
  (!
   (has_type (Poly%lib!all_blocks.AllBlocks. x) (TYPE%lib!all_blocks.AllBlocks. FLLEN&.
     FLLEN& SLLEN&. SLLEN&
   ))
   :pattern ((has_type (Poly%lib!all_blocks.AllBlocks. x) (TYPE%lib!all_blocks.AllBlocks.
      FLLEN&. FLLEN& SLLEN&. SLLEN&
   )))
   :qid internal_lib__all_blocks__AllBlocks_has_type_always_definition
   :skolemid skolem_internal_lib__all_blocks__AllBlocks_has_type_always_definition
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (= x (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. x)))
   :pattern ((Poly%lib!all_blocks.ShadowFreelist. x))
   :qid internal_lib__all_blocks__ShadowFreelist_box_axiom_definition
   :skolemid skolem_internal_lib__all_blocks__ShadowFreelist_box_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (= x (Poly%lib!all_blocks.ShadowFreelist. (%Poly%lib!all_blocks.ShadowFreelist. x)))
   )
   :pattern ((has_type x (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&)))
   :qid internal_lib__all_blocks__ShadowFreelist_unbox_axiom_definition
   :skolemid skolem_internal_lib__all_blocks__ShadowFreelist_unbox_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (_m! Poly) (_pi! Poly))
  (!
   (=>
    (and
     (has_type _m! (TYPE%vstd!map.Map. $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN&
        SLLEN&. SLLEN&
       ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.))
     ))
     (has_type _pi! (TYPE%vstd!map.Map. (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
         FLLEN&. FLLEN& SLLEN&. SLLEN&
        ) $ INT
       ) $ INT
    )))
    (has_type (Poly%lib!all_blocks.ShadowFreelist. (lib!all_blocks.ShadowFreelist./ShadowFreelist
       _m! _pi!
      )
     ) (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((has_type (Poly%lib!all_blocks.ShadowFreelist. (lib!all_blocks.ShadowFreelist./ShadowFreelist
       _m! _pi!
      )
     ) (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :qid internal_lib!all_blocks.ShadowFreelist./ShadowFreelist_constructor_definition
   :skolemid skolem_internal_lib!all_blocks.ShadowFreelist./ShadowFreelist_constructor_definition
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (= (lib!all_blocks.ShadowFreelist./ShadowFreelist/m x) (lib!all_blocks.ShadowFreelist./ShadowFreelist/?m
     x
   ))
   :pattern ((lib!all_blocks.ShadowFreelist./ShadowFreelist/m x))
   :qid internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/m_accessor_definition
   :skolemid skolem_internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/m_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
       x
      )
     ) (TYPE%vstd!map.Map. $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
      $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.))
   )))
   :pattern ((lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
      x
     )
    ) (has_type x (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
   )
   :qid internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/m_invariant_definition
   :skolemid skolem_internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/m_invariant_definition
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (= (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi x) (lib!all_blocks.ShadowFreelist./ShadowFreelist/?pi
     x
   ))
   :pattern ((lib!all_blocks.ShadowFreelist./ShadowFreelist/pi x))
   :qid internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi_accessor_definition
   :skolemid skolem_internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
       x
      )
     ) (TYPE%vstd!map.Map. (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex. FLLEN&.
        FLLEN& SLLEN&. SLLEN&
       ) $ INT
      ) $ INT
   )))
   :pattern ((lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
      x
     )
    ) (has_type x (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
   )
   :qid internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi_invariant_definition
   :skolemid skolem_internal_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi_invariant_definition
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (=>
    (is-lib!all_blocks.ShadowFreelist./ShadowFreelist x)
    (height_lt (height (lib!all_blocks.ShadowFreelist./ShadowFreelist/m x)) (height (Poly%lib!all_blocks.ShadowFreelist.
       x
   ))))
   :pattern ((height (lib!all_blocks.ShadowFreelist./ShadowFreelist/m x)))
   :qid prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/m
   :skolemid skolem_prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/m
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (=>
    (is-lib!all_blocks.ShadowFreelist./ShadowFreelist x)
    (height_lt (height (fun_from_recursive_field (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
        x
      ))
     ) (height (Poly%lib!all_blocks.ShadowFreelist. x))
   ))
   :pattern ((height (fun_from_recursive_field (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
       x
   ))))
   :qid prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/m
   :skolemid skolem_prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/m
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (=>
    (is-lib!all_blocks.ShadowFreelist./ShadowFreelist x)
    (height_lt (height (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi x)) (height (Poly%lib!all_blocks.ShadowFreelist.
       x
   ))))
   :pattern ((height (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi x)))
   :qid prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi
   :skolemid skolem_prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi
)))
(assert
 (forall ((x lib!all_blocks.ShadowFreelist.)) (!
   (=>
    (is-lib!all_blocks.ShadowFreelist./ShadowFreelist x)
    (height_lt (height (fun_from_recursive_field (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi
        x
      ))
     ) (height (Poly%lib!all_blocks.ShadowFreelist. x))
   ))
   :pattern ((height (fun_from_recursive_field (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi
       x
   ))))
   :qid prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi
   :skolemid skolem_prelude_datatype_height_lib!all_blocks.ShadowFreelist./ShadowFreelist/pi
)))
(assert
 (forall ((x lib!block.BlockHdr.)) (!
   (= x (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr. x)))
   :pattern ((Poly%lib!block.BlockHdr. x))
   :qid internal_lib__block__BlockHdr_box_axiom_definition
   :skolemid skolem_internal_lib__block__BlockHdr_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.BlockHdr.)
    (= x (Poly%lib!block.BlockHdr. (%Poly%lib!block.BlockHdr. x)))
   )
   :pattern ((has_type x TYPE%lib!block.BlockHdr.))
   :qid internal_lib__block__BlockHdr_unbox_axiom_definition
   :skolemid skolem_internal_lib__block__BlockHdr_unbox_axiom_definition
)))
(assert
 (forall ((_size! Int) (_prev_phys_block! ptr_mut%<lib!block.BlockHdr.>.)) (!
   (=>
    (uInv SZ _size!)
    (has_type (Poly%lib!block.BlockHdr. (lib!block.BlockHdr./BlockHdr _size! _prev_phys_block!))
     TYPE%lib!block.BlockHdr.
   ))
   :pattern ((has_type (Poly%lib!block.BlockHdr. (lib!block.BlockHdr./BlockHdr _size! _prev_phys_block!))
     TYPE%lib!block.BlockHdr.
   ))
   :qid internal_lib!block.BlockHdr./BlockHdr_constructor_definition
   :skolemid skolem_internal_lib!block.BlockHdr./BlockHdr_constructor_definition
)))
(assert
 (forall ((x lib!block.BlockHdr.)) (!
   (= (lib!block.BlockHdr./BlockHdr/size x) (lib!block.BlockHdr./BlockHdr/?size x))
   :pattern ((lib!block.BlockHdr./BlockHdr/size x))
   :qid internal_lib!block.BlockHdr./BlockHdr/size_accessor_definition
   :skolemid skolem_internal_lib!block.BlockHdr./BlockHdr/size_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.BlockHdr.)
    (uInv SZ (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. x)))
   )
   :pattern ((lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. x)) (has_type
     x TYPE%lib!block.BlockHdr.
   ))
   :qid internal_lib!block.BlockHdr./BlockHdr/size_invariant_definition
   :skolemid skolem_internal_lib!block.BlockHdr./BlockHdr/size_invariant_definition
)))
(assert
 (forall ((x lib!block.BlockHdr.)) (!
   (= (lib!block.BlockHdr./BlockHdr/prev_phys_block x) (lib!block.BlockHdr./BlockHdr/?prev_phys_block
     x
   ))
   :pattern ((lib!block.BlockHdr./BlockHdr/prev_phys_block x))
   :qid internal_lib!block.BlockHdr./BlockHdr/prev_phys_block_accessor_definition
   :skolemid skolem_internal_lib!block.BlockHdr./BlockHdr/prev_phys_block_accessor_definition
)))
(assert
 (forall ((x lib!block.FreeLink.)) (!
   (= x (%Poly%lib!block.FreeLink. (Poly%lib!block.FreeLink. x)))
   :pattern ((Poly%lib!block.FreeLink. x))
   :qid internal_lib__block__FreeLink_box_axiom_definition
   :skolemid skolem_internal_lib__block__FreeLink_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.FreeLink.)
    (= x (Poly%lib!block.FreeLink. (%Poly%lib!block.FreeLink. x)))
   )
   :pattern ((has_type x TYPE%lib!block.FreeLink.))
   :qid internal_lib__block__FreeLink_unbox_axiom_definition
   :skolemid skolem_internal_lib__block__FreeLink_unbox_axiom_definition
)))
(assert
 (forall ((x lib!block.FreeLink.)) (!
   (= (lib!block.FreeLink./FreeLink/next_free x) (lib!block.FreeLink./FreeLink/?next_free
     x
   ))
   :pattern ((lib!block.FreeLink./FreeLink/next_free x))
   :qid internal_lib!block.FreeLink./FreeLink/next_free_accessor_definition
   :skolemid skolem_internal_lib!block.FreeLink./FreeLink/next_free_accessor_definition
)))
(assert
 (forall ((x lib!block.FreeLink.)) (!
   (= (lib!block.FreeLink./FreeLink/prev_free x) (lib!block.FreeLink./FreeLink/?prev_free
     x
   ))
   :pattern ((lib!block.FreeLink./FreeLink/prev_free x))
   :qid internal_lib!block.FreeLink./FreeLink/prev_free_accessor_definition
   :skolemid skolem_internal_lib!block.FreeLink./FreeLink/prev_free_accessor_definition
)))
(assert
 (forall ((x lib!block.FreeLink.)) (!
   (has_type (Poly%lib!block.FreeLink. x) TYPE%lib!block.FreeLink.)
   :pattern ((has_type (Poly%lib!block.FreeLink. x) TYPE%lib!block.FreeLink.))
   :qid internal_lib__block__FreeLink_has_type_always_definition
   :skolemid skolem_internal_lib__block__FreeLink_has_type_always_definition
)))
(assert
 (forall ((x lib!block.BlockPerm.)) (!
   (= x (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. x)))
   :pattern ((Poly%lib!block.BlockPerm. x))
   :qid internal_lib__block__BlockPerm_box_axiom_definition
   :skolemid skolem_internal_lib__block__BlockPerm_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.BlockPerm.)
    (= x (Poly%lib!block.BlockPerm. (%Poly%lib!block.BlockPerm. x)))
   )
   :pattern ((has_type x TYPE%lib!block.BlockPerm.))
   :qid internal_lib__block__BlockPerm_unbox_axiom_definition
   :skolemid skolem_internal_lib__block__BlockPerm_unbox_axiom_definition
)))
(assert
 (forall ((_points_to! vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.) (_free_link_perm!
    core!option.Option.
   ) (_mem! vstd!raw_ptr.PointsToRaw.) (_overhead_mem! vstd!raw_ptr.PointsToRaw.) (_pad_perm!
    core!option.Option.
   )
  ) (!
   (=>
    (and
     (has_type (Poly%core!option.Option. _free_link_perm!) (TYPE%core!option.Option. $ (
        TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.
     )))
     (has_type (Poly%core!option.Option. _pad_perm!) (TYPE%core!option.Option. $ (TYPE%vstd!raw_ptr.PointsTo.
        $ TYPE%lib!block.UsedBlockPad.
    ))))
    (has_type (Poly%lib!block.BlockPerm. (lib!block.BlockPerm./BlockPerm _points_to! _free_link_perm!
       _mem! _overhead_mem! _pad_perm!
      )
     ) TYPE%lib!block.BlockPerm.
   ))
   :pattern ((has_type (Poly%lib!block.BlockPerm. (lib!block.BlockPerm./BlockPerm _points_to!
       _free_link_perm! _mem! _overhead_mem! _pad_perm!
      )
     ) TYPE%lib!block.BlockPerm.
   ))
   :qid internal_lib!block.BlockPerm./BlockPerm_constructor_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm_constructor_definition
)))
(assert
 (forall ((x lib!block.BlockPerm.)) (!
   (= (lib!block.BlockPerm./BlockPerm/points_to x) (lib!block.BlockPerm./BlockPerm/?points_to
     x
   ))
   :pattern ((lib!block.BlockPerm./BlockPerm/points_to x))
   :qid internal_lib!block.BlockPerm./BlockPerm/points_to_accessor_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/points_to_accessor_definition
)))
(assert
 (forall ((x lib!block.BlockPerm.)) (!
   (= (lib!block.BlockPerm./BlockPerm/free_link_perm x) (lib!block.BlockPerm./BlockPerm/?free_link_perm
     x
   ))
   :pattern ((lib!block.BlockPerm./BlockPerm/free_link_perm x))
   :qid internal_lib!block.BlockPerm./BlockPerm/free_link_perm_accessor_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/free_link_perm_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.BlockPerm.)
    (has_type (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm (
        %Poly%lib!block.BlockPerm. x
      ))
     ) (TYPE%core!option.Option. $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.))
   ))
   :pattern ((lib!block.BlockPerm./BlockPerm/free_link_perm (%Poly%lib!block.BlockPerm.
      x
     )
    ) (has_type x TYPE%lib!block.BlockPerm.)
   )
   :qid internal_lib!block.BlockPerm./BlockPerm/free_link_perm_invariant_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/free_link_perm_invariant_definition
)))
(assert
 (forall ((x lib!block.BlockPerm.)) (!
   (= (lib!block.BlockPerm./BlockPerm/mem x) (lib!block.BlockPerm./BlockPerm/?mem x))
   :pattern ((lib!block.BlockPerm./BlockPerm/mem x))
   :qid internal_lib!block.BlockPerm./BlockPerm/mem_accessor_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/mem_accessor_definition
)))
(assert
 (forall ((x lib!block.BlockPerm.)) (!
   (= (lib!block.BlockPerm./BlockPerm/overhead_mem x) (lib!block.BlockPerm./BlockPerm/?overhead_mem
     x
   ))
   :pattern ((lib!block.BlockPerm./BlockPerm/overhead_mem x))
   :qid internal_lib!block.BlockPerm./BlockPerm/overhead_mem_accessor_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/overhead_mem_accessor_definition
)))
(assert
 (forall ((x lib!block.BlockPerm.)) (!
   (= (lib!block.BlockPerm./BlockPerm/pad_perm x) (lib!block.BlockPerm./BlockPerm/?pad_perm
     x
   ))
   :pattern ((lib!block.BlockPerm./BlockPerm/pad_perm x))
   :qid internal_lib!block.BlockPerm./BlockPerm/pad_perm_accessor_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/pad_perm_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.BlockPerm.)
    (has_type (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm.
        x
      ))
     ) (TYPE%core!option.Option. $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.UsedBlockPad.))
   ))
   :pattern ((lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm. x))
    (has_type x TYPE%lib!block.BlockPerm.)
   )
   :qid internal_lib!block.BlockPerm./BlockPerm/pad_perm_invariant_definition
   :skolemid skolem_internal_lib!block.BlockPerm./BlockPerm/pad_perm_invariant_definition
)))
(assert
 (forall ((x lib!block.UsedBlockPad.)) (!
   (= x (%Poly%lib!block.UsedBlockPad. (Poly%lib!block.UsedBlockPad. x)))
   :pattern ((Poly%lib!block.UsedBlockPad. x))
   :qid internal_lib__block__UsedBlockPad_box_axiom_definition
   :skolemid skolem_internal_lib__block__UsedBlockPad_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!block.UsedBlockPad.)
    (= x (Poly%lib!block.UsedBlockPad. (%Poly%lib!block.UsedBlockPad. x)))
   )
   :pattern ((has_type x TYPE%lib!block.UsedBlockPad.))
   :qid internal_lib__block__UsedBlockPad_unbox_axiom_definition
   :skolemid skolem_internal_lib__block__UsedBlockPad_unbox_axiom_definition
)))
(assert
 (forall ((x lib!block.UsedBlockPad.)) (!
   (= (lib!block.UsedBlockPad./UsedBlockPad/block_hdr x) (lib!block.UsedBlockPad./UsedBlockPad/?block_hdr
     x
   ))
   :pattern ((lib!block.UsedBlockPad./UsedBlockPad/block_hdr x))
   :qid internal_lib!block.UsedBlockPad./UsedBlockPad/block_hdr_accessor_definition
   :skolemid skolem_internal_lib!block.UsedBlockPad./UsedBlockPad/block_hdr_accessor_definition
)))
(assert
 (forall ((x lib!block.UsedBlockPad.)) (!
   (has_type (Poly%lib!block.UsedBlockPad. x) TYPE%lib!block.UsedBlockPad.)
   :pattern ((has_type (Poly%lib!block.UsedBlockPad. x) TYPE%lib!block.UsedBlockPad.))
   :qid internal_lib__block__UsedBlockPad_has_type_always_definition
   :skolemid skolem_internal_lib__block__UsedBlockPad_has_type_always_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= x (%Poly%lib!Tlsf. (Poly%lib!Tlsf. x)))
   :pattern ((Poly%lib!Tlsf. x))
   :qid internal_lib__Tlsf_box_axiom_definition
   :skolemid skolem_internal_lib__Tlsf_box_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (= x (Poly%lib!Tlsf. (%Poly%lib!Tlsf. x)))
   )
   :pattern ((has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&)))
   :qid internal_lib__Tlsf_unbox_axiom_definition
   :skolemid skolem_internal_lib__Tlsf_unbox_axiom_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (_fl_bitmap! Int)
   (_sl_bitmap! %%Function%%) (_first_free! %%Function%%) (__phantom! core!marker.PhantomData.)
   (_valid_range! vstd!set.Set<int.>.) (_all_blocks! lib!all_blocks.AllBlocks.) (_root_provenances!
    core!option.Option.
   ) (_shadow_freelist! lib!all_blocks.ShadowFreelist.) (_user_block_map! vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.)
  ) (!
   (=>
    (and
     (uInv SZ _fl_bitmap!)
     (has_type (Poly%array%. _sl_bitmap!) (ARRAY $ USIZE FLLEN&. FLLEN&))
     (has_type (Poly%array%. _first_free!) (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.)
        SLLEN&. SLLEN&
       ) FLLEN&. FLLEN&
     ))
     (has_type (Poly%core!option.Option. _root_provenances!) (TYPE%core!option.Option. $
       TYPE%vstd!raw_ptr.IsExposed.
     ))
     (has_type (Poly%lib!all_blocks.ShadowFreelist. _shadow_freelist!) (TYPE%lib!all_blocks.ShadowFreelist.
       FLLEN&. FLLEN& SLLEN&. SLLEN&
    )))
    (has_type (Poly%lib!Tlsf. (lib!Tlsf./Tlsf _fl_bitmap! _sl_bitmap! _first_free! __phantom!
       _valid_range! _all_blocks! _root_provenances! _shadow_freelist! _user_block_map!
      )
     ) (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((has_type (Poly%lib!Tlsf. (lib!Tlsf./Tlsf _fl_bitmap! _sl_bitmap! _first_free!
       __phantom! _valid_range! _all_blocks! _root_provenances! _shadow_freelist! _user_block_map!
      )
     ) (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :qid internal_lib!Tlsf./Tlsf_constructor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf_constructor_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/fl_bitmap x) (lib!Tlsf./Tlsf/?fl_bitmap x))
   :pattern ((lib!Tlsf./Tlsf/fl_bitmap x))
   :qid internal_lib!Tlsf./Tlsf/fl_bitmap_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/fl_bitmap_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (uInv SZ (lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf. x)))
   )
   :pattern ((lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf. x)) (has_type x (TYPE%lib!Tlsf.
      FLLEN&. FLLEN& SLLEN&. SLLEN&
   )))
   :qid internal_lib!Tlsf./Tlsf/fl_bitmap_invariant_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/fl_bitmap_invariant_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/sl_bitmap x) (lib!Tlsf./Tlsf/?sl_bitmap x))
   :pattern ((lib!Tlsf./Tlsf/sl_bitmap x))
   :qid internal_lib!Tlsf./Tlsf/sl_bitmap_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/sl_bitmap_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. x))) (ARRAY $ USIZE
      FLLEN&. FLLEN&
   )))
   :pattern ((lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. x)) (has_type x (TYPE%lib!Tlsf.
      FLLEN&. FLLEN& SLLEN&. SLLEN&
   )))
   :qid internal_lib!Tlsf./Tlsf/sl_bitmap_invariant_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/sl_bitmap_invariant_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/first_free x) (lib!Tlsf./Tlsf/?first_free x))
   :pattern ((lib!Tlsf./Tlsf/first_free x))
   :qid internal_lib!Tlsf./Tlsf/first_free_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/first_free_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. x))) (ARRAY $ (
       ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&
      ) FLLEN&. FLLEN&
   )))
   :pattern ((lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. x)) (has_type x (TYPE%lib!Tlsf.
      FLLEN&. FLLEN& SLLEN&. SLLEN&
   )))
   :qid internal_lib!Tlsf./Tlsf/first_free_invariant_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/first_free_invariant_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/_phantom x) (lib!Tlsf./Tlsf/?_phantom x))
   :pattern ((lib!Tlsf./Tlsf/_phantom x))
   :qid internal_lib!Tlsf./Tlsf/_phantom_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/_phantom_accessor_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/valid_range x) (lib!Tlsf./Tlsf/?valid_range x))
   :pattern ((lib!Tlsf./Tlsf/valid_range x))
   :qid internal_lib!Tlsf./Tlsf/valid_range_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/valid_range_accessor_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/all_blocks x) (lib!Tlsf./Tlsf/?all_blocks x))
   :pattern ((lib!Tlsf./Tlsf/all_blocks x))
   :qid internal_lib!Tlsf./Tlsf/all_blocks_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/all_blocks_accessor_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/root_provenances x) (lib!Tlsf./Tlsf/?root_provenances x))
   :pattern ((lib!Tlsf./Tlsf/root_provenances x))
   :qid internal_lib!Tlsf./Tlsf/root_provenances_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/root_provenances_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (Poly%core!option.Option. (lib!Tlsf./Tlsf/root_provenances (%Poly%lib!Tlsf.
        x
      ))
     ) (TYPE%core!option.Option. $ TYPE%vstd!raw_ptr.IsExposed.)
   ))
   :pattern ((lib!Tlsf./Tlsf/root_provenances (%Poly%lib!Tlsf. x)) (has_type x (TYPE%lib!Tlsf.
      FLLEN&. FLLEN& SLLEN&. SLLEN&
   )))
   :qid internal_lib!Tlsf./Tlsf/root_provenances_invariant_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/root_provenances_invariant_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/shadow_freelist x) (lib!Tlsf./Tlsf/?shadow_freelist x))
   :pattern ((lib!Tlsf./Tlsf/shadow_freelist x))
   :qid internal_lib!Tlsf./Tlsf/shadow_freelist_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/shadow_freelist_accessor_definition
)))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
        x
      ))
     ) (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. x)) (has_type x (TYPE%lib!Tlsf.
      FLLEN&. FLLEN& SLLEN&. SLLEN&
   )))
   :qid internal_lib!Tlsf./Tlsf/shadow_freelist_invariant_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/shadow_freelist_invariant_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (= (lib!Tlsf./Tlsf/user_block_map x) (lib!Tlsf./Tlsf/?user_block_map x))
   :pattern ((lib!Tlsf./Tlsf/user_block_map x))
   :qid internal_lib!Tlsf./Tlsf/user_block_map_accessor_definition
   :skolemid skolem_internal_lib!Tlsf./Tlsf/user_block_map_accessor_definition
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (=>
    (is-lib!Tlsf./Tlsf x)
    (height_lt (height (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks x)))
     (height (Poly%lib!Tlsf. x))
   ))
   :pattern ((height (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks x))))
   :qid prelude_datatype_height_lib!Tlsf./Tlsf/all_blocks
   :skolemid skolem_prelude_datatype_height_lib!Tlsf./Tlsf/all_blocks
)))
(assert
 (forall ((x lib!Tlsf.)) (!
   (=>
    (is-lib!Tlsf./Tlsf x)
    (height_lt (height (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
        x
      ))
     ) (height (Poly%lib!Tlsf. x))
   ))
   :pattern ((height (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
       x
   ))))
   :qid prelude_datatype_height_lib!Tlsf./Tlsf/shadow_freelist
   :skolemid skolem_prelude_datatype_height_lib!Tlsf./Tlsf/shadow_freelist
)))
(assert
 (forall ((x lib!DeallocToken.)) (!
   (= x (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken. x)))
   :pattern ((Poly%lib!DeallocToken. x))
   :qid internal_lib__DeallocToken_box_axiom_definition
   :skolemid skolem_internal_lib__DeallocToken_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!DeallocToken.)
    (= x (Poly%lib!DeallocToken. (%Poly%lib!DeallocToken. x)))
   )
   :pattern ((has_type x TYPE%lib!DeallocToken.))
   :qid internal_lib__DeallocToken_unbox_axiom_definition
   :skolemid skolem_internal_lib__DeallocToken_unbox_axiom_definition
)))
(assert
 (forall ((_ptr! ptr_mut%<u8.>.) (_user_size! Int) (_align! Int)) (!
   (=>
    (uInv SZ _align!)
    (has_type (Poly%lib!DeallocToken. (lib!DeallocToken./DeallocToken _ptr! _user_size!
       _align!
      )
     ) TYPE%lib!DeallocToken.
   ))
   :pattern ((has_type (Poly%lib!DeallocToken. (lib!DeallocToken./DeallocToken _ptr! _user_size!
       _align!
      )
     ) TYPE%lib!DeallocToken.
   ))
   :qid internal_lib!DeallocToken./DeallocToken_constructor_definition
   :skolemid skolem_internal_lib!DeallocToken./DeallocToken_constructor_definition
)))
(assert
 (forall ((x lib!DeallocToken.)) (!
   (= (lib!DeallocToken./DeallocToken/ptr x) (lib!DeallocToken./DeallocToken/?ptr x))
   :pattern ((lib!DeallocToken./DeallocToken/ptr x))
   :qid internal_lib!DeallocToken./DeallocToken/ptr_accessor_definition
   :skolemid skolem_internal_lib!DeallocToken./DeallocToken/ptr_accessor_definition
)))
(assert
 (forall ((x lib!DeallocToken.)) (!
   (= (lib!DeallocToken./DeallocToken/user_size x) (lib!DeallocToken./DeallocToken/?user_size
     x
   ))
   :pattern ((lib!DeallocToken./DeallocToken/user_size x))
   :qid internal_lib!DeallocToken./DeallocToken/user_size_accessor_definition
   :skolemid skolem_internal_lib!DeallocToken./DeallocToken/user_size_accessor_definition
)))
(assert
 (forall ((x lib!DeallocToken.)) (!
   (= (lib!DeallocToken./DeallocToken/align x) (lib!DeallocToken./DeallocToken/?align
     x
   ))
   :pattern ((lib!DeallocToken./DeallocToken/align x))
   :qid internal_lib!DeallocToken./DeallocToken/align_accessor_definition
   :skolemid skolem_internal_lib!DeallocToken./DeallocToken/align_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib!DeallocToken.)
    (uInv SZ (lib!DeallocToken./DeallocToken/align (%Poly%lib!DeallocToken. x)))
   )
   :pattern ((lib!DeallocToken./DeallocToken/align (%Poly%lib!DeallocToken. x)) (has_type
     x TYPE%lib!DeallocToken.
   ))
   :qid internal_lib!DeallocToken./DeallocToken/align_invariant_definition
   :skolemid skolem_internal_lib!DeallocToken./DeallocToken/align_invariant_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (= x (%Poly%tuple%0. (Poly%tuple%0. x)))
   :pattern ((Poly%tuple%0. x))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%tuple%0.)
    (= x (Poly%tuple%0. (%Poly%tuple%0. x)))
   )
   :pattern ((has_type x TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (has_type (Poly%tuple%0. x) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= x (%Poly%tuple%2. (Poly%tuple%2. x)))
   :pattern ((Poly%tuple%2. x))
   :qid internal_crate__tuple__2_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__2_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (= x (Poly%tuple%2. (%Poly%tuple%2. x)))
   )
   :pattern ((has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&)))
   :qid internal_crate__tuple__2_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__2_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (_0! Poly) (_1! Poly)) (!
   (=>
    (and
     (has_type _0! T%0&)
     (has_type _1! T%1&)
    )
    (has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&. T%0& T%1&.
      T%1&
   )))
   :pattern ((has_type (Poly%tuple%2. (tuple%2./tuple%2 _0! _1!)) (TYPE%tuple%2. T%0&.
      T%0& T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2_constructor_definition
   :skolemid skolem_internal_tuple__2./tuple__2_constructor_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/0 x) (tuple%2./tuple%2/?0 x))
   :pattern ((tuple%2./tuple%2/0 x))
   :qid internal_tuple__2./tuple__2/0_accessor_definition
   :skolemid skolem_internal_tuple__2./tuple__2/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) T%0&)
   )
   :pattern ((tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/0_invariant_definition
   :skolemid skolem_internal_tuple__2./tuple__2/0_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (= (tuple%2./tuple%2/1 x) (tuple%2./tuple%2/?1 x))
   :pattern ((tuple%2./tuple%2/1 x))
   :qid internal_tuple__2./tuple__2/1_accessor_definition
   :skolemid skolem_internal_tuple__2./tuple__2/1_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
    (has_type (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) T%1&)
   )
   :pattern ((tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (has_type x (TYPE%tuple%2. T%0&. T%0&
      T%1&. T%1&
   )))
   :qid internal_tuple__2./tuple__2/1_invariant_definition
   :skolemid skolem_internal_tuple__2./tuple__2/1_invariant_definition
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (height_lt (height (tuple%2./tuple%2/0 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/0 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/0
   :skolemid skolem_prelude_datatype_height_tuple%2./tuple%2/0
)))
(assert
 (forall ((x tuple%2.)) (!
   (=>
    (is-tuple%2./tuple%2 x)
    (height_lt (height (tuple%2./tuple%2/1 x)) (height (Poly%tuple%2. x)))
   )
   :pattern ((height (tuple%2./tuple%2/1 x)))
   :qid prelude_datatype_height_tuple%2./tuple%2/1
   :skolemid skolem_prelude_datatype_height_tuple%2./tuple%2/1
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (deep Bool) (x Poly) (y Poly))
  (!
   (=>
    (and
     (has_type x (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (has_type y (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&))
     (ext_eq deep T%0& (tuple%2./tuple%2/0 (%Poly%tuple%2. x)) (tuple%2./tuple%2/0 (%Poly%tuple%2.
        y
     )))
     (ext_eq deep T%1& (tuple%2./tuple%2/1 (%Poly%tuple%2. x)) (tuple%2./tuple%2/1 (%Poly%tuple%2.
        y
    ))))
    (ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y)
   )
   :pattern ((ext_eq deep (TYPE%tuple%2. T%0&. T%0& T%1&. T%1&) x y))
   :qid internal_tuple__2./tuple__2_ext_equal_definition
   :skolemid skolem_internal_tuple__2./tuple__2_ext_equal_definition
)))
(assert
 (forall ((x tuple%3.)) (!
   (= x (%Poly%tuple%3. (Poly%tuple%3. x)))
   :pattern ((Poly%tuple%3. x))
   :qid internal_crate__tuple__3_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__3_box_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    Poly
   )
  ) (!
   (=>
    (has_type x (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
    (= x (Poly%tuple%3. (%Poly%tuple%3. x)))
   )
   :pattern ((has_type x (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&)))
   :qid internal_crate__tuple__3_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__3_unbox_axiom_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (_0!
    Poly
   ) (_1! Poly) (_2! Poly)
  ) (!
   (=>
    (and
     (has_type _0! T%0&)
     (has_type _1! T%1&)
     (has_type _2! T%2&)
    )
    (has_type (Poly%tuple%3. (tuple%3./tuple%3 _0! _1! _2!)) (TYPE%tuple%3. T%0&. T%0&
      T%1&. T%1& T%2&. T%2&
   )))
   :pattern ((has_type (Poly%tuple%3. (tuple%3./tuple%3 _0! _1! _2!)) (TYPE%tuple%3. T%0&.
      T%0& T%1&. T%1& T%2&. T%2&
   )))
   :qid internal_tuple__3./tuple__3_constructor_definition
   :skolemid skolem_internal_tuple__3./tuple__3_constructor_definition
)))
(assert
 (forall ((x tuple%3.)) (!
   (= (tuple%3./tuple%3/0 x) (tuple%3./tuple%3/?0 x))
   :pattern ((tuple%3./tuple%3/0 x))
   :qid internal_tuple__3./tuple__3/0_accessor_definition
   :skolemid skolem_internal_tuple__3./tuple__3/0_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    Poly
   )
  ) (!
   (=>
    (has_type x (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
    (has_type (tuple%3./tuple%3/0 (%Poly%tuple%3. x)) T%0&)
   )
   :pattern ((tuple%3./tuple%3/0 (%Poly%tuple%3. x)) (has_type x (TYPE%tuple%3. T%0&. T%0&
      T%1&. T%1& T%2&. T%2&
   )))
   :qid internal_tuple__3./tuple__3/0_invariant_definition
   :skolemid skolem_internal_tuple__3./tuple__3/0_invariant_definition
)))
(assert
 (forall ((x tuple%3.)) (!
   (= (tuple%3./tuple%3/1 x) (tuple%3./tuple%3/?1 x))
   :pattern ((tuple%3./tuple%3/1 x))
   :qid internal_tuple__3./tuple__3/1_accessor_definition
   :skolemid skolem_internal_tuple__3./tuple__3/1_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    Poly
   )
  ) (!
   (=>
    (has_type x (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
    (has_type (tuple%3./tuple%3/1 (%Poly%tuple%3. x)) T%1&)
   )
   :pattern ((tuple%3./tuple%3/1 (%Poly%tuple%3. x)) (has_type x (TYPE%tuple%3. T%0&. T%0&
      T%1&. T%1& T%2&. T%2&
   )))
   :qid internal_tuple__3./tuple__3/1_invariant_definition
   :skolemid skolem_internal_tuple__3./tuple__3/1_invariant_definition
)))
(assert
 (forall ((x tuple%3.)) (!
   (= (tuple%3./tuple%3/2 x) (tuple%3./tuple%3/?2 x))
   :pattern ((tuple%3./tuple%3/2 x))
   :qid internal_tuple__3./tuple__3/2_accessor_definition
   :skolemid skolem_internal_tuple__3./tuple__3/2_accessor_definition
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (x
    Poly
   )
  ) (!
   (=>
    (has_type x (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
    (has_type (tuple%3./tuple%3/2 (%Poly%tuple%3. x)) T%2&)
   )
   :pattern ((tuple%3./tuple%3/2 (%Poly%tuple%3. x)) (has_type x (TYPE%tuple%3. T%0&. T%0&
      T%1&. T%1& T%2&. T%2&
   )))
   :qid internal_tuple__3./tuple__3/2_invariant_definition
   :skolemid skolem_internal_tuple__3./tuple__3/2_invariant_definition
)))
(assert
 (forall ((x tuple%3.)) (!
   (=>
    (is-tuple%3./tuple%3 x)
    (height_lt (height (tuple%3./tuple%3/0 x)) (height (Poly%tuple%3. x)))
   )
   :pattern ((height (tuple%3./tuple%3/0 x)))
   :qid prelude_datatype_height_tuple%3./tuple%3/0
   :skolemid skolem_prelude_datatype_height_tuple%3./tuple%3/0
)))
(assert
 (forall ((x tuple%3.)) (!
   (=>
    (is-tuple%3./tuple%3 x)
    (height_lt (height (tuple%3./tuple%3/1 x)) (height (Poly%tuple%3. x)))
   )
   :pattern ((height (tuple%3./tuple%3/1 x)))
   :qid prelude_datatype_height_tuple%3./tuple%3/1
   :skolemid skolem_prelude_datatype_height_tuple%3./tuple%3/1
)))
(assert
 (forall ((x tuple%3.)) (!
   (=>
    (is-tuple%3./tuple%3 x)
    (height_lt (height (tuple%3./tuple%3/2 x)) (height (Poly%tuple%3. x)))
   )
   :pattern ((height (tuple%3./tuple%3/2 x)))
   :qid prelude_datatype_height_tuple%3./tuple%3/2
   :skolemid skolem_prelude_datatype_height_tuple%3./tuple%3/2
)))
(assert
 (forall ((T%0&. Dcr) (T%0& Type) (T%1&. Dcr) (T%1& Type) (T%2&. Dcr) (T%2& Type) (deep
    Bool
   ) (x Poly) (y Poly)
  ) (!
   (=>
    (and
     (has_type x (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (has_type y (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&))
     (ext_eq deep T%0& (tuple%3./tuple%3/0 (%Poly%tuple%3. x)) (tuple%3./tuple%3/0 (%Poly%tuple%3.
        y
     )))
     (ext_eq deep T%1& (tuple%3./tuple%3/1 (%Poly%tuple%3. x)) (tuple%3./tuple%3/1 (%Poly%tuple%3.
        y
     )))
     (ext_eq deep T%2& (tuple%3./tuple%3/2 (%Poly%tuple%3. x)) (tuple%3./tuple%3/2 (%Poly%tuple%3.
        y
    ))))
    (ext_eq deep (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&) x y)
   )
   :pattern ((ext_eq deep (TYPE%tuple%3. T%0&. T%0& T%1&. T%1& T%2&. T%2&) x y))
   :qid internal_tuple__3./tuple__3_ext_equal_definition
   :skolemid skolem_internal_tuple__3./tuple__3_ext_equal_definition
)))
(declare-fun array_new (Dcr Type Int %%Function%%) Poly)
(declare-fun array_index (Dcr Type Dcr Type %%Function%% Poly) Poly)
(assert
 (forall ((Tdcr Dcr) (T Type) (N Int) (Fn %%Function%%)) (!
   (= (array_new Tdcr T N Fn) (Poly%array%. Fn))
   :pattern ((array_new Tdcr T N Fn))
   :qid prelude_array_new
   :skolemid skolem_prelude_array_new
)))
(declare-fun %%apply%%2 (%%Function%% Int) Poly)
(assert
 (forall ((Tdcr Dcr) (T Type) (N Int) (Fn %%Function%%)) (!
   (=>
    (forall ((i Int)) (!
      (=>
       (and
        (<= 0 i)
        (< i N)
       )
       (has_type (%%apply%%2 Fn i) T)
      )
      :pattern ((has_type (%%apply%%2 Fn i) T))
      :qid prelude_has_type_array_elts
      :skolemid skolem_prelude_has_type_array_elts
    ))
    (has_type (array_new Tdcr T N Fn) (ARRAY Tdcr T $ (CONST_INT N)))
   )
   :pattern ((array_new Tdcr T N Fn))
   :qid prelude_has_type_array_new
   :skolemid skolem_prelude_has_type_array_new
)))
(assert
 (forall ((Tdcr Dcr) (T Type) (Ndcr Dcr) (N Type) (Fn %%Function%%) (i Poly)) (!
   (=>
    (and
     (has_type (Poly%array%. Fn) (ARRAY Tdcr T Ndcr N))
     (has_type i INT)
    )
    (has_type (array_index Tdcr T $ N Fn i) T)
   )
   :pattern ((array_index Tdcr T $ N Fn i) (has_type (Poly%array%. Fn) (ARRAY Tdcr T Ndcr
      N
   )))
   :qid prelude_has_type_array_index
   :skolemid skolem_prelude_has_type_array_index
)))
(assert
 (!
  (forall ((Tdcr Dcr) (T Type) (N Int) (Fn %%Function%%) (i Int)) (!
    (= (array_index Tdcr T $ (CONST_INT N) Fn (I i)) (%%apply%%2 Fn i))
    :pattern ((array_new Tdcr T N Fn) (%%apply%%2 Fn i))
    :qid prelude_array_index_trigger
    :skolemid skolem_prelude_array_index_trigger
  ))
  :named
  prelude_axiom_array_index
))

;; Trait-Bounds
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%vstd!array.ArrayAdditionalSpecFns. Self%&. Self%& T&. T&)
    (and
     (tr_bound%vstd!view.View. Self%&. Self%&)
     (and
      (= $ (proj%%vstd!view.View./V Self%&. Self%&))
      (= (TYPE%vstd!seq.Seq. T&. T&) (proj%vstd!view.View./V Self%&. Self%&))
     )
     (sized T&.)
   ))
   :pattern ((tr_bound%vstd!array.ArrayAdditionalSpecFns. Self%&. Self%& T&. T&))
   :qid internal_vstd__array__ArrayAdditionalSpecFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__array__ArrayAdditionalSpecFns_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%vstd!slice.SliceAdditionalSpecFns. Self%&. Self%& T&. T&)
    (and
     (tr_bound%vstd!view.View. Self%&. Self%&)
     (and
      (= $ (proj%%vstd!view.View./V Self%&. Self%&))
      (= (TYPE%vstd!seq.Seq. T&. T&) (proj%vstd!view.View./V Self%&. Self%&))
     )
     (sized T&.)
   ))
   :pattern ((tr_bound%vstd!slice.SliceAdditionalSpecFns. Self%&. Self%& T&. T&))
   :qid internal_vstd__slice__SliceAdditionalSpecFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__slice__SliceAdditionalSpecFns_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   (=>
    (tr_bound%vstd!view.View. Self%&. Self%&)
    (sized (proj%%vstd!view.View./V Self%&. Self%&))
   )
   :pattern ((tr_bound%vstd!view.View. Self%&. Self%&))
   :qid internal_vstd__view__View_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__view__View_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type)) (!
   true
   :pattern ((tr_bound%core!cmp.PartialEq. Self%&. Self%& Rhs&. Rhs&))
   :qid internal_core__cmp__PartialEq_trait_type_bounds_definition
   :skolemid skolem_internal_core__cmp__PartialEq_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type)) (!
   (=>
    (tr_bound%vstd!std_specs.cmp.PartialEqSpec. Self%&. Self%& Rhs&. Rhs&)
    (tr_bound%core!cmp.PartialEq. Self%&. Self%& Rhs&. Rhs&)
   )
   :pattern ((tr_bound%vstd!std_specs.cmp.PartialEqSpec. Self%&. Self%& Rhs&. Rhs&))
   :qid internal_vstd__std_specs__cmp__PartialEqSpec_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__std_specs__cmp__PartialEqSpec_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   true
   :pattern ((tr_bound%core!alloc.Allocator. Self%&. Self%&))
   :qid internal_core__alloc__Allocator_trait_type_bounds_definition
   :skolemid skolem_internal_core__alloc__Allocator_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%vstd!std_specs.option.OptionAdditionalFns. Self%&. Self%& T&. T&)
    (and
     (sized Self%&.)
     (sized T&.)
   ))
   :pattern ((tr_bound%vstd!std_specs.option.OptionAdditionalFns. Self%&. Self%& T&. T&))
   :qid internal_vstd__std_specs__option__OptionAdditionalFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__std_specs__option__OptionAdditionalFns_trait_type_bounds_definition
)))

;; Associated-Type-Impls
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type)) (!
   (= (proj%%vstd!view.View./V $ (ARRAY T&. T& N&. N&)) $)
   :pattern ((proj%%vstd!view.View./V $ (ARRAY T&. T& N&. N&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type)) (!
   (= (proj%vstd!view.View./V $ (ARRAY T&. T& N&. N&)) (TYPE%vstd!seq.Seq. T&. T&))
   :pattern ((proj%vstd!view.View./V $ (ARRAY T&. T& N&. N&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V $ (PTR T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V $ (PTR T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V $ (PTR T&. T&)) (TYPE%vstd!raw_ptr.PtrData. T&. T&))
   :pattern ((proj%vstd!view.View./V $ (PTR T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)) (TYPE%vstd!raw_ptr.PtrData.
     T&. T&
   ))
   :pattern ((proj%vstd!view.View./V (CONST_PTR $) (PTR T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&)) (TYPE%vstd!raw_ptr.PointsToData.
     T&. T&
   ))
   :pattern ((proj%vstd!view.View./V $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V $slice (SLICE T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V $slice (SLICE T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V $slice (SLICE T&. T&)) (TYPE%vstd!seq.Seq. T&. T&))
   :pattern ((proj%vstd!view.View./V $slice (SLICE T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (REF A&.) A&) (proj%%vstd!view.View./V A&. A&))
   :pattern ((proj%%vstd!view.View./V (REF A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (REF A&.) A&) (proj%vstd!view.View./V A&. A&))
   :pattern ((proj%vstd!view.View./V (REF A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (BOX $ TYPE%alloc!alloc.Global. A&.) A&) (proj%%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%%vstd!view.View./V (BOX $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (BOX $ TYPE%alloc!alloc.Global. A&.) A&) (proj%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%vstd!view.View./V (BOX $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (RC $ TYPE%alloc!alloc.Global. A&.) A&) (proj%%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%%vstd!view.View./V (RC $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (RC $ TYPE%alloc!alloc.Global. A&.) A&) (proj%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%vstd!view.View./V (RC $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%%vstd!view.View./V (ARC $ TYPE%alloc!alloc.Global. A&.) A&) (proj%%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%%vstd!view.View./V (ARC $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (= (proj%vstd!view.View./V (ARC $ TYPE%alloc!alloc.Global. A&.) A&) (proj%vstd!view.View./V
     A&. A&
   ))
   :pattern ((proj%vstd!view.View./V (ARC $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%%vstd!view.View./V $ (TYPE%core!option.Option. T&. T&)) $)
   :pattern ((proj%%vstd!view.View./V $ (TYPE%core!option.Option. T&. T&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (= (proj%vstd!view.View./V $ (TYPE%core!option.Option. T&. T&)) (TYPE%core!option.Option.
     T&. T&
   ))
   :pattern ((proj%vstd!view.View./V $ (TYPE%core!option.Option. T&. T&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (= (proj%%vstd!view.View./V $ TYPE%tuple%0.) $)
)
(assert
 (= (proj%vstd!view.View./V $ TYPE%tuple%0.) TYPE%tuple%0.)
)
(assert
 (= (proj%%vstd!view.View./V $ BOOL) $)
)
(assert
 (= (proj%vstd!view.View./V $ BOOL) BOOL)
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 8)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 8)) (UINT 8))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 16)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 16)) (UINT 16))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 32)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 32)) (UINT 32))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 64)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 64)) (UINT 64))
)
(assert
 (= (proj%%vstd!view.View./V $ (UINT 128)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (UINT 128)) (UINT 128))
)
(assert
 (= (proj%%vstd!view.View./V $ USIZE) $)
)
(assert
 (= (proj%vstd!view.View./V $ USIZE) USIZE)
)
(assert
 (= (proj%%vstd!view.View./V $ (SINT 8)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (SINT 8)) (SINT 8))
)
(assert
 (= (proj%%vstd!view.View./V $ (SINT 16)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (SINT 16)) (SINT 16))
)
(assert
 (= (proj%%vstd!view.View./V $ (SINT 32)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (SINT 32)) (SINT 32))
)
(assert
 (= (proj%%vstd!view.View./V $ (SINT 64)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (SINT 64)) (SINT 64))
)
(assert
 (= (proj%%vstd!view.View./V $ (SINT 128)) $)
)
(assert
 (= (proj%vstd!view.View./V $ (SINT 128)) (SINT 128))
)
(assert
 (= (proj%%vstd!view.View./V $ ISIZE) $)
)
(assert
 (= (proj%vstd!view.View./V $ ISIZE) ISIZE)
)
(assert
 (= (proj%%vstd!view.View./V $ CHAR) $)
)
(assert
 (= (proj%vstd!view.View./V $ CHAR) CHAR)
)
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type)) (!
   (= (proj%%vstd!view.View./V (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&)) (DST (proj%%vstd!view.View./V
      A1&. A1&
   )))
   :pattern ((proj%%vstd!view.View./V (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&)))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type)) (!
   (= (proj%vstd!view.View./V (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&)) (TYPE%tuple%2.
     (proj%%vstd!view.View./V A0&. A0&) (proj%vstd!view.View./V A0&. A0&) (proj%%vstd!view.View./V
      A1&. A1&
     ) (proj%vstd!view.View./V A1&. A1&)
   ))
   :pattern ((proj%vstd!view.View./V (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type) (A2&. Dcr) (A2& Type)) (!
   (= (proj%%vstd!view.View./V (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&. A2&))
    (DST (proj%%vstd!view.View./V A2&. A2&))
   )
   :pattern ((proj%%vstd!view.View./V (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&.
      A2&
   )))
   :qid internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
   :skolemid skolem_internal_proj____vstd!view.View./V_assoc_type_impl_true_definition
)))
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type) (A2&. Dcr) (A2& Type)) (!
   (= (proj%vstd!view.View./V (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&. A2&))
    (TYPE%tuple%3. (proj%%vstd!view.View./V A0&. A0&) (proj%vstd!view.View./V A0&. A0&)
     (proj%%vstd!view.View./V A1&. A1&) (proj%vstd!view.View./V A1&. A1&) (proj%%vstd!view.View./V
      A2&. A2&
     ) (proj%vstd!view.View./V A2&. A2&)
   ))
   :pattern ((proj%vstd!view.View./V (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&. A2&)))
   :qid internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
   :skolemid skolem_internal_proj__vstd!view.View./V_assoc_type_impl_false_definition
)))

;; Function-Decl vstd::seq::Seq::len
(declare-fun vstd!seq.Seq.len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::seq::Seq::index
(declare-fun vstd!seq.Seq.index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::spec_index
(declare-fun vstd!seq.impl&%0.spec_index.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::subrange
(declare-fun vstd!seq.Seq.subrange.? (Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::empty
(declare-fun vstd!seq.Seq.empty.? (Dcr Type) Poly)

;; Function-Decl vstd::seq::Seq::new
(declare-fun vstd!seq.Seq.new.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::push
(declare-fun vstd!seq.Seq.push.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::Seq::add
(declare-fun vstd!seq.Seq.add.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::spec_add
(declare-fun vstd!seq.impl&%0.spec_add.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::finite
(declare-fun vstd!set.impl&%0.finite.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::map::impl&%0::dom
(declare-fun vstd!map.impl&%0.dom.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl vstd::set::Set::contains
(declare-fun vstd!set.Set.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::map::impl&%0::index
(declare-fun vstd!map.impl&%0.index.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::spec_index
(declare-fun vstd!map.impl&%0.spec_index.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::Set::empty
(declare-fun vstd!set.Set.empty.? (Dcr Type) Poly)

;; Function-Decl vstd::map::impl&%0::insert
(declare-fun vstd!map.impl&%0.insert.? (Dcr Type Dcr Type Poly Poly Poly) Poly)

;; Function-Decl vstd::set::Set::insert
(declare-fun vstd!set.Set.insert.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map::impl&%0::remove
(declare-fun vstd!map.impl&%0.remove.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::Set::remove
(declare-fun vstd!set.Set.remove.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::new
(declare-fun vstd!set.impl&%0.new.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::set::impl&%0::difference
(declare-fun vstd!set.impl&%0.difference.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::mk_map
(declare-fun vstd!set.impl&%0.mk_map.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::set::impl&%0::len
(declare-fun vstd!set.impl&%0.len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::set_lib::impl&%0::is_empty
(declare-fun vstd!set_lib.impl&%0.is_empty.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::set::Set::subset_of
(declare-fun vstd!set.Set.subset_of.? (Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::slice::spec_slice_len
(declare-fun vstd!slice.spec_slice_len.? (Dcr Type Poly) Int)

;; Function-Decl vstd::view::View::view
(declare-fun vstd!view.View.view.? (Dcr Type Poly) Poly)
(declare-fun vstd!view.View.view%default%.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::slice::len%returns_clause_autospec
(declare-fun vstd!slice.len%returns_clause_autospec.? (Dcr Type Poly) Int)

;; Function-Decl vstd::slice::SliceAdditionalSpecFns::spec_index
(declare-fun vstd!slice.SliceAdditionalSpecFns.spec_index.? (Dcr Type Dcr Type Poly
  Poly
 ) Poly
)
(declare-fun vstd!slice.SliceAdditionalSpecFns.spec_index%default%.? (Dcr Type Dcr
  Type Poly Poly
 ) Poly
)

;; Function-Decl vstd::array::array_view
(declare-fun vstd!array.array_view.? (Dcr Type Dcr Type Poly) Poly)

;; Function-Decl vstd::array::ArrayAdditionalSpecFns::spec_index
(declare-fun vstd!array.ArrayAdditionalSpecFns.spec_index.? (Dcr Type Dcr Type Poly
  Poly
 ) Poly
)
(declare-fun vstd!array.ArrayAdditionalSpecFns.spec_index%default%.? (Dcr Type Dcr
  Type Poly Poly
 ) Poly
)

;; Function-Decl vstd::raw_ptr::ptr_mut_from_data
(declare-fun vstd!raw_ptr.ptr_mut_from_data.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::view_reverse_for_eq
(declare-fun vstd!raw_ptr.view_reverse_for_eq.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::view_reverse_for_eq_sized
(declare-fun vstd!raw_ptr.view_reverse_for_eq_sized.? (Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::layout::size_of
(declare-fun vstd!layout.size_of.? (Dcr Type) Int)

;; Function-Decl vstd::layout::align_of
(declare-fun vstd!layout.align_of.? (Dcr Type) Int)

;; Function-Decl vstd::arithmetic::power2::is_pow2
(declare-fun vstd!arithmetic.power2.is_pow2.? (Poly) Bool)

;; Function-Decl vstd::std_specs::bits::u64_trailing_zeros
(declare-fun vstd!std_specs.bits.u64_trailing_zeros.? (Poly) Int)
(declare-fun vstd!std_specs.bits.rec%u64_trailing_zeros.? (Poly Fuel) Int)

;; Function-Decl vstd::std_specs::cmp::PartialEqSpec::obeys_eq_spec
(declare-fun vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? (Dcr Type Dcr Type)
 Poly
)
(declare-fun vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec%default%.? (Dcr Type Dcr
  Type
 ) Poly
)

;; Function-Decl vstd::std_specs::cmp::PartialEqSpec::eq_spec
(declare-fun vstd!std_specs.cmp.PartialEqSpec.eq_spec.? (Dcr Type Dcr Type Poly Poly)
 Poly
)
(declare-fun vstd!std_specs.cmp.PartialEqSpec.eq_spec%default%.? (Dcr Type Dcr Type
  Poly Poly
 ) Poly
)

;; Function-Decl vstd::arithmetic::logarithm::log
(declare-fun vstd!arithmetic.logarithm.log.? (Poly Poly) Int)

;; Function-Decl vstd::arithmetic::power::pow
(declare-fun vstd!arithmetic.power.pow.? (Poly Poly) Int)

;; Function-Decl vstd::arithmetic::power2::pow2
(declare-fun vstd!arithmetic.power2.pow2.? (Poly) Int)

;; Function-Decl vstd::std_specs::option::is_none
(declare-fun vstd!std_specs.option.is_none.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::std_specs::option::OptionAdditionalFns::is_Some
(declare-fun vstd!std_specs.option.OptionAdditionalFns.is_Some.? (Dcr Type Dcr Type
  Poly
 ) Poly
)
(declare-fun vstd!std_specs.option.OptionAdditionalFns.is_Some%default%.? (Dcr Type
  Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::option::OptionAdditionalFns::arrow_0
(declare-fun vstd!std_specs.option.OptionAdditionalFns.arrow_0.? (Dcr Type Dcr Type
  Poly
 ) Poly
)
(declare-fun vstd!std_specs.option.OptionAdditionalFns.arrow_0%default%.? (Dcr Type
  Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::option::spec_unwrap
(declare-fun vstd!std_specs.option.spec_unwrap.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::ptr_mut_specs::spec_addr
(declare-fun vstd!raw_ptr.ptr_mut_specs.spec_addr.? (Dcr Type Poly) Int)

;; Function-Decl vstd::layout::valid_layout
(declare-fun vstd!layout.valid_layout.? (Poly Poly) Bool)

;; Function-Decl vstd::pervasive::arbitrary
(declare-fun vstd!pervasive.arbitrary.? (Dcr Type) Poly)

;; Function-Decl vstd::raw_ptr::impl&%5::ptr
(declare-fun vstd!raw_ptr.impl&%5.ptr.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::impl&%6::is_uninit
(declare-fun vstd!raw_ptr.impl&%6.is_uninit.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::raw_ptr::impl&%5::opt_value
(declare-fun vstd!raw_ptr.impl&%5.opt_value.? (Dcr Type Poly) vstd!raw_ptr.MemContents.)

;; Function-Decl vstd::raw_ptr::impl&%5::is_uninit
(declare-fun vstd!raw_ptr.impl&%5.is_uninit.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::raw_ptr::spec_cast_ptr_to_usize
(declare-fun vstd!raw_ptr.spec_cast_ptr_to_usize.? (Dcr Type Poly) Int)

;; Function-Decl vstd::raw_ptr::impl&%6::is_init
(declare-fun vstd!raw_ptr.impl&%6.is_init.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::raw_ptr::impl&%5::is_init
(declare-fun vstd!raw_ptr.impl&%5.is_init.? (Dcr Type Poly) Bool)

;; Function-Decl vstd::raw_ptr::impl&%1::arrow_0
(declare-fun vstd!raw_ptr.impl&%1.arrow_0.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::impl&%6::value
(declare-fun vstd!raw_ptr.impl&%6.value.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::impl&%5::value
(declare-fun vstd!raw_ptr.impl&%5.value.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::raw_ptr::impl&%9::provenance
(declare-fun vstd!raw_ptr.impl&%9.provenance.? (Poly) vstd!raw_ptr.Provenance.)

;; Function-Decl vstd::raw_ptr::impl&%9::view
(declare-fun vstd!raw_ptr.impl&%9.view.? (Poly) vstd!raw_ptr.Provenance.)

;; Function-Decl vstd::raw_ptr::impl&%10::provenance
(declare-fun vstd!raw_ptr.impl&%10.provenance.? (Poly) vstd!raw_ptr.Provenance.)

;; Function-Decl vstd::raw_ptr::impl&%10::dom
(declare-fun vstd!raw_ptr.impl&%10.dom.? (Poly) vstd!set.Set<int.>.)

;; Function-Decl vstd::set_lib::set_int_range
(declare-fun vstd!set_lib.set_int_range.? (Poly Poly) vstd!set.Set<int.>.)

;; Function-Decl vstd::raw_ptr::impl&%10::is_range
(declare-fun vstd!raw_ptr.impl&%10.is_range.? (Poly Poly Poly) Bool)

;; Function-Decl vstd::seq_lib::impl&%0::remove
(declare-fun vstd!seq_lib.impl&%0.remove.? (Dcr Type Poly Poly) Poly)

;; Function-Decl lib::block_index::BlockIndex::valid_block_index
(declare-fun lib!block_index.impl&%7.valid_block_index.? (Dcr Type Dcr Type Poly)
 Bool
)

;; Function-Decl lib::block_index::BlockIndex::view
(declare-fun lib!block_index.impl&%7.view.? (Dcr Type Dcr Type Poly) tuple%2.)

;; Function-Decl lib::block_index::BlockIndex::wf
(declare-fun lib!block_index.impl&%7.wf.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::parameters::GRANULARITY
(declare-fun lib!parameters.GRANULARITY.? () Int)

;; Function-Decl lib::Tlsf::granularity_log2_spec
(declare-fun lib!parameters.impl&%0.granularity_log2_spec.? (Dcr Type Dcr Type) Int)

;; Function-Decl lib::bits::is_power_of_two
(declare-fun lib!bits.is_power_of_two.? (Poly) Bool)

;; Function-Decl lib::Tlsf::parameter_validity
(declare-fun lib!parameters.impl&%0.parameter_validity.? (Dcr Type Dcr Type) Bool)

;; Function-Decl lib::bits::usize_trailing_zeros
(declare-fun lib!bits.usize_trailing_zeros.? (Poly) Int)

;; Function-Decl vstd::std_specs::num::usize_specs::wrapping_sub%returns_clause_autospec
(declare-fun vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.?
 (Poly Poly) Int
)

;; Function-Decl vstd::std_specs::num::usize_specs::checked_add%returns_clause_autospec
(declare-fun vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.?
 (Poly Poly) core!option.Option.
)

;; Function-Decl vstd::std_specs::num::usize_specs::saturating_sub%returns_clause_autospec
(declare-fun vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.?
 (Poly Poly) Int
)

;; Function-Decl vstd::layout::size_of_as_usize
(declare-fun vstd!layout.size_of_as_usize.? (Dcr Type) Int)

;; Function-Decl vstd::map::impl&%0::new
(declare-fun vstd!map.impl&%0.new.? (Dcr Type Dcr Type Poly Poly) Poly)

;; Function-Decl vstd::map_lib::impl&%0::contains_key
(declare-fun vstd!map_lib.impl&%0.contains_key.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl vstd::map_lib::impl&%0::map_entries
(declare-fun vstd!map_lib.impl&%0.map_entries.? (Dcr Type Dcr Type Dcr Type Poly Poly)
 Poly
)

;; Function-Decl vstd::map_lib::impl&%0::map_values
(declare-fun vstd!map_lib.impl&%0.map_values.? (Dcr Type Dcr Type Dcr Type Poly Poly)
 Poly
)

;; Function-Decl vstd::map_lib::impl&%0::is_injective
(declare-fun vstd!map_lib.impl&%0.is_injective.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl vstd::seq::Seq::last
(declare-fun vstd!seq.Seq.last.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq::impl&%0::first
(declare-fun vstd!seq.impl&%0.first.? (Dcr Type Poly) Poly)

;; Function-Decl vstd::seq_lib::impl&%0::contains
(declare-fun vstd!seq_lib.impl&%0.contains.? (Dcr Type Poly Poly) Bool)

;; Function-Decl lib::block_index::GRANULARITY
(declare-fun lib!block_index.GRANULARITY.? () Int)

;; Function-Decl lib::block_index::BlockIndex::granularity_log2_spec
(declare-fun lib!block_index.impl&%7.granularity_log2_spec.? (Dcr Type Dcr Type) Int)

;; Function-Decl lib::block_index::BlockIndex::parameter_validity
(declare-fun lib!block_index.impl&%7.parameter_validity.? (Dcr Type Dcr Type) Bool)

;; Function-Decl lib::half_open_range::HalfOpenRange::start
(declare-fun lib!half_open_range.impl&%0.start.? (Poly) Int)

;; Function-Decl lib::half_open_range::HalfOpenRange::end
(declare-fun lib!half_open_range.impl&%0.end.? (Poly) Int)

;; Function-Decl lib::half_open_range::HalfOpenRange::wf
(declare-fun lib!half_open_range.impl&%0.wf.? (Poly) Bool)

;; Function-Decl lib::half_open_range::HalfOpenRange::new
(declare-fun lib!half_open_range.impl&%0.new.? (Poly Poly) lib!half_open_range.HalfOpenRange.)

;; Function-Decl lib::block_index::BlockIndex::block_size_range
(declare-fun lib!block_index.impl&%7.block_size_range.? (Dcr Type Dcr Type Poly) lib!half_open_range.HalfOpenRange.)

;; Function-Decl lib::block_index::BlockIndex::valid_block_size
(declare-fun lib!block_index.impl&%7.valid_block_size.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::half_open_range::HalfOpenRange::contains
(declare-fun lib!half_open_range.impl&%0.contains.? (Poly Poly) Bool)

;; Function-Decl lib::all_blocks::ShadowFreelist::shadow_freelist_has_all_wf_index
(declare-fun lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.? (Dcr Type Dcr
  Type Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::shadow_ptrs_nonnull
(declare-fun lib!linked_list.impl&%0.shadow_ptrs_nonnull.? (Dcr Type Dcr Type Poly)
 Bool
)

;; Function-Decl lib::ordered_pointer_list::ptrs_no_duplicates
(declare-fun lib!ordered_pointer_list.ptrs_no_duplicates.? (Poly) Bool)

;; Function-Decl lib::all_blocks::is_identity_injection
(declare-fun lib!all_blocks.is_identity_injection.? (Dcr Type Dcr Type Poly Poly)
 Bool
)

;; Function-Decl lib::Tlsf::wf_shadow
(declare-fun lib!linked_list.impl&%0.wf_shadow.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::wf_node_ptr
(declare-fun lib!all_blocks.impl&%0.wf_node_ptr.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::parameters::SIZE_USED
(declare-fun lib!parameters.SIZE_USED.? () Int)

;; Function-Decl lib::block::BlockHdr::is_free
(declare-fun lib!block.impl&%1.is_free.? (Poly) Bool)

;; Function-Decl lib::block::get_freelink_ptr_spec
(declare-fun lib!block.get_freelink_ptr_spec.? (Poly) ptr_mut%<lib!block.FreeLink.>.)

;; Function-Decl lib::parameters::SPEC_SIZE_SIZE_MASK
(declare-fun lib!parameters.SPEC_SIZE_SIZE_MASK.? () Int)

;; Function-Decl lib::block::BlockPerm::wf
(declare-fun lib!block.impl&%2.wf.? (Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::contains
(declare-fun lib!all_blocks.impl&%0.contains.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::value_at
(declare-fun lib!all_blocks.impl&%0.value_at.? (Dcr Type Dcr Type Poly Poly) lib!block.BlockHdr.)

;; Function-Decl lib::all_blocks::AllBlocks::phys_prev_of
(declare-fun lib!all_blocks.impl&%0.phys_prev_of.? (Dcr Type Dcr Type Poly Poly) core!option.Option.)

;; Function-Decl lib::parameters::SIZE_SENTINEL
(declare-fun lib!parameters.SIZE_SENTINEL.? () Int)

;; Function-Decl lib::block::BlockHdr::is_sentinel
(declare-fun lib!block.impl&%1.is_sentinel.? (Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::phys_next_of
(declare-fun lib!all_blocks.impl&%0.phys_next_of.? (Dcr Type Dcr Type Poly Poly) core!option.Option.)

;; Function-Decl lib::all_blocks::AllBlocks::wf_node_glue
(declare-fun lib!all_blocks.impl&%0.wf_node_glue.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::wf_node_structural
(declare-fun lib!all_blocks.impl&%0.wf_node_structural.? (Dcr Type Dcr Type Poly Poly)
 Bool
)

;; Function-Decl lib::all_blocks::AllBlocks::wf_node
(declare-fun lib!all_blocks.impl&%0.wf_node.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::all_nodes_wf
(declare-fun lib!all_blocks.impl&%0.all_nodes_wf.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::ordered_pointer_list::ghost_pointer_ordered
(declare-fun lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::pool_size_bounded
(declare-fun lib!all_blocks.impl&%0.pool_size_bounded.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::wf
(declare-fun lib!all_blocks.impl&%0.wf.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::all_blocks::AllBlocks::ptr_is_null
(declare-fun lib!all_blocks.impl&%0.ptr_is_null.? (Dcr Type Dcr Type Dcr Type Poly)
 Bool
)

;; Function-Decl lib::Tlsf::free_next_of
(declare-fun lib!linked_list.impl&%0.free_next_of.? (Dcr Type Dcr Type Poly Poly)
 core!option.Option.
)

;; Function-Decl lib::Tlsf::free_prev_of
(declare-fun lib!linked_list.impl&%0.free_prev_of.? (Dcr Type Dcr Type Poly Poly)
 core!option.Option.
)

;; Function-Decl lib::Tlsf::wf_free_node
(declare-fun lib!linked_list.impl&%0.wf_free_node.? (Dcr Type Dcr Type Poly Poly Poly)
 Bool
)

;; Function-Decl lib::Tlsf::freelist_wf
(declare-fun lib!linked_list.impl&%0.freelist_wf.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl lib::all_blocks::ShadowFreelist::contains
(declare-fun lib!all_blocks.impl&%1.contains.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl lib::Tlsf::free_blocks_in_freelist_except
(declare-fun lib!linked_list.impl&%0.free_blocks_in_freelist_except.? (Dcr Type Dcr
  Type Poly Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::all_freelist_wf_weak
(declare-fun lib!linked_list.impl&%0.all_freelist_wf_weak.? (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::all_freelist_wf
(declare-fun lib!linked_list.impl&%0.all_freelist_wf.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::Tlsf::shadow_freelist_nodup
(declare-fun lib!linked_list.impl&%0.shadow_freelist_nodup.? (Dcr Type Dcr Type Poly)
 Bool
)

;; Function-Decl lib::Tlsf::map_floor_spec
(declare-fun lib!mapping.impl&%0.map_floor_spec.? (Dcr Type Dcr Type Poly) lib!block_index.BlockIndex.)

;; Function-Decl lib::Tlsf::size_class_condition
(declare-fun lib!linked_list.impl&%0.size_class_condition.? (Dcr Type Dcr Type Poly)
 Bool
)

;; Function-Decl lib::Tlsf::shadow_freelist_popped_at
(declare-fun lib!linked_list.impl&%0.shadow_freelist_popped_at.? (Dcr Type Dcr Type
  Poly Poly Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::perms_size_unchanged_for_freelist
(declare-fun lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.? (Dcr Type
  Dcr Type Poly Poly Poly Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::free_blocks_in_freelist
(declare-fun lib!linked_list.impl&%0.free_blocks_in_freelist.? (Dcr Type Dcr Type Poly)
 Bool
)

;; Function-Decl lib::all_blocks::AllBlocks::phys_next_matches
(declare-fun lib!all_blocks.impl&%0.phys_next_matches.? (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)

;; Function-Decl lib::all_blocks::AllBlocks::get_ptr_internal_index
(declare-fun lib!all_blocks.impl&%0.get_ptr_internal_index.? (Dcr Type Dcr Type Poly
  Poly
 ) Int
)

;; Function-Decl lib::all_blocks::ShadowFreelist::ii_remove_for_index
(declare-fun lib!all_blocks.impl&%1.ii_remove_for_index.? (Dcr Type Dcr Type Poly Poly
  Poly Poly
 ) lib!all_blocks.ShadowFreelist.
)

;; Function-Decl lib::all_blocks::ShadowFreelist::ii_shift_after_insert
(declare-fun lib!all_blocks.impl&%1.ii_shift_after_insert.? (Dcr Type Dcr Type Poly
  Poly
 ) lib!all_blocks.ShadowFreelist.
)

;; Function-Decl lib::Tlsf::bitmap_wf
(declare-fun lib!bitmap.impl&%0.bitmap_wf.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::Tlsf::bitmap_sync
(declare-fun lib!bitmap.impl&%0.bitmap_sync.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::Tlsf::wf_dealloc_base
(declare-fun lib!deallocate.impl&%0.wf_dealloc_base.? (Dcr Type Dcr Type Poly Poly)
 Bool
)

;; Function-Decl lib::Tlsf::wf_dealloc_granularity_aligned
(declare-fun lib!deallocate.impl&%0.wf_dealloc_granularity_aligned.? (Dcr Type Dcr
  Type Poly Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::wf_dealloc_granularity_unaligned
(declare-fun lib!deallocate.impl&%0.wf_dealloc_granularity_unaligned.? (Dcr Type Dcr
  Type Poly Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::wf_dealloc
(declare-fun lib!deallocate.impl&%0.wf_dealloc.? (Dcr Type Dcr Type Poly Poly) Bool)

;; Function-Decl lib::ordered_pointer_list::add_ghost_pointer
(declare-fun lib!ordered_pointer_list.add_ghost_pointer.? (Poly Poly) vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.)

;; Function-Decl lib::Tlsf::max_block_size
(declare-fun lib!parameters.impl&%0.max_block_size.? (Dcr Type Dcr Type) Int)

;; Function-Decl lib::Tlsf::max_allocatable_size
(declare-fun lib!parameters.impl&%0.max_allocatable_size.? (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)

;; Function-Decl lib::Tlsf::wf
(declare-fun lib!impl&%0.wf.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::Tlsf::is_ii
(declare-fun lib!impl&%0.is_ii.? (Dcr Type Dcr Type Poly) Bool)

;; Function-Decl lib::Tlsf::is_root_provenance
(declare-fun lib!impl&%0.is_root_provenance.? (Dcr Type Dcr Type Dcr Type Poly Poly)
 Bool
)

;; Function-Axioms vstd::seq::Seq::len
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (<= 0 (vstd!seq.Seq.len.? A&. A& self!))
   )
   :pattern ((vstd!seq.Seq.len.? A&. A& self!))
   :qid internal_vstd!seq.Seq.len.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.len.?_pre_post_definition
)))

;; Function-Specs vstd::seq::Seq::index
(declare-fun req%vstd!seq.Seq.index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.Seq.index. A&. A& self! i!) (=>
     %%global_location_label%%0
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& self!)))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!seq.Seq.index. A&. A& self! i!))
   :qid internal_req__vstd!seq.Seq.index._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.index._definition
)))

;; Function-Axioms vstd::seq::Seq::index
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.Seq.index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.Seq.index.? A&. A& self! i!))
   :qid internal_vstd!seq.Seq.index.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.index.?_pre_post_definition
)))

;; Function-Specs vstd::seq::impl&%0::spec_index
(declare-fun req%vstd!seq.impl&%0.spec_index. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%1 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq.impl&%0.spec_index. A&. A& self! i!) (=>
     %%global_location_label%%1
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& self!)))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!seq.impl&%0.spec_index. A&. A& self! i!))
   :qid internal_req__vstd!seq.impl&__0.spec_index._definition
   :skolemid skolem_internal_req__vstd!seq.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::seq::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.spec_index.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (= (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) (vstd!seq.Seq.index.? A&. A& self!
      i!
    ))
    :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
    :qid internal_vstd!seq.impl&__0.spec_index.?_definition
    :skolemid skolem_internal_vstd!seq.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq.impl&%0.spec_index.? A&. A& self! i!) A&)
   )
   :pattern ((vstd!seq.impl&%0.spec_index.? A&. A& self! i!))
   :qid internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.impl&__0.spec_index.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_index_decreases
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_index_decreases.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& s!)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
      )))))
      (height_lt (height (vstd!seq.Seq.index.? A&. A& s! i!)) (height s!))
    ))
    :pattern ((height (vstd!seq.Seq.index.? A&. A& s! i!)))
    :qid user_vstd__seq__axiom_seq_index_decreases_0
    :skolemid skolem_user_vstd__seq__axiom_seq_index_decreases_0
))))

;; Function-Specs vstd::seq::Seq::subrange
(declare-fun req%vstd!seq.Seq.subrange. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%2 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (start_inclusive! Poly) (end_exclusive! Poly))
  (!
   (= (req%vstd!seq.Seq.subrange. A&. A& self! start_inclusive! end_exclusive!) (=>
     %%global_location_label%%2
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I start_inclusive!)))
       (let
        ((tmp%%$2 (%I end_exclusive!)))
        (let
         ((tmp%%$3 (vstd!seq.Seq.len.? A&. A& self!)))
         (and
          (and
           (<= tmp%%$ tmp%%$1)
           (<= tmp%%$1 tmp%%$2)
          )
          (<= tmp%%$2 tmp%%$3)
   )))))))
   :pattern ((req%vstd!seq.Seq.subrange. A&. A& self! start_inclusive! end_exclusive!))
   :qid internal_req__vstd!seq.Seq.subrange._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.subrange._definition
)))

;; Function-Axioms vstd::seq::Seq::subrange
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (start_inclusive! Poly) (end_exclusive! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type start_inclusive! INT)
     (has_type end_exclusive! INT)
    )
    (has_type (vstd!seq.Seq.subrange.? A&. A& self! start_inclusive! end_exclusive!) (
      TYPE%vstd!seq.Seq. A&. A&
   )))
   :pattern ((vstd!seq.Seq.subrange.? A&. A& self! start_inclusive! end_exclusive!))
   :qid internal_vstd!seq.Seq.subrange.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.subrange.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_subrange_decreases
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_subrange_decreases.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (i! Poly) (j! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
      (has_type j! INT)
     )
     (=>
      (and
       (and
        (sized A&.)
        (let
         ((tmp%%$ 0))
         (let
          ((tmp%%$1 (%I i!)))
          (let
           ((tmp%%$2 (%I j!)))
           (let
            ((tmp%%$3 (vstd!seq.Seq.len.? A&. A& s!)))
            (and
             (and
              (<= tmp%%$ tmp%%$1)
              (<= tmp%%$1 tmp%%$2)
             )
             (<= tmp%%$2 tmp%%$3)
       ))))))
       (< (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! i! j!)) (vstd!seq.Seq.len.?
         A&. A& s!
      )))
      (height_lt (height (vstd!seq.Seq.subrange.? A&. A& s! i! j!)) (height s!))
    ))
    :pattern ((height (vstd!seq.Seq.subrange.? A&. A& s! i! j!)))
    :qid user_vstd__seq__axiom_seq_subrange_decreases_1
    :skolemid skolem_user_vstd__seq__axiom_seq_subrange_decreases_1
))))

;; Function-Axioms vstd::seq::Seq::empty
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!seq.Seq.empty.? A&. A&) (TYPE%vstd!seq.Seq. A&. A&))
   :pattern ((vstd!seq.Seq.empty.? A&. A&))
   :qid internal_vstd!seq.Seq.empty.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.empty.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_empty
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_empty.)
  (forall ((A&. Dcr) (A& Type)) (!
    (=>
     (sized A&.)
     (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.? A&. A&)) 0)
    )
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.empty.? A&. A&)))
    :qid user_vstd__seq__axiom_seq_empty_2
    :skolemid skolem_user_vstd__seq__axiom_seq_empty_2
))))

;; Function-Axioms vstd::seq::Seq::new
(assert
 (forall ((A&. Dcr) (A& Type) (impl%1&. Dcr) (impl%1& Type) (len! Poly) (f! Poly))
  (!
   (=>
    (and
     (has_type len! NAT)
     (has_type f! impl%1&)
    )
    (has_type (vstd!seq.Seq.new.? A&. A& impl%1&. impl%1& len! f!) (TYPE%vstd!seq.Seq.
      A&. A&
   )))
   :pattern ((vstd!seq.Seq.new.? A&. A& impl%1&. impl%1& len! f!))
   :qid internal_vstd!seq.Seq.new.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.new.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_new_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_new_len.)
  (forall ((A&. Dcr) (A& Type) (len! Poly) (f! Poly)) (!
    (=>
     (and
      (has_type len! NAT)
      (has_type f! (TYPE%fun%1. $ INT A&. A&))
     )
     (=>
      (sized A&.)
      (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&)
         len! f!
        )
       ) (%I len!)
    )))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT
        A&. A&
       ) len! f!
    )))
    :qid user_vstd__seq__axiom_seq_new_len_3
    :skolemid skolem_user_vstd__seq__axiom_seq_new_len_3
))))

;; Broadcast vstd::seq::axiom_seq_new_index
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_new_index.)
  (forall ((A&. Dcr) (A& Type) (len! Poly) (f! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type len! NAT)
      (has_type f! (TYPE%fun%1. $ INT A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (%I len!)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
      )))))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT A&. A&)
         len! f!
        ) i!
       ) (%%apply%%0 (%Poly%fun%1. f!) i!)
    )))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.new.? A&. A& $ (TYPE%fun%1. $ INT
        A&. A&
       ) len! f!
      ) i!
    ))
    :qid user_vstd__seq__axiom_seq_new_index_4
    :skolemid skolem_user_vstd__seq__axiom_seq_new_index_4
))))

;; Function-Axioms vstd::seq::Seq::push
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!seq.Seq.push.? A&. A& self! a!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.push.? A&. A& self! a!))
   :qid internal_vstd!seq.Seq.push.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.push.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_push_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_push_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!)) (nClip (Add (vstd!seq.Seq.len.?
          A&. A& s!
         ) 1
    )))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!)))
    :qid user_vstd__seq__axiom_seq_push_len_5
    :skolemid skolem_user_vstd__seq__axiom_seq_push_len_5
))))

;; Broadcast vstd::seq::axiom_seq_push_index_same
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_push_index_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type a! A&)
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (= (%I i!) (vstd!seq.Seq.len.? A&. A& s!))
      )
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!) a!)
    ))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!))
    :qid user_vstd__seq__axiom_seq_push_index_same_6
    :skolemid skolem_user_vstd__seq__axiom_seq_push_index_same_6
))))

;; Broadcast vstd::seq::axiom_seq_push_index_different
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_push_index_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type a! A&)
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& s!)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
      )))))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!) (vstd!seq.Seq.index.?
        A&. A& s! i!
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.push.? A&. A& s! a!) i!))
    :qid user_vstd__seq__axiom_seq_push_index_different_7
    :skolemid skolem_user_vstd__seq__axiom_seq_push_index_different_7
))))

;; Broadcast vstd::seq::axiom_seq_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_ext_equal.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
        (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
        (forall ((i$ Poly)) (!
          (=>
           (has_type i$ INT)
           (=>
            (let
             ((tmp%%$ 0))
             (let
              ((tmp%%$1 (%I i$)))
              (let
               ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& s1!)))
               (and
                (<= tmp%%$ tmp%%$1)
                (< tmp%%$1 tmp%%$2)
            ))))
            (= (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2! i$))
          ))
          :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
          :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
          :qid user_vstd__seq__axiom_seq_ext_equal_8
          :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_8
    ))))))
    :pattern ((ext_eq false (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
    :qid user_vstd__seq__axiom_seq_ext_equal_9
    :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_9
))))

;; Broadcast vstd::seq::axiom_seq_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_ext_equal_deep.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!) (and
        (= (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!))
        (forall ((i$ Poly)) (!
          (=>
           (has_type i$ INT)
           (=>
            (let
             ((tmp%%$ 0))
             (let
              ((tmp%%$1 (%I i$)))
              (let
               ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& s1!)))
               (and
                (<= tmp%%$ tmp%%$1)
                (< tmp%%$1 tmp%%$2)
            ))))
            (ext_eq true A& (vstd!seq.Seq.index.? A&. A& s1! i$) (vstd!seq.Seq.index.? A&. A& s2!
              i$
          ))))
          :pattern ((vstd!seq.Seq.index.? A&. A& s1! i$))
          :pattern ((vstd!seq.Seq.index.? A&. A& s2! i$))
          :qid user_vstd__seq__axiom_seq_ext_equal_deep_10
          :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_10
    ))))))
    :pattern ((ext_eq true (TYPE%vstd!seq.Seq. A&. A&) s1! s2!))
    :qid user_vstd__seq__axiom_seq_ext_equal_deep_11
    :skolemid skolem_user_vstd__seq__axiom_seq_ext_equal_deep_11
))))

;; Broadcast vstd::seq::axiom_seq_subrange_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_subrange_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type j! INT)
      (has_type k! INT)
     )
     (=>
      (and
       (sized A&.)
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I j!)))
         (let
          ((tmp%%$2 (%I k!)))
          (let
           ((tmp%%$3 (vstd!seq.Seq.len.? A&. A& s!)))
           (and
            (and
             (<= tmp%%$ tmp%%$1)
             (<= tmp%%$1 tmp%%$2)
            )
            (<= tmp%%$2 tmp%%$3)
      ))))))
      (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!)) (Sub (%I k!)
        (%I j!)
    ))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!)))
    :qid user_vstd__seq__axiom_seq_subrange_len_12
    :skolemid skolem_user_vstd__seq__axiom_seq_subrange_len_12
))))

;; Broadcast vstd::seq::axiom_seq_subrange_index
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_subrange_index.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type j! INT)
      (has_type k! INT)
      (has_type i! INT)
     )
     (=>
      (and
       (and
        (sized A&.)
        (let
         ((tmp%%$ 0))
         (let
          ((tmp%%$1 (%I j!)))
          (let
           ((tmp%%$2 (%I k!)))
           (let
            ((tmp%%$3 (vstd!seq.Seq.len.? A&. A& s!)))
            (and
             (and
              (<= tmp%%$ tmp%%$1)
              (<= tmp%%$1 tmp%%$2)
             )
             (<= tmp%%$2 tmp%%$3)
       ))))))
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$5 (%I i!)))
         (let
          ((tmp%%$6 (Sub (%I k!) (%I j!))))
          (and
           (<= tmp%%$ tmp%%$5)
           (< tmp%%$5 tmp%%$6)
      )))))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!) i!) (vstd!seq.Seq.index.?
        A&. A& s! (I (Add (%I i!) (%I j!)))
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k!) i!))
    :qid user_vstd__seq__axiom_seq_subrange_index_13
    :skolemid skolem_user_vstd__seq__axiom_seq_subrange_index_13
))))

;; Broadcast vstd::seq::lemma_seq_two_subranges_index
(assert
 (=>
  (fuel_bool fuel%vstd!seq.lemma_seq_two_subranges_index.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (j! Poly) (k1! Poly) (k2! Poly) (i! Poly))
   (!
    (=>
     (and
      (has_type s! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type j! INT)
      (has_type k1! INT)
      (has_type k2! INT)
      (has_type i! INT)
     )
     (=>
      (and
       (and
        (and
         (and
          (sized A&.)
          (let
           ((tmp%%$ 0))
           (let
            ((tmp%%$1 (%I j!)))
            (let
             ((tmp%%$2 (%I k1!)))
             (let
              ((tmp%%$3 (vstd!seq.Seq.len.? A&. A& s!)))
              (and
               (and
                (<= tmp%%$ tmp%%$1)
                (<= tmp%%$1 tmp%%$2)
               )
               (<= tmp%%$2 tmp%%$3)
         ))))))
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$5 (%I j!)))
           (let
            ((tmp%%$6 (%I k2!)))
            (let
             ((tmp%%$7 (vstd!seq.Seq.len.? A&. A& s!)))
             (and
              (and
               (<= tmp%%$ tmp%%$5)
               (<= tmp%%$5 tmp%%$6)
              )
              (<= tmp%%$6 tmp%%$7)
        ))))))
        (let
         ((tmp%%$ 0))
         (let
          ((tmp%%$9 (%I i!)))
          (let
           ((tmp%%$10 (Sub (%I k1!) (%I j!))))
           (and
            (<= tmp%%$ tmp%%$9)
            (< tmp%%$9 tmp%%$10)
       )))))
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$12 (%I i!)))
         (let
          ((tmp%%$13 (Sub (%I k2!) (%I j!))))
          (and
           (<= tmp%%$ tmp%%$12)
           (< tmp%%$12 tmp%%$13)
      )))))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k1!) i!) (vstd!seq.Seq.index.?
        A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k2!) i!
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.subrange.? A&. A& s! j! k1!) i!)
     (vstd!seq.Seq.subrange.? A&. A& s! j! k2!)
    )
    :qid user_vstd__seq__lemma_seq_two_subranges_index_14
    :skolemid skolem_user_vstd__seq__lemma_seq_two_subranges_index_14
))))

;; Function-Axioms vstd::seq::Seq::add
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type rhs! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (has_type (vstd!seq.Seq.add.? A&. A& self! rhs!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.Seq.add.? A&. A& self! rhs!))
   :qid internal_vstd!seq.Seq.add.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.add.?_pre_post_definition
)))

;; Broadcast vstd::seq::axiom_seq_add_len
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_add_len.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (sized A&.)
      (= (vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!)) (nClip (Add (vstd!seq.Seq.len.?
          A&. A& s1!
         ) (vstd!seq.Seq.len.? A&. A& s2!)
    )))))
    :pattern ((vstd!seq.Seq.len.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!)))
    :qid user_vstd__seq__axiom_seq_add_len_15
    :skolemid skolem_user_vstd__seq__axiom_seq_add_len_15
))))

;; Broadcast vstd::seq::axiom_seq_add_index1
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_add_index1.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& s1!)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
      )))))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!) (vstd!seq.Seq.index.?
        A&. A& s1! i!
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!))
    :qid user_vstd__seq__axiom_seq_add_index1_16
    :skolemid skolem_user_vstd__seq__axiom_seq_add_index1_16
))))

;; Broadcast vstd::seq::axiom_seq_add_index2
(assert
 (=>
  (fuel_bool fuel%vstd!seq.axiom_seq_add_index2.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type s2! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type i! INT)
     )
     (=>
      (and
       (sized A&.)
       (let
        ((tmp%%$ (vstd!seq.Seq.len.? A&. A& s1!)))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (nClip (Add (vstd!seq.Seq.len.? A&. A& s1!) (vstd!seq.Seq.len.? A&. A& s2!)))))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
      )))))
      (= (vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!) (vstd!seq.Seq.index.?
        A&. A& s2! (I (Sub (%I i!) (vstd!seq.Seq.len.? A&. A& s1!)))
    ))))
    :pattern ((vstd!seq.Seq.index.? A&. A& (vstd!seq.Seq.add.? A&. A& s1! s2!) i!))
    :qid user_vstd__seq__axiom_seq_add_index2_17
    :skolemid skolem_user_vstd__seq__axiom_seq_add_index2_17
))))

;; Function-Axioms vstd::seq::impl&%0::spec_add
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.spec_add.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.spec_add.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
    (= (vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!) (vstd!seq.Seq.add.? A&. A& self!
      rhs!
    ))
    :pattern ((vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!))
    :qid internal_vstd!seq.impl&__0.spec_add.?_definition
    :skolemid skolem_internal_vstd!seq.impl&__0.spec_add.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (rhs! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type rhs! (TYPE%vstd!seq.Seq. A&. A&))
    )
    (has_type (vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq.impl&%0.spec_add.? A&. A& self! rhs!))
   :qid internal_vstd!seq.impl&__0.spec_add.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.impl&__0.spec_add.?_pre_post_definition
)))

;; Broadcast vstd::seq_lib::impl&%0::add_empty_left
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.add_empty_left.)
  (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
    (=>
     (and
      (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (and
       (sized A&.)
       (= (vstd!seq.Seq.len.? A&. A& a!) 0)
      )
      (= (vstd!seq.Seq.add.? A&. A& a! b!) b!)
    ))
    :pattern ((vstd!seq.Seq.add.? A&. A& a! b!))
    :qid user_vstd__seq_lib__impl&%0__add_empty_left_18
    :skolemid skolem_user_vstd__seq_lib__impl&%0__add_empty_left_18
))))

;; Broadcast vstd::seq_lib::impl&%0::add_empty_right
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.add_empty_right.)
  (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly)) (!
    (=>
     (and
      (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
     )
     (=>
      (and
       (sized A&.)
       (= (vstd!seq.Seq.len.? A&. A& b!) 0)
      )
      (= (vstd!seq.Seq.add.? A&. A& a! b!) a!)
    ))
    :pattern ((vstd!seq.Seq.add.? A&. A& a! b!))
    :qid user_vstd__seq_lib__impl&%0__add_empty_right_19
    :skolemid skolem_user_vstd__seq_lib__impl&%0__add_empty_right_19
))))

;; Broadcast vstd::seq_lib::impl&%0::push_distributes_over_add
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.push_distributes_over_add.)
  (forall ((A&. Dcr) (A& Type) (a! Poly) (b! Poly) (elt! Poly)) (!
    (=>
     (and
      (has_type a! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type b! (TYPE%vstd!seq.Seq. A&. A&))
      (has_type elt! A&)
     )
     (=>
      (sized A&.)
      (= (vstd!seq.Seq.push.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) elt!) (vstd!seq.Seq.add.?
        A&. A& a! (vstd!seq.Seq.push.? A&. A& b! elt!)
    ))))
    :pattern ((vstd!seq.Seq.push.? A&. A& (vstd!seq.Seq.add.? A&. A& a! b!) elt!))
    :qid user_vstd__seq_lib__impl&%0__push_distributes_over_add_20
    :skolemid skolem_user_vstd__seq_lib__impl&%0__push_distributes_over_add_20
))))

;; Function-Axioms vstd::map::impl&%0::dom
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
    (has_type (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) (TYPE%vstd!set.Set. K&. K&))
   )
   :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& self!))
   :qid internal_vstd!map.impl&__0.dom.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.dom.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::index
(declare-fun req%vstd!map.impl&%0.index. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%3 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.index. K&. K& V&. V& self! key!) (=>
     %%global_location_label%%3
     (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.index. K&. K& V&. V& self! key!))
   :qid internal_req__vstd!map.impl&__0.index._definition
   :skolemid skolem_internal_req__vstd!map.impl&__0.index._definition
)))

;; Function-Axioms vstd::map::impl&%0::index
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.index.? K&. K& V&. V& self! key!) V&)
   )
   :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.index.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.index.?_pre_post_definition
)))

;; Function-Specs vstd::map::impl&%0::spec_index
(declare-fun req%vstd!map.impl&%0.spec_index. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%4 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.spec_index. K&. K& V&. V& self! key!) (=>
     %%global_location_label%%4
     (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.spec_index. K&. K& V&. V& self! key!))
   :qid internal_req__vstd!map.impl&__0.spec_index._definition
   :skolemid skolem_internal_req__vstd!map.impl&__0.spec_index._definition
)))

;; Function-Axioms vstd::map::impl&%0::spec_index
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.spec_index.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
    (= (vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!) (vstd!map.impl&%0.index.?
      K&. K& V&. V& self! key!
    ))
    :pattern ((vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!))
    :qid internal_vstd!map.impl&__0.spec_index.?_definition
    :skolemid skolem_internal_vstd!map.impl&__0.spec_index.?_definition
))))
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!) V&)
   )
   :pattern ((vstd!map.impl&%0.spec_index.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.spec_index.?_pre_post_definition
)))

;; Broadcast vstd::map::axiom_map_index_decreases_finite
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_index_decreases_finite.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (and
        (and
         (sized K&.)
         (sized V&.)
        )
        (vstd!set.impl&%0.finite.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!))
       )
       (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
      )
      (height_lt (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height m!))
    ))
    :pattern ((height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)))
    :qid user_vstd__map__axiom_map_index_decreases_finite_21
    :skolemid skolem_user_vstd__map__axiom_map_index_decreases_finite_21
))))

;; Broadcast vstd::map::axiom_map_index_decreases_infinite
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_index_decreases_infinite.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
      )
      (height_lt (height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)) (height (fun_from_recursive_field
         m!
    )))))
    :pattern ((height (vstd!map.impl&%0.index.? K&. K& V&. V& m! key!)))
    :qid user_vstd__map__axiom_map_index_decreases_infinite_22
    :skolemid skolem_user_vstd__map__axiom_map_index_decreases_infinite_22
))))

;; Function-Axioms vstd::set::Set::empty
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!set.Set.empty.? A&. A&) (TYPE%vstd!set.Set. A&. A&))
   :pattern ((vstd!set.Set.empty.? A&. A&))
   :qid internal_vstd!set.Set.empty.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.Set.empty.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::insert
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly) (value! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
     (has_type value! V&)
    )
    (has_type (vstd!map.impl&%0.insert.? K&. K& V&. V& self! key! value!) (TYPE%vstd!map.Map.
      K&. K& V&. V&
   )))
   :pattern ((vstd!map.impl&%0.insert.? K&. K& V&. V& self! key! value!))
   :qid internal_vstd!map.impl&__0.insert.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.insert.?_pre_post_definition
)))

;; Function-Axioms vstd::set::Set::insert
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.Set.insert.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.Set.insert.? A&. A& self! a!))
   :qid internal_vstd!set.Set.insert.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.Set.insert.?_pre_post_definition
)))

;; Broadcast vstd::map::axiom_map_insert_domain
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_insert_domain.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
   (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
      (has_type value! V&)
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V& m!
         key! value!
        )
       ) (vstd!set.Set.insert.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
    )))
    :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&.
       V& m! key! value!
    )))
    :qid user_vstd__map__axiom_map_insert_domain_23
    :skolemid skolem_user_vstd__map__axiom_map_insert_domain_23
))))

;; Broadcast vstd::map::axiom_map_insert_same
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_insert_same.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly) (value! Poly))
   (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
      (has_type value! V&)
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
         m! key! value!
        ) key!
       ) value!
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K&
       V&. V& m! key! value!
      ) key!
    ))
    :qid user_vstd__map__axiom_map_insert_same_24
    :skolemid skolem_user_vstd__map__axiom_map_insert_same_24
))))

;; Broadcast vstd::map::axiom_map_insert_different
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_insert_different.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly)
    (value! Poly)
   ) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key1! K&)
      (has_type key2! K&)
      (has_type value! V&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (not (= key1! key2!))
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K& V&. V&
         m! key2! value!
        ) key1!
       ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.insert.? K&. K&
       V&. V& m! key2! value!
      ) key1!
    ))
    :qid user_vstd__map__axiom_map_insert_different_25
    :skolemid skolem_user_vstd__map__axiom_map_insert_different_25
))))

;; Function-Axioms vstd::map::impl&%0::remove
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (key! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type key! K&)
    )
    (has_type (vstd!map.impl&%0.remove.? K&. K& V&. V& self! key!) (TYPE%vstd!map.Map.
      K&. K& V&. V&
   )))
   :pattern ((vstd!map.impl&%0.remove.? K&. K& V&. V& self! key!))
   :qid internal_vstd!map.impl&__0.remove.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.remove.?_pre_post_definition
)))

;; Function-Axioms vstd::set::Set::remove
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (a! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type a! A&)
    )
    (has_type (vstd!set.Set.remove.? A&. A& self! a!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.Set.remove.? A&. A& self! a!))
   :qid internal_vstd!set.Set.remove.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.Set.remove.?_pre_post_definition
)))

;; Broadcast vstd::map::axiom_map_remove_domain
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_remove_domain.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key! Poly)) (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V& m!
         key!
        )
       ) (vstd!set.Set.remove.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m!) key!)
    )))
    :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&.
       V& m! key!
    )))
    :qid user_vstd__map__axiom_map_remove_domain_26
    :skolemid skolem_user_vstd__map__axiom_map_remove_domain_26
))))

;; Broadcast vstd::map::axiom_map_remove_different
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_remove_different.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m! Poly) (key1! Poly) (key2! Poly))
   (!
    (=>
     (and
      (has_type m! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type key1! K&)
      (has_type key2! K&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (not (= key1! key2!))
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K& V&. V&
         m! key2!
        ) key1!
       ) (vstd!map.impl&%0.index.? K&. K& V&. V& m! key1!)
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!map.impl&%0.remove.? K&. K&
       V&. V& m! key2!
      ) key1!
    ))
    :qid user_vstd__map__axiom_map_remove_different_27
    :skolemid skolem_user_vstd__map__axiom_map_remove_different_27
))))

;; Broadcast vstd::map::axiom_map_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_ext_equal.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
    (=>
     (and
      (has_type m1! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type m2! (TYPE%vstd!map.Map. K&. K& V&. V&))
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (ext_eq false (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!) (and
        (ext_eq false (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
         (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
        )
        (forall ((k$ Poly)) (!
          (=>
           (has_type k$ K&)
           (=>
            (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
            (= (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.? K&. K&
              V&. V& m2! k$
          ))))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
          :qid user_vstd__map__axiom_map_ext_equal_28
          :skolemid skolem_user_vstd__map__axiom_map_ext_equal_28
    ))))))
    :pattern ((ext_eq false (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!))
    :qid user_vstd__map__axiom_map_ext_equal_29
    :skolemid skolem_user_vstd__map__axiom_map_ext_equal_29
))))

;; Broadcast vstd::map::axiom_map_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!map.axiom_map_ext_equal_deep.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (m1! Poly) (m2! Poly)) (!
    (=>
     (and
      (has_type m1! (TYPE%vstd!map.Map. K&. K& V&. V&))
      (has_type m2! (TYPE%vstd!map.Map. K&. K& V&. V&))
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (ext_eq true (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!) (and
        (ext_eq true (TYPE%vstd!set.Set. K&. K&) (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!)
         (vstd!map.impl&%0.dom.? K&. K& V&. V& m2!)
        )
        (forall ((k$ Poly)) (!
          (=>
           (has_type k$ K&)
           (=>
            (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& m1!) k$)
            (ext_eq true V& (vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$) (vstd!map.impl&%0.index.?
              K&. K& V&. V& m2! k$
          ))))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m1! k$))
          :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& m2! k$))
          :qid user_vstd__map__axiom_map_ext_equal_deep_30
          :skolemid skolem_user_vstd__map__axiom_map_ext_equal_deep_30
    ))))))
    :pattern ((ext_eq true (TYPE%vstd!map.Map. K&. K& V&. V&) m1! m2!))
    :qid user_vstd__map__axiom_map_ext_equal_deep_31
    :skolemid skolem_user_vstd__map__axiom_map_ext_equal_deep_31
))))

;; Broadcast vstd::set::axiom_set_empty
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_empty.)
  (forall ((A&. Dcr) (A& Type) (a! Poly)) (!
    (=>
     (has_type a! A&)
     (=>
      (sized A&.)
      (not (vstd!set.Set.contains.? A&. A& (vstd!set.Set.empty.? A&. A&) a!))
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.empty.? A&. A&) a!))
    :qid user_vstd__set__axiom_set_empty_32
    :skolemid skolem_user_vstd__set__axiom_set_empty_32
))))

;; Function-Axioms vstd::set::impl&%0::new
(assert
 (forall ((A&. Dcr) (A& Type) (f! Poly)) (!
   (=>
    (has_type f! (TYPE%fun%1. A&. A& $ BOOL))
    (has_type (vstd!set.impl&%0.new.? A&. A& f!) (TYPE%vstd!set.Set. A&. A&))
   )
   :pattern ((vstd!set.impl&%0.new.? A&. A& f!))
   :qid internal_vstd!set.impl&__0.new.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.impl&__0.new.?_pre_post_definition
)))

;; Broadcast vstd::set::axiom_set_new
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_new.)
  (forall ((A&. Dcr) (A& Type) (f! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type f! (TYPE%fun%1. A&. A& $ BOOL))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.impl&%0.new.? A&. A& f!) a!) (%B (%%apply%%0
         (%Poly%fun%1. f!) a!
    )))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.impl&%0.new.? A&. A& f!) a!))
    :qid user_vstd__set__axiom_set_new_33
    :skolemid skolem_user_vstd__set__axiom_set_new_33
))))

;; Broadcast vstd::set::axiom_set_insert_same
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!) a!)
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!) a!))
    :qid user_vstd__set__axiom_set_insert_same_34
    :skolemid skolem_user_vstd__set__axiom_set_insert_same_34
))))

;; Broadcast vstd::set::axiom_set_insert_different
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a1! A&)
      (has_type a2! A&)
     )
     (=>
      (and
       (sized A&.)
       (not (= a1! a2!))
      )
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a2!) a1!) (vstd!set.Set.contains.?
        A&. A& s! a1!
    ))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.insert.? A&. A& s! a2!) a1!))
    :qid user_vstd__set__axiom_set_insert_different_35
    :skolemid skolem_user_vstd__set__axiom_set_insert_different_35
))))

;; Broadcast vstd::set::axiom_set_remove_same
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_same.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (not (vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!) a!))
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!) a!))
    :qid user_vstd__set__axiom_set_remove_same_36
    :skolemid skolem_user_vstd__set__axiom_set_remove_same_36
))))

;; Broadcast vstd::set::axiom_set_remove_insert
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_insert.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.Set.contains.? A&. A& s! a!)
      )
      (= (vstd!set.Set.insert.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!) a!) s!)
    ))
    :pattern ((vstd!set.Set.remove.? A&. A& s! a!))
    :qid user_vstd__set__axiom_set_remove_insert_37
    :skolemid skolem_user_vstd__set__axiom_set_remove_insert_37
))))

;; Broadcast vstd::set::axiom_set_remove_different
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_different.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a1! Poly) (a2! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a1! A&)
      (has_type a2! A&)
     )
     (=>
      (and
       (sized A&.)
       (not (= a1! a2!))
      )
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a2!) a1!) (vstd!set.Set.contains.?
        A&. A& s! a1!
    ))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.Set.remove.? A&. A& s! a2!) a1!))
    :qid user_vstd__set__axiom_set_remove_different_38
    :skolemid skolem_user_vstd__set__axiom_set_remove_different_38
))))

;; Function-Axioms vstd::set::impl&%0::difference
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (s2! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type s2! (TYPE%vstd!set.Set. A&. A&))
    )
    (has_type (vstd!set.impl&%0.difference.? A&. A& self! s2!) (TYPE%vstd!set.Set. A&.
      A&
   )))
   :pattern ((vstd!set.impl&%0.difference.? A&. A& self! s2!))
   :qid internal_vstd!set.impl&__0.difference.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.impl&__0.difference.?_pre_post_definition
)))

;; Broadcast vstd::set::axiom_set_difference
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_difference.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (sized A&.)
      (= (vstd!set.Set.contains.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1! s2!) a!)
       (and
        (vstd!set.Set.contains.? A&. A& s1! a!)
        (not (vstd!set.Set.contains.? A&. A& s2! a!))
    ))))
    :pattern ((vstd!set.Set.contains.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1!
       s2!
      ) a!
    ))
    :qid user_vstd__set__axiom_set_difference_39
    :skolemid skolem_user_vstd__set__axiom_set_difference_39
))))

;; Broadcast vstd::set::axiom_set_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_ext_equal.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!) (forall ((a$ Poly)) (!
         (=>
          (has_type a$ A&)
          (= (vstd!set.Set.contains.? A&. A& s1! a$) (vstd!set.Set.contains.? A&. A& s2! a$))
         )
         :pattern ((vstd!set.Set.contains.? A&. A& s1! a$))
         :pattern ((vstd!set.Set.contains.? A&. A& s2! a$))
         :qid user_vstd__set__axiom_set_ext_equal_40
         :skolemid skolem_user_vstd__set__axiom_set_ext_equal_40
    )))))
    :pattern ((ext_eq false (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    :qid user_vstd__set__axiom_set_ext_equal_41
    :skolemid skolem_user_vstd__set__axiom_set_ext_equal_41
))))

;; Broadcast vstd::set::axiom_set_ext_equal_deep
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_ext_equal_deep.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (sized A&.)
      (= (ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!) (ext_eq false (TYPE%vstd!set.Set.
         A&. A&
        ) s1! s2!
    ))))
    :pattern ((ext_eq true (TYPE%vstd!set.Set. A&. A&) s1! s2!))
    :qid user_vstd__set__axiom_set_ext_equal_deep_42
    :skolemid skolem_user_vstd__set__axiom_set_ext_equal_deep_42
))))

;; Function-Axioms vstd::set::impl&%0::mk_map
(assert
 (forall ((A&. Dcr) (A& Type) (V&. Dcr) (V& Type) (self! Poly) (f! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!set.Set. A&. A&))
     (has_type f! (TYPE%fun%1. A&. A& V&. V&))
    )
    (has_type (vstd!set.impl&%0.mk_map.? A&. A& V&. V& self! f!) (TYPE%vstd!map.Map. A&.
      A& V&. V&
   )))
   :pattern ((vstd!set.impl&%0.mk_map.? A&. A& V&. V& self! f!))
   :qid internal_vstd!set.impl&__0.mk_map.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.impl&__0.mk_map.?_pre_post_definition
)))

;; Broadcast vstd::set::axiom_mk_map_domain
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_mk_map_domain.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. K&. K&))
      (has_type f! (TYPE%fun%1. K&. K& V&. V&))
     )
     (=>
      (and
       (sized K&.)
       (sized V&.)
      )
      (= (vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&. V& s!
         f!
        )
       ) s!
    )))
    :pattern ((vstd!map.impl&%0.dom.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&.
       V& s! f!
    )))
    :qid user_vstd__set__axiom_mk_map_domain_43
    :skolemid skolem_user_vstd__set__axiom_mk_map_domain_43
))))

;; Broadcast vstd::set::axiom_mk_map_index
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_mk_map_index.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (s! Poly) (f! Poly) (key! Poly))
   (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. K&. K&))
      (has_type f! (TYPE%fun%1. K&. K& V&. V&))
      (has_type key! K&)
     )
     (=>
      (and
       (and
        (sized K&.)
        (sized V&.)
       )
       (vstd!set.Set.contains.? K&. K& s! key!)
      )
      (= (vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K& V&. V&
         s! f!
        ) key!
       ) (%%apply%%0 (%Poly%fun%1. f!) key!)
    )))
    :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& (vstd!set.impl&%0.mk_map.? K&. K&
       V&. V& s! f!
      ) key!
    ))
    :qid user_vstd__set__axiom_mk_map_index_44
    :skolemid skolem_user_vstd__set__axiom_mk_map_index_44
))))

;; Broadcast vstd::set::axiom_set_empty_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_empty_finite.)
  (forall ((A&. Dcr) (A& Type)) (!
    (=>
     (sized A&.)
     (vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.empty.? A&. A&))
    )
    :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.empty.? A&. A&)))
    :qid user_vstd__set__axiom_set_empty_finite_45
    :skolemid skolem_user_vstd__set__axiom_set_empty_finite_45
))))

;; Broadcast vstd::set::axiom_set_insert_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_finite.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s!)
      )
      (vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!))
    ))
    :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!)))
    :qid user_vstd__set__axiom_set_insert_finite_46
    :skolemid skolem_user_vstd__set__axiom_set_insert_finite_46
))))

;; Broadcast vstd::set::axiom_set_remove_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_finite.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s!)
      )
      (vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!))
    ))
    :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!)))
    :qid user_vstd__set__axiom_set_remove_finite_47
    :skolemid skolem_user_vstd__set__axiom_set_remove_finite_47
))))

;; Broadcast vstd::set::axiom_set_difference_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_difference_finite.)
  (forall ((A&. Dcr) (A& Type) (s1! Poly) (s2! Poly)) (!
    (=>
     (and
      (has_type s1! (TYPE%vstd!set.Set. A&. A&))
      (has_type s2! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s1!)
      )
      (vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1! s2!))
    ))
    :pattern ((vstd!set.impl&%0.finite.? A&. A& (vstd!set.impl&%0.difference.? A&. A& s1!
       s2!
    )))
    :qid user_vstd__set__axiom_set_difference_finite_48
    :skolemid skolem_user_vstd__set__axiom_set_difference_finite_48
))))

;; Function-Axioms vstd::set::impl&%0::len
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!set.Set. A&. A&))
    (<= 0 (vstd!set.impl&%0.len.? A&. A& self!))
   )
   :pattern ((vstd!set.impl&%0.len.? A&. A& self!))
   :qid internal_vstd!set.impl&__0.len.?_pre_post_definition
   :skolemid skolem_internal_vstd!set.impl&__0.len.?_pre_post_definition
)))

;; Broadcast vstd::set::axiom_set_empty_len
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_empty_len.)
  (forall ((A&. Dcr) (A& Type)) (!
    (=>
     (sized A&.)
     (= (vstd!set.impl&%0.len.? A&. A& (vstd!set.Set.empty.? A&. A&)) 0)
    )
    :pattern ((vstd!set.impl&%0.len.? A&. A& (vstd!set.Set.empty.? A&. A&)))
    :qid user_vstd__set__axiom_set_empty_len_49
    :skolemid skolem_user_vstd__set__axiom_set_empty_len_49
))))

;; Broadcast vstd::set::axiom_set_insert_len
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_insert_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s!)
      )
      (= (vstd!set.impl&%0.len.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!)) (Add (vstd!set.impl&%0.len.?
         A&. A& s!
        ) (ite
         (vstd!set.Set.contains.? A&. A& s! a!)
         0
         1
    )))))
    :pattern ((vstd!set.impl&%0.len.? A&. A& (vstd!set.Set.insert.? A&. A& s! a!)))
    :qid user_vstd__set__axiom_set_insert_len_50
    :skolemid skolem_user_vstd__set__axiom_set_insert_len_50
))))

;; Broadcast vstd::set::axiom_set_remove_len
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_remove_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (sized A&.)
       (vstd!set.impl&%0.finite.? A&. A& s!)
      )
      (= (vstd!set.impl&%0.len.? A&. A& s!) (Add (vstd!set.impl&%0.len.? A&. A& (vstd!set.Set.remove.?
          A&. A& s! a!
         )
        ) (ite
         (vstd!set.Set.contains.? A&. A& s! a!)
         1
         0
    )))))
    :pattern ((vstd!set.impl&%0.len.? A&. A& (vstd!set.Set.remove.? A&. A& s! a!)))
    :qid user_vstd__set__axiom_set_remove_len_51
    :skolemid skolem_user_vstd__set__axiom_set_remove_len_51
))))

;; Broadcast vstd::set::axiom_set_contains_len
(assert
 (=>
  (fuel_bool fuel%vstd!set.axiom_set_contains_len.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (a! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type a! A&)
     )
     (=>
      (and
       (and
        (sized A&.)
        (vstd!set.impl&%0.finite.? A&. A& s!)
       )
       (vstd!set.Set.contains.? A&. A& s! a!)
      )
      (not (= (vstd!set.impl&%0.len.? A&. A& s!) 0))
    ))
    :pattern ((vstd!set.Set.contains.? A&. A& s! a!) (vstd!set.impl&%0.len.? A&. A& s!))
    :qid user_vstd__set__axiom_set_contains_len_52
    :skolemid skolem_user_vstd__set__axiom_set_contains_len_52
))))

;; Function-Axioms vstd::set_lib::impl&%0::is_empty
(assert
 (fuel_bool_default fuel%vstd!set_lib.impl&%0.is_empty.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!set_lib.impl&%0.is_empty.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!set_lib.impl&%0.is_empty.? A&. A& self!) (ext_eq false (TYPE%vstd!set.Set.
       A&. A&
      ) self! (vstd!set.Set.empty.? A&. A&)
    ))
    :pattern ((vstd!set_lib.impl&%0.is_empty.? A&. A& self!))
    :qid internal_vstd!set_lib.impl&__0.is_empty.?_definition
    :skolemid skolem_internal_vstd!set_lib.impl&__0.is_empty.?_definition
))))

;; Broadcast vstd::set_lib::axiom_is_empty
(assert
 (=>
  (fuel_bool fuel%vstd!set_lib.axiom_is_empty.)
  (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
    (=>
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (=>
      (and
       (sized A&.)
       (not (vstd!set_lib.impl&%0.is_empty.? A&. A& s!))
      )
      (exists ((a$ Poly)) (!
        (and
         (has_type a$ A&)
         (vstd!set.Set.contains.? A&. A& s! a$)
        )
        :pattern ((vstd!set.Set.contains.? A&. A& s! a$))
        :qid user_vstd__set_lib__axiom_is_empty_53
        :skolemid skolem_user_vstd__set_lib__axiom_is_empty_53
    ))))
    :pattern ((vstd!set_lib.impl&%0.is_empty.? A&. A& s!))
    :qid user_vstd__set_lib__axiom_is_empty_54
    :skolemid skolem_user_vstd__set_lib__axiom_is_empty_54
))))

;; Broadcast vstd::set_lib::axiom_is_empty_len0
(assert
 (=>
  (fuel_bool fuel%vstd!set_lib.axiom_is_empty_len0.)
  (forall ((A&. Dcr) (A& Type) (s! Poly)) (!
    (=>
     (has_type s! (TYPE%vstd!set.Set. A&. A&))
     (=>
      (sized A&.)
      (= (vstd!set_lib.impl&%0.is_empty.? A&. A& s!) (and
        (vstd!set.impl&%0.finite.? A&. A& s!)
        (= (vstd!set.impl&%0.len.? A&. A& s!) 0)
    ))))
    :pattern ((vstd!set_lib.impl&%0.is_empty.? A&. A& s!))
    :qid user_vstd__set_lib__axiom_is_empty_len0_55
    :skolemid skolem_user_vstd__set_lib__axiom_is_empty_len0_55
))))

;; Function-Axioms vstd::set::Set::subset_of
(assert
 (fuel_bool_default fuel%vstd!set.Set.subset_of.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!set.Set.subset_of.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (s2! Poly)) (!
    (= (vstd!set.Set.subset_of.? A&. A& self! s2!) (forall ((a$ Poly)) (!
       (=>
        (has_type a$ A&)
        (=>
         (vstd!set.Set.contains.? A&. A& self! a$)
         (vstd!set.Set.contains.? A&. A& s2! a$)
       ))
       :pattern ((vstd!set.Set.contains.? A&. A& self! a$))
       :pattern ((vstd!set.Set.contains.? A&. A& s2! a$))
       :qid user_vstd__set__Set__subset_of_56
       :skolemid skolem_user_vstd__set__Set__subset_of_56
    )))
    :pattern ((vstd!set.Set.subset_of.? A&. A& self! s2!))
    :qid internal_vstd!set.Set.subset_of.?_definition
    :skolemid skolem_internal_vstd!set.Set.subset_of.?_definition
))))

;; Broadcast vstd::set_lib::lemma_set_subset_finite
(assert
 (=>
  (fuel_bool fuel%vstd!set_lib.lemma_set_subset_finite.)
  (forall ((A&. Dcr) (A& Type) (s! Poly) (sub! Poly)) (!
    (=>
     (and
      (has_type s! (TYPE%vstd!set.Set. A&. A&))
      (has_type sub! (TYPE%vstd!set.Set. A&. A&))
     )
     (=>
      (and
       (and
        (sized A&.)
        (vstd!set.impl&%0.finite.? A&. A& s!)
       )
       (vstd!set.Set.subset_of.? A&. A& sub! s!)
      )
      (vstd!set.impl&%0.finite.? A&. A& sub!)
    ))
    :pattern ((vstd!set.Set.subset_of.? A&. A& sub! s!))
    :qid user_vstd__set_lib__lemma_set_subset_finite_57
    :skolemid skolem_user_vstd__set_lib__lemma_set_subset_finite_57
))))

;; Function-Axioms vstd::slice::spec_slice_len
(assert
 (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
   (=>
    (has_type slice! (SLICE T&. T&))
    (uInv SZ (vstd!slice.spec_slice_len.? T&. T& slice!))
   )
   :pattern ((vstd!slice.spec_slice_len.? T&. T& slice!))
   :qid internal_vstd!slice.spec_slice_len.?_pre_post_definition
   :skolemid skolem_internal_vstd!slice.spec_slice_len.?_pre_post_definition
)))

;; Function-Axioms vstd::view::View::view
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!view.View.view.? Self%&. Self%& self!) (proj%vstd!view.View./V Self%&.
      Self%&
   )))
   :pattern ((vstd!view.View.view.? Self%&. Self%& self!))
   :qid internal_vstd!view.View.view.?_pre_post_definition
   :skolemid skolem_internal_vstd!view.View.view.?_pre_post_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!view.View. $slice (SLICE T&. T&))
   )
   :pattern ((tr_bound%vstd!view.View. $slice (SLICE T&. T&)))
   :qid internal_vstd__slice__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__slice__impl&__0_trait_impl_definition
)))

;; Broadcast vstd::slice::axiom_spec_len
(assert
 (=>
  (fuel_bool fuel%vstd!slice.axiom_spec_len.)
  (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
    (=>
     (has_type slice! (SLICE T&. T&))
     (=>
      (sized T&.)
      (= (vstd!slice.spec_slice_len.? T&. T& slice!) (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.?
         $slice (SLICE T&. T&) slice!
    )))))
    :pattern ((vstd!slice.spec_slice_len.? T&. T& slice!))
    :qid user_vstd__slice__axiom_spec_len_58
    :skolemid skolem_user_vstd__slice__axiom_spec_len_58
))))

;; Function-Axioms vstd::slice::len%returns_clause_autospec
(assert
 (fuel_bool_default fuel%vstd!slice.len%returns_clause_autospec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!slice.len%returns_clause_autospec.)
  (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
    (= (vstd!slice.len%returns_clause_autospec.? T&. T& slice!) (vstd!slice.spec_slice_len.?
      T&. T& slice!
    ))
    :pattern ((vstd!slice.len%returns_clause_autospec.? T&. T& slice!))
    :qid internal_vstd!slice.len__returns_clause_autospec.?_definition
    :skolemid skolem_internal_vstd!slice.len__returns_clause_autospec.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (slice! Poly)) (!
   (=>
    (has_type slice! (SLICE T&. T&))
    (uInv SZ (vstd!slice.len%returns_clause_autospec.? T&. T& slice!))
   )
   :pattern ((vstd!slice.len%returns_clause_autospec.? T&. T& slice!))
   :qid internal_vstd!slice.len__returns_clause_autospec.?_pre_post_definition
   :skolemid skolem_internal_vstd!slice.len__returns_clause_autospec.?_pre_post_definition
)))

;; Function-Specs vstd::slice::SliceAdditionalSpecFns::spec_index
(declare-fun req%vstd!slice.SliceAdditionalSpecFns.spec_index. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%5 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (= (req%vstd!slice.SliceAdditionalSpecFns.spec_index. Self%&. Self%& T&. T& self! i!)
    (=>
     %%global_location_label%%5
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? Self%&. Self%& self!))))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!slice.SliceAdditionalSpecFns.spec_index. Self%&. Self%& T&. T&
     self! i!
   ))
   :qid internal_req__vstd!slice.SliceAdditionalSpecFns.spec_index._definition
   :skolemid skolem_internal_req__vstd!slice.SliceAdditionalSpecFns.spec_index._definition
)))

;; Function-Axioms vstd::slice::SliceAdditionalSpecFns::spec_index
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (=>
    (and
     (has_type self! Self%&)
     (has_type i! INT)
    )
    (has_type (vstd!slice.SliceAdditionalSpecFns.spec_index.? Self%&. Self%& T&. T& self!
      i!
     ) T&
   ))
   :pattern ((vstd!slice.SliceAdditionalSpecFns.spec_index.? Self%&. Self%& T&. T& self!
     i!
   ))
   :qid internal_vstd!slice.SliceAdditionalSpecFns.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!slice.SliceAdditionalSpecFns.spec_index.?_pre_post_definition
)))

;; Function-Axioms vstd::slice::impl&%2::spec_index
(assert
 (fuel_bool_default fuel%vstd!slice.impl&%2.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!slice.impl&%2.spec_index.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (!
    (=>
     (sized T&.)
     (= (vstd!slice.SliceAdditionalSpecFns.spec_index.? $slice (SLICE T&. T&) T&. T& self!
       i!
      ) (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $slice (SLICE T&. T&) self!)
       i!
    )))
    :pattern ((vstd!slice.SliceAdditionalSpecFns.spec_index.? $slice (SLICE T&. T&) T&.
      T& self! i!
    ))
    :qid internal_vstd!slice.SliceAdditionalSpecFns.spec_index.?_definition
    :skolemid skolem_internal_vstd!slice.SliceAdditionalSpecFns.spec_index.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!slice.SliceAdditionalSpecFns. $slice (SLICE T&. T&) T&. T&)
   )
   :pattern ((tr_bound%vstd!slice.SliceAdditionalSpecFns. $slice (SLICE T&. T&) T&. T&))
   :qid internal_vstd__slice__impl&__2_trait_impl_definition
   :skolemid skolem_internal_vstd__slice__impl&__2_trait_impl_definition
)))

;; Broadcast vstd::slice::axiom_slice_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!slice.axiom_slice_ext_equal.)
  (forall ((T&. Dcr) (T& Type) (a1! Poly) (a2! Poly)) (!
    (=>
     (and
      (has_type a1! (SLICE T&. T&))
      (has_type a2! (SLICE T&. T&))
     )
     (=>
      (sized T&.)
      (= (ext_eq false (SLICE T&. T&) a1! a2!) (and
        (= (vstd!slice.len%returns_clause_autospec.? T&. T& a1!) (vstd!slice.len%returns_clause_autospec.?
          T&. T& a2!
        ))
        (forall ((i$ Poly)) (!
          (=>
           (has_type i$ INT)
           (=>
            (let
             ((tmp%%$ 0))
             (let
              ((tmp%%$1 (%I i$)))
              (let
               ((tmp%%$2 (vstd!slice.len%returns_clause_autospec.? T&. T& a1!)))
               (and
                (<= tmp%%$ tmp%%$1)
                (< tmp%%$1 tmp%%$2)
            ))))
            (= (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $slice (SLICE T&. T&) a1!) i$)
             (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $slice (SLICE T&. T&) a2!) i$)
          )))
          :pattern ((vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $slice (SLICE T&. T&)
             a1!
            ) i$
          ))
          :pattern ((vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $slice (SLICE T&. T&)
             a2!
            ) i$
          ))
          :qid user_vstd__slice__axiom_slice_ext_equal_59
          :skolemid skolem_user_vstd__slice__axiom_slice_ext_equal_59
    ))))))
    :pattern ((ext_eq false (SLICE T&. T&) a1! a2!))
    :qid user_vstd__slice__axiom_slice_ext_equal_60
    :skolemid skolem_user_vstd__slice__axiom_slice_ext_equal_60
))))

;; Broadcast vstd::slice::axiom_slice_has_resolved
(assert
 (=>
  (fuel_bool fuel%vstd!slice.axiom_slice_has_resolved.)
  (forall ((T&. Dcr) (T& Type) (slice! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type slice! (SLICE T&. T&))
      (has_type i! INT)
     )
     (=>
      (sized T&.)
      (=>
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (vstd!slice.spec_slice_len.? T&. T& slice!)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
       ))))
       (=>
        (has_resolved $slice (SLICE T&. T&) slice!)
        (has_resolved T&. T& (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $slice (SLICE
            T&. T&
           ) slice!
          ) i!
    ))))))
    :pattern ((has_resolved $slice (SLICE T&. T&) slice!) (vstd!seq.Seq.index.? T&. T&
      (vstd!view.View.view.? $slice (SLICE T&. T&) slice!) i!
    ))
    :qid user_vstd__slice__axiom_slice_has_resolved_61
    :skolemid skolem_user_vstd__slice__axiom_slice_has_resolved_61
))))

;; Function-Axioms vstd::array::array_view
(assert
 (fuel_bool_default fuel%vstd!array.array_view.)
)
(declare-fun %%lambda%%0 (Dcr Type Dcr Type %%Function%%) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Dcr) (%%hole%%3 Type) (%%hole%%4
    %%Function%%
   ) (i$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4) i$)
    (array_index %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 i$)
   )
   :pattern ((%%apply%%0 (%%lambda%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4)
     i$
)))))
(assert
 (=>
  (fuel_bool fuel%vstd!array.array_view.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (a! Poly)) (!
    (= (vstd!array.array_view.? T&. T& N&. N& a!) (vstd!seq.Seq.new.? T&. T& $ (TYPE%fun%1.
       $ INT T&. T&
      ) (I (const_int N&)) (Poly%fun%1. (mk_fun (%%lambda%%0 T&. T& N&. N& (%Poly%array%. a!))))
    ))
    :pattern ((vstd!array.array_view.? T&. T& N&. N& a!))
    :qid internal_vstd!array.array_view.?_definition
    :skolemid skolem_internal_vstd!array.array_view.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (a! Poly)) (!
   (=>
    (has_type a! (ARRAY T&. T& N&. N&))
    (has_type (vstd!array.array_view.? T&. T& N&. N& a!) (TYPE%vstd!seq.Seq. T&. T&))
   )
   :pattern ((vstd!array.array_view.? T&. T& N&. N& a!))
   :qid internal_vstd!array.array_view.?_pre_post_definition
   :skolemid skolem_internal_vstd!array.array_view.?_pre_post_definition
)))

;; Function-Axioms vstd::array::impl&%0::view
(assert
 (fuel_bool_default fuel%vstd!array.impl&%0.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!array.impl&%0.view.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (self! Poly)) (!
    (=>
     (and
      (sized T&.)
      (uInv SZ (const_int N&))
     )
     (= (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) self!) (vstd!array.array_view.? T&.
       T& N&. N& self!
    )))
    :pattern ((vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (uInv SZ (const_int N&))
    )
    (tr_bound%vstd!view.View. $ (ARRAY T&. T& N&. N&))
   )
   :pattern ((tr_bound%vstd!view.View. $ (ARRAY T&. T& N&. N&)))
   :qid internal_vstd__array__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__array__impl&__0_trait_impl_definition
)))

;; Broadcast vstd::array::array_len_matches_n
(assert
 (=>
  (fuel_bool fuel%vstd!array.array_len_matches_n.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (ar! Poly)) (!
    (=>
     (has_type ar! (ARRAY T&. T& N&. N&))
     (=>
      (and
       (sized T&.)
       (uInv SZ (const_int N&))
      )
      (= (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) ar!))
       (const_int N&)
    )))
    :pattern ((vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&)
       ar!
    )))
    :qid user_vstd__array__array_len_matches_n_62
    :skolemid skolem_user_vstd__array__array_len_matches_n_62
))))

;; Function-Specs vstd::array::ArrayAdditionalSpecFns::spec_index
(declare-fun req%vstd!array.ArrayAdditionalSpecFns.spec_index. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%6 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (= (req%vstd!array.ArrayAdditionalSpecFns.spec_index. Self%&. Self%& T&. T& self! i!)
    (=>
     %%global_location_label%%6
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? T&. T& (vstd!view.View.view.? Self%&. Self%& self!))))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!array.ArrayAdditionalSpecFns.spec_index. Self%&. Self%& T&. T&
     self! i!
   ))
   :qid internal_req__vstd!array.ArrayAdditionalSpecFns.spec_index._definition
   :skolemid skolem_internal_req__vstd!array.ArrayAdditionalSpecFns.spec_index._definition
)))

;; Function-Axioms vstd::array::ArrayAdditionalSpecFns::spec_index
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (i! Poly)) (
   !
   (=>
    (and
     (has_type self! Self%&)
     (has_type i! INT)
    )
    (has_type (vstd!array.ArrayAdditionalSpecFns.spec_index.? Self%&. Self%& T&. T& self!
      i!
     ) T&
   ))
   :pattern ((vstd!array.ArrayAdditionalSpecFns.spec_index.? Self%&. Self%& T&. T& self!
     i!
   ))
   :qid internal_vstd!array.ArrayAdditionalSpecFns.spec_index.?_pre_post_definition
   :skolemid skolem_internal_vstd!array.ArrayAdditionalSpecFns.spec_index.?_pre_post_definition
)))

;; Function-Axioms vstd::array::impl&%2::spec_index
(assert
 (fuel_bool_default fuel%vstd!array.impl&%2.spec_index.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!array.impl&%2.spec_index.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (self! Poly) (i! Poly)) (!
    (=>
     (and
      (sized T&.)
      (uInv SZ (const_int N&))
     )
     (= (vstd!array.ArrayAdditionalSpecFns.spec_index.? $ (ARRAY T&. T& N&. N&) T&. T& self!
       i!
      ) (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) self!)
       i!
    )))
    :pattern ((vstd!array.ArrayAdditionalSpecFns.spec_index.? $ (ARRAY T&. T& N&. N&) T&.
      T& self! i!
    ))
    :qid internal_vstd!array.ArrayAdditionalSpecFns.spec_index.?_definition
    :skolemid skolem_internal_vstd!array.ArrayAdditionalSpecFns.spec_index.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (uInv SZ (const_int N&))
    )
    (tr_bound%vstd!array.ArrayAdditionalSpecFns. $ (ARRAY T&. T& N&. N&) T&. T&)
   )
   :pattern ((tr_bound%vstd!array.ArrayAdditionalSpecFns. $ (ARRAY T&. T& N&. N&) T&.
     T&
   ))
   :qid internal_vstd__array__impl&__2_trait_impl_definition
   :skolemid skolem_internal_vstd__array__impl&__2_trait_impl_definition
)))

;; Broadcast vstd::array::lemma_array_index
(assert
 (=>
  (fuel_bool fuel%vstd!array.lemma_array_index.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (a! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type a! (ARRAY T&. T& N&. N&))
      (has_type i! INT)
     )
     (=>
      (and
       (and
        (sized T&.)
        (uInv SZ (const_int N&))
       )
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (const_int N&)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
      )))))
      (= (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) a!)
        i!
       ) (vstd!seq.Seq.index.? T&. T& (vstd!array.array_view.? T&. T& N&. N& a!) i!)
    )))
    :pattern ((array_index T&. T& N&. N& (%Poly%array%. a!) i!))
    :qid user_vstd__array__lemma_array_index_63
    :skolemid skolem_user_vstd__array__lemma_array_index_63
))))

;; Broadcast vstd::array::axiom_array_ext_equal
(assert
 (=>
  (fuel_bool fuel%vstd!array.axiom_array_ext_equal.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (a1! Poly) (a2! Poly)) (!
    (=>
     (and
      (has_type a1! (ARRAY T&. T& N&. N&))
      (has_type a2! (ARRAY T&. T& N&. N&))
     )
     (=>
      (and
       (sized T&.)
       (uInv SZ (const_int N&))
      )
      (= (ext_eq false (ARRAY T&. T& N&. N&) a1! a2!) (forall ((i$ Poly)) (!
         (=>
          (has_type i$ INT)
          (=>
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I i$)))
             (let
              ((tmp%%$2 (const_int N&)))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
           ))))
           (= (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) a1!)
             i$
            ) (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) a2!)
             i$
         ))))
         :pattern ((vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&)
            a1!
           ) i$
         ))
         :pattern ((vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&)
            a2!
           ) i$
         ))
         :qid user_vstd__array__axiom_array_ext_equal_64
         :skolemid skolem_user_vstd__array__axiom_array_ext_equal_64
    )))))
    :pattern ((ext_eq false (ARRAY T&. T& N&. N&) a1! a2!))
    :qid user_vstd__array__axiom_array_ext_equal_65
    :skolemid skolem_user_vstd__array__axiom_array_ext_equal_65
))))

;; Broadcast vstd::array::axiom_array_has_resolved
(assert
 (=>
  (fuel_bool fuel%vstd!array.axiom_array_has_resolved.)
  (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (array! Poly) (i! Poly)) (!
    (=>
     (and
      (has_type array! (ARRAY T&. T& N&. N&))
      (has_type i! INT)
     )
     (=>
      (and
       (sized T&.)
       (uInv SZ (const_int N&))
      )
      (=>
       (let
        ((tmp%%$ 0))
        (let
         ((tmp%%$1 (%I i!)))
         (let
          ((tmp%%$2 (const_int N&)))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
       ))))
       (=>
        (has_resolved $ (ARRAY T&. T& N&. N&) array!)
        (has_resolved T&. T& (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&.
            T& N&. N&
           ) array!
          ) i!
    ))))))
    :pattern ((has_resolved $ (ARRAY T&. T& N&. N&) array!) (vstd!seq.Seq.index.? T&. T&
      (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&) array!) i!
    ))
    :qid user_vstd__array__axiom_array_has_resolved_66
    :skolemid skolem_user_vstd__array__axiom_array_has_resolved_66
))))

;; Function-Axioms vstd::raw_ptr::ptr_mut_from_data
(assert
 (forall ((T&. Dcr) (T& Type) (data! Poly)) (!
   (=>
    (has_type data! (TYPE%vstd!raw_ptr.PtrData. T&. T&))
    (has_type (vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!) (PTR T&. T&))
   )
   :pattern ((vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!))
   :qid internal_vstd!raw_ptr.ptr_mut_from_data.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.ptr_mut_from_data.?_pre_post_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%vstd!view.View. $ (PTR T&. T&))
   :pattern ((tr_bound%vstd!view.View. $ (PTR T&. T&)))
   :qid internal_vstd__raw_ptr__impl&__2_trait_impl_definition
   :skolemid skolem_internal_vstd__raw_ptr__impl&__2_trait_impl_definition
)))

;; Broadcast vstd::raw_ptr::axiom_ptr_mut_from_data
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.axiom_ptr_mut_from_data.)
  (forall ((T&. Dcr) (T& Type) (data! Poly)) (!
    (=>
     (has_type data! (TYPE%vstd!raw_ptr.PtrData. T&. T&))
     (= (vstd!view.View.view.? $ (PTR T&. T&) (vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!))
      data!
    ))
    :pattern ((vstd!raw_ptr.ptr_mut_from_data.? T&. T& data!))
    :qid user_vstd__raw_ptr__axiom_ptr_mut_from_data_67
    :skolemid skolem_user_vstd__raw_ptr__axiom_ptr_mut_from_data_67
))))

;; Function-Axioms vstd::raw_ptr::view_reverse_for_eq
(assert
 (forall ((T&. Dcr) (T& Type) (data! Poly)) (!
   (=>
    (has_type data! (TYPE%vstd!raw_ptr.PtrData. T&. T&))
    (has_type (vstd!raw_ptr.view_reverse_for_eq.? T&. T& data!) (PTR T&. T&))
   )
   :pattern ((vstd!raw_ptr.view_reverse_for_eq.? T&. T& data!))
   :qid internal_vstd!raw_ptr.view_reverse_for_eq.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.view_reverse_for_eq.?_pre_post_definition
)))

;; Broadcast vstd::raw_ptr::ptrs_mut_eq
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.ptrs_mut_eq.)
  (forall ((T&. Dcr) (T& Type) (a! Poly)) (!
    (=>
     (has_type a! (PTR T&. T&))
     (= (vstd!raw_ptr.view_reverse_for_eq.? T&. T& (vstd!view.View.view.? $ (PTR T&. T&)
        a!
       )
      ) a!
    ))
    :pattern ((vstd!view.View.view.? $ (PTR T&. T&) a!))
    :qid user_vstd__raw_ptr__ptrs_mut_eq_68
    :skolemid skolem_user_vstd__raw_ptr__ptrs_mut_eq_68
))))

;; Function-Axioms vstd::raw_ptr::view_reverse_for_eq_sized
(assert
 (forall ((T&. Dcr) (T& Type) (addr! Poly) (provenance! Poly)) (!
   (=>
    (and
     (has_type addr! USIZE)
     (has_type provenance! TYPE%vstd!raw_ptr.Provenance.)
    )
    (has_type (vstd!raw_ptr.view_reverse_for_eq_sized.? T&. T& addr! provenance!) (PTR
      T&. T&
   )))
   :pattern ((vstd!raw_ptr.view_reverse_for_eq_sized.? T&. T& addr! provenance!))
   :qid internal_vstd!raw_ptr.view_reverse_for_eq_sized.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.view_reverse_for_eq_sized.?_pre_post_definition
)))

;; Broadcast vstd::raw_ptr::ptrs_mut_eq_sized
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.ptrs_mut_eq_sized.)
  (forall ((T&. Dcr) (T& Type) (a! Poly)) (!
    (=>
     (has_type a! (PTR T&. T&))
     (=>
      (sized T&.)
      (= (vstd!raw_ptr.view_reverse_for_eq_sized.? T&. T& (I (vstd!raw_ptr.PtrData./PtrData/addr
          (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.? $ (PTR T&. T&) a!))
         )
        ) (Poly%vstd!raw_ptr.Provenance. (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData.
           (vstd!view.View.view.? $ (PTR T&. T&) a!)
        )))
       ) a!
    )))
    :pattern ((vstd!view.View.view.? $ (PTR T&. T&) a!))
    :qid user_vstd__raw_ptr__ptrs_mut_eq_sized_69
    :skolemid skolem_user_vstd__raw_ptr__ptrs_mut_eq_sized_69
))))

;; Function-Axioms vstd::layout::size_of
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (<= 0 (vstd!layout.size_of.? V&. V&))
   :pattern ((vstd!layout.size_of.? V&. V&))
   :qid internal_vstd!layout.size_of.?_pre_post_definition
   :skolemid skolem_internal_vstd!layout.size_of.?_pre_post_definition
)))

;; Broadcast vstd::layout::layout_of_primitives
(assert
 (=>
  (fuel_bool fuel%vstd!layout.layout_of_primitives.)
  (and
   (and
    (and
     (and
      (and
       (and
        (and
         (and
          (= (vstd!layout.size_of.? $ BOOL) 1)
          (= (vstd!layout.size_of.? $ CHAR) 4)
         )
         (let
          ((tmp%%$ (vstd!layout.size_of.? $ (UINT 8))))
          (let
           ((tmp%%$1 (vstd!layout.size_of.? $ (SINT 8))))
           (let
            ((tmp%%$2 1))
            (and
             (= tmp%%$ tmp%%$1)
             (= tmp%%$1 tmp%%$2)
        )))))
        (let
         ((tmp%%$ (vstd!layout.size_of.? $ (UINT 16))))
         (let
          ((tmp%%$4 (vstd!layout.size_of.? $ (SINT 16))))
          (let
           ((tmp%%$5 2))
           (and
            (= tmp%%$ tmp%%$4)
            (= tmp%%$4 tmp%%$5)
       )))))
       (let
        ((tmp%%$ (vstd!layout.size_of.? $ (UINT 32))))
        (let
         ((tmp%%$7 (vstd!layout.size_of.? $ (SINT 32))))
         (let
          ((tmp%%$8 4))
          (and
           (= tmp%%$ tmp%%$7)
           (= tmp%%$7 tmp%%$8)
      )))))
      (let
       ((tmp%%$ (vstd!layout.size_of.? $ (UINT 64))))
       (let
        ((tmp%%$10 (vstd!layout.size_of.? $ (SINT 64))))
        (let
         ((tmp%%$11 8))
         (and
          (= tmp%%$ tmp%%$10)
          (= tmp%%$10 tmp%%$11)
     )))))
     (let
      ((tmp%%$ (vstd!layout.size_of.? $ (UINT 128))))
      (let
       ((tmp%%$13 (vstd!layout.size_of.? $ (SINT 128))))
       (let
        ((tmp%%$14 16))
        (and
         (= tmp%%$ tmp%%$13)
         (= tmp%%$13 tmp%%$14)
    )))))
    (= (vstd!layout.size_of.? $ USIZE) (vstd!layout.size_of.? $ ISIZE))
   )
   (= (nClip (Mul (vstd!layout.size_of.? $ USIZE) 8)) SZ)
)))

;; Function-Axioms vstd::layout::align_of
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (<= 0 (vstd!layout.align_of.? V&. V&))
   :pattern ((vstd!layout.align_of.? V&. V&))
   :qid internal_vstd!layout.align_of.?_pre_post_definition
   :skolemid skolem_internal_vstd!layout.align_of.?_pre_post_definition
)))

;; Broadcast vstd::layout::layout_of_unit_tuple
(assert
 (=>
  (fuel_bool fuel%vstd!layout.layout_of_unit_tuple.)
  (and
   (= (vstd!layout.size_of.? $ TYPE%tuple%0.) 0)
   (= (vstd!layout.align_of.? $ TYPE%tuple%0.) 1)
)))

;; Broadcast vstd::layout::layout_of_references_and_pointers
(assert
 (=>
  (fuel_bool fuel%vstd!layout.layout_of_references_and_pointers.)
  (forall ((T&. Dcr) (T& Type)) (!
    (and
     (let
      ((tmp%%$ (vstd!layout.size_of.? $ (PTR T&. T&))))
      (let
       ((tmp%%$1 (vstd!layout.size_of.? (CONST_PTR $) (PTR T&. T&))))
       (let
        ((tmp%%$2 (vstd!layout.size_of.? (REF T&.) T&)))
        (and
         (= tmp%%$ tmp%%$1)
         (= tmp%%$1 tmp%%$2)
     ))))
     (let
      ((tmp%%$ (vstd!layout.align_of.? $ (PTR T&. T&))))
      (let
       ((tmp%%$4 (vstd!layout.align_of.? (CONST_PTR $) (PTR T&. T&))))
       (let
        ((tmp%%$5 (vstd!layout.align_of.? (REF T&.) T&)))
        (and
         (= tmp%%$ tmp%%$4)
         (= tmp%%$4 tmp%%$5)
    )))))
    :pattern ((vstd!layout.size_of.? $ (PTR T&. T&)))
    :pattern ((vstd!layout.size_of.? (CONST_PTR $) (PTR T&. T&)))
    :pattern ((vstd!layout.size_of.? (REF T&.) T&))
    :pattern ((vstd!layout.align_of.? $ (PTR T&. T&)))
    :pattern ((vstd!layout.align_of.? (CONST_PTR $) (PTR T&. T&)))
    :pattern ((vstd!layout.align_of.? (REF T&.) T&))
    :qid user_vstd__layout__layout_of_references_and_pointers_72
    :skolemid skolem_user_vstd__layout__layout_of_references_and_pointers_72
))))

;; Broadcast vstd::layout::layout_of_references_and_pointers_for_sized_types
(assert
 (=>
  (fuel_bool fuel%vstd!layout.layout_of_references_and_pointers_for_sized_types.)
  (forall ((T&. Dcr) (T& Type)) (!
    (=>
     (sized T&.)
     (and
      (= (vstd!layout.size_of.? $ (PTR T&. T&)) (vstd!layout.size_of.? $ USIZE))
      (= (vstd!layout.align_of.? $ (PTR T&. T&)) (vstd!layout.align_of.? $ USIZE))
    ))
    :pattern ((vstd!layout.size_of.? $ (PTR T&. T&)))
    :pattern ((vstd!layout.align_of.? $ (PTR T&. T&)))
    :qid user_vstd__layout__layout_of_references_and_pointers_for_sized_types_73
    :skolemid skolem_user_vstd__layout__layout_of_references_and_pointers_for_sized_types_73
))))

;; Broadcast vstd::layout::layout_of_references_and_pointers_for_unsized_types
(assert
 (=>
  (fuel_bool fuel%vstd!layout.layout_of_references_and_pointers_for_unsized_types.)
  (forall ((T&. Dcr) (T& Type)) (!
    (and
     (>= (vstd!layout.size_of.? $ (PTR T&. T&)) (vstd!layout.size_of.? $ USIZE))
     (>= (vstd!layout.align_of.? $ (PTR T&. T&)) (vstd!layout.align_of.? $ USIZE))
    )
    :pattern ((vstd!layout.size_of.? $ (PTR T&. T&)))
    :pattern ((vstd!layout.align_of.? $ (PTR T&. T&)))
    :qid user_vstd__layout__layout_of_references_and_pointers_for_unsized_types_74
    :skolemid skolem_user_vstd__layout__layout_of_references_and_pointers_for_unsized_types_74
))))

;; Broadcast vstd::layout::align_properties
(assert
 (=>
  (fuel_bool fuel%vstd!layout.align_properties.)
  (forall ((T&. Dcr) (T& Type)) (!
    (=>
     (sized T&.)
     (and
      (= (EucMod (vstd!layout.size_of.? T&. T&) (vstd!layout.align_of.? T&. T&)) 0)
      (vstd!arithmetic.power2.is_pow2.? (I (vstd!layout.align_of.? T&. T&)))
    ))
    :pattern ((vstd!layout.align_of.? T&. T&))
    :qid user_vstd__layout__align_properties_75
    :skolemid skolem_user_vstd__layout__align_properties_75
))))

;; Broadcast vstd::layout::align_nonzero
(assert
 (=>
  (fuel_bool fuel%vstd!layout.align_nonzero.)
  (forall ((T&. Dcr) (T& Type)) (!
    (=>
     (sized T&.)
     (> (vstd!layout.align_of.? T&. T&) 0)
    )
    :pattern ((vstd!layout.align_of.? T&. T&))
    :qid user_vstd__layout__align_nonzero_76
    :skolemid skolem_user_vstd__layout__align_nonzero_76
))))

;; Function-Axioms vstd::std_specs::bits::u64_trailing_zeros
(declare-const fuel_nat%vstd!std_specs.bits.u64_trailing_zeros. Fuel)
(assert
 (forall ((i! Poly) (fuel% Fuel)) (!
   (= (vstd!std_specs.bits.rec%u64_trailing_zeros.? i! fuel%) (vstd!std_specs.bits.rec%u64_trailing_zeros.?
     i! zero
   ))
   :pattern ((vstd!std_specs.bits.rec%u64_trailing_zeros.? i! fuel%))
   :qid internal_vstd!std_specs.bits.u64_trailing_zeros._fuel_to_zero_definition
   :skolemid skolem_internal_vstd!std_specs.bits.u64_trailing_zeros._fuel_to_zero_definition
)))
(assert
 (forall ((i! Poly) (fuel% Fuel)) (!
   (=>
    (has_type i! (UINT 64))
    (= (vstd!std_specs.bits.rec%u64_trailing_zeros.? i! (succ fuel%)) (ite
      (= (%I i!) 0)
      64
      (ite
       (not (= (uClip 64 (bitand (I (%I i!)) (I 1))) 0))
       0
       (uClip 32 (Add 1 (vstd!std_specs.bits.rec%u64_trailing_zeros.? (I (EucDiv (%I i!) 2))
          fuel%
   )))))))
   :pattern ((vstd!std_specs.bits.rec%u64_trailing_zeros.? i! (succ fuel%)))
   :qid internal_vstd!std_specs.bits.u64_trailing_zeros._fuel_to_body_definition
   :skolemid skolem_internal_vstd!std_specs.bits.u64_trailing_zeros._fuel_to_body_definition
)))
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.bits.u64_trailing_zeros.)
  (forall ((i! Poly)) (!
    (=>
     (has_type i! (UINT 64))
     (= (vstd!std_specs.bits.u64_trailing_zeros.? i!) (vstd!std_specs.bits.rec%u64_trailing_zeros.?
       i! (succ fuel_nat%vstd!std_specs.bits.u64_trailing_zeros.)
    )))
    :pattern ((vstd!std_specs.bits.u64_trailing_zeros.? i!))
    :qid internal_vstd!std_specs.bits.u64_trailing_zeros.?_definition
    :skolemid skolem_internal_vstd!std_specs.bits.u64_trailing_zeros.?_definition
))))
(assert
 (forall ((i! Poly)) (!
   (=>
    (has_type i! (UINT 64))
    (uInv 32 (vstd!std_specs.bits.u64_trailing_zeros.? i!))
   )
   :pattern ((vstd!std_specs.bits.u64_trailing_zeros.? i!))
   :qid internal_vstd!std_specs.bits.u64_trailing_zeros.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.bits.u64_trailing_zeros.?_pre_post_definition
)))
(assert
 (forall ((i! Poly) (fuel% Fuel)) (!
   (=>
    (has_type i! (UINT 64))
    (uInv 32 (vstd!std_specs.bits.rec%u64_trailing_zeros.? i! fuel%))
   )
   :pattern ((vstd!std_specs.bits.rec%u64_trailing_zeros.? i! fuel%))
   :qid internal_vstd!std_specs.bits.rec__u64_trailing_zeros.?_pre_post_rec_definition
   :skolemid skolem_internal_vstd!std_specs.bits.rec__u64_trailing_zeros.?_pre_post_rec_definition
)))

;; Broadcast vstd::std_specs::bits::axiom_u64_trailing_zeros
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.bits.axiom_u64_trailing_zeros.)
  (forall ((i! Poly)) (!
    (=>
     (has_type i! (UINT 64))
     (and
      (and
       (and
        (and
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$1 (vstd!std_specs.bits.u64_trailing_zeros.? i!)))
           (let
            ((tmp%%$2 64))
            (and
             (<= tmp%%$ tmp%%$1)
             (<= tmp%%$1 tmp%%$2)
         ))))
         (= (= (%I i!) 0) (= (vstd!std_specs.bits.u64_trailing_zeros.? i!) 64))
        )
        (=>
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$4 (vstd!std_specs.bits.u64_trailing_zeros.? i!)))
           (let
            ((tmp%%$5 64))
            (and
             (<= tmp%%$ tmp%%$4)
             (< tmp%%$4 tmp%%$5)
         ))))
         (= (uClip 64 (bitand (I (uClip 64 (bitshr (I (%I i!)) (I (uClip 64 (vstd!std_specs.bits.u64_trailing_zeros.?
                  i!
             )))))
            ) (I 1)
           )
          ) 1
       )))
       (= (uClip 64 (bitshl (I (%I i!)) (I (uClip 64 (Sub 64 (uClip 64 (vstd!std_specs.bits.u64_trailing_zeros.?
               i!
         ))))))
        ) 0
      ))
      (forall ((j$ Poly)) (!
        (=>
         (has_type j$ (UINT 64))
         (=>
          (let
           ((tmp%%$ 0))
           (let
            ((tmp%%$7 (%I j$)))
            (let
             ((tmp%%$8 (vstd!std_specs.bits.u64_trailing_zeros.? i!)))
             (and
              (<= tmp%%$ tmp%%$7)
              (< tmp%%$7 tmp%%$8)
          ))))
          (= (uClip 64 (bitand (I (uClip 64 (bitshr (I (%I i!)) (I (%I j$))))) (I 1))) 0)
        ))
        :pattern ((uClip 64 (bitshr (I (%I i!)) (I (%I j$)))))
        :qid user_vstd__std_specs__bits__axiom_u64_trailing_zeros_77
        :skolemid skolem_user_vstd__std_specs__bits__axiom_u64_trailing_zeros_77
    ))))
    :pattern ((vstd!std_specs.bits.u64_trailing_zeros.? i!))
    :qid user_vstd__std_specs__bits__axiom_u64_trailing_zeros_78
    :skolemid skolem_user_vstd__std_specs__bits__axiom_u64_trailing_zeros_78
))))

;; Function-Axioms vstd::std_specs::cmp::PartialEqSpec::obeys_eq_spec
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type)) (!
   (has_type (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? Self%&. Self%& Rhs&. Rhs&)
    BOOL
   )
   :pattern ((vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? Self%&. Self%& Rhs&. Rhs&))
   :qid internal_vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::cmp::PartialEqSpec::eq_spec
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type) (self! Poly) (other! Poly))
  (!
   (=>
    (and
     (has_type self! Self%&)
     (has_type other! Rhs&)
    )
    (has_type (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? Self%&. Self%& Rhs&. Rhs& self!
      other!
     ) BOOL
   ))
   :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? Self%&. Self%& Rhs&. Rhs& self!
     other!
   ))
   :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_pre_post_definition
)))

;; Function-Specs core::cmp::PartialEq::eq
(declare-fun ens%core!cmp.PartialEq.eq. (Dcr Type Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type) (self! Poly) (other! Poly)
   (r! Poly)
  ) (!
   (= (ens%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs& self! other! r!) (and
     (has_type r! BOOL)
     (=>
      (%B (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? Self%&. Self%& Rhs&. Rhs&))
      (= r! (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? Self%&. Self%& Rhs&. Rhs& self! other!))
   )))
   :pattern ((ens%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs& self! other! r!))
   :qid internal_ens__core!cmp.PartialEq.eq._definition
   :skolemid skolem_internal_ens__core!cmp.PartialEq.eq._definition
)))
(assert
 (forall ((closure%$ Poly) (Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type)) (!
   (=>
    (has_type closure%$ (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&))
    (=>
     (let
      ((self$ (tuple%2./tuple%2/0 (%Poly%tuple%2. closure%$))))
      (let
       ((other$ (tuple%2./tuple%2/1 (%Poly%tuple%2. closure%$))))
       true
     ))
     (closure_req (FNDEF%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs&) (DST (REF Rhs&.))
      (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&) (F fndef_singleton) closure%$
   )))
   :pattern ((closure_req (FNDEF%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs&) (DST
      (REF Rhs&.)
     ) (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&) (F fndef_singleton) closure%$
   ))
   :qid user_core__cmp__PartialEq__eq_79
   :skolemid skolem_user_core__cmp__PartialEq__eq_79
)))
(assert
 (forall ((closure%$ Poly) (r$ Poly) (Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type))
  (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&))
     (has_type r$ BOOL)
    )
    (=>
     (closure_ens (FNDEF%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs&) (DST (REF Rhs&.))
      (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&) (F fndef_singleton) closure%$
      r$
     )
     (let
      ((self$ (tuple%2./tuple%2/0 (%Poly%tuple%2. closure%$))))
      (let
       ((other$ (tuple%2./tuple%2/1 (%Poly%tuple%2. closure%$))))
       (=>
        (%B (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? Self%&. Self%& Rhs&. Rhs&))
        (= r$ (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? Self%&. Self%& Rhs&. Rhs& self$ other$))
   )))))
   :pattern ((closure_ens (FNDEF%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs&) (DST
      (REF Rhs&.)
     ) (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&) (F fndef_singleton) closure%$
     r$
   ))
   :qid user_core__cmp__PartialEq__eq_80
   :skolemid skolem_user_core__cmp__PartialEq__eq_80
)))

;; Function-Specs core::cmp::PartialEq::ne
(declare-fun ens%core!cmp.PartialEq.ne. (Bool Dcr Type Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((default_ensures Bool) (Self%&. Dcr) (Self%& Type) (Rhs&. Dcr) (Rhs& Type)
   (self! Poly) (other! Poly) (r! Poly)
  ) (!
   (= (ens%core!cmp.PartialEq.ne. default_ensures Self%&. Self%& Rhs&. Rhs& self! other!
     r!
    ) (and
     (has_type r! BOOL)
     (=>
      (%B (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? Self%&. Self%& Rhs&. Rhs&))
      (= (%B r!) (not (%B (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? Self%&. Self%& Rhs&.
          Rhs& self! other!
     )))))
     (=>
      default_ensures
      (closure_ens (FNDEF%core!cmp.PartialEq.eq. Self%&. Self%& Rhs&. Rhs&) (DST (REF Rhs&.))
       (TYPE%tuple%2. (REF Self%&.) Self%& (REF Rhs&.) Rhs&) (F fndef_singleton) (Poly%tuple%2.
        (tuple%2./tuple%2 self! other!)
       ) (B (not (%B r!)))
   ))))
   :pattern ((ens%core!cmp.PartialEq.ne. default_ensures Self%&. Self%& Rhs&. Rhs& self!
     other! r!
   ))
   :qid internal_ens__core!cmp.PartialEq.ne._definition
   :skolemid skolem_internal_ens__core!cmp.PartialEq.ne._definition
)))

;; Function-Specs core::num::impl&%11::wrapping_add
(declare-fun ens%core!num.impl&%11.wrapping_add. (Int Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int) (%return! Int)) (!
   (= (ens%core!num.impl&%11.wrapping_add. x! y! %return!) (and
     (uInv SZ %return!)
     (= %return! (ite
       (> (Add x! y!) (- (uHi SZ) 1))
       (uClip SZ (Sub (Add x! y!) (Add (Sub (- (uHi SZ) 1) 0) 1)))
       (uClip SZ (Add x! y!))
   ))))
   :pattern ((ens%core!num.impl&%11.wrapping_add. x! y! %return!))
   :qid internal_ens__core!num.impl&__11.wrapping_add._definition
   :skolemid skolem_internal_ens__core!num.impl&__11.wrapping_add._definition
)))

;; Function-Specs core::num::impl&%11::checked_add
(declare-fun ens%core!num.impl&%11.checked_add. (Int Int core!option.Option.) Bool)
(assert
 (forall ((x! Int) (y! Int) (%return! core!option.Option.)) (!
   (= (ens%core!num.impl&%11.checked_add. x! y! %return!) (and
     (has_type (Poly%core!option.Option. %return!) (TYPE%core!option.Option. $ USIZE))
     (= %return! (ite
       (> (Add x! y!) (- (uHi SZ) 1))
       core!option.Option./None
       (core!option.Option./Some (I (uClip SZ (Add x! y!))))
   ))))
   :pattern ((ens%core!num.impl&%11.checked_add. x! y! %return!))
   :qid internal_ens__core!num.impl&__11.checked_add._definition
   :skolemid skolem_internal_ens__core!num.impl&__11.checked_add._definition
)))

;; Function-Specs core::num::impl&%11::saturating_sub
(declare-fun ens%core!num.impl&%11.saturating_sub. (Int Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int) (%return! Int)) (!
   (= (ens%core!num.impl&%11.saturating_sub. x! y! %return!) (and
     (uInv SZ %return!)
     (= %return! (ite
       (< (Sub x! y!) 0)
       0
       (uClip SZ (Sub x! y!))
   ))))
   :pattern ((ens%core!num.impl&%11.saturating_sub. x! y! %return!))
   :qid internal_ens__core!num.impl&__11.saturating_sub._definition
   :skolemid skolem_internal_ens__core!num.impl&__11.saturating_sub._definition
)))

;; Function-Specs vstd::arithmetic::div_mod::lemma_basic_div
(declare-fun req%vstd!arithmetic.div_mod.lemma_basic_div. (Int Int) Bool)
(declare-const %%global_location_label%%7 Bool)
(assert
 (forall ((x! Int) (d! Int)) (!
   (= (req%vstd!arithmetic.div_mod.lemma_basic_div. x! d!) (=>
     %%global_location_label%%7
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 x!))
       (let
        ((tmp%%$2 d!))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!arithmetic.div_mod.lemma_basic_div. x! d!))
   :qid internal_req__vstd!arithmetic.div_mod.lemma_basic_div._definition
   :skolemid skolem_internal_req__vstd!arithmetic.div_mod.lemma_basic_div._definition
)))
(declare-fun ens%vstd!arithmetic.div_mod.lemma_basic_div. (Int Int) Bool)
(assert
 (forall ((x! Int) (d! Int)) (!
   (= (ens%vstd!arithmetic.div_mod.lemma_basic_div. x! d!) (= (EucDiv x! d!) 0))
   :pattern ((ens%vstd!arithmetic.div_mod.lemma_basic_div. x! d!))
   :qid internal_ens__vstd!arithmetic.div_mod.lemma_basic_div._definition
   :skolemid skolem_internal_ens__vstd!arithmetic.div_mod.lemma_basic_div._definition
)))

;; Broadcast vstd::arithmetic::div_mod::lemma_basic_div
(assert
 (=>
  (fuel_bool fuel%vstd!arithmetic.div_mod.lemma_basic_div.)
  (forall ((x! Int) (d! Int)) (!
    (=>
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 x!))
       (let
        ((tmp%%$2 d!))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
     ))))
     (= (EucDiv x! d!) 0)
    )
    :pattern ((EucDiv x! d!))
    :qid user_vstd__arithmetic__div_mod__lemma_basic_div_81
    :skolemid skolem_user_vstd__arithmetic__div_mod__lemma_basic_div_81
))))

;; Function-Specs vstd::arithmetic::div_mod::lemma_fundamental_div_mod
(declare-fun req%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. (Int Int) Bool)
(declare-const %%global_location_label%%8 Bool)
(assert
 (forall ((x! Int) (d! Int)) (!
   (= (req%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. x! d!) (=>
     %%global_location_label%%8
     (not (= d! 0))
   ))
   :pattern ((req%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. x! d!))
   :qid internal_req__vstd!arithmetic.div_mod.lemma_fundamental_div_mod._definition
   :skolemid skolem_internal_req__vstd!arithmetic.div_mod.lemma_fundamental_div_mod._definition
)))
(declare-fun ens%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. (Int Int) Bool)
(assert
 (forall ((x! Int) (d! Int)) (!
   (= (ens%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. x! d!) (= x! (Add (Mul d!
       (EucDiv x! d!)
      ) (EucMod x! d!)
   )))
   :pattern ((ens%vstd!arithmetic.div_mod.lemma_fundamental_div_mod. x! d!))
   :qid internal_ens__vstd!arithmetic.div_mod.lemma_fundamental_div_mod._definition
   :skolemid skolem_internal_ens__vstd!arithmetic.div_mod.lemma_fundamental_div_mod._definition
)))

;; Broadcast vstd::arithmetic::div_mod::lemma_fundamental_div_mod
(assert
 (=>
  (fuel_bool fuel%vstd!arithmetic.div_mod.lemma_fundamental_div_mod.)
  (forall ((x! Int) (d! Int)) (!
    (=>
     (not (= d! 0))
     (= x! (Add (Mul d! (EucDiv x! d!)) (EucMod x! d!)))
    )
    :pattern ((Add (Mul d! (EucDiv x! d!)) (EucMod x! d!)))
    :qid user_vstd__arithmetic__div_mod__lemma_fundamental_div_mod_82
    :skolemid skolem_user_vstd__arithmetic__div_mod__lemma_fundamental_div_mod_82
))))

;; Function-Specs vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish
(declare-fun req%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. (Int Int)
 Bool
)
(declare-const %%global_location_label%%9 Bool)
(assert
 (forall ((b! Int) (m! Int)) (!
   (= (req%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. b! m!) (=>
     %%global_location_label%%9
     (< 0 m!)
   ))
   :pattern ((req%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. b! m!))
   :qid internal_req__vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish._definition
   :skolemid skolem_internal_req__vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish._definition
)))
(declare-fun ens%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. (Int Int)
 Bool
)
(assert
 (forall ((b! Int) (m! Int)) (!
   (= (ens%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. b! m!) (= (EucMod (Add
       (Sub 0 m!) b!
      ) m!
     ) (EucMod b! m!)
   ))
   :pattern ((ens%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish. b! m!))
   :qid internal_ens__vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish._definition
   :skolemid skolem_internal_ens__vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish._definition
)))

;; Broadcast vstd::arithmetic::div_mod::lemma_mod_sub_multiples_vanish
(assert
 (=>
  (fuel_bool fuel%vstd!arithmetic.div_mod.lemma_mod_sub_multiples_vanish.)
  (forall ((b! Int) (m! Int)) (!
    (=>
     (< 0 m!)
     (= (EucMod (Add (Sub 0 m!) b!) m!) (EucMod b! m!))
    )
    :pattern ((EucMod b! m!))
    :qid user_vstd__arithmetic__div_mod__lemma_mod_sub_multiples_vanish_83
    :skolemid skolem_user_vstd__arithmetic__div_mod__lemma_mod_sub_multiples_vanish_83
))))

;; Function-Specs vstd::arithmetic::div_mod::lemma_mod_equivalence
(declare-fun req%vstd!arithmetic.div_mod.lemma_mod_equivalence. (Int Int Int) Bool)
(declare-const %%global_location_label%%10 Bool)
(assert
 (forall ((x! Int) (y! Int) (m! Int)) (!
   (= (req%vstd!arithmetic.div_mod.lemma_mod_equivalence. x! y! m!) (=>
     %%global_location_label%%10
     (< 0 m!)
   ))
   :pattern ((req%vstd!arithmetic.div_mod.lemma_mod_equivalence. x! y! m!))
   :qid internal_req__vstd!arithmetic.div_mod.lemma_mod_equivalence._definition
   :skolemid skolem_internal_req__vstd!arithmetic.div_mod.lemma_mod_equivalence._definition
)))
(declare-fun ens%vstd!arithmetic.div_mod.lemma_mod_equivalence. (Int Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int) (m! Int)) (!
   (= (ens%vstd!arithmetic.div_mod.lemma_mod_equivalence. x! y! m!) (= (= (EucMod x! m!)
      (EucMod y! m!)
     ) (= (EucMod (Sub x! y!) m!) 0)
   ))
   :pattern ((ens%vstd!arithmetic.div_mod.lemma_mod_equivalence. x! y! m!))
   :qid internal_ens__vstd!arithmetic.div_mod.lemma_mod_equivalence._definition
   :skolemid skolem_internal_ens__vstd!arithmetic.div_mod.lemma_mod_equivalence._definition
)))

;; Broadcast vstd::arithmetic::div_mod::lemma_mod_equivalence
(assert
 (=>
  (fuel_bool fuel%vstd!arithmetic.div_mod.lemma_mod_equivalence.)
  (forall ((x! Int) (y! Int) (m! Int)) (!
    (=>
     (< 0 m!)
     (= (= (EucMod x! m!) (EucMod y! m!)) (= (EucMod (Sub x! y!) m!) 0))
    )
    :pattern ((EucMod (Sub x! y!) m!))
    :qid user_vstd__arithmetic__div_mod__lemma_mod_equivalence_84
    :skolemid skolem_user_vstd__arithmetic__div_mod__lemma_mod_equivalence_84
))))

;; Function-Specs vstd::arithmetic::logarithm::log
(declare-fun req%vstd!arithmetic.logarithm.log. (Poly Poly) Bool)
(declare-const %%global_location_label%%11 Bool)
(declare-const %%global_location_label%%12 Bool)
(assert
 (forall ((base! Poly) (pow! Poly)) (!
   (= (req%vstd!arithmetic.logarithm.log. base! pow!) (and
     (=>
      %%global_location_label%%11
      (> (%I base!) 1)
     )
     (=>
      %%global_location_label%%12
      (>= (%I pow!) 0)
   )))
   :pattern ((req%vstd!arithmetic.logarithm.log. base! pow!))
   :qid internal_req__vstd!arithmetic.logarithm.log._definition
   :skolemid skolem_internal_req__vstd!arithmetic.logarithm.log._definition
)))

;; Function-Axioms vstd::arithmetic::power2::pow2
(assert
 (fuel_bool_default fuel%vstd!arithmetic.power2.pow2.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!arithmetic.power2.pow2.)
  (forall ((e! Poly)) (!
    (= (vstd!arithmetic.power2.pow2.? e!) (nClip (vstd!arithmetic.power.pow.? (I 2) e!)))
    :pattern ((vstd!arithmetic.power2.pow2.? e!))
    :qid internal_vstd!arithmetic.power2.pow2.?_definition
    :skolemid skolem_internal_vstd!arithmetic.power2.pow2.?_definition
))))
(assert
 (forall ((e! Poly)) (!
   (=>
    (has_type e! NAT)
    (<= 0 (vstd!arithmetic.power2.pow2.? e!))
   )
   :pattern ((vstd!arithmetic.power2.pow2.? e!))
   :qid internal_vstd!arithmetic.power2.pow2.?_pre_post_definition
   :skolemid skolem_internal_vstd!arithmetic.power2.pow2.?_pre_post_definition
)))

;; Function-Specs core::option::impl&%41::branch
(declare-fun ens%core!option.impl&%41.branch. (Dcr Type core!option.Option. core!ops.control_flow.ControlFlow.)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (option! core!option.Option.) (cf! core!ops.control_flow.ControlFlow.))
  (!
   (= (ens%core!option.impl&%41.branch. T&. T& option! cf!) (and
     (has_type (Poly%core!ops.control_flow.ControlFlow. cf!) (TYPE%core!ops.control_flow.ControlFlow.
       $ (TYPE%core!option.Option. $ TYPE%core!convert.Infallible.) T&. T&
     ))
     (= cf! (let
       ((tmp%%$ option!))
       (ite
        (is-core!option.Option./Some tmp%%$)
        (let
         ((v$ (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. (Poly%core!option.Option.
              tmp%%$
         )))))
         (core!ops.control_flow.ControlFlow./Continue v$)
        )
        (core!ops.control_flow.ControlFlow./Break (Poly%core!option.Option. core!option.Option./None))
   )))))
   :pattern ((ens%core!option.impl&%41.branch. T&. T& option! cf!))
   :qid internal_ens__core!option.impl&__41.branch._definition
   :skolemid skolem_internal_ens__core!option.impl&__41.branch._definition
)))

;; Function-Axioms vstd::std_specs::option::is_none
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.is_none.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.is_none.)
  (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
    (= (vstd!std_specs.option.is_none.? T&. T& option!) (is-core!option.Option./None (%Poly%core!option.Option.
       option!
    )))
    :pattern ((vstd!std_specs.option.is_none.? T&. T& option!))
    :qid internal_vstd!std_specs.option.is_none.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.is_none.?_definition
))))

;; Function-Specs core::option::impl&%42::from_residual
(declare-fun ens%core!option.impl&%42.from_residual. (Dcr Type core!option.Option.
  core!option.Option.
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (option! core!option.Option.) (option2! core!option.Option.))
  (!
   (= (ens%core!option.impl&%42.from_residual. T&. T& option! option2!) (and
     (has_type (Poly%core!option.Option. option2!) (TYPE%core!option.Option. T&. T&))
     (is-core!option.Option./None option!)
     (is-core!option.Option./None option2!)
   ))
   :pattern ((ens%core!option.impl&%42.from_residual. T&. T& option! option2!))
   :qid internal_ens__core!option.impl&__42.from_residual._definition
   :skolemid skolem_internal_ens__core!option.impl&__42.from_residual._definition
)))

;; Function-Axioms vstd::std_specs::option::OptionAdditionalFns::is_Some
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.option.OptionAdditionalFns.is_Some.? Self%&. Self%& T&. T&
      self!
     ) BOOL
   ))
   :pattern ((vstd!std_specs.option.OptionAdditionalFns.is_Some.? Self%&. Self%& T&. T&
     self!
   ))
   :qid internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::option::OptionAdditionalFns::arrow_0
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.option.OptionAdditionalFns.arrow_0.? Self%&. Self%& T&. T&
      self!
     ) T&
   ))
   :pattern ((vstd!std_specs.option.OptionAdditionalFns.arrow_0.? Self%&. Self%& T&. T&
     self!
   ))
   :qid internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_pre_post_definition
)))

;; Function-Specs vstd::std_specs::option::OptionAdditionalFns::tracked_unwrap
(declare-fun req%vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap. (Dcr Type
  Dcr Type Poly
 ) Bool
)
(declare-const %%global_location_label%%13 Bool)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly)) (!
   (= (req%vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap. Self%&. Self%& T&.
     T& self!
    ) (=>
     %%global_location_label%%13
     (%B (vstd!std_specs.option.OptionAdditionalFns.is_Some.? Self%&. Self%& T&. T& self!))
   ))
   :pattern ((req%vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap. Self%&. Self%&
     T&. T& self!
   ))
   :qid internal_req__vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap._definition
   :skolemid skolem_internal_req__vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap._definition
)))
(declare-fun ens%vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap. (Dcr Type
  Dcr Type Poly Poly
 ) Bool
)
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (self! Poly) (t! Poly)) (
   !
   (= (ens%vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap. Self%&. Self%& T&.
     T& self! t!
    ) (and
     (has_type t! T&)
     (= t! (vstd!std_specs.option.OptionAdditionalFns.arrow_0.? Self%&. Self%& T&. T& self!))
   ))
   :pattern ((ens%vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap. Self%&. Self%&
     T&. T& self! t!
   ))
   :qid internal_ens__vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap._definition
   :skolemid skolem_internal_ens__vstd!std_specs.option.OptionAdditionalFns.tracked_unwrap._definition
)))

;; Function-Axioms vstd::std_specs::option::impl&%0::arrow_0
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%0.arrow_0.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%0.arrow_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (=>
     (sized T&.)
     (= (vstd!std_specs.option.OptionAdditionalFns.arrow_0.? $ (TYPE%core!option.Option.
        T&. T&
       ) T&. T& self!
      ) (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. self!))
    ))
    :pattern ((vstd!std_specs.option.OptionAdditionalFns.arrow_0.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
    ))
    :qid internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.arrow_0.?_definition
))))

;; Function-Axioms vstd::std_specs::option::impl&%0::is_Some
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%0.is_Some.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%0.is_Some.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (=>
     (sized T&.)
     (= (vstd!std_specs.option.OptionAdditionalFns.is_Some.? $ (TYPE%core!option.Option.
        T&. T&
       ) T&. T& self!
      ) (B (is-core!option.Option./Some (%Poly%core!option.Option. self!)))
    ))
    :pattern ((vstd!std_specs.option.OptionAdditionalFns.is_Some.? $ (TYPE%core!option.Option.
       T&. T&
      ) T&. T& self!
    ))
    :qid internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.OptionAdditionalFns.is_Some.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!std_specs.option.OptionAdditionalFns. $ (TYPE%core!option.Option. T&.
      T&
     ) T&. T&
   ))
   :pattern ((tr_bound%vstd!std_specs.option.OptionAdditionalFns. $ (TYPE%core!option.Option.
      T&. T&
     ) T&. T&
   ))
   :qid internal_vstd__std_specs__option__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__option__impl&__0_trait_impl_definition
)))

;; Function-Specs vstd::std_specs::option::spec_unwrap
(declare-fun req%vstd!std_specs.option.spec_unwrap. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%14 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
   (= (req%vstd!std_specs.option.spec_unwrap. T&. T& option!) (=>
     %%global_location_label%%14
     (is-core!option.Option./Some (%Poly%core!option.Option. option!))
   ))
   :pattern ((req%vstd!std_specs.option.spec_unwrap. T&. T& option!))
   :qid internal_req__vstd!std_specs.option.spec_unwrap._definition
   :skolemid skolem_internal_req__vstd!std_specs.option.spec_unwrap._definition
)))

;; Function-Axioms vstd::std_specs::option::spec_unwrap
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.spec_unwrap.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.spec_unwrap.)
  (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
    (= (vstd!std_specs.option.spec_unwrap.? T&. T& option!) (core!option.Option./Some/0
      T&. T& (%Poly%core!option.Option. option!)
    ))
    :pattern ((vstd!std_specs.option.spec_unwrap.? T&. T& option!))
    :qid internal_vstd!std_specs.option.spec_unwrap.?_definition
    :skolemid skolem_internal_vstd!std_specs.option.spec_unwrap.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (option! Poly)) (!
   (=>
    (has_type option! (TYPE%core!option.Option. T&. T&))
    (has_type (vstd!std_specs.option.spec_unwrap.? T&. T& option!) T&)
   )
   :pattern ((vstd!std_specs.option.spec_unwrap.? T&. T& option!))
   :qid internal_vstd!std_specs.option.spec_unwrap.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.option.spec_unwrap.?_pre_post_definition
)))

;; Function-Axioms vstd::raw_ptr::ptr_mut_specs::spec_addr
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.ptr_mut_specs.spec_addr.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.ptr_mut_specs.spec_addr.)
  (forall ((T&. Dcr) (T& Type) (p! Poly)) (!
    (= (vstd!raw_ptr.ptr_mut_specs.spec_addr.? T&. T& p!) (vstd!raw_ptr.PtrData./PtrData/addr
      (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.? $ (PTR T&. T&) p!))
    ))
    :pattern ((vstd!raw_ptr.ptr_mut_specs.spec_addr.? T&. T& p!))
    :qid internal_vstd!raw_ptr.ptr_mut_specs.spec_addr.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.ptr_mut_specs.spec_addr.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (p! Poly)) (!
   (=>
    (has_type p! (PTR T&. T&))
    (uInv SZ (vstd!raw_ptr.ptr_mut_specs.spec_addr.? T&. T& p!))
   )
   :pattern ((vstd!raw_ptr.ptr_mut_specs.spec_addr.? T&. T& p!))
   :qid internal_vstd!raw_ptr.ptr_mut_specs.spec_addr.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.ptr_mut_specs.spec_addr.?_pre_post_definition
)))

;; Function-Specs vstd::array::array_index_get
(declare-fun req%vstd!array.array_index_get. (Dcr Type Dcr Type %%Function%% Int)
 Bool
)
(declare-const %%global_location_label%%15 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (ar! %%Function%%) (i! Int)) (!
   (= (req%vstd!array.array_index_get. T&. T& N&. N& ar! i!) (=>
     %%global_location_label%%15
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 i!))
       (let
        ((tmp%%$2 (const_int N&)))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!array.array_index_get. T&. T& N&. N& ar! i!))
   :qid internal_req__vstd!array.array_index_get._definition
   :skolemid skolem_internal_req__vstd!array.array_index_get._definition
)))
(declare-fun ens%vstd!array.array_index_get. (Dcr Type Dcr Type %%Function%% Int Poly)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (N&. Dcr) (N& Type) (ar! %%Function%%) (i! Int) (out! Poly))
  (!
   (= (ens%vstd!array.array_index_get. T&. T& N&. N& ar! i! out!) (and
     (has_type out! T&)
     (= out! (vstd!seq.Seq.index.? T&. T& (vstd!view.View.view.? $ (ARRAY T&. T& N&. N&)
        (Poly%array%. ar!)
       ) (I i!)
   ))))
   :pattern ((ens%vstd!array.array_index_get. T&. T& N&. N& ar! i! out!))
   :qid internal_ens__vstd!array.array_index_get._definition
   :skolemid skolem_internal_ens__vstd!array.array_index_get._definition
)))

;; Function-Specs core::mem::size_of
(declare-fun ens%core!mem.size_of. (Dcr Type Int) Bool)
(assert
 (forall ((V&. Dcr) (V& Type) (u! Int)) (!
   (= (ens%core!mem.size_of. V&. V& u!) (and
     (uInv SZ u!)
     (= u! (vstd!layout.size_of.? V&. V&))
   ))
   :pattern ((ens%core!mem.size_of. V&. V& u!))
   :qid internal_ens__core!mem.size_of._definition
   :skolemid skolem_internal_ens__core!mem.size_of._definition
)))

;; Function-Axioms vstd::layout::valid_layout
(assert
 (fuel_bool_default fuel%vstd!layout.valid_layout.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!layout.valid_layout.)
  (forall ((size! Poly) (align! Poly)) (!
    (= (vstd!layout.valid_layout.? size! align!) (and
      (vstd!arithmetic.power2.is_pow2.? align!)
      (<= (%I size!) (Sub (- (iHi SZ) 1) (EucMod (- (iHi SZ) 1) (%I align!))))
    ))
    :pattern ((vstd!layout.valid_layout.? size! align!))
    :qid internal_vstd!layout.valid_layout.?_definition
    :skolemid skolem_internal_vstd!layout.valid_layout.?_definition
))))

;; Function-Specs vstd::layout::layout_for_type_is_valid
(declare-fun ens%vstd!layout.layout_for_type_is_valid. (Dcr Type) Bool)
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (= (ens%vstd!layout.layout_for_type_is_valid. V&. V&) (and
     (vstd!layout.valid_layout.? (I (uClip SZ (vstd!layout.size_of.? V&. V&))) (I (uClip
        SZ (vstd!layout.align_of.? V&. V&)
     )))
     (= (uClip SZ (vstd!layout.size_of.? V&. V&)) (vstd!layout.size_of.? V&. V&))
     (= (uClip SZ (vstd!layout.align_of.? V&. V&)) (vstd!layout.align_of.? V&. V&))
     (not (= (vstd!layout.align_of.? V&. V&) 0))
     (= (EucMod (vstd!layout.size_of.? V&. V&) (vstd!layout.align_of.? V&. V&)) 0)
   ))
   :pattern ((ens%vstd!layout.layout_for_type_is_valid. V&. V&))
   :qid internal_ens__vstd!layout.layout_for_type_is_valid._definition
   :skolemid skolem_internal_ens__vstd!layout.layout_for_type_is_valid._definition
)))

;; Function-Specs vstd::map::impl&%0::tracked_insert
(declare-fun ens%vstd!map.impl&%0.tracked_insert. (Dcr Type Dcr Type Poly Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (pre%self! Poly) (self! Poly) (key!
    Poly
   ) (value! Poly)
  ) (!
   (= (ens%vstd!map.impl&%0.tracked_insert. K&. K& V&. V& pre%self! self! key! value!)
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (= self! (vstd!map.impl&%0.insert.? K&. K& V&. V& pre%self! key! value!))
   ))
   :pattern ((ens%vstd!map.impl&%0.tracked_insert. K&. K& V&. V& pre%self! self! key!
     value!
   ))
   :qid internal_ens__vstd!map.impl&__0.tracked_insert._definition
   :skolemid skolem_internal_ens__vstd!map.impl&__0.tracked_insert._definition
)))

;; Function-Specs vstd::map::impl&%0::tracked_remove
(declare-fun req%vstd!map.impl&%0.tracked_remove. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%16 Bool)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (pre%self! Poly) (key! Poly)) (!
   (= (req%vstd!map.impl&%0.tracked_remove. K&. K& V&. V& pre%self! key!) (=>
     %%global_location_label%%16
     (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& pre%self!) key!)
   ))
   :pattern ((req%vstd!map.impl&%0.tracked_remove. K&. K& V&. V& pre%self! key!))
   :qid internal_req__vstd!map.impl&__0.tracked_remove._definition
   :skolemid skolem_internal_req__vstd!map.impl&__0.tracked_remove._definition
)))
(declare-fun ens%vstd!map.impl&%0.tracked_remove. (Dcr Type Dcr Type Poly Poly Poly
  Poly
 ) Bool
)
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (pre%self! Poly) (self! Poly) (key!
    Poly
   ) (v! Poly)
  ) (!
   (= (ens%vstd!map.impl&%0.tracked_remove. K&. K& V&. V& pre%self! self! key! v!) (and
     (has_type v! V&)
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (= self! (vstd!map.impl&%0.remove.? K&. K& V&. V& pre%self! key!))
     (= v! (vstd!map.impl&%0.index.? K&. K& V&. V& pre%self! key!))
   ))
   :pattern ((ens%vstd!map.impl&%0.tracked_remove. K&. K& V&. V& pre%self! self! key!
     v!
   ))
   :qid internal_ens__vstd!map.impl&__0.tracked_remove._definition
   :skolemid skolem_internal_ens__vstd!map.impl&__0.tracked_remove._definition
)))

;; Function-Axioms vstd::pervasive::arbitrary
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (has_type (vstd!pervasive.arbitrary.? A&. A&) A&)
   :pattern ((vstd!pervasive.arbitrary.? A&. A&))
   :qid internal_vstd!pervasive.arbitrary.?_pre_post_definition
   :skolemid skolem_internal_vstd!pervasive.arbitrary.?_pre_post_definition
)))

;; Function-Specs core::ptr::mut_ptr::impl&%7::eq
(declare-fun ens%core!ptr.mut_ptr.impl&%7.eq. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly) (y! Poly) (res! Poly)) (!
   (= (ens%core!ptr.mut_ptr.impl&%7.eq. T&. T& x! y! res!) (and
     (ens%core!cmp.PartialEq.eq. $ (PTR T&. T&) $ (PTR T&. T&) x! y! res!)
     (= (%B res!) (and
       (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) x!
         ))
        ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) y!
       ))))
       (= (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) x!
         ))
        ) (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) y!
   ))))))))
   :pattern ((ens%core!ptr.mut_ptr.impl&%7.eq. T&. T& x! y! res!))
   :qid internal_ens__core!ptr.mut_ptr.impl&__7.eq._definition
   :skolemid skolem_internal_ens__core!ptr.mut_ptr.impl&__7.eq._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%2. (REF $) (PTR T&. T&) (REF $) (PTR T&. T&)))
     (has_type res$ BOOL)
    )
    (=>
     (closure_ens (FNDEF%core!cmp.PartialEq.eq. $ (PTR T&. T&) $ (PTR T&. T&)) (DST (REF
        $
       )
      ) (TYPE%tuple%2. (REF $) (PTR T&. T&) (REF $) (PTR T&. T&)) (F fndef_singleton) closure%$
      res$
     )
     (let
      ((x$ (tuple%2./tuple%2/0 (%Poly%tuple%2. closure%$))))
      (let
       ((y$ (tuple%2./tuple%2/1 (%Poly%tuple%2. closure%$))))
       (= (%B res$) (and
         (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) x$
           ))
          ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) y$
         ))))
         (= (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) x$
           ))
          ) (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) y$
   ))))))))))
   :pattern ((closure_ens (FNDEF%core!cmp.PartialEq.eq. $ (PTR T&. T&) $ (PTR T&. T&))
     (DST (REF $)) (TYPE%tuple%2. (REF $) (PTR T&. T&) (REF $) (PTR T&. T&)) (F fndef_singleton)
     closure%$ res$
   ))
   :qid user_core__ptr__mut_ptr__impl&%7__eq_85
   :skolemid skolem_user_core__ptr__mut_ptr__impl&%7__eq_85
)))

;; Function-Axioms vstd::raw_ptr::impl&%3::view
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%3.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%3.view.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!view.View.view.? (CONST_PTR $) (PTR T&. T&) self!) (vstd!view.View.view.?
      $ (PTR T&. T&) self!
    ))
    :pattern ((vstd!view.View.view.? (CONST_PTR $) (PTR T&. T&) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%vstd!view.View. (CONST_PTR $) (PTR T&. T&))
   :pattern ((tr_bound%vstd!view.View. (CONST_PTR $) (PTR T&. T&)))
   :qid internal_vstd__raw_ptr__impl&__3_trait_impl_definition
   :skolemid skolem_internal_vstd__raw_ptr__impl&__3_trait_impl_definition
)))

;; Function-Specs core::ptr::const_ptr::impl&%7::eq
(declare-fun ens%core!ptr.const_ptr.impl&%7.eq. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (x! Poly) (y! Poly) (res! Poly)) (!
   (= (ens%core!ptr.const_ptr.impl&%7.eq. T&. T& x! y! res!) (and
     (ens%core!cmp.PartialEq.eq. (CONST_PTR $) (PTR T&. T&) (CONST_PTR $) (PTR T&. T&)
      x! y! res!
     )
     (= (%B res!) (and
       (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) x!
         ))
        ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) y!
       ))))
       (= (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) x!
         ))
        ) (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) y!
   ))))))))
   :pattern ((ens%core!ptr.const_ptr.impl&%7.eq. T&. T& x! y! res!))
   :qid internal_ens__core!ptr.const_ptr.impl&__7.eq._definition
   :skolemid skolem_internal_ens__core!ptr.const_ptr.impl&__7.eq._definition
)))
(assert
 (forall ((closure%$ Poly) (res$ Poly) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (has_type closure%$ (TYPE%tuple%2. (REF (CONST_PTR $)) (PTR T&. T&) (REF (CONST_PTR $))
       (PTR T&. T&)
     ))
     (has_type res$ BOOL)
    )
    (=>
     (closure_ens (FNDEF%core!cmp.PartialEq.eq. (CONST_PTR $) (PTR T&. T&) (CONST_PTR $)
       (PTR T&. T&)
      ) (DST (REF (CONST_PTR $))) (TYPE%tuple%2. (REF (CONST_PTR $)) (PTR T&. T&) (REF (CONST_PTR
         $
        )
       ) (PTR T&. T&)
      ) (F fndef_singleton) closure%$ res$
     )
     (let
      ((x$ (tuple%2./tuple%2/0 (%Poly%tuple%2. closure%$))))
      (let
       ((y$ (tuple%2./tuple%2/1 (%Poly%tuple%2. closure%$))))
       (= (%B res$) (and
         (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) x$
           ))
          ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) y$
         ))))
         (= (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) x$
           ))
          ) (vstd!raw_ptr.PtrData./PtrData/metadata (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR T&. T&) y$
   ))))))))))
   :pattern ((closure_ens (FNDEF%core!cmp.PartialEq.eq. (CONST_PTR $) (PTR T&. T&) (CONST_PTR
       $
      ) (PTR T&. T&)
     ) (DST (REF (CONST_PTR $))) (TYPE%tuple%2. (REF (CONST_PTR $)) (PTR T&. T&) (REF (CONST_PTR
        $
       )
      ) (PTR T&. T&)
     ) (F fndef_singleton) closure%$ res$
   ))
   :qid user_core__ptr__const_ptr__impl&%7__eq_86
   :skolemid skolem_user_core__ptr__const_ptr__impl&%7__eq_86
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!view.View. $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&))
   )
   :pattern ((tr_bound%vstd!view.View. $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&)))
   :qid internal_vstd__raw_ptr__impl&__4_trait_impl_definition
   :skolemid skolem_internal_vstd__raw_ptr__impl&__4_trait_impl_definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%5::ptr
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%5.ptr.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%5.ptr.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%5.ptr.? T&. T& self!) (vstd!raw_ptr.PointsToData./PointsToData/ptr
      (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
         T&. T&
        ) self!
    ))))
    :pattern ((vstd!raw_ptr.impl&%5.ptr.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__5.ptr.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__5.ptr.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!raw_ptr.PointsTo. T&. T&))
    (has_type (vstd!raw_ptr.impl&%5.ptr.? T&. T& self!) (PTR T&. T&))
   )
   :pattern ((vstd!raw_ptr.impl&%5.ptr.? T&. T& self!))
   :qid internal_vstd!raw_ptr.impl&__5.ptr.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.impl&__5.ptr.?_pre_post_definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%6::is_uninit
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%6.is_uninit.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%6.is_uninit.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%6.is_uninit.? T&. T& self!) (is-vstd!raw_ptr.MemContents./Uninit
      (%Poly%vstd!raw_ptr.MemContents. self!)
    ))
    :pattern ((vstd!raw_ptr.impl&%6.is_uninit.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__6.is_uninit.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__6.is_uninit.?_definition
))))

;; Function-Axioms vstd::raw_ptr::impl&%5::opt_value
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%5.opt_value.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%5.opt_value.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%5.opt_value.? T&. T& self!) (vstd!raw_ptr.PointsToData./PointsToData/opt_value
      (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
         T&. T&
        ) self!
    ))))
    :pattern ((vstd!raw_ptr.impl&%5.opt_value.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__5.opt_value.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__5.opt_value.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!raw_ptr.PointsTo. T&. T&))
    (has_type (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.impl&%5.opt_value.? T&. T& self!))
     (TYPE%vstd!raw_ptr.MemContents. T&. T&)
   ))
   :pattern ((vstd!raw_ptr.impl&%5.opt_value.? T&. T& self!))
   :qid internal_vstd!raw_ptr.impl&__5.opt_value.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.impl&__5.opt_value.?_pre_post_definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%5::is_uninit
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%5.is_uninit.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%5.is_uninit.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%5.is_uninit.? T&. T& self!) (is-vstd!raw_ptr.MemContents./Uninit
      (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
        (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) self!)
    ))))
    :pattern ((vstd!raw_ptr.impl&%5.is_uninit.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__5.is_uninit.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__5.is_uninit.?_definition
))))

;; Function-Specs vstd::raw_ptr::impl&%5::leak_contents
(declare-fun ens%vstd!raw_ptr.impl&%5.leak_contents. (Dcr Type Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (pre%self! Poly) (self! Poly)) (!
   (= (ens%vstd!raw_ptr.impl&%5.leak_contents. T&. T& pre%self! self!) (and
     (has_type self! (TYPE%vstd!raw_ptr.PointsTo. T&. T&))
     (= (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
         $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) self!
       ))
      ) (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
         $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) pre%self!
     ))))
     (is-vstd!raw_ptr.MemContents./Uninit (vstd!raw_ptr.PointsToData./PointsToData/opt_value
       (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
          T&. T&
         ) self!
   ))))))
   :pattern ((ens%vstd!raw_ptr.impl&%5.leak_contents. T&. T& pre%self! self!))
   :qid internal_ens__vstd!raw_ptr.impl&__5.leak_contents._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.impl&__5.leak_contents._definition
)))

;; Function-Axioms vstd::raw_ptr::spec_cast_ptr_to_usize
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.spec_cast_ptr_to_usize.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.spec_cast_ptr_to_usize.)
  (forall ((T&. Dcr) (T& Type) (ptr! Poly)) (!
    (= (vstd!raw_ptr.spec_cast_ptr_to_usize.? T&. T& ptr!) (vstd!raw_ptr.PtrData./PtrData/addr
      (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.? $ (PTR T&. T&) ptr!))
    ))
    :pattern ((vstd!raw_ptr.spec_cast_ptr_to_usize.? T&. T& ptr!))
    :qid internal_vstd!raw_ptr.spec_cast_ptr_to_usize.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.spec_cast_ptr_to_usize.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (ptr! Poly)) (!
   (=>
    (has_type ptr! (PTR T&. T&))
    (uInv SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? T&. T& ptr!))
   )
   :pattern ((vstd!raw_ptr.spec_cast_ptr_to_usize.? T&. T& ptr!))
   :qid internal_vstd!raw_ptr.spec_cast_ptr_to_usize.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.spec_cast_ptr_to_usize.?_pre_post_definition
)))

;; Function-Specs vstd::raw_ptr::cast_ptr_to_usize
(declare-fun ens%vstd!raw_ptr.cast_ptr_to_usize. (Dcr Type Poly Int) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (ptr! Poly) (result! Int)) (!
   (= (ens%vstd!raw_ptr.cast_ptr_to_usize. T&. T& ptr! result!) (and
     (uInv SZ result!)
     (= result! (vstd!raw_ptr.spec_cast_ptr_to_usize.? T&. T& ptr!))
   ))
   :pattern ((ens%vstd!raw_ptr.cast_ptr_to_usize. T&. T& ptr! result!))
   :qid internal_ens__vstd!raw_ptr.cast_ptr_to_usize._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.cast_ptr_to_usize._definition
)))

;; Function-Specs vstd::raw_ptr::ptr_mut_write
(declare-fun req%vstd!raw_ptr.ptr_mut_write. (Dcr Type Poly Poly Poly) Bool)
(declare-const %%global_location_label%%17 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (ptr! Poly) (pre%perm! Poly) (v! Poly)) (!
   (= (req%vstd!raw_ptr.ptr_mut_write. T&. T& ptr! pre%perm! v!) (=>
     %%global_location_label%%17
     (= (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
         $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) pre%perm!
       ))
      ) ptr!
   )))
   :pattern ((req%vstd!raw_ptr.ptr_mut_write. T&. T& ptr! pre%perm! v!))
   :qid internal_req__vstd!raw_ptr.ptr_mut_write._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.ptr_mut_write._definition
)))
(declare-fun ens%vstd!raw_ptr.ptr_mut_write. (Dcr Type Poly Poly Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (ptr! Poly) (pre%perm! Poly) (perm! Poly) (v! Poly))
  (!
   (= (ens%vstd!raw_ptr.ptr_mut_write. T&. T& ptr! pre%perm! perm! v!) (and
     (has_type perm! (TYPE%vstd!raw_ptr.PointsTo. T&. T&))
     (= (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
         $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) perm!
       ))
      ) ptr!
     )
     (= (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
        (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) perm!)
       )
      ) (vstd!raw_ptr.MemContents./Init v!)
   )))
   :pattern ((ens%vstd!raw_ptr.ptr_mut_write. T&. T& ptr! pre%perm! perm! v!))
   :qid internal_ens__vstd!raw_ptr.ptr_mut_write._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.ptr_mut_write._definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%6::is_init
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%6.is_init.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%6.is_init.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%6.is_init.? T&. T& self!) (is-vstd!raw_ptr.MemContents./Init
      (%Poly%vstd!raw_ptr.MemContents. self!)
    ))
    :pattern ((vstd!raw_ptr.impl&%6.is_init.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__6.is_init.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__6.is_init.?_definition
))))

;; Function-Axioms vstd::raw_ptr::impl&%5::is_init
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%5.is_init.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%5.is_init.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%5.is_init.? T&. T& self!) (is-vstd!raw_ptr.MemContents./Init
      (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
        (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) self!)
    ))))
    :pattern ((vstd!raw_ptr.impl&%5.is_init.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__5.is_init.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__5.is_init.?_definition
))))

;; Function-Axioms vstd::raw_ptr::impl&%1::arrow_0
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%1.arrow_0.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%1.arrow_0.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%1.arrow_0.? T&. T& self!) (vstd!raw_ptr.MemContents./Init/0
      T&. T& (%Poly%vstd!raw_ptr.MemContents. self!)
    ))
    :pattern ((vstd!raw_ptr.impl&%1.arrow_0.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__1.arrow_0.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__1.arrow_0.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!raw_ptr.MemContents. T&. T&))
    (has_type (vstd!raw_ptr.impl&%1.arrow_0.? T&. T& self!) T&)
   )
   :pattern ((vstd!raw_ptr.impl&%1.arrow_0.? T&. T& self!))
   :qid internal_vstd!raw_ptr.impl&__1.arrow_0.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.impl&__1.arrow_0.?_pre_post_definition
)))

;; Function-Specs vstd::raw_ptr::impl&%6::value
(declare-fun req%vstd!raw_ptr.impl&%6.value. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%18 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (= (req%vstd!raw_ptr.impl&%6.value. T&. T& self!) (=>
     %%global_location_label%%18
     (is-vstd!raw_ptr.MemContents./Init (%Poly%vstd!raw_ptr.MemContents. self!))
   ))
   :pattern ((req%vstd!raw_ptr.impl&%6.value. T&. T& self!))
   :qid internal_req__vstd!raw_ptr.impl&__6.value._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.impl&__6.value._definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%6::value
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%6.value.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%6.value.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%6.value.? T&. T& self!) (vstd!raw_ptr.MemContents./Init/0 T&.
      T& (%Poly%vstd!raw_ptr.MemContents. self!)
    ))
    :pattern ((vstd!raw_ptr.impl&%6.value.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__6.value.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__6.value.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!raw_ptr.MemContents. T&. T&))
    (has_type (vstd!raw_ptr.impl&%6.value.? T&. T& self!) T&)
   )
   :pattern ((vstd!raw_ptr.impl&%6.value.? T&. T& self!))
   :qid internal_vstd!raw_ptr.impl&__6.value.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.impl&__6.value.?_pre_post_definition
)))

;; Function-Specs vstd::raw_ptr::impl&%5::value
(declare-fun req%vstd!raw_ptr.impl&%5.value. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%19 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (= (req%vstd!raw_ptr.impl&%5.value. T&. T& self!) (=>
     %%global_location_label%%19
     (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
       (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
          T&. T&
         ) self!
   ))))))
   :pattern ((req%vstd!raw_ptr.impl&%5.value. T&. T& self!))
   :qid internal_req__vstd!raw_ptr.impl&__5.value._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.impl&__5.value._definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%5::value
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%5.value.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%5.value.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (= (vstd!raw_ptr.impl&%5.value.? T&. T& self!) (vstd!raw_ptr.MemContents./Init/0 T&.
      T& (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
         (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
            T&. T&
           ) self!
    )))))))
    :pattern ((vstd!raw_ptr.impl&%5.value.? T&. T& self!))
    :qid internal_vstd!raw_ptr.impl&__5.value.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__5.value.?_definition
))))
(assert
 (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!raw_ptr.PointsTo. T&. T&))
    (has_type (vstd!raw_ptr.impl&%5.value.? T&. T& self!) T&)
   )
   :pattern ((vstd!raw_ptr.impl&%5.value.? T&. T& self!))
   :qid internal_vstd!raw_ptr.impl&__5.value.?_pre_post_definition
   :skolemid skolem_internal_vstd!raw_ptr.impl&__5.value.?_pre_post_definition
)))

;; Function-Specs vstd::raw_ptr::ptr_ref
(declare-fun req%vstd!raw_ptr.ptr_ref. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%20 Bool)
(declare-const %%global_location_label%%21 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (ptr! Poly) (perm! Poly)) (!
   (= (req%vstd!raw_ptr.ptr_ref. T&. T& ptr! perm!) (and
     (=>
      %%global_location_label%%20
      (= (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
          $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) perm!
        ))
       ) ptr!
     ))
     (=>
      %%global_location_label%%21
      (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
        (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
           T&. T&
          ) perm!
   )))))))
   :pattern ((req%vstd!raw_ptr.ptr_ref. T&. T& ptr! perm!))
   :qid internal_req__vstd!raw_ptr.ptr_ref._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.ptr_ref._definition
)))
(declare-fun ens%vstd!raw_ptr.ptr_ref. (Dcr Type Poly Poly Poly) Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (ptr! Poly) (perm! Poly) (v! Poly)) (!
   (= (ens%vstd!raw_ptr.ptr_ref. T&. T& ptr! perm! v!) (and
     (has_type v! T&)
     (= v! (vstd!raw_ptr.MemContents./Init/0 T&. T& (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
         (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
           (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. T&. T&) perm!)
   ))))))))
   :pattern ((ens%vstd!raw_ptr.ptr_ref. T&. T& ptr! perm! v!))
   :qid internal_ens__vstd!raw_ptr.ptr_ref._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.ptr_ref._definition
)))

;; Function-Axioms vstd::raw_ptr::impl&%9::view
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%9.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%9.view.)
  (forall ((self! Poly)) (!
    (= (vstd!raw_ptr.impl&%9.view.? self!) (vstd!raw_ptr.impl&%9.provenance.? self!))
    :pattern ((vstd!raw_ptr.impl&%9.view.? self!))
    :qid internal_vstd!raw_ptr.impl&__9.view.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__9.view.?_definition
))))

;; Function-Specs vstd::raw_ptr::expose_provenance
(declare-fun ens%vstd!raw_ptr.expose_provenance. (Dcr Type Poly vstd!raw_ptr.IsExposed.)
 Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (m! Poly) (provenance! vstd!raw_ptr.IsExposed.)) (!
   (= (ens%vstd!raw_ptr.expose_provenance. T&. T& m! provenance!) (= (vstd!raw_ptr.impl&%9.view.?
      (Poly%vstd!raw_ptr.IsExposed. provenance!)
     ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
        $ (PTR T&. T&) m!
   )))))
   :pattern ((ens%vstd!raw_ptr.expose_provenance. T&. T& m! provenance!))
   :qid internal_ens__vstd!raw_ptr.expose_provenance._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.expose_provenance._definition
)))

;; Function-Specs vstd::raw_ptr::with_exposed_provenance
(declare-fun ens%vstd!raw_ptr.with_exposed_provenance. (Dcr Type Int vstd!raw_ptr.IsExposed.
  Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (addr! Int) (provenance! vstd!raw_ptr.IsExposed.) (p! Poly))
  (!
   (= (ens%vstd!raw_ptr.with_exposed_provenance. T&. T& addr! provenance! p!) (and
     (has_type p! (PTR T&. T&))
     (= p! (vstd!raw_ptr.ptr_mut_from_data.? T&. T& (Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData./PtrData
         (%I (I addr!)) (%Poly%vstd!raw_ptr.Provenance. (Poly%vstd!raw_ptr.Provenance. (vstd!raw_ptr.impl&%9.view.?
            (Poly%vstd!raw_ptr.IsExposed. provenance!)
          ))
         ) (Poly%tuple%0. tuple%0./tuple%0)
   ))))))
   :pattern ((ens%vstd!raw_ptr.with_exposed_provenance. T&. T& addr! provenance! p!))
   :qid internal_ens__vstd!raw_ptr.with_exposed_provenance._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.with_exposed_provenance._definition
)))

;; Function-Specs vstd::raw_ptr::impl&%10::empty
(declare-fun ens%vstd!raw_ptr.impl&%10.empty. (vstd!raw_ptr.Provenance. vstd!raw_ptr.PointsToRaw.)
 Bool
)
(assert
 (forall ((provenance! vstd!raw_ptr.Provenance.) (points_to_raw! vstd!raw_ptr.PointsToRaw.))
  (!
   (= (ens%vstd!raw_ptr.impl&%10.empty. provenance! points_to_raw!) (and
     (= (vstd!raw_ptr.impl&%10.dom.? (Poly%vstd!raw_ptr.PointsToRaw. points_to_raw!)) (
       %Poly%vstd!set.Set<int.>. (vstd!set.Set.empty.? $ INT)
     ))
     (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. points_to_raw!))
      provenance!
   )))
   :pattern ((ens%vstd!raw_ptr.impl&%10.empty. provenance! points_to_raw!))
   :qid internal_ens__vstd!raw_ptr.impl&__10.empty._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.impl&__10.empty._definition
)))

;; Function-Specs vstd::raw_ptr::impl&%10::split
(declare-fun req%vstd!raw_ptr.impl&%10.split. (vstd!raw_ptr.PointsToRaw. vstd!set.Set<int.>.)
 Bool
)
(declare-const %%global_location_label%%22 Bool)
(assert
 (forall ((self! vstd!raw_ptr.PointsToRaw.) (range! vstd!set.Set<int.>.)) (!
   (= (req%vstd!raw_ptr.impl&%10.split. self! range!) (=>
     %%global_location_label%%22
     (vstd!set.Set.subset_of.? $ INT (Poly%vstd!set.Set<int.>. range!) (Poly%vstd!set.Set<int.>.
       (vstd!raw_ptr.impl&%10.dom.? (Poly%vstd!raw_ptr.PointsToRaw. self!))
   ))))
   :pattern ((req%vstd!raw_ptr.impl&%10.split. self! range!))
   :qid internal_req__vstd!raw_ptr.impl&__10.split._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.impl&__10.split._definition
)))
(declare-fun ens%vstd!raw_ptr.impl&%10.split. (vstd!raw_ptr.PointsToRaw. vstd!set.Set<int.>.
  tuple%2.
 ) Bool
)
(assert
 (forall ((self! vstd!raw_ptr.PointsToRaw.) (range! vstd!set.Set<int.>.) (res! tuple%2.))
  (!
   (= (ens%vstd!raw_ptr.impl&%10.split. self! range! res!) (and
     (has_type (Poly%tuple%2. res!) (TYPE%tuple%2. $ TYPE%vstd!raw_ptr.PointsToRaw. $ TYPE%vstd!raw_ptr.PointsToRaw.))
     (= (vstd!raw_ptr.impl&%10.provenance.? (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2.
          res!
       )))
      ) (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. self!))
     )
     (= (vstd!raw_ptr.impl&%10.provenance.? (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2.
          res!
       )))
      ) (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. self!))
     )
     (= (vstd!raw_ptr.impl&%10.dom.? (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. res!))))
      range!
     )
     (= (vstd!raw_ptr.impl&%10.dom.? (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. res!))))
      (%Poly%vstd!set.Set<int.>. (vstd!set.impl&%0.difference.? $ INT (Poly%vstd!set.Set<int.>.
         (vstd!raw_ptr.impl&%10.dom.? (Poly%vstd!raw_ptr.PointsToRaw. self!))
        ) (Poly%vstd!set.Set<int.>. range!)
   )))))
   :pattern ((ens%vstd!raw_ptr.impl&%10.split. self! range! res!))
   :qid internal_ens__vstd!raw_ptr.impl&__10.split._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.impl&__10.split._definition
)))

;; Function-Axioms vstd::set_lib::set_int_range
(assert
 (fuel_bool_default fuel%vstd!set_lib.set_int_range.)
)
(declare-fun %%lambda%%1 (Int Int) %%Function%%)
(assert
 (forall ((%%hole%%0 Int) (%%hole%%1 Int) (i$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%1 %%hole%%0 %%hole%%1) i$) (B (and
      (<= %%hole%%0 (%I i$))
      (< (%I i$) %%hole%%1)
   )))
   :pattern ((%%apply%%0 (%%lambda%%1 %%hole%%0 %%hole%%1) i$))
)))
(assert
 (=>
  (fuel_bool fuel%vstd!set_lib.set_int_range.)
  (forall ((lo! Poly) (hi! Poly)) (!
    (= (vstd!set_lib.set_int_range.? lo! hi!) (%Poly%vstd!set.Set<int.>. (vstd!set.impl&%0.new.?
       $ INT (Poly%fun%1. (mk_fun (%%lambda%%1 (%I lo!) (%I hi!))))
    )))
    :pattern ((vstd!set_lib.set_int_range.? lo! hi!))
    :qid internal_vstd!set_lib.set_int_range.?_definition
    :skolemid skolem_internal_vstd!set_lib.set_int_range.?_definition
))))

;; Function-Axioms vstd::raw_ptr::impl&%10::is_range
(assert
 (fuel_bool_default fuel%vstd!raw_ptr.impl&%10.is_range.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!raw_ptr.impl&%10.is_range.)
  (forall ((self! Poly) (start! Poly) (len! Poly)) (!
    (= (vstd!raw_ptr.impl&%10.is_range.? self! start! len!) (ext_eq false (TYPE%vstd!set.Set.
       $ INT
      ) (Poly%vstd!set.Set<int.>. (vstd!set_lib.set_int_range.? start! (I (Add (%I start!)
          (%I len!)
       )))
      ) (Poly%vstd!set.Set<int.>. (vstd!raw_ptr.impl&%10.dom.? self!))
    ))
    :pattern ((vstd!raw_ptr.impl&%10.is_range.? self! start! len!))
    :qid internal_vstd!raw_ptr.impl&__10.is_range.?_definition
    :skolemid skolem_internal_vstd!raw_ptr.impl&__10.is_range.?_definition
))))

;; Function-Specs vstd::raw_ptr::impl&%10::into_typed
(declare-fun req%vstd!raw_ptr.impl&%10.into_typed. (Dcr Type vstd!raw_ptr.PointsToRaw.
  Int
 ) Bool
)
(declare-const %%global_location_label%%23 Bool)
(declare-const %%global_location_label%%24 Bool)
(declare-const %%global_location_label%%25 Bool)
(assert
 (forall ((V&. Dcr) (V& Type) (self! vstd!raw_ptr.PointsToRaw.) (start! Int)) (!
   (= (req%vstd!raw_ptr.impl&%10.into_typed. V&. V& self! start!) (and
     (=>
      %%global_location_label%%23
      (or
       (not (= start! 0))
       (not (= (vstd!layout.size_of.? V&. V&) 0))
     ))
     (=>
      %%global_location_label%%24
      (= (EucMod start! (vstd!layout.align_of.? V&. V&)) 0)
     )
     (=>
      %%global_location_label%%25
      (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. self!) (I start!)
       (I (vstd!layout.size_of.? V&. V&))
   ))))
   :pattern ((req%vstd!raw_ptr.impl&%10.into_typed. V&. V& self! start!))
   :qid internal_req__vstd!raw_ptr.impl&__10.into_typed._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.impl&__10.into_typed._definition
)))
(declare-fun ens%vstd!raw_ptr.impl&%10.into_typed. (Dcr Type vstd!raw_ptr.PointsToRaw.
  Int Poly
 ) Bool
)
(assert
 (forall ((V&. Dcr) (V& Type) (self! vstd!raw_ptr.PointsToRaw.) (start! Int) (points_to!
    Poly
   )
  ) (!
   (= (ens%vstd!raw_ptr.impl&%10.into_typed. V&. V& self! start! points_to!) (and
     (has_type points_to! (TYPE%vstd!raw_ptr.PointsTo. V&. V&))
     (= (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
         $ (TYPE%vstd!raw_ptr.PointsTo. V&. V&) points_to!
       ))
      ) (vstd!raw_ptr.ptr_mut_from_data.? V&. V& (Poly%vstd!raw_ptr.PtrData. (vstd!raw_ptr.PtrData./PtrData
         (%I (I start!)) (%Poly%vstd!raw_ptr.Provenance. (Poly%vstd!raw_ptr.Provenance. (vstd!raw_ptr.impl&%10.provenance.?
            (Poly%vstd!raw_ptr.PointsToRaw. self!)
          ))
         ) (Poly%tuple%0. tuple%0./tuple%0)
     ))))
     (is-vstd!raw_ptr.MemContents./Uninit (vstd!raw_ptr.PointsToData./PointsToData/opt_value
       (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
          V&. V&
         ) points_to!
   ))))))
   :pattern ((ens%vstd!raw_ptr.impl&%10.into_typed. V&. V& self! start! points_to!))
   :qid internal_ens__vstd!raw_ptr.impl&__10.into_typed._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.impl&__10.into_typed._definition
)))

;; Function-Specs vstd::raw_ptr::impl&%11::into_raw
(declare-fun req%vstd!raw_ptr.impl&%11.into_raw. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%26 Bool)
(assert
 (forall ((V&. Dcr) (V& Type) (self! Poly)) (!
   (= (req%vstd!raw_ptr.impl&%11.into_raw. V&. V& self!) (=>
     %%global_location_label%%26
     (is-vstd!raw_ptr.MemContents./Uninit (vstd!raw_ptr.PointsToData./PointsToData/opt_value
       (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
          V&. V&
         ) self!
   ))))))
   :pattern ((req%vstd!raw_ptr.impl&%11.into_raw. V&. V& self!))
   :qid internal_req__vstd!raw_ptr.impl&__11.into_raw._definition
   :skolemid skolem_internal_req__vstd!raw_ptr.impl&__11.into_raw._definition
)))
(declare-fun ens%vstd!raw_ptr.impl&%11.into_raw. (Dcr Type Poly vstd!raw_ptr.PointsToRaw.)
 Bool
)
(assert
 (forall ((V&. Dcr) (V& Type) (self! Poly) (points_to_raw! vstd!raw_ptr.PointsToRaw.))
  (!
   (= (ens%vstd!raw_ptr.impl&%11.into_raw. V&. V& self! points_to_raw!) (and
     (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. points_to_raw!)
      (I (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR V&. V&) (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData.
            (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. V&. V&) self!)
       )))))
      ) (I (vstd!layout.size_of.? V&. V&))
     )
     (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. points_to_raw!))
      (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR V&. V&) (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData.
           (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. V&. V&) self!)
   ))))))))
   :pattern ((ens%vstd!raw_ptr.impl&%11.into_raw. V&. V& self! points_to_raw!))
   :qid internal_ens__vstd!raw_ptr.impl&__11.into_raw._definition
   :skolemid skolem_internal_ens__vstd!raw_ptr.impl&__11.into_raw._definition
)))

;; Function-Specs vstd::seq_lib::impl&%0::remove
(declare-fun req%vstd!seq_lib.impl&%0.remove. (Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%27 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (= (req%vstd!seq_lib.impl&%0.remove. A&. A& self! i!) (=>
     %%global_location_label%%27
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& self!)))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%vstd!seq_lib.impl&%0.remove. A&. A& self! i!))
   :qid internal_req__vstd!seq_lib.impl&__0.remove._definition
   :skolemid skolem_internal_req__vstd!seq_lib.impl&__0.remove._definition
)))

;; Function-Axioms vstd::seq_lib::impl&%0::remove
(assert
 (fuel_bool_default fuel%vstd!seq_lib.impl&%0.remove.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.remove.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
    (= (vstd!seq_lib.impl&%0.remove.? A&. A& self! i!) (vstd!seq.Seq.add.? A&. A& (vstd!seq.Seq.subrange.?
       A&. A& self! (I 0) i!
      ) (vstd!seq.Seq.subrange.? A&. A& self! (I (Add (%I i!) 1)) (I (vstd!seq.Seq.len.? A&.
         A& self!
    )))))
    :pattern ((vstd!seq_lib.impl&%0.remove.? A&. A& self! i!))
    :qid internal_vstd!seq_lib.impl&__0.remove.?_definition
    :skolemid skolem_internal_vstd!seq_lib.impl&__0.remove.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly) (i! Poly)) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
     (has_type i! INT)
    )
    (has_type (vstd!seq_lib.impl&%0.remove.? A&. A& self! i!) (TYPE%vstd!seq.Seq. A&. A&))
   )
   :pattern ((vstd!seq_lib.impl&%0.remove.? A&. A& self! i!))
   :qid internal_vstd!seq_lib.impl&__0.remove.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq_lib.impl&__0.remove.?_pre_post_definition
)))

;; Function-Axioms lib::block_index::BlockIndex::valid_block_index
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.valid_block_index.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.valid_block_index.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (idx! Poly)) (!
    (= (lib!block_index.impl&%7.valid_block_index.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx!)
     (let
      ((tmp%%$ (%Poly%tuple%2. idx!)))
      (let
       ((fl$ (%I (tuple%2./tuple%2/0 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))))))
       (let
        ((sl$ (%I (tuple%2./tuple%2/1 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))))))
        (and
         (let
          ((tmp%%$1 0))
          (let
           ((tmp%%$2 fl$))
           (let
            ((tmp%%$3 (const_int FLLEN&)))
            (and
             (<= tmp%%$1 tmp%%$2)
             (< tmp%%$2 tmp%%$3)
         ))))
         (let
          ((tmp%%$4 0))
          (let
           ((tmp%%$5 sl$))
           (let
            ((tmp%%$6 (const_int SLLEN&)))
            (and
             (<= tmp%%$4 tmp%%$5)
             (< tmp%%$5 tmp%%$6)
    )))))))))
    :pattern ((lib!block_index.impl&%7.valid_block_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      idx!
    ))
    :qid internal_lib!block_index.impl&__7.valid_block_index.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.valid_block_index.?_definition
))))

;; Function-Axioms lib::block_index::BlockIndex::view
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.view.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.view.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!block_index.impl&%7.view.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (tuple%2./tuple%2
      (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. self!)))
      (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. self!)))
    ))
    :pattern ((lib!block_index.impl&%7.view.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!block_index.impl&__7.view.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.view.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
    (has_type (Poly%tuple%2. (lib!block_index.impl&%7.view.? FLLEN&. FLLEN& SLLEN&. SLLEN&
       self!
      )
     ) (TYPE%tuple%2. $ INT $ INT)
   ))
   :pattern ((lib!block_index.impl&%7.view.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
   :qid internal_lib!block_index.impl&__7.view.?_pre_post_definition
   :skolemid skolem_internal_lib!block_index.impl&__7.view.?_pre_post_definition
)))

;; Function-Axioms lib::block_index::BlockIndex::wf
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.wf.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (lib!block_index.impl&%7.valid_block_index.?
      FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%tuple%2. (lib!block_index.impl&%7.view.? FLLEN&.
        FLLEN& SLLEN&. SLLEN& self!
    ))))
    :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!block_index.impl&__7.wf.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.wf.?_definition
))))

;; Function-Specs lib::Tlsf::set_freelist
(declare-fun req%lib!linked_list.impl&%0.set_freelist. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%28 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (e! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!linked_list.impl&%0.set_freelist. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     idx! e!
    ) (=>
     %%global_location_label%%28
     (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
       idx!
   ))))
   :pattern ((req%lib!linked_list.impl&%0.set_freelist. FLLEN&. FLLEN& SLLEN&. SLLEN&
     pre%self! idx! e!
   ))
   :qid internal_req__lib!linked_list.impl&__0.set_freelist._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.set_freelist._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.set_freelist. (Dcr Type Dcr Type lib!Tlsf.
  lib!Tlsf. lib!block_index.BlockIndex. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.) (e! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.set_freelist. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     self! idx! e!
    ) (and
     (has_type (Poly%lib!Tlsf. self!) (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
        (vstd!view.View.view.? $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&)
         (vstd!seq.Seq.index.? $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&)
          (vstd!view.View.view.? $ (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&.
             SLLEN&
            ) FLLEN&. FLLEN&
           ) (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))))
          ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
              idx!
         )))))
        ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
            idx!
       )))))
      ) e!
     )
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (=>
         (and
          (not (= (%Poly%lib!block_index.BlockIndex. i$) idx!))
          (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& i$)
         )
         (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
            (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
             (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
              (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
              (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))))
             ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. i$)))
            )
           ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. i$)))
          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
            (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
             (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
              (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
              (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))))
             ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. i$)))
            )
           ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. i$)))
       ))))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& i$))
       :qid user_lib__Tlsf__set_freelist_87
       :skolemid skolem_user_lib__Tlsf__set_freelist_87
     ))
     (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/shadow_freelist
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/all_blocks
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/sl_bitmap
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/fl_bitmap
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
   ))))
   :pattern ((ens%lib!linked_list.impl&%0.set_freelist. FLLEN&. FLLEN& SLLEN&. SLLEN&
     pre%self! self! idx! e!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.set_freelist._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.set_freelist._definition
)))

;; Function-Specs lib::VERUS_layout_of_usize
(declare-fun ens%lib!VERUS_layout_of_usize. () Bool)
(assert
 (= ens%lib!VERUS_layout_of_usize. (= (vstd!layout.size_of.? $ USIZE) 8))
)

;; Broadcast lib::VERUS_layout_of_usize
(assert
 (= (vstd!layout.size_of.? $ USIZE) 8)
)

;; Function-Specs lib::VERUS_layout_of_BlockHdr
(declare-fun ens%lib!VERUS_layout_of_BlockHdr. () Bool)
(assert
 (= ens%lib!VERUS_layout_of_BlockHdr. (and
   (= (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.) 16)
   (= (vstd!layout.align_of.? $ TYPE%lib!block.BlockHdr.) 8)
)))

;; Broadcast lib::VERUS_layout_of_BlockHdr
(assert
 (and
  (= (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.) 16)
  (= (vstd!layout.align_of.? $ TYPE%lib!block.BlockHdr.) 8)
))

;; Function-Specs lib::VERUS_layout_of_FreeLink
(declare-fun ens%lib!VERUS_layout_of_FreeLink. () Bool)
(assert
 (= ens%lib!VERUS_layout_of_FreeLink. (and
   (= (vstd!layout.size_of.? $ TYPE%lib!block.FreeLink.) 16)
   (= (vstd!layout.align_of.? $ TYPE%lib!block.FreeLink.) 8)
)))

;; Broadcast lib::VERUS_layout_of_FreeLink
(assert
 (and
  (= (vstd!layout.size_of.? $ TYPE%lib!block.FreeLink.) 16)
  (= (vstd!layout.align_of.? $ TYPE%lib!block.FreeLink.) 8)
))

;; Function-Specs lib::VERUS_layout_of_UsedBlockPad
(declare-fun ens%lib!VERUS_layout_of_UsedBlockPad. () Bool)
(assert
 (= ens%lib!VERUS_layout_of_UsedBlockPad. (and
   (= (vstd!layout.size_of.? $ TYPE%lib!block.UsedBlockPad.) 8)
   (= (vstd!layout.align_of.? $ TYPE%lib!block.UsedBlockPad.) 8)
)))

;; Broadcast lib::VERUS_layout_of_UsedBlockPad
(assert
 (and
  (= (vstd!layout.size_of.? $ TYPE%lib!block.UsedBlockPad.) 8)
  (= (vstd!layout.align_of.? $ TYPE%lib!block.UsedBlockPad.) 8)
))

;; Function-Axioms lib::parameters::GRANULARITY
(assert
 (fuel_bool_default fuel%lib!parameters.GRANULARITY.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.GRANULARITY.)
  (= lib!parameters.GRANULARITY.? (uClip SZ (Mul 8 4)))
))
(assert
 (uInv SZ lib!parameters.GRANULARITY.?)
)

;; Function-Axioms lib::Tlsf::granularity_log2_spec
(assert
 (fuel_bool_default fuel%lib!parameters.impl&%0.granularity_log2_spec.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.impl&%0.granularity_log2_spec.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
    (= (lib!parameters.impl&%0.granularity_log2_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     (vstd!arithmetic.logarithm.log.? (I 2) (I lib!parameters.GRANULARITY.?))
    )
    :pattern ((lib!parameters.impl&%0.granularity_log2_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN&))
    :qid internal_lib!parameters.impl&__0.granularity_log2_spec.?_definition
    :skolemid skolem_internal_lib!parameters.impl&__0.granularity_log2_spec.?_definition
))))

;; Function-Axioms lib::bits::is_power_of_two
(assert
 (fuel_bool_default fuel%lib!bits.is_power_of_two.)
)
(assert
 (=>
  (fuel_bool fuel%lib!bits.is_power_of_two.)
  (forall ((n! Poly)) (!
    (= (lib!bits.is_power_of_two.? n!) (exists ((p$ Poly)) (!
       (and
        (has_type p$ NAT)
        (= (%I n!) (vstd!arithmetic.power2.pow2.? p$))
       )
       :pattern ((vstd!arithmetic.power2.pow2.? p$))
       :qid user_lib__bits__is_power_of_two_92
       :skolemid skolem_user_lib__bits__is_power_of_two_92
    )))
    :pattern ((lib!bits.is_power_of_two.? n!))
    :qid internal_lib!bits.is_power_of_two.?_definition
    :skolemid skolem_internal_lib!bits.is_power_of_two.?_definition
))))

;; Function-Axioms lib::Tlsf::parameter_validity
(assert
 (fuel_bool_default fuel%lib!parameters.impl&%0.parameter_validity.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.impl&%0.parameter_validity.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
    (= (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&) (and
      (and
       (and
        (let
         ((tmp%%$ 0))
         (let
          ((tmp%%$1 (const_int FLLEN&)))
          (let
           ((tmp%%$2 (Sub SZ (lib!parameters.impl&%0.granularity_log2_spec.? FLLEN&. FLLEN& SLLEN&.
               SLLEN&
           ))))
           (and
            (< tmp%%$ tmp%%$1)
            (< tmp%%$1 tmp%%$2)
        ))))
        (and
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$4 (const_int SLLEN&)))
           (let
            ((tmp%%$5 SZ))
            (and
             (< tmp%%$ tmp%%$4)
             (<= tmp%%$4 tmp%%$5)
         ))))
         (lib!bits.is_power_of_two.? (I (const_int SLLEN&)))
       ))
       (=>
        (= SZ 64)
        (= lib!parameters.GRANULARITY.? 32)
      ))
      (=>
       (= SZ 32)
       (= lib!parameters.GRANULARITY.? 16)
    )))
    :pattern ((lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&))
    :qid internal_lib!parameters.impl&__0.parameter_validity.?_definition
    :skolemid skolem_internal_lib!parameters.impl&__0.parameter_validity.?_definition
))))

;; Function-Axioms lib::bits::usize_trailing_zeros
(assert
 (fuel_bool_default fuel%lib!bits.usize_trailing_zeros.)
)
(assert
 (=>
  (fuel_bool fuel%lib!bits.usize_trailing_zeros.)
  (forall ((x! Poly)) (!
    (= (lib!bits.usize_trailing_zeros.? x!) (uClip 32 (vstd!std_specs.bits.u64_trailing_zeros.?
       (I (uClip 64 (%I x!)))
    )))
    :pattern ((lib!bits.usize_trailing_zeros.? x!))
    :qid internal_lib!bits.usize_trailing_zeros.?_definition
    :skolemid skolem_internal_lib!bits.usize_trailing_zeros.?_definition
))))
(assert
 (forall ((x! Poly)) (!
   (=>
    (has_type x! USIZE)
    (uInv 32 (lib!bits.usize_trailing_zeros.? x!))
   )
   :pattern ((lib!bits.usize_trailing_zeros.? x!))
   :qid internal_lib!bits.usize_trailing_zeros.?_pre_post_definition
   :skolemid skolem_internal_lib!bits.usize_trailing_zeros.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::num::usize_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.usize_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.usize_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ USIZE $ USIZE) (B true))
))

;; Function-Axioms vstd::std_specs::num::usize_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.usize_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.usize_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ USIZE $ USIZE self! other!) (B (= self!
       other!
    )))
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ USIZE $ USIZE self! other!))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::usize_specs::wrapping_sub%returns_clause_autospec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.)
  (forall ((x! Poly) (y! Poly)) (!
    (= (vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.? x! y!) (
      ite
      (< (Sub (%I x!) (%I y!)) 0)
      (uClip SZ (Add (Sub (%I x!) (%I y!)) (Add (Sub (- (uHi SZ) 1) 0) 1)))
      (uClip SZ (Sub (%I x!) (%I y!)))
    ))
    :pattern ((vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.? x!
      y!
    ))
    :qid internal_vstd!std_specs.num.usize_specs.wrapping_sub__returns_clause_autospec.?_definition
    :skolemid skolem_internal_vstd!std_specs.num.usize_specs.wrapping_sub__returns_clause_autospec.?_definition
))))
(assert
 (forall ((x! Poly) (y! Poly)) (!
   (=>
    (and
     (has_type x! USIZE)
     (has_type y! USIZE)
    )
    (uInv SZ (vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.? x!
      y!
   )))
   :pattern ((vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.? x!
     y!
   ))
   :qid internal_vstd!std_specs.num.usize_specs.wrapping_sub__returns_clause_autospec.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.num.usize_specs.wrapping_sub__returns_clause_autospec.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::num::usize_specs::checked_add%returns_clause_autospec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.)
  (forall ((x! Poly) (y! Poly)) (!
    (= (vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.? x! y!) (ite
      (> (Add (%I x!) (%I y!)) (- (uHi SZ) 1))
      core!option.Option./None
      (core!option.Option./Some (I (uClip SZ (Add (%I x!) (%I y!)))))
    ))
    :pattern ((vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.? x!
      y!
    ))
    :qid internal_vstd!std_specs.num.usize_specs.checked_add__returns_clause_autospec.?_definition
    :skolemid skolem_internal_vstd!std_specs.num.usize_specs.checked_add__returns_clause_autospec.?_definition
))))
(assert
 (forall ((x! Poly) (y! Poly)) (!
   (=>
    (and
     (has_type x! USIZE)
     (has_type y! USIZE)
    )
    (has_type (Poly%core!option.Option. (vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.?
       x! y!
      )
     ) (TYPE%core!option.Option. $ USIZE)
   ))
   :pattern ((vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.? x!
     y!
   ))
   :qid internal_vstd!std_specs.num.usize_specs.checked_add__returns_clause_autospec.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.num.usize_specs.checked_add__returns_clause_autospec.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::num::usize_specs::saturating_sub%returns_clause_autospec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.)
  (forall ((x! Poly) (y! Poly)) (!
    (= (vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.? x! y!)
     (ite
      (< (Sub (%I x!) (%I y!)) 0)
      0
      (uClip SZ (Sub (%I x!) (%I y!)))
    ))
    :pattern ((vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.?
      x! y!
    ))
    :qid internal_vstd!std_specs.num.usize_specs.saturating_sub__returns_clause_autospec.?_definition
    :skolemid skolem_internal_vstd!std_specs.num.usize_specs.saturating_sub__returns_clause_autospec.?_definition
))))
(assert
 (forall ((x! Poly) (y! Poly)) (!
   (=>
    (and
     (has_type x! USIZE)
     (has_type y! USIZE)
    )
    (uInv SZ (vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.? x!
      y!
   )))
   :pattern ((vstd!std_specs.num.usize_specs.saturating_sub%returns_clause_autospec.?
     x! y!
   ))
   :qid internal_vstd!std_specs.num.usize_specs.saturating_sub__returns_clause_autospec.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.num.usize_specs.saturating_sub__returns_clause_autospec.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::num::isize_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.isize_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.isize_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ ISIZE $ ISIZE) (B true))
))

;; Function-Axioms vstd::std_specs::num::isize_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.isize_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.isize_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ ISIZE $ ISIZE self! other!) (B (= self!
       other!
    )))
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ ISIZE $ ISIZE self! other!))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::u128_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u128_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u128_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (UINT 128) $ (UINT 128)) (B
    true
))))

;; Function-Axioms vstd::std_specs::num::u128_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u128_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u128_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 128) $ (UINT 128) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 128) $ (UINT 128) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::i128_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i128_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i128_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (SINT 128) $ (SINT 128)) (B
    true
))))

;; Function-Axioms vstd::std_specs::num::i128_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i128_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i128_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 128) $ (SINT 128) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 128) $ (SINT 128) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::u64_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u64_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u64_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (UINT 64) $ (UINT 64)) (B true))
))

;; Function-Axioms vstd::std_specs::num::u64_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u64_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u64_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 64) $ (UINT 64) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 64) $ (UINT 64) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::i64_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i64_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i64_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (SINT 64) $ (SINT 64)) (B true))
))

;; Function-Axioms vstd::std_specs::num::i64_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i64_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i64_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 64) $ (SINT 64) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 64) $ (SINT 64) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::u32_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u32_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u32_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (UINT 32) $ (UINT 32)) (B true))
))

;; Function-Axioms vstd::std_specs::num::u32_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u32_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u32_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 32) $ (UINT 32) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 32) $ (UINT 32) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::i32_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i32_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i32_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (SINT 32) $ (SINT 32)) (B true))
))

;; Function-Axioms vstd::std_specs::num::i32_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i32_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i32_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 32) $ (SINT 32) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 32) $ (SINT 32) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::u16_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u16_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u16_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (UINT 16) $ (UINT 16)) (B true))
))

;; Function-Axioms vstd::std_specs::num::u16_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u16_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u16_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 16) $ (UINT 16) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 16) $ (UINT 16) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::i16_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i16_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i16_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (SINT 16) $ (SINT 16)) (B true))
))

;; Function-Axioms vstd::std_specs::num::i16_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i16_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i16_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 16) $ (SINT 16) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 16) $ (SINT 16) self!
      other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::u8_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u8_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u8_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (UINT 8) $ (UINT 8)) (B true))
))

;; Function-Axioms vstd::std_specs::num::u8_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.u8_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.u8_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 8) $ (UINT 8) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (UINT 8) $ (UINT 8) self! other!))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::num::i8_specs::impl&%0::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i8_specs.impl&%0.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i8_specs.impl&%0.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (SINT 8) $ (SINT 8)) (B true))
))

;; Function-Axioms vstd::std_specs::num::i8_specs::impl&%0::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.num.i8_specs.impl&%0.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.num.i8_specs.impl&%0.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 8) $ (SINT 8) self! other!)
     (B (= self! other!))
    )
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (SINT 8) $ (SINT 8) self! other!))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::cmp::impl&%2::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.cmp.impl&%2.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.cmp.impl&%2.obeys_eq_spec.)
  (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ BOOL $ BOOL) (B true))
))

;; Function-Axioms vstd::std_specs::cmp::impl&%2::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.cmp.impl&%2.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.cmp.impl&%2.eq_spec.)
  (forall ((self! Poly) (other! Poly)) (!
    (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ BOOL $ BOOL self! other!) (B (= self!
       other!
    )))
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ BOOL $ BOOL self! other!))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::option::impl&%1::obeys_eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%1.obeys_eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%1.obeys_eq_spec.)
  (forall ((T&. Dcr) (T& Type)) (!
    (=>
     (and
      (sized T&.)
      (tr_bound%vstd!std_specs.cmp.PartialEqSpec. T&. T& T&. T&)
     )
     (= (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (TYPE%core!option.Option. T&.
        T&
       ) $ (TYPE%core!option.Option. T&. T&)
      ) (vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? T&. T& T&. T&)
    ))
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.? $ (TYPE%core!option.Option.
       T&. T&
      ) $ (TYPE%core!option.Option. T&. T&)
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.obeys_eq_spec.?_definition
))))

;; Function-Axioms vstd::std_specs::option::impl&%1::eq_spec
(assert
 (fuel_bool_default fuel%vstd!std_specs.option.impl&%1.eq_spec.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.option.impl&%1.eq_spec.)
  (forall ((T&. Dcr) (T& Type) (self! Poly) (other! Poly)) (!
    (=>
     (and
      (sized T&.)
      (tr_bound%vstd!std_specs.cmp.PartialEqSpec. T&. T& T&. T&)
     )
     (= (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (TYPE%core!option.Option. T&. T&)
       $ (TYPE%core!option.Option. T&. T&) self! other!
      ) (B (let
        ((tmp%%$ (tuple%2./tuple%2 self! other!)))
        (=>
         (not (and
           (and
            (is-tuple%2./tuple%2 tmp%%$)
            (is-core!option.Option./None (%Poly%core!option.Option. (tuple%2./tuple%2/0 (%Poly%tuple%2.
                (Poly%tuple%2. tmp%%$)
           )))))
           (is-core!option.Option./None (%Poly%core!option.Option. (tuple%2./tuple%2/1 (%Poly%tuple%2.
               (Poly%tuple%2. tmp%%$)
         ))))))
         (and
          (and
           (and
            (is-tuple%2./tuple%2 tmp%%$)
            (is-core!option.Option./Some (%Poly%core!option.Option. (tuple%2./tuple%2/0 (%Poly%tuple%2.
                (Poly%tuple%2. tmp%%$)
           )))))
           (is-core!option.Option./Some (%Poly%core!option.Option. (tuple%2./tuple%2/1 (%Poly%tuple%2.
               (Poly%tuple%2. tmp%%$)
          )))))
          (%B (let
            ((x$ (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. (tuple%2./tuple%2/0
                 (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
            )))))
            (let
             ((y$ (core!option.Option./Some/0 T&. T& (%Poly%core!option.Option. (tuple%2./tuple%2/1
                  (%Poly%tuple%2. (Poly%tuple%2. tmp%%$))
             )))))
             (vstd!std_specs.cmp.PartialEqSpec.eq_spec.? T&. T& T&. T& x$ y$)
    )))))))))
    :pattern ((vstd!std_specs.cmp.PartialEqSpec.eq_spec.? $ (TYPE%core!option.Option. T&.
       T&
      ) $ (TYPE%core!option.Option. T&. T&) self! other!
    ))
    :qid internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
    :skolemid skolem_internal_vstd!std_specs.cmp.PartialEqSpec.eq_spec.?_definition
))))

;; Function-Specs vstd::layout::size_of_as_usize
(declare-fun req%vstd!layout.size_of_as_usize. (Dcr Type) Bool)
(declare-const %%global_location_label%%29 Bool)
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (= (req%vstd!layout.size_of_as_usize. V&. V&) (=>
     %%global_location_label%%29
     (= (uClip SZ (vstd!layout.size_of.? V&. V&)) (vstd!layout.size_of.? V&. V&))
   ))
   :pattern ((req%vstd!layout.size_of_as_usize. V&. V&))
   :qid internal_req__vstd!layout.size_of_as_usize._definition
   :skolemid skolem_internal_req__vstd!layout.size_of_as_usize._definition
)))

;; Function-Axioms vstd::layout::size_of_as_usize
(assert
 (fuel_bool_default fuel%vstd!layout.size_of_as_usize.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!layout.size_of_as_usize.)
  (forall ((V&. Dcr) (V& Type)) (!
    (= (vstd!layout.size_of_as_usize.? V&. V&) (uClip SZ (vstd!layout.size_of.? V&. V&)))
    :pattern ((vstd!layout.size_of_as_usize.? V&. V&))
    :qid internal_vstd!layout.size_of_as_usize.?_definition
    :skolemid skolem_internal_vstd!layout.size_of_as_usize.?_definition
))))
(assert
 (forall ((V&. Dcr) (V& Type)) (!
   (uInv SZ (vstd!layout.size_of_as_usize.? V&. V&))
   :pattern ((vstd!layout.size_of_as_usize.? V&. V&))
   :qid internal_vstd!layout.size_of_as_usize.?_pre_post_definition
   :skolemid skolem_internal_vstd!layout.size_of_as_usize.?_pre_post_definition
)))

;; Function-Axioms vstd::map::impl&%0::new
(assert
 (fuel_bool_default fuel%vstd!map.impl&%0.new.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map.impl&%0.new.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (fk! Poly) (fv! Poly)) (!
    (= (vstd!map.impl&%0.new.? K&. K& V&. V& fk! fv!) (vstd!set.impl&%0.mk_map.? K&. K&
      V&. V& (vstd!set.impl&%0.new.? K&. K& fk!) fv!
    ))
    :pattern ((vstd!map.impl&%0.new.? K&. K& V&. V& fk! fv!))
    :qid internal_vstd!map.impl&__0.new.?_definition
    :skolemid skolem_internal_vstd!map.impl&__0.new.?_definition
))))
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (fk! Poly) (fv! Poly)) (!
   (=>
    (and
     (has_type fk! (TYPE%fun%1. K&. K& $ BOOL))
     (has_type fv! (TYPE%fun%1. K&. K& V&. V&))
    )
    (has_type (vstd!map.impl&%0.new.? K&. K& V&. V& fk! fv!) (TYPE%vstd!map.Map. K&. K&
      V&. V&
   )))
   :pattern ((vstd!map.impl&%0.new.? K&. K& V&. V& fk! fv!))
   :qid internal_vstd!map.impl&__0.new.?_pre_post_definition
   :skolemid skolem_internal_vstd!map.impl&__0.new.?_pre_post_definition
)))

;; Function-Axioms vstd::map_lib::impl&%0::contains_key
(assert
 (fuel_bool_default fuel%vstd!map_lib.impl&%0.contains_key.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map_lib.impl&%0.contains_key.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly) (k! Poly)) (!
    (= (vstd!map_lib.impl&%0.contains_key.? K&. K& V&. V& self! k!) (vstd!set.Set.contains.?
      K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) k!
    ))
    :pattern ((vstd!map_lib.impl&%0.contains_key.? K&. K& V&. V& self! k!))
    :qid internal_vstd!map_lib.impl&__0.contains_key.?_definition
    :skolemid skolem_internal_vstd!map_lib.impl&__0.contains_key.?_definition
))))

;; Function-Axioms vstd::map_lib::impl&%0::map_entries
(assert
 (fuel_bool_default fuel%vstd!map_lib.impl&%0.map_entries.)
)
(declare-fun %%lambda%%2 (Dcr Type Poly) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Poly) (k$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%2 %%hole%%0 %%hole%%1 %%hole%%2) k$) (B (vstd!set.Set.contains.?
      %%hole%%0 %%hole%%1 %%hole%%2 k$
   )))
   :pattern ((%%apply%%0 (%%lambda%%2 %%hole%%0 %%hole%%1 %%hole%%2) k$))
)))
(declare-fun %%lambda%%3 (Dcr Type Dcr Type Poly %%Function%%) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Dcr) (%%hole%%3 Type) (%%hole%%4
    Poly
   ) (%%hole%%5 %%Function%%) (k$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%3 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5)
     k$
    ) (%%apply%%1 %%hole%%5 k$ (vstd!map.impl&%0.index.? %%hole%%0 %%hole%%1 %%hole%%2
      %%hole%%3 %%hole%%4 k$
   )))
   :pattern ((%%apply%%0 (%%lambda%%3 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5
     ) k$
)))))
(assert
 (=>
  (fuel_bool fuel%vstd!map_lib.impl&%0.map_entries.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (W&. Dcr) (W& Type) (self! Poly) (
     f! Poly
    )
   ) (!
    (= (vstd!map_lib.impl&%0.map_entries.? K&. K& V&. V& W&. W& self! f!) (vstd!map.impl&%0.new.?
      K&. K& W&. W& (Poly%fun%1. (mk_fun (%%lambda%%2 K&. K& (vstd!map.impl&%0.dom.? K&. K&
          V&. V& self!
       )))
      ) (Poly%fun%1. (mk_fun (%%lambda%%3 K&. K& V&. V& self! (%Poly%fun%2. f!))))
    ))
    :pattern ((vstd!map_lib.impl&%0.map_entries.? K&. K& V&. V& W&. W& self! f!))
    :qid internal_vstd!map_lib.impl&__0.map_entries.?_definition
    :skolemid skolem_internal_vstd!map_lib.impl&__0.map_entries.?_definition
))))
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (W&. Dcr) (W& Type) (self! Poly) (
    f! Poly
   )
  ) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type f! (TYPE%fun%2. K&. K& V&. V& W&. W&))
    )
    (has_type (vstd!map_lib.impl&%0.map_entries.? K&. K& V&. V& W&. W& self! f!) (TYPE%vstd!map.Map.
      K&. K& W&. W&
   )))
   :pattern ((vstd!map_lib.impl&%0.map_entries.? K&. K& V&. V& W&. W& self! f!))
   :qid internal_vstd!map_lib.impl&__0.map_entries.?_pre_post_definition
   :skolemid skolem_internal_vstd!map_lib.impl&__0.map_entries.?_pre_post_definition
)))

;; Function-Axioms vstd::map_lib::impl&%0::map_values
(assert
 (fuel_bool_default fuel%vstd!map_lib.impl&%0.map_values.)
)
(declare-fun %%lambda%%4 (Dcr Type Dcr Type Poly %%Function%%) %%Function%%)
(assert
 (forall ((%%hole%%0 Dcr) (%%hole%%1 Type) (%%hole%%2 Dcr) (%%hole%%3 Type) (%%hole%%4
    Poly
   ) (%%hole%%5 %%Function%%) (k$ Poly)
  ) (!
   (= (%%apply%%0 (%%lambda%%4 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5)
     k$
    ) (%%apply%%0 %%hole%%5 (vstd!map.impl&%0.index.? %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3
      %%hole%%4 k$
   )))
   :pattern ((%%apply%%0 (%%lambda%%4 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5
     ) k$
)))))
(assert
 (=>
  (fuel_bool fuel%vstd!map_lib.impl&%0.map_values.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (W&. Dcr) (W& Type) (self! Poly) (
     f! Poly
    )
   ) (!
    (= (vstd!map_lib.impl&%0.map_values.? K&. K& V&. V& W&. W& self! f!) (vstd!map.impl&%0.new.?
      K&. K& W&. W& (Poly%fun%1. (mk_fun (%%lambda%%2 K&. K& (vstd!map.impl&%0.dom.? K&. K&
          V&. V& self!
       )))
      ) (Poly%fun%1. (mk_fun (%%lambda%%4 K&. K& V&. V& self! (%Poly%fun%1. f!))))
    ))
    :pattern ((vstd!map_lib.impl&%0.map_values.? K&. K& V&. V& W&. W& self! f!))
    :qid internal_vstd!map_lib.impl&__0.map_values.?_definition
    :skolemid skolem_internal_vstd!map_lib.impl&__0.map_values.?_definition
))))
(assert
 (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (W&. Dcr) (W& Type) (self! Poly) (
    f! Poly
   )
  ) (!
   (=>
    (and
     (has_type self! (TYPE%vstd!map.Map. K&. K& V&. V&))
     (has_type f! (TYPE%fun%1. V&. V& W&. W&))
    )
    (has_type (vstd!map_lib.impl&%0.map_values.? K&. K& V&. V& W&. W& self! f!) (TYPE%vstd!map.Map.
      K&. K& W&. W&
   )))
   :pattern ((vstd!map_lib.impl&%0.map_values.? K&. K& V&. V& W&. W& self! f!))
   :qid internal_vstd!map_lib.impl&__0.map_values.?_pre_post_definition
   :skolemid skolem_internal_vstd!map_lib.impl&__0.map_values.?_pre_post_definition
)))

;; Function-Axioms vstd::map_lib::impl&%0::is_injective
(assert
 (fuel_bool_default fuel%vstd!map_lib.impl&%0.is_injective.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!map_lib.impl&%0.is_injective.)
  (forall ((K&. Dcr) (K& Type) (V&. Dcr) (V& Type) (self! Poly)) (!
    (= (vstd!map_lib.impl&%0.is_injective.? K&. K& V&. V& self!) (forall ((x$ Poly) (y$ Poly))
      (!
       (=>
        (and
         (has_type x$ K&)
         (has_type y$ K&)
        )
        (=>
         (and
          (and
           (not (= x$ y$))
           (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) x$)
          )
          (vstd!set.Set.contains.? K&. K& (vstd!map.impl&%0.dom.? K&. K& V&. V& self!) y$)
         )
         (not (= (vstd!map.impl&%0.index.? K&. K& V&. V& self! x$) (vstd!map.impl&%0.index.?
            K&. K& V&. V& self! y$
       )))))
       :pattern ((vstd!map.impl&%0.index.? K&. K& V&. V& self! x$) (vstd!map.impl&%0.index.?
         K&. K& V&. V& self! y$
       ))
       :qid user_vstd__map_lib__impl&%0__is_injective_93
       :skolemid skolem_user_vstd__map_lib__impl&%0__is_injective_93
    )))
    :pattern ((vstd!map_lib.impl&%0.is_injective.? K&. K& V&. V& self!))
    :qid internal_vstd!map_lib.impl&__0.is_injective.?_definition
    :skolemid skolem_internal_vstd!map_lib.impl&__0.is_injective.?_definition
))))

;; Function-Specs vstd::seq::Seq::last
(declare-fun req%vstd!seq.Seq.last. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%30 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (= (req%vstd!seq.Seq.last. A&. A& self!) (=>
     %%global_location_label%%30
     (< 0 (vstd!seq.Seq.len.? A&. A& self!))
   ))
   :pattern ((req%vstd!seq.Seq.last. A&. A& self!))
   :qid internal_req__vstd!seq.Seq.last._definition
   :skolemid skolem_internal_req__vstd!seq.Seq.last._definition
)))

;; Function-Axioms vstd::seq::Seq::last
(assert
 (fuel_bool_default fuel%vstd!seq.Seq.last.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.Seq.last.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!seq.Seq.last.? A&. A& self!) (vstd!seq.Seq.index.? A&. A& self! (I (Sub (vstd!seq.Seq.len.?
         A&. A& self!
        ) 1
    ))))
    :pattern ((vstd!seq.Seq.last.? A&. A& self!))
    :qid internal_vstd!seq.Seq.last.?_definition
    :skolemid skolem_internal_vstd!seq.Seq.last.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (has_type (vstd!seq.Seq.last.? A&. A& self!) A&)
   )
   :pattern ((vstd!seq.Seq.last.? A&. A& self!))
   :qid internal_vstd!seq.Seq.last.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.Seq.last.?_pre_post_definition
)))

;; Function-Specs vstd::seq::impl&%0::first
(declare-fun req%vstd!seq.impl&%0.first. (Dcr Type Poly) Bool)
(declare-const %%global_location_label%%31 Bool)
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (= (req%vstd!seq.impl&%0.first. A&. A& self!) (=>
     %%global_location_label%%31
     (< 0 (vstd!seq.Seq.len.? A&. A& self!))
   ))
   :pattern ((req%vstd!seq.impl&%0.first. A&. A& self!))
   :qid internal_req__vstd!seq.impl&__0.first._definition
   :skolemid skolem_internal_req__vstd!seq.impl&__0.first._definition
)))

;; Function-Axioms vstd::seq::impl&%0::first
(assert
 (fuel_bool_default fuel%vstd!seq.impl&%0.first.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq.impl&%0.first.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (= (vstd!seq.impl&%0.first.? A&. A& self!) (vstd!seq.Seq.index.? A&. A& self! (I 0)))
    :pattern ((vstd!seq.impl&%0.first.? A&. A& self!))
    :qid internal_vstd!seq.impl&__0.first.?_definition
    :skolemid skolem_internal_vstd!seq.impl&__0.first.?_definition
))))
(assert
 (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
   (=>
    (has_type self! (TYPE%vstd!seq.Seq. A&. A&))
    (has_type (vstd!seq.impl&%0.first.? A&. A& self!) A&)
   )
   :pattern ((vstd!seq.impl&%0.first.? A&. A& self!))
   :qid internal_vstd!seq.impl&__0.first.?_pre_post_definition
   :skolemid skolem_internal_vstd!seq.impl&__0.first.?_pre_post_definition
)))

;; Function-Axioms vstd::seq_lib::impl&%0::contains
(assert
 (fuel_bool_default fuel%vstd!seq_lib.impl&%0.contains.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!seq_lib.impl&%0.contains.)
  (forall ((A&. Dcr) (A& Type) (self! Poly) (needle! Poly)) (!
    (= (vstd!seq_lib.impl&%0.contains.? A&. A& self! needle!) (exists ((i$ Poly)) (!
       (and
        (has_type i$ INT)
        (and
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$1 (%I i$)))
           (let
            ((tmp%%$2 (vstd!seq.Seq.len.? A&. A& self!)))
            (and
             (<= tmp%%$ tmp%%$1)
             (< tmp%%$1 tmp%%$2)
         ))))
         (= (vstd!seq.Seq.index.? A&. A& self! i$) needle!)
       ))
       :pattern ((vstd!seq.Seq.index.? A&. A& self! i$))
       :qid user_vstd__seq_lib__impl&%0__contains_94
       :skolemid skolem_user_vstd__seq_lib__impl&%0__contains_94
    )))
    :pattern ((vstd!seq_lib.impl&%0.contains.? A&. A& self! needle!))
    :qid internal_vstd!seq_lib.impl&__0.contains.?_definition
    :skolemid skolem_internal_vstd!seq_lib.impl&__0.contains.?_definition
))))

;; Function-Axioms vstd::view::impl&%0::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%0.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%0.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (tr_bound%vstd!view.View. A&. A&)
     (= (vstd!view.View.view.? (REF A&.) A& self!) (vstd!view.View.view.? A&. A& self!))
    )
    :pattern ((vstd!view.View.view.? (REF A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%2::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%2.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%2.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (tr_bound%vstd!view.View. A&. A&)
     (= (vstd!view.View.view.? (BOX $ TYPE%alloc!alloc.Global. A&.) A& self!) (vstd!view.View.view.?
       A&. A& self!
    )))
    :pattern ((vstd!view.View.view.? (BOX $ TYPE%alloc!alloc.Global. A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%4::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%4.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%4.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (and
      (sized A&.)
      (tr_bound%vstd!view.View. A&. A&)
     )
     (= (vstd!view.View.view.? (RC $ TYPE%alloc!alloc.Global. A&.) A& self!) (vstd!view.View.view.?
       A&. A& self!
    )))
    :pattern ((vstd!view.View.view.? (RC $ TYPE%alloc!alloc.Global. A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%6::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%6.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%6.view.)
  (forall ((A&. Dcr) (A& Type) (self! Poly)) (!
    (=>
     (and
      (sized A&.)
      (tr_bound%vstd!view.View. A&. A&)
     )
     (= (vstd!view.View.view.? (ARC $ TYPE%alloc!alloc.Global. A&.) A& self!) (vstd!view.View.view.?
       A&. A& self!
    )))
    :pattern ((vstd!view.View.view.? (ARC $ TYPE%alloc!alloc.Global. A&.) A& self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%14::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%14.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%14.view.)
  (forall ((T&. Dcr) (T& Type) (self! Poly)) (!
    (=>
     (sized T&.)
     (= (vstd!view.View.view.? $ (TYPE%core!option.Option. T&. T&) self!) self!)
    )
    :pattern ((vstd!view.View.view.? $ (TYPE%core!option.Option. T&. T&) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%16::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%16.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%16.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ TYPE%tuple%0. self!) self!)
    :pattern ((vstd!view.View.view.? $ TYPE%tuple%0. self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%18::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%18.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%18.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ BOOL self!) self!)
    :pattern ((vstd!view.View.view.? $ BOOL self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%20::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%20.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%20.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 8) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 8) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%22::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%22.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%22.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 16) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 16) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%24::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%24.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%24.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 32) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 32) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%26::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%26.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%26.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 64) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 64) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%28::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%28.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%28.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (UINT 128) self!) self!)
    :pattern ((vstd!view.View.view.? $ (UINT 128) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%30::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%30.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%30.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ USIZE self!) self!)
    :pattern ((vstd!view.View.view.? $ USIZE self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%32::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%32.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%32.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (SINT 8) self!) self!)
    :pattern ((vstd!view.View.view.? $ (SINT 8) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%34::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%34.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%34.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (SINT 16) self!) self!)
    :pattern ((vstd!view.View.view.? $ (SINT 16) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%36::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%36.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%36.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (SINT 32) self!) self!)
    :pattern ((vstd!view.View.view.? $ (SINT 32) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%38::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%38.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%38.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (SINT 64) self!) self!)
    :pattern ((vstd!view.View.view.? $ (SINT 64) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%40::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%40.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%40.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ (SINT 128) self!) self!)
    :pattern ((vstd!view.View.view.? $ (SINT 128) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%42::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%42.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%42.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ ISIZE self!) self!)
    :pattern ((vstd!view.View.view.? $ ISIZE self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%44::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%44.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%44.view.)
  (forall ((self! Poly)) (!
    (= (vstd!view.View.view.? $ CHAR self!) self!)
    :pattern ((vstd!view.View.view.? $ CHAR self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%48::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%48.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%48.view.)
  (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type) (self! Poly)) (!
    (=>
     (and
      (sized A0&.)
      (sized A1&.)
      (tr_bound%vstd!view.View. A0&. A0&)
      (tr_bound%vstd!view.View. A1&. A1&)
     )
     (= (vstd!view.View.view.? (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&) self!) (Poly%tuple%2.
       (tuple%2./tuple%2 (vstd!view.View.view.? A0&. A0& (tuple%2./tuple%2/0 (%Poly%tuple%2.
           self!
         ))
        ) (vstd!view.View.view.? A1&. A1& (tuple%2./tuple%2/1 (%Poly%tuple%2. self!)))
    ))))
    :pattern ((vstd!view.View.view.? (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&) self!))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms vstd::view::impl&%50::view
(assert
 (fuel_bool_default fuel%vstd!view.impl&%50.view.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!view.impl&%50.view.)
  (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type) (A2&. Dcr) (A2& Type) (self! Poly))
   (!
    (=>
     (and
      (sized A0&.)
      (sized A1&.)
      (sized A2&.)
      (tr_bound%vstd!view.View. A0&. A0&)
      (tr_bound%vstd!view.View. A1&. A1&)
      (tr_bound%vstd!view.View. A2&. A2&)
     )
     (= (vstd!view.View.view.? (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&. A2&) self!)
      (Poly%tuple%3. (tuple%3./tuple%3 (vstd!view.View.view.? A0&. A0& (tuple%3./tuple%3/0
          (%Poly%tuple%3. self!)
         )
        ) (vstd!view.View.view.? A1&. A1& (tuple%3./tuple%3/1 (%Poly%tuple%3. self!))) (vstd!view.View.view.?
         A2&. A2& (tuple%3./tuple%3/2 (%Poly%tuple%3. self!))
    )))))
    :pattern ((vstd!view.View.view.? (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&. A2&)
      self!
    ))
    :qid internal_vstd!view.View.view.?_definition
    :skolemid skolem_internal_vstd!view.View.view.?_definition
))))

;; Function-Axioms lib::block_index::GRANULARITY
(assert
 (fuel_bool_default fuel%lib!block_index.GRANULARITY.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.GRANULARITY.)
  (= lib!block_index.GRANULARITY.? (uClip SZ (Mul 8 4)))
))
(assert
 (uInv SZ lib!block_index.GRANULARITY.?)
)

;; Function-Axioms lib::block_index::BlockIndex::granularity_log2_spec
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.granularity_log2_spec.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.granularity_log2_spec.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
    (= (lib!block_index.impl&%7.granularity_log2_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     (vstd!arithmetic.logarithm.log.? (I 2) (I lib!block_index.GRANULARITY.?))
    )
    :pattern ((lib!block_index.impl&%7.granularity_log2_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN&))
    :qid internal_lib!block_index.impl&__7.granularity_log2_spec.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.granularity_log2_spec.?_definition
))))

;; Function-Axioms lib::block_index::BlockIndex::parameter_validity
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.parameter_validity.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.parameter_validity.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
    (= (lib!block_index.impl&%7.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&) (and
      (and
       (and
        (let
         ((tmp%%$ 0))
         (let
          ((tmp%%$1 (const_int FLLEN&)))
          (let
           ((tmp%%$2 (Sub SZ (lib!block_index.impl&%7.granularity_log2_spec.? FLLEN&. FLLEN& SLLEN&.
               SLLEN&
           ))))
           (and
            (< tmp%%$ tmp%%$1)
            (< tmp%%$1 tmp%%$2)
        ))))
        (and
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$4 (const_int SLLEN&)))
           (let
            ((tmp%%$5 SZ))
            (and
             (< tmp%%$ tmp%%$4)
             (<= tmp%%$4 tmp%%$5)
         ))))
         (lib!bits.is_power_of_two.? (I (const_int SLLEN&)))
       ))
       (=>
        (= SZ 64)
        (= lib!block_index.GRANULARITY.? 32)
      ))
      (=>
       (= SZ 32)
       (= lib!block_index.GRANULARITY.? 16)
    )))
    :pattern ((lib!block_index.impl&%7.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&))
    :qid internal_lib!block_index.impl&__7.parameter_validity.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.parameter_validity.?_definition
))))

;; Function-Axioms lib::half_open_range::HalfOpenRange::wf
(assert
 (fuel_bool_default fuel%lib!half_open_range.impl&%0.wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!half_open_range.impl&%0.wf.)
  (forall ((self! Poly)) (!
    (= (lib!half_open_range.impl&%0.wf.? self!) (<= (lib!half_open_range.impl&%0.start.?
       self!
      ) (lib!half_open_range.impl&%0.end.? self!)
    ))
    :pattern ((lib!half_open_range.impl&%0.wf.? self!))
    :qid internal_lib!half_open_range.impl&__0.wf.?_definition
    :skolemid skolem_internal_lib!half_open_range.impl&__0.wf.?_definition
))))

;; Function-Specs lib::half_open_range::HalfOpenRange::new
(declare-fun req%lib!half_open_range.impl&%0.new. (Poly Poly) Bool)
(declare-const %%global_location_label%%32 Bool)
(assert
 (forall ((start! Poly) (size! Poly)) (!
   (= (req%lib!half_open_range.impl&%0.new. start! size!) (=>
     %%global_location_label%%32
     (>= (%I size!) 0)
   ))
   :pattern ((req%lib!half_open_range.impl&%0.new. start! size!))
   :qid internal_req__lib!half_open_range.impl&__0.new._definition
   :skolemid skolem_internal_req__lib!half_open_range.impl&__0.new._definition
)))

;; Function-Specs lib::block_index::BlockIndex::block_size_range
(declare-fun req%lib!block_index.impl&%7.block_size_range. (Dcr Type Dcr Type Poly)
 Bool
)
(declare-const %%global_location_label%%33 Bool)
(declare-const %%global_location_label%%34 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
   (= (req%lib!block_index.impl&%7.block_size_range. FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    (and
     (=>
      %%global_location_label%%33
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
     )
     (=>
      %%global_location_label%%34
      (lib!block_index.impl&%7.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
   )))
   :pattern ((req%lib!block_index.impl&%7.block_size_range. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
   ))
   :qid internal_req__lib!block_index.impl&__7.block_size_range._definition
   :skolemid skolem_internal_req__lib!block_index.impl&__7.block_size_range._definition
)))

;; Function-Axioms lib::block_index::BlockIndex::block_size_range
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.block_size_range.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.block_size_range.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!block_index.impl&%7.block_size_range.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
     (let
      ((tmp%%$ (%Poly%lib!block_index.BlockIndex. self!)))
      (let
       ((fl$ (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
            tmp%%$
       )))))
       (let
        ((sl$ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             tmp%%$
        )))))
        (let
         ((fl_block_bytes$ (vstd!arithmetic.power2.pow2.? (I (nClip (Add fl$ (lib!block_index.impl&%7.granularity_log2_spec.?
                FLLEN&. FLLEN& SLLEN&. SLLEN&
         )))))))
         (ite
          (< fl_block_bytes$ (const_int SLLEN&))
          (lib!half_open_range.impl&%0.new.? (I lib!block_index.GRANULARITY.?) (I lib!block_index.GRANULARITY.?))
          (let
           ((sl_block_bytes$ (EucDiv fl_block_bytes$ (const_int SLLEN&))))
           (let
            ((start$ (Add fl_block_bytes$ (Mul sl_block_bytes$ sl$))))
            (let
             ((size$ sl_block_bytes$))
             (lib!half_open_range.impl&%0.new.? (I start$) (I size$))
    )))))))))
    :pattern ((lib!block_index.impl&%7.block_size_range.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self!
    ))
    :qid internal_lib!block_index.impl&__7.block_size_range.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.block_size_range.?_definition
))))

;; Function-Axioms lib::block_index::BlockIndex::valid_block_size
(assert
 (fuel_bool_default fuel%lib!block_index.impl&%7.valid_block_size.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block_index.impl&%7.valid_block_size.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (size! Poly)) (!
    (= (lib!block_index.impl&%7.valid_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN& size!)
     (and
      (and
       (<= lib!block_index.GRANULARITY.? (%I size!))
       (< (%I size!) (Mul (vstd!arithmetic.power2.pow2.? (I (const_int FLLEN&))) lib!block_index.GRANULARITY.?))
      )
      (= (EucMod (%I size!) lib!block_index.GRANULARITY.?) 0)
    ))
    :pattern ((lib!block_index.impl&%7.valid_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      size!
    ))
    :qid internal_lib!block_index.impl&__7.valid_block_size.?_definition
    :skolemid skolem_internal_lib!block_index.impl&__7.valid_block_size.?_definition
))))

;; Function-Specs lib::half_open_range::HalfOpenRange::contains
(declare-fun req%lib!half_open_range.impl&%0.contains. (Poly Poly) Bool)
(declare-const %%global_location_label%%35 Bool)
(assert
 (forall ((self! Poly) (e! Poly)) (!
   (= (req%lib!half_open_range.impl&%0.contains. self! e!) (=>
     %%global_location_label%%35
     (lib!half_open_range.impl&%0.wf.? self!)
   ))
   :pattern ((req%lib!half_open_range.impl&%0.contains. self! e!))
   :qid internal_req__lib!half_open_range.impl&__0.contains._definition
   :skolemid skolem_internal_req__lib!half_open_range.impl&__0.contains._definition
)))

;; Function-Axioms lib::half_open_range::HalfOpenRange::contains
(assert
 (fuel_bool_default fuel%lib!half_open_range.impl&%0.contains.)
)
(assert
 (=>
  (fuel_bool fuel%lib!half_open_range.impl&%0.contains.)
  (forall ((self! Poly) (e! Poly)) (!
    (= (lib!half_open_range.impl&%0.contains.? self! e!) (let
      ((tmp%%$ (lib!half_open_range.impl&%0.start.? self!)))
      (let
       ((tmp%%$1 (%I e!)))
       (let
        ((tmp%%$2 (lib!half_open_range.impl&%0.end.? self!)))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
    )))))
    :pattern ((lib!half_open_range.impl&%0.contains.? self! e!))
    :qid internal_lib!half_open_range.impl&__0.contains.?_definition
    :skolemid skolem_internal_lib!half_open_range.impl&__0.contains.?_definition
))))

;; Function-Axioms lib::all_blocks::ShadowFreelist::shadow_freelist_has_all_wf_index
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.? FLLEN&. FLLEN& SLLEN&.
      SLLEN& self!
     ) (forall ((idx$ Poly)) (!
       (=>
        (has_type idx$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (= (vstd!set.Set.contains.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
           SLLEN&
          ) (vstd!map.impl&%0.dom.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
            SLLEN&
           ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
            (%Poly%lib!all_blocks.ShadowFreelist. self!)
           )
          ) idx$
         ) (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$)
       ))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$))
       :qid user_lib__all_blocks__ShadowFreelist__shadow_freelist_has_all_wf_index_95
       :skolemid skolem_user_lib__all_blocks__ShadowFreelist__shadow_freelist_has_all_wf_index_95
    )))
    :pattern ((lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.? FLLEN&. FLLEN&
      SLLEN&. SLLEN& self!
    ))
    :qid internal_lib!all_blocks.impl&__1.shadow_freelist_has_all_wf_index.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__1.shadow_freelist_has_all_wf_index.?_definition
))))

;; Function-Specs lib::all_blocks::is_identity_injection
(declare-fun req%lib!all_blocks.is_identity_injection. (Dcr Type Dcr Type Poly Poly)
 Bool
)
(declare-const %%global_location_label%%36 Bool)
(declare-const %%global_location_label%%37 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sfl! Poly) (all_block_ptrs!
    Poly
   )
  ) (!
   (= (req%lib!all_blocks.is_identity_injection. FLLEN&. FLLEN& SLLEN&. SLLEN& sfl! all_block_ptrs!)
    (and
     (=>
      %%global_location_label%%36
      (lib!ordered_pointer_list.ptrs_no_duplicates.? all_block_ptrs!)
     )
     (=>
      %%global_location_label%%37
      (lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.? FLLEN&. FLLEN& SLLEN&.
       SLLEN& sfl!
   ))))
   :pattern ((req%lib!all_blocks.is_identity_injection. FLLEN&. FLLEN& SLLEN&. SLLEN&
     sfl! all_block_ptrs!
   ))
   :qid internal_req__lib!all_blocks.is_identity_injection._definition
   :skolemid skolem_internal_req__lib!all_blocks.is_identity_injection._definition
)))

;; Function-Axioms lib::all_blocks::is_identity_injection
(assert
 (fuel_bool_default fuel%lib!all_blocks.is_identity_injection.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.is_identity_injection.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sfl! Poly) (all_block_ptrs!
     Poly
    )
   ) (!
    (= (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& sfl! all_block_ptrs!)
     (and
      (and
       (vstd!map_lib.impl&%0.is_injective.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
          FLLEN&. FLLEN& SLLEN&. SLLEN&
         ) $ INT
        ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
          sfl!
       )))
       (forall ((idx$ Poly) (m$ Poly)) (!
         (=>
          (and
           (has_type idx$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
           (has_type m$ INT)
          )
          (= (vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
              FLLEN&. FLLEN& SLLEN&. SLLEN&
             ) $ INT
            ) (vstd!map.impl&%0.dom.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
               FLLEN&. FLLEN& SLLEN&. SLLEN&
              ) $ INT
             ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
               sfl!
             ))
            ) (Poly%tuple%2. (tuple%2./tuple%2 idx$ m$))
           ) (and
            (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$)
            (let
             ((tmp%%$ 0))
             (let
              ((tmp%%$1 (%I m$)))
              (let
               ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                   $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                    $ (PTR $ TYPE%lib!block.BlockHdr.)
                   ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                     sfl!
                    )
                   ) idx$
               ))))
               (and
                (<= tmp%%$ tmp%%$1)
                (< tmp%%$1 tmp%%$2)
         )))))))
         :pattern ((vstd!set.Set.contains.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
             FLLEN&. FLLEN& SLLEN&. SLLEN&
            ) $ INT
           ) (vstd!map.impl&%0.dom.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
              FLLEN&. FLLEN& SLLEN&. SLLEN&
             ) $ INT
            ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
              sfl!
            ))
           ) (Poly%tuple%2. (tuple%2./tuple%2 idx$ m$))
         ))
         :qid user_lib__all_blocks__is_identity_injection_96
         :skolemid skolem_user_lib__all_blocks__is_identity_injection_96
      )))
      (forall ((idx$ Poly) (m$ Poly)) (!
        (=>
         (and
          (has_type idx$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
          (has_type m$ INT)
         )
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$)
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$4 (%I m$)))
             (let
              ((tmp%%$5 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                  $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                   $ (PTR $ TYPE%lib!block.BlockHdr.)
                  ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                    sfl!
                   )
                  ) idx$
              ))))
              (and
               (<= tmp%%$ tmp%%$4)
               (< tmp%%$4 tmp%%$5)
          )))))
          (and
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$7 (%I (vstd!map.impl&%0.index.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
                   FLLEN&. FLLEN& SLLEN&. SLLEN&
                  ) $ INT
                 ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
                   sfl!
                  )
                 ) (Poly%tuple%2. (tuple%2./tuple%2 idx$ m$))
             ))))
             (let
              ((tmp%%$8 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) all_block_ptrs!)))
              (and
               (<= tmp%%$ tmp%%$7)
               (< tmp%%$7 tmp%%$8)
           ))))
           (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                sfl!
               )
              ) idx$
             ) m$
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) all_block_ptrs! (vstd!map.impl&%0.index.?
              (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
               $ INT
              ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
                sfl!
               )
              ) (Poly%tuple%2. (tuple%2./tuple%2 idx$ m$))
        ))))))
        :pattern ((vstd!map.impl&%0.index.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
            FLLEN&. FLLEN& SLLEN&. SLLEN&
           ) $ INT
          ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
            sfl!
           )
          ) (Poly%tuple%2. (tuple%2./tuple%2 idx$ m$))
        ))
        :qid user_lib__all_blocks__is_identity_injection_97
        :skolemid skolem_user_lib__all_blocks__is_identity_injection_97
    ))))
    :pattern ((lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& sfl!
      all_block_ptrs!
    ))
    :qid internal_lib!all_blocks.is_identity_injection.?_definition
    :skolemid skolem_internal_lib!all_blocks.is_identity_injection.?_definition
))))

;; Function-Axioms lib::Tlsf::wf_shadow
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.wf_shadow.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.wf_shadow.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (and
      (and
       (lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.? FLLEN&. FLLEN& SLLEN&.
        SLLEN& (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
           self!
       ))))
       (lib!linked_list.impl&%0.shadow_ptrs_nonnull.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
      )
      (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
        (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. self!))
       ) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
         (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
            (%Poly%lib!Tlsf. self!)
    ))))))))
    :pattern ((lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!linked_list.impl&__0.wf_shadow.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.wf_shadow.?_definition
))))

;; Function-Axioms lib::parameters::SIZE_USED
(assert
 (fuel_bool_default fuel%lib!parameters.SIZE_USED.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.SIZE_USED.)
  (= lib!parameters.SIZE_USED.? 1)
))
(assert
 (uInv SZ lib!parameters.SIZE_USED.?)
)

;; Function-Axioms lib::block::BlockHdr::is_free
(assert
 (fuel_bool_default fuel%lib!block.impl&%1.is_free.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block.impl&%1.is_free.)
  (forall ((self! Poly)) (!
    (= (lib!block.impl&%1.is_free.? self!) (= (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size
          (%Poly%lib!block.BlockHdr. self!)
         )
        ) (I lib!parameters.SIZE_USED.?)
       )
      ) 0
    ))
    :pattern ((lib!block.impl&%1.is_free.? self!))
    :qid internal_lib!block.impl&__1.is_free.?_definition
    :skolemid skolem_internal_lib!block.impl&__1.is_free.?_definition
))))

;; Function-Axioms lib::parameters::SPEC_SIZE_SIZE_MASK
(assert
 (fuel_bool_default fuel%lib!parameters.SPEC_SIZE_SIZE_MASK.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.SPEC_SIZE_SIZE_MASK.)
  (= lib!parameters.SPEC_SIZE_SIZE_MASK.? (uClip SZ (bitnot (I (uClip SZ (Sub (uClip SZ (uClip
          SZ (bitshl (I 1) (I (lib!bits.usize_trailing_zeros.? (I lib!parameters.GRANULARITY.?))))
         )
        ) 1
))))))))
(assert
 (uInv SZ lib!parameters.SPEC_SIZE_SIZE_MASK.?)
)

;; Function-Axioms lib::block::BlockPerm::wf
(assert
 (fuel_bool_default fuel%lib!block.impl&%2.wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block.impl&%2.wf.)
  (forall ((self! Poly)) (!
    (= (lib!block.impl&%2.wf.? self!) (and
      (and
       (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
         (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
            $ TYPE%lib!block.BlockHdr.
           ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
             (%Poly%lib!block.BlockPerm. self!)
       ))))))
       (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/mem
           (%Poly%lib!block.BlockPerm. self!)
         ))
        ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData.
             (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
              (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                (%Poly%lib!block.BlockPerm. self!)
      ))))))))))
      (=>
       (lib!block.impl&%1.is_free.? (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr.
         (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
            (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
               $ TYPE%lib!block.BlockHdr.
              ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                (%Poly%lib!block.BlockPerm. self!)
       )))))))))
       (let
        ((size$ (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
             $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
               (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                 (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
                  (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                    (%Poly%lib!block.BlockPerm. self!)
        ))))))))))))
        (and
         (and
          (and
           (and
            (let
             ((tmp%%$ (lib!block.BlockPerm./BlockPerm/free_link_perm (%Poly%lib!block.BlockPerm. self!))))
             (and
              (is-core!option.Option./Some tmp%%$)
              (let
               ((pt$ (%Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (core!option.Option./Some/0
                   $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.) (%Poly%core!option.Option.
                    (Poly%core!option.Option. tmp%%$)
               )))))
               (and
                (= (lib!block.get_freelink_ptr_spec.? (vstd!raw_ptr.PointsToData./PointsToData/ptr (
                    %Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                      $ TYPE%lib!block.BlockHdr.
                     ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                       (%Poly%lib!block.BlockPerm. self!)
                  )))))
                 ) (%Poly%ptr_mut%<lib!block.FreeLink.>. (vstd!raw_ptr.PointsToData./PointsToData/ptr
                   (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                      $ TYPE%lib!block.FreeLink.
                     ) (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. pt$)
                )))))
                (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                  (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                     $ TYPE%lib!block.FreeLink.
                    ) (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. pt$)
            ))))))))
            (= size$ (uClip SZ (bitand (I size$) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?))))
           )
           (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/mem
              (%Poly%lib!block.BlockPerm. self!)
             )
            ) (I (Add (Add (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!raw_ptr.PointsToData./PointsToData/ptr
                 (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                    $ TYPE%lib!block.BlockHdr.
                   ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                     (%Poly%lib!block.BlockPerm. self!)
                )))))
               ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
              ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.FreeLink.))
             )
            ) (I (Sub (Sub size$ (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.)))
              (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.FreeLink.))
          ))))
          (vstd!set_lib.impl&%0.is_empty.? $ INT (Poly%vstd!set.Set<int.>. (vstd!raw_ptr.impl&%10.dom.?
             (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/overhead_mem (%Poly%lib!block.BlockPerm.
                self!
         )))))))
         (is-core!option.Option./None (lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm.
            self!
    ))))))))
    :pattern ((lib!block.impl&%2.wf.? self!))
    :qid internal_lib!block.impl&__2.wf.?_definition
    :skolemid skolem_internal_lib!block.impl&__2.wf.?_definition
))))

;; Function-Axioms lib::all_blocks::AllBlocks::contains
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.contains.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.contains.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (ptr!
     Poly
    )
   ) (!
    (= (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!) (vstd!seq_lib.impl&%0.contains.?
      $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
       (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
      ) ptr!
    ))
    :pattern ((lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!))
    :qid internal_lib!all_blocks.impl&__0.contains.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.contains.?_definition
))))

;; Function-Specs lib::all_blocks::AllBlocks::value_at
(declare-fun req%lib!all_blocks.impl&%0.value_at. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%38 Bool)
(declare-const %%global_location_label%%39 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (ptr!
    Poly
   )
  ) (!
   (= (req%lib!all_blocks.impl&%0.value_at. FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!)
    (and
     (=>
      %%global_location_label%%38
      (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!)
     )
     (=>
      %%global_location_label%%39
      (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
        (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
           $ TYPE%lib!block.BlockHdr.
          ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
            (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
              $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. self!))
              ) ptr!
   )))))))))))
   :pattern ((req%lib!all_blocks.impl&%0.value_at. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     ptr!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.value_at._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.value_at._definition
)))

;; Function-Axioms lib::all_blocks::AllBlocks::value_at
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.value_at.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.value_at.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (ptr!
     Poly
    )
   ) (!
    (= (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!) (%Poly%lib!block.BlockHdr.
      (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents.
        (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
          (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
             $ TYPE%lib!block.BlockHdr.
            ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
              (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. self!))
                ) ptr!
    ))))))))))))
    :pattern ((lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!))
    :qid internal_lib!all_blocks.impl&__0.value_at.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.value_at.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (ptr!
    Poly
   )
  ) (!
   (=>
    (and
     (has_type self! (TYPE%lib!all_blocks.AllBlocks. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type ptr! (PTR $ TYPE%lib!block.BlockHdr.))
    )
    (has_type (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN&
       SLLEN&. SLLEN& self! ptr!
      )
     ) TYPE%lib!block.BlockHdr.
   ))
   :pattern ((lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! ptr!))
   :qid internal_lib!all_blocks.impl&__0.value_at.?_pre_post_definition
   :skolemid skolem_internal_lib!all_blocks.impl&__0.value_at.?_pre_post_definition
)))

;; Function-Axioms lib::all_blocks::AllBlocks::phys_prev_of
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.phys_prev_of.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.phys_prev_of.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
   (!
    (= (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!)
     (ite
      (= (%I i!) 0)
      core!option.Option./None
      (core!option.Option./Some (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
          (%Poly%lib!all_blocks.AllBlocks. self!)
         )
        ) (I (Sub (%I i!) 1))
    ))))
    :pattern ((lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      i!
    ))
    :qid internal_lib!all_blocks.impl&__0.phys_prev_of.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.phys_prev_of.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%lib!all_blocks.AllBlocks. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type i! INT)
    )
    (has_type (Poly%core!option.Option. (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN&
       SLLEN&. SLLEN& self! i!
      )
     ) (TYPE%core!option.Option. $ (PTR $ TYPE%lib!block.BlockHdr.))
   ))
   :pattern ((lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
   ))
   :qid internal_lib!all_blocks.impl&__0.phys_prev_of.?_pre_post_definition
   :skolemid skolem_internal_lib!all_blocks.impl&__0.phys_prev_of.?_pre_post_definition
)))

;; Function-Axioms lib::parameters::SIZE_SENTINEL
(assert
 (fuel_bool_default fuel%lib!parameters.SIZE_SENTINEL.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.SIZE_SENTINEL.)
  (= lib!parameters.SIZE_SENTINEL.? 2)
))
(assert
 (uInv SZ lib!parameters.SIZE_SENTINEL.?)
)

;; Function-Axioms lib::block::BlockHdr::is_sentinel
(assert
 (fuel_bool_default fuel%lib!block.impl&%1.is_sentinel.)
)
(assert
 (=>
  (fuel_bool fuel%lib!block.impl&%1.is_sentinel.)
  (forall ((self! Poly)) (!
    (= (lib!block.impl&%1.is_sentinel.? self!) (not (= (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size
           (%Poly%lib!block.BlockHdr. self!)
          )
         ) (I lib!parameters.SIZE_SENTINEL.?)
        )
       ) 0
    )))
    :pattern ((lib!block.impl&%1.is_sentinel.? self!))
    :qid internal_lib!block.impl&__1.is_sentinel.?_definition
    :skolemid skolem_internal_lib!block.impl&__1.is_sentinel.?_definition
))))

;; Function-Axioms lib::all_blocks::AllBlocks::phys_next_of
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.phys_next_of.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.phys_next_of.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
   (!
    (= (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!)
     (ite
      (= (Sub (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
         )
        ) 1
       ) (%I i!)
      )
      core!option.Option./None
      (core!option.Option./Some (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
          (%Poly%lib!all_blocks.AllBlocks. self!)
         )
        ) (I (Add (%I i!) 1))
    ))))
    :pattern ((lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      i!
    ))
    :qid internal_lib!all_blocks.impl&__0.phys_next_of.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.phys_next_of.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
  (!
   (=>
    (and
     (has_type self! (TYPE%lib!all_blocks.AllBlocks. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type i! INT)
    )
    (has_type (Poly%core!option.Option. (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN&
       SLLEN&. SLLEN& self! i!
      )
     ) (TYPE%core!option.Option. $ (PTR $ TYPE%lib!block.BlockHdr.))
   ))
   :pattern ((lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
   ))
   :qid internal_lib!all_blocks.impl&__0.phys_next_of.?_pre_post_definition
   :skolemid skolem_internal_lib!all_blocks.impl&__0.phys_next_of.?_pre_post_definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::wf_node_glue
(declare-fun req%lib!all_blocks.impl&%0.wf_node_glue. (Dcr Type Dcr Type Poly Poly)
 Bool
)
(declare-const %%global_location_label%%40 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
  (!
   (= (req%lib!all_blocks.impl&%0.wf_node_glue. FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!)
    (=>
     %%global_location_label%%40
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
        ))))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%lib!all_blocks.impl&%0.wf_node_glue. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.wf_node_glue._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.wf_node_glue._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::wf_node_structural
(declare-fun req%lib!all_blocks.impl&%0.wf_node_structural. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%41 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
  (!
   (= (req%lib!all_blocks.impl&%0.wf_node_structural. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
    ) (=>
     %%global_location_label%%41
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
        ))))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%lib!all_blocks.impl&%0.wf_node_structural. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.wf_node_structural._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.wf_node_structural._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::wf_node
(declare-fun req%lib!all_blocks.impl&%0.wf_node. (Dcr Type Dcr Type Poly Poly) Bool)
(declare-const %%global_location_label%%42 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
  (!
   (= (req%lib!all_blocks.impl&%0.wf_node. FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!) (=>
     %%global_location_label%%42
     (let
      ((tmp%%$ 0))
      (let
       ((tmp%%$1 (%I i!)))
       (let
        ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
        ))))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
   ))))))
   :pattern ((req%lib!all_blocks.impl&%0.wf_node. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.wf_node._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.wf_node._definition
)))

;; Function-Axioms lib::all_blocks::AllBlocks::wf_node
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.wf_node.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.wf_node.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (i! Poly))
   (!
    (= (lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!) (let
      ((ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
          (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
            (%Poly%lib!all_blocks.AllBlocks. self!)
           )
          ) i!
      ))))
      (and
       (and
        (and
         (and
          (and
           (lib!all_blocks.impl&%0.wf_node_ptr.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%ptr_mut%<lib!block.BlockHdr.>.
             ptr$
           ))
           (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
             $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
              (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. self!))
             )
            ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
          ))
          (= ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!raw_ptr.PointsToData./PointsToData/ptr
             (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                $ TYPE%lib!block.BlockHdr.
               ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                 (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                   $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                    (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. self!))
                   ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
         ))))))))))
         (lib!block.impl&%2.wf.? (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
            (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. self!))
           ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
        )))
        (lib!all_blocks.impl&%0.wf_node_glue.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!)
       )
       (lib!all_blocks.impl&%0.wf_node_structural.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!)
    )))
    :pattern ((lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! i!))
    :qid internal_lib!all_blocks.impl&__0.wf_node.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.wf_node.?_definition
))))

;; Function-Axioms lib::all_blocks::AllBlocks::wf
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.wf.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (and
      (and
       (lib!all_blocks.impl&%0.all_nodes_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
       (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
      )))
      (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    ))
    :pattern ((lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!all_blocks.impl&__0.wf.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.wf.?_definition
))))

;; Function-Axioms lib::Tlsf::free_next_of
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.free_next_of.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.free_next_of.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (ls! Poly) (i! Poly))
   (!
    (= (lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& ls! i!) (
      ite
      (= (%I i!) (Sub (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) ls!) 1))
      core!option.Option./None
      (core!option.Option./Some (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
        ls! (I (Add (%I i!) 1))
    ))))
    :pattern ((lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& ls!
      i!
    ))
    :qid internal_lib!linked_list.impl&__0.free_next_of.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.free_next_of.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (ls! Poly) (i! Poly))
  (!
   (=>
    (and
     (has_type ls! (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)))
     (has_type i! INT)
    )
    (has_type (Poly%core!option.Option. (lib!linked_list.impl&%0.free_next_of.? FLLEN&.
       FLLEN& SLLEN&. SLLEN& ls! i!
      )
     ) (TYPE%core!option.Option. $ (PTR $ TYPE%lib!block.BlockHdr.))
   ))
   :pattern ((lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& ls!
     i!
   ))
   :qid internal_lib!linked_list.impl&__0.free_next_of.?_pre_post_definition
   :skolemid skolem_internal_lib!linked_list.impl&__0.free_next_of.?_pre_post_definition
)))

;; Function-Axioms lib::Tlsf::free_prev_of
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.free_prev_of.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.free_prev_of.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (ls! Poly) (i! Poly))
   (!
    (= (lib!linked_list.impl&%0.free_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& ls! i!) (
      ite
      (= (%I i!) 0)
      core!option.Option./None
      (core!option.Option./Some (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
        ls! (I (Sub (%I i!) 1))
    ))))
    :pattern ((lib!linked_list.impl&%0.free_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& ls!
      i!
    ))
    :qid internal_lib!linked_list.impl&__0.free_prev_of.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.free_prev_of.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (ls! Poly) (i! Poly))
  (!
   (=>
    (and
     (has_type ls! (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)))
     (has_type i! INT)
    )
    (has_type (Poly%core!option.Option. (lib!linked_list.impl&%0.free_prev_of.? FLLEN&.
       FLLEN& SLLEN&. SLLEN& ls! i!
      )
     ) (TYPE%core!option.Option. $ (PTR $ TYPE%lib!block.BlockHdr.))
   ))
   :pattern ((lib!linked_list.impl&%0.free_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& ls!
     i!
   ))
   :qid internal_lib!linked_list.impl&__0.free_prev_of.?_pre_post_definition
   :skolemid skolem_internal_lib!linked_list.impl&__0.free_prev_of.?_pre_post_definition
)))

;; Function-Specs lib::Tlsf::wf_free_node
(declare-fun req%lib!linked_list.impl&%0.wf_free_node. (Dcr Type Dcr Type Poly Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%43 Bool)
(declare-const %%global_location_label%%44 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (idx!
    Poly
   ) (i! Poly)
  ) (!
   (= (req%lib!linked_list.impl&%0.wf_free_node. FLLEN&. FLLEN& SLLEN&. SLLEN& self! idx!
     i!
    ) (and
     (=>
      %%global_location_label%%43
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
     )))
     (=>
      %%global_location_label%%44
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 (%I i!)))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  self!
              ))))
             ) idx!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!linked_list.impl&%0.wf_free_node. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx! i!
   ))
   :qid internal_req__lib!linked_list.impl&__0.wf_free_node._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.wf_free_node._definition
)))

;; Function-Axioms lib::Tlsf::wf_free_node
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.wf_free_node.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.wf_free_node.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (idx!
     Poly
    ) (i! Poly)
   ) (!
    (= (lib!linked_list.impl&%0.wf_free_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! idx!
      i!
     ) (let
      ((freelist$ (%Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (vstd!map.impl&%0.index.?
          $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
           $ (PTR $ TYPE%lib!block.BlockHdr.)
          ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
            (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
               self!
           ))))
          ) idx!
      ))))
      (let
       ((node_link_ptr$ (lib!block.get_freelink_ptr_spec.? (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. freelist$) i!
       ))))
       (let
        ((node_link$ (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.FreeLink.
            (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
               (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                  $ TYPE%lib!block.FreeLink.
                 ) (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                  (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                     (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                       $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                        (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                           (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
                        )))
                       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                         freelist$
                        ) i!
        ))))))))))))))))
        (and
         (and
          (and
           (and
            (and
             (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
               (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                freelist$
               ) i!
             ))
             (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
                FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                  (%Poly%lib!Tlsf. self!)
                 )
                ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                  freelist$
                 ) i!
            )))))
            (=>
             (not (lib!all_blocks.impl&%0.ptr_is_null.? FLLEN&. FLLEN& SLLEN&. SLLEN& $ TYPE%lib!block.BlockHdr.
               (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free (%Poly%lib!block.FreeLink.
                  (Poly%lib!block.FreeLink. node_link$)
             )))))
             (= (core!option.Option./Some (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free
                 (%Poly%lib!block.FreeLink. (Poly%lib!block.FreeLink. node_link$))
               ))
              ) (lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                freelist$
               ) i!
           ))))
           (=>
            (lib!all_blocks.impl&%0.ptr_is_null.? FLLEN&. FLLEN& SLLEN&. SLLEN& $ TYPE%lib!block.BlockHdr.
             (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free (%Poly%lib!block.FreeLink.
                (Poly%lib!block.FreeLink. node_link$)
            ))))
            (is-core!option.Option./None (lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN&
              SLLEN&. SLLEN& (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. freelist$) i!
          ))))
          (=>
           (not (lib!all_blocks.impl&%0.ptr_is_null.? FLLEN&. FLLEN& SLLEN&. SLLEN& $ TYPE%lib!block.BlockHdr.
             (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/prev_free (%Poly%lib!block.FreeLink.
                (Poly%lib!block.FreeLink. node_link$)
           )))))
           (= (lib!linked_list.impl&%0.free_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
              freelist$
             ) i!
            ) (core!option.Option./Some (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/prev_free
               (%Poly%lib!block.FreeLink. (Poly%lib!block.FreeLink. node_link$))
         ))))))
         (=>
          (lib!all_blocks.impl&%0.ptr_is_null.? FLLEN&. FLLEN& SLLEN&. SLLEN& $ TYPE%lib!block.BlockHdr.
           (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/prev_free (%Poly%lib!block.FreeLink.
              (Poly%lib!block.FreeLink. node_link$)
          ))))
          (is-core!option.Option./None (lib!linked_list.impl&%0.free_prev_of.? FLLEN&. FLLEN&
            SLLEN&. SLLEN& (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. freelist$) i!
    ))))))))
    :pattern ((lib!linked_list.impl&%0.wf_free_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      idx! i!
    ))
    :qid internal_lib!linked_list.impl&__0.wf_free_node.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.wf_free_node.?_definition
))))

;; Function-Axioms lib::all_blocks::ShadowFreelist::contains
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%1.contains.)
)
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%1.contains.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (node!
     Poly
    )
   ) (!
    (= (lib!all_blocks.impl&%1.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! node!) (
      exists ((i$ Poly)) (!
       (and
        (has_type i$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (and
         (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& i$)
         (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
           $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
            $ (PTR $ TYPE%lib!block.BlockHdr.)
           ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
             self!
            )
           ) i$
          ) node!
       )))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& i$))
       :qid user_lib__all_blocks__ShadowFreelist__contains_98
       :skolemid skolem_user_lib__all_blocks__ShadowFreelist__contains_98
    )))
    :pattern ((lib!all_blocks.impl&%1.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! node!))
    :qid internal_lib!all_blocks.impl&__1.contains.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__1.contains.?_definition
))))

;; Function-Axioms lib::Tlsf::free_blocks_in_freelist_except
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.free_blocks_in_freelist_except.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (exceptions!
     Poly
    )
   ) (!
    (= (lib!linked_list.impl&%0.free_blocks_in_freelist_except.? FLLEN&. FLLEN& SLLEN&.
      SLLEN& self! exceptions!
     ) (forall ((i$ Poly)) (!
       (=>
        (has_type i$ INT)
        (=>
         (and
          (and
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I i$)))
             (let
              ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                  (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                     (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
              )))))))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
           ))))
           (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
              FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                (%Poly%lib!Tlsf. self!)
               )
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
                )))
               ) i$
          )))))
          (not (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) exceptions! (vstd!seq.Seq.index.?
             $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
              (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                 (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
              )))
             ) i$
         ))))
         (lib!all_blocks.impl&%1.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
           (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. self!))
          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
               (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
            )))
           ) i$
       ))))
       :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
          )))
         ) i$
       ))
       :qid user_lib__Tlsf__free_blocks_in_freelist_except_99
       :skolemid skolem_user_lib__Tlsf__free_blocks_in_freelist_except_99
    )))
    :pattern ((lib!linked_list.impl&%0.free_blocks_in_freelist_except.? FLLEN&. FLLEN&
      SLLEN&. SLLEN& self! exceptions!
    ))
    :qid internal_lib!linked_list.impl&__0.free_blocks_in_freelist_except.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.free_blocks_in_freelist_except.?_definition
))))

;; Function-Axioms lib::Tlsf::all_freelist_wf_weak
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.all_freelist_wf_weak.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.all_freelist_wf_weak.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (exceptions!
     Poly
    )
   ) (!
    (= (lib!linked_list.impl&%0.all_freelist_wf_weak.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      exceptions!
     ) (and
      (and
       (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
       (forall ((idx$ Poly)) (!
         (=>
          (has_type idx$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
          (=>
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$)
           (lib!linked_list.impl&%0.freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! idx$)
         ))
         :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$))
         :qid user_lib__Tlsf__all_freelist_wf_weak_100
         :skolemid skolem_user_lib__Tlsf__all_freelist_wf_weak_100
      )))
      (lib!linked_list.impl&%0.free_blocks_in_freelist_except.? FLLEN&. FLLEN& SLLEN&. SLLEN&
       self! exceptions!
    )))
    :pattern ((lib!linked_list.impl&%0.all_freelist_wf_weak.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self! exceptions!
    ))
    :qid internal_lib!linked_list.impl&__0.all_freelist_wf_weak.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.all_freelist_wf_weak.?_definition
))))

;; Function-Axioms lib::Tlsf::all_freelist_wf
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.all_freelist_wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.all_freelist_wf.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
     (lib!linked_list.impl&%0.all_freelist_wf_weak.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      (vstd!set.Set.empty.? $ (PTR $ TYPE%lib!block.BlockHdr.))
    ))
    :pattern ((lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self!
    ))
    :qid internal_lib!linked_list.impl&__0.all_freelist_wf.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.all_freelist_wf.?_definition
))))

;; Function-Specs lib::Tlsf::map_floor_spec
(declare-fun req%lib!mapping.impl&%0.map_floor_spec. (Dcr Type Dcr Type Poly) Bool)
(declare-const %%global_location_label%%45 Bool)
(declare-const %%global_location_label%%46 Bool)
(declare-const %%global_location_label%%47 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (size! Poly)) (!
   (= (req%lib!mapping.impl&%0.map_floor_spec. FLLEN&. FLLEN& SLLEN&. SLLEN& size!) (
     and
     (=>
      %%global_location_label%%45
      (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     )
     (=>
      %%global_location_label%%46
      (= (EucMod (%I size!) lib!parameters.GRANULARITY.?) 0)
     )
     (=>
      %%global_location_label%%47
      (>= (%I size!) lib!parameters.GRANULARITY.?)
   )))
   :pattern ((req%lib!mapping.impl&%0.map_floor_spec. FLLEN&. FLLEN& SLLEN&. SLLEN& size!))
   :qid internal_req__lib!mapping.impl&__0.map_floor_spec._definition
   :skolemid skolem_internal_req__lib!mapping.impl&__0.map_floor_spec._definition
)))

;; Function-Axioms lib::Tlsf::map_floor_spec
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (size! Poly)) (!
   (=>
    (has_type size! USIZE)
    (has_type (Poly%lib!block_index.BlockIndex. (lib!mapping.impl&%0.map_floor_spec.? FLLEN&.
       FLLEN& SLLEN&. SLLEN& size!
      )
     ) (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((lib!mapping.impl&%0.map_floor_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN& size!))
   :qid internal_lib!mapping.impl&__0.map_floor_spec.?_pre_post_definition
   :skolemid skolem_internal_lib!mapping.impl&__0.map_floor_spec.?_pre_post_definition
)))

;; Function-Axioms lib::Tlsf::shadow_freelist_popped_at
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.shadow_freelist_popped_at.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_sfl! Poly) (new_sfl!
     Poly
    ) (idx! Poly)
   ) (!
    (= (lib!linked_list.impl&%0.shadow_freelist_popped_at.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      old_sfl! new_sfl! idx!
     ) (and
      (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
         SLLEN&
        ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
         (%Poly%lib!all_blocks.ShadowFreelist. new_sfl!)
        ) idx!
       ) (vstd!seq_lib.impl&%0.remove.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           old_sfl!
          )
         ) idx!
        ) (I 0)
      ))
      (forall ((bi$ Poly)) (!
        (=>
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (not (= bi$ idx!))
          )
          (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
             SLLEN&
            ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
             (%Poly%lib!all_blocks.ShadowFreelist. new_sfl!)
            ) bi$
           ) (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
             SLLEN&
            ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
             (%Poly%lib!all_blocks.ShadowFreelist. old_sfl!)
            ) bi$
        ))))
        :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
        :qid user_lib__Tlsf__shadow_freelist_popped_at_101
        :skolemid skolem_user_lib__Tlsf__shadow_freelist_popped_at_101
    ))))
    :pattern ((lib!linked_list.impl&%0.shadow_freelist_popped_at.? FLLEN&. FLLEN& SLLEN&.
      SLLEN& old_sfl! new_sfl! idx!
    ))
    :qid internal_lib!linked_list.impl&__0.shadow_freelist_popped_at.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.shadow_freelist_popped_at.?_definition
))))

;; Function-Axioms lib::Tlsf::perms_size_unchanged_for_freelist
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_sfl! Poly) (old_blocks!
     Poly
    ) (new_blocks! Poly) (allocated_block! Poly)
   ) (!
    (= (lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.? FLLEN&. FLLEN& SLLEN&.
      SLLEN& old_sfl! old_blocks! new_blocks! allocated_block!
     ) (forall ((bi$ Poly) (i$ Poly)) (!
       (=>
        (and
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (has_type i$ INT)
        )
        (=>
         (and
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I i$)))
             (let
              ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                  $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                   $ (PTR $ TYPE%lib!block.BlockHdr.)
                  ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                    old_sfl!
                   )
                  ) bi$
              ))))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
          )))))
          (not (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                old_sfl!
               )
              ) bi$
             ) i$
            ) allocated_block!
         )))
         (= (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
             $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
               (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                 (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
                  (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                    (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                      $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                       (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. new_blocks!))
                      ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                        $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                         $ (PTR $ TYPE%lib!block.BlockHdr.)
                        ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                          old_sfl!
                         )
                        ) bi$
                       ) i$
           ))))))))))))
          ) (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
             $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
               (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                 (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
                  (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                    (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                      $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                       (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. old_blocks!))
                      ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                        $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                         $ (PTR $ TYPE%lib!block.BlockHdr.)
                        ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                          old_sfl!
                         )
                        ) bi$
                       ) i$
       ))))))))))))))))
       :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
          $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
           $ (PTR $ TYPE%lib!block.BlockHdr.)
          ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
            old_sfl!
           )
          ) bi$
         ) i$
       ))
       :qid user_lib__Tlsf__perms_size_unchanged_for_freelist_102
       :skolemid skolem_user_lib__Tlsf__perms_size_unchanged_for_freelist_102
    )))
    :pattern ((lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.? FLLEN&. FLLEN&
      SLLEN&. SLLEN& old_sfl! old_blocks! new_blocks! allocated_block!
    ))
    :qid internal_lib!linked_list.impl&__0.perms_size_unchanged_for_freelist.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.perms_size_unchanged_for_freelist.?_definition
))))

;; Function-Axioms lib::Tlsf::free_blocks_in_freelist
(assert
 (fuel_bool_default fuel%lib!linked_list.impl&%0.free_blocks_in_freelist.)
)
(assert
 (=>
  (fuel_bool fuel%lib!linked_list.impl&%0.free_blocks_in_freelist.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!linked_list.impl&%0.free_blocks_in_freelist.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self!
     ) (lib!linked_list.impl&%0.free_blocks_in_freelist_except.? FLLEN&. FLLEN& SLLEN&.
      SLLEN& self! (vstd!set.Set.empty.? $ (PTR $ TYPE%lib!block.BlockHdr.))
    ))
    :pattern ((lib!linked_list.impl&%0.free_blocks_in_freelist.? FLLEN&. FLLEN& SLLEN&.
      SLLEN& self!
    ))
    :qid internal_lib!linked_list.impl&__0.free_blocks_in_freelist.?_definition
    :skolemid skolem_internal_lib!linked_list.impl&__0.free_blocks_in_freelist.?_definition
))))

;; Function-Specs lib::all_blocks::AllBlocks::get_ptr_internal_index
(declare-fun req%lib!all_blocks.impl&%0.get_ptr_internal_index. (Dcr Type Dcr Type
  Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%48 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (x! Poly))
  (!
   (= (req%lib!all_blocks.impl&%0.get_ptr_internal_index. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! x!
    ) (=>
     %%global_location_label%%48
     (exists ((i$ Poly)) (!
       (and
        (has_type i$ INT)
        (and
         (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
           ) i$
          ) x!
         )
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$1 (%I i$)))
           (let
            ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
            ))))
            (and
             (<= tmp%%$ tmp%%$1)
             (< tmp%%$1 tmp%%$2)
       ))))))
       :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
         ) i$
       ))
       :qid user_lib__all_blocks__AllBlocks__get_ptr_internal_index_103
       :skolemid skolem_user_lib__all_blocks__AllBlocks__get_ptr_internal_index_103
   ))))
   :pattern ((req%lib!all_blocks.impl&%0.get_ptr_internal_index. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! x!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.get_ptr_internal_index._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.get_ptr_internal_index._definition
)))

;; Function-Axioms lib::all_blocks::AllBlocks::get_ptr_internal_index
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%0.get_ptr_internal_index.)
)
(declare-fun %%choose%%0 (Type Dcr Type Poly Poly Int Int Dcr Type Poly) Poly)
(assert
 (forall ((%%hole%%0 Type) (%%hole%%1 Dcr) (%%hole%%2 Type) (%%hole%%3 Poly) (%%hole%%4
    Poly
   ) (%%hole%%5 Int) (%%hole%%6 Int) (%%hole%%7 Dcr) (%%hole%%8 Type) (%%hole%%9 Poly)
  ) (!
   (=>
    (exists ((i$ Poly)) (!
      (and
       (has_type i$ %%hole%%0)
       (and
        (= (vstd!seq.Seq.index.? %%hole%%1 %%hole%%2 %%hole%%3 i$) %%hole%%4)
        (let
         ((tmp%%$ %%hole%%6))
         (let
          ((tmp%%$1 (%I i$)))
          (let
           ((tmp%%$2 %%hole%%5))
           (and
            (<= tmp%%$ tmp%%$1)
            (< tmp%%$1 tmp%%$2)
      ))))))
      :pattern ((vstd!seq.Seq.index.? %%hole%%7 %%hole%%8 %%hole%%9 i$))
      :qid user_lib__all_blocks__AllBlocks__get_ptr_internal_index_104
      :skolemid skolem_user_lib__all_blocks__AllBlocks__get_ptr_internal_index_104
    ))
    (exists ((i$ Poly)) (!
      (and
       (and
        (has_type i$ %%hole%%0)
        (and
         (= (vstd!seq.Seq.index.? %%hole%%1 %%hole%%2 %%hole%%3 i$) %%hole%%4)
         (let
          ((tmp%%$ %%hole%%6))
          (let
           ((tmp%%$1 (%I i$)))
           (let
            ((tmp%%$2 %%hole%%5))
            (and
             (<= tmp%%$ tmp%%$1)
             (< tmp%%$1 tmp%%$2)
       ))))))
       (= (%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5 %%hole%%6
         %%hole%%7 %%hole%%8 %%hole%%9
        ) i$
      ))
      :pattern ((vstd!seq.Seq.index.? %%hole%%7 %%hole%%8 %%hole%%9 i$))
   )))
   :pattern ((%%choose%%0 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
     %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9
)))))
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%0.get_ptr_internal_index.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (x! Poly))
   (!
    (= (lib!all_blocks.impl&%0.get_ptr_internal_index.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      x!
     ) (%I (as_type (%%choose%%0 INT $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
        ) x! (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
         )
        ) 0 $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. self!))
        )
       ) INT
    )))
    :pattern ((lib!all_blocks.impl&%0.get_ptr_internal_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self! x!
    ))
    :qid internal_lib!all_blocks.impl&__0.get_ptr_internal_index.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__0.get_ptr_internal_index.?_definition
))))

;; Function-Specs lib::all_blocks::ShadowFreelist::ii_remove_for_index
(declare-fun req%lib!all_blocks.impl&%1.ii_remove_for_index. (Dcr Type Dcr Type Poly
  Poly Poly Poly
 ) Bool
)
(declare-const %%global_location_label%%49 Bool)
(declare-const %%global_location_label%%50 Bool)
(declare-const %%global_location_label%%51 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (all_blocks!
    Poly
   ) (rm_bi! Poly) (rm_pos! Poly)
  ) (!
   (= (req%lib!all_blocks.impl&%1.ii_remove_for_index. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     all_blocks! rm_bi! rm_pos!
    ) (and
     (=>
      %%global_location_label%%49
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& rm_bi!)
     )
     (=>
      %%global_location_label%%50
      (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& self! (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. all_blocks!))
     )))
     (=>
      %%global_location_label%%51
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 (%I rm_pos!)))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               self!
              )
             ) rm_bi!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!all_blocks.impl&%1.ii_remove_for_index. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! all_blocks! rm_bi! rm_pos!
   ))
   :qid internal_req__lib!all_blocks.impl&__1.ii_remove_for_index._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__1.ii_remove_for_index._definition
)))

;; Function-Axioms lib::all_blocks::ShadowFreelist::ii_remove_for_index
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%1.ii_remove_for_index.)
)
(declare-fun %%lambda%%5 (Poly Int Poly Dcr Type Dcr Type Poly Int Int Int Poly Dcr
  Type Dcr Type Poly Poly
 ) %%Function%%
)
(assert
 (forall ((%%hole%%0 Poly) (%%hole%%1 Int) (%%hole%%2 Poly) (%%hole%%3 Dcr) (%%hole%%4
    Type
   ) (%%hole%%5 Dcr) (%%hole%%6 Type) (%%hole%%7 Poly) (%%hole%%8 Int) (%%hole%%9 Int)
   (%%hole%%10 Int) (%%hole%%11 Poly) (%%hole%%12 Dcr) (%%hole%%13 Type) (%%hole%%14
    Dcr
   ) (%%hole%%15 Type) (%%hole%%16 Poly) (%%hole%%17 Poly) (k$ Poly) (v$ Poly)
  ) (!
   (= (%%apply%%1 (%%lambda%%5 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4 %%hole%%5
      %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9 %%hole%%10 %%hole%%11 %%hole%%12 %%hole%%13
      %%hole%%14 %%hole%%15 %%hole%%16 %%hole%%17
     ) k$ v$
    ) (ite
     (= (tuple%2./tuple%2/0 (%Poly%tuple%2. k$)) %%hole%%0)
     (ite
      (< (%I (tuple%2./tuple%2/1 (%Poly%tuple%2. k$))) %%hole%%1)
      (vstd!map.impl&%0.index.? %%hole%%3 %%hole%%4 %%hole%%5 %%hole%%6 %%hole%%7 (Poly%tuple%2.
        (tuple%2./tuple%2 %%hole%%2 (tuple%2./tuple%2/1 (%Poly%tuple%2. k$)))
      ))
      (ite
       (let
        ((tmp%%$ %%hole%%9))
        (let
         ((tmp%%$1 (%I (tuple%2./tuple%2/1 (%Poly%tuple%2. k$)))))
         (let
          ((tmp%%$2 %%hole%%8))
          (and
           (<= tmp%%$ tmp%%$1)
           (< tmp%%$1 tmp%%$2)
       ))))
       (vstd!map.impl&%0.index.? %%hole%%12 %%hole%%13 %%hole%%14 %%hole%%15 %%hole%%16 (
         Poly%tuple%2. (tuple%2./tuple%2 %%hole%%11 (I (Add (%I (tuple%2./tuple%2/1 (%Poly%tuple%2.
               k$
             ))
            ) %%hole%%10
       )))))
       %%hole%%17
     ))
     v$
   ))
   :pattern ((%%apply%%1 (%%lambda%%5 %%hole%%0 %%hole%%1 %%hole%%2 %%hole%%3 %%hole%%4
      %%hole%%5 %%hole%%6 %%hole%%7 %%hole%%8 %%hole%%9 %%hole%%10 %%hole%%11 %%hole%%12
      %%hole%%13 %%hole%%14 %%hole%%15 %%hole%%16 %%hole%%17
     ) k$ v$
)))))
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%1.ii_remove_for_index.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (all_blocks!
     Poly
    ) (rm_bi! Poly) (rm_pos! Poly)
   ) (!
    (= (lib!all_blocks.impl&%1.ii_remove_for_index.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      all_blocks! rm_bi! rm_pos!
     ) (let
      ((new_m_idx$ (%Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (vstd!seq_lib.impl&%0.remove.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex.
            FLLEN&. FLLEN& SLLEN&. SLLEN&
           ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
            (%Poly%lib!all_blocks.ShadowFreelist. self!)
           ) rm_bi!
          ) rm_pos!
      ))))
      (let
       ((old_len$ (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
           $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
            $ (PTR $ TYPE%lib!block.BlockHdr.)
           ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
             self!
            )
           ) rm_bi!
       ))))
       (let
        ((last_key$ (tuple%2./tuple%2 rm_bi! (I (Sub old_len$ 1)))))
        (lib!all_blocks.ShadowFreelist./ShadowFreelist (vstd!map.impl&%0.insert.? $ (TYPE%lib!block_index.BlockIndex.
           FLLEN&. FLLEN& SLLEN&. SLLEN&
          ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
           (%Poly%lib!all_blocks.ShadowFreelist. self!)
          ) rm_bi! (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. new_m_idx$)
         ) (vstd!map.impl&%0.remove.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
            FLLEN&. FLLEN& SLLEN&. SLLEN&
           ) $ INT
          ) $ INT (vstd!map_lib.impl&%0.map_entries.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
             FLLEN&. FLLEN& SLLEN&. SLLEN&
            ) $ INT
           ) $ INT $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
             self!
            )
           ) (Poly%fun%2. (mk_fun (%%lambda%%5 rm_bi! (%I rm_pos!) rm_bi! (DST $) (TYPE%tuple%2.
               $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ INT
              ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
                self!
               )
              ) (Sub old_len$ 1) (%I rm_pos!) 1 rm_bi! (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
                FLLEN&. FLLEN& SLLEN&. SLLEN&
               ) $ INT
              ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
                self!
               )
              ) (vstd!pervasive.arbitrary.? $ INT)
           )))
          ) (Poly%tuple%2. last_key$)
    ))))))
    :pattern ((lib!all_blocks.impl&%1.ii_remove_for_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self! all_blocks! rm_bi! rm_pos!
    ))
    :qid internal_lib!all_blocks.impl&__1.ii_remove_for_index.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__1.ii_remove_for_index.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (all_blocks!
    Poly
   ) (rm_bi! Poly) (rm_pos! Poly)
  ) (!
   (=>
    (and
     (has_type self! (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type all_blocks! (TYPE%lib!all_blocks.AllBlocks. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type rm_bi! (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type rm_pos! INT)
    )
    (has_type (Poly%lib!all_blocks.ShadowFreelist. (lib!all_blocks.impl&%1.ii_remove_for_index.?
       FLLEN&. FLLEN& SLLEN&. SLLEN& self! all_blocks! rm_bi! rm_pos!
      )
     ) (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((lib!all_blocks.impl&%1.ii_remove_for_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! all_blocks! rm_bi! rm_pos!
   ))
   :qid internal_lib!all_blocks.impl&__1.ii_remove_for_index.?_pre_post_definition
   :skolemid skolem_internal_lib!all_blocks.impl&__1.ii_remove_for_index.?_pre_post_definition
)))

;; Function-Axioms lib::all_blocks::ShadowFreelist::ii_shift_after_insert
(assert
 (fuel_bool_default fuel%lib!all_blocks.impl&%1.ii_shift_after_insert.)
)
(declare-fun %%lambda%%6 (Int Int) %%Function%%)
(assert
 (forall ((%%hole%%0 Int) (%%hole%%1 Int) (ai$ Poly)) (!
   (= (%%apply%%0 (%%lambda%%6 %%hole%%0 %%hole%%1) ai$) (I (ite
      (<= %%hole%%0 (%I ai$))
      (Add (%I ai$) %%hole%%1)
      (%I ai$)
   )))
   :pattern ((%%apply%%0 (%%lambda%%6 %%hole%%0 %%hole%%1) ai$))
)))
(assert
 (=>
  (fuel_bool fuel%lib!all_blocks.impl&%1.ii_shift_after_insert.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (insert_ai!
     Poly
    )
   ) (!
    (= (lib!all_blocks.impl&%1.ii_shift_after_insert.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!
      insert_ai!
     ) (lib!all_blocks.ShadowFreelist./ShadowFreelist (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
       (%Poly%lib!all_blocks.ShadowFreelist. self!)
      ) (vstd!map_lib.impl&%0.map_values.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
         FLLEN&. FLLEN& SLLEN&. SLLEN&
        ) $ INT
       ) $ INT $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
         self!
        )
       ) (Poly%fun%1. (mk_fun (%%lambda%%6 (Add (%I insert_ai!) 1) 1)))
    )))
    :pattern ((lib!all_blocks.impl&%1.ii_shift_after_insert.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      self! insert_ai!
    ))
    :qid internal_lib!all_blocks.impl&__1.ii_shift_after_insert.?_definition
    :skolemid skolem_internal_lib!all_blocks.impl&__1.ii_shift_after_insert.?_definition
))))
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly) (insert_ai!
    Poly
   )
  ) (!
   (=>
    (and
     (has_type self! (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (has_type insert_ai! INT)
    )
    (has_type (Poly%lib!all_blocks.ShadowFreelist. (lib!all_blocks.impl&%1.ii_shift_after_insert.?
       FLLEN&. FLLEN& SLLEN&. SLLEN& self! insert_ai!
      )
     ) (TYPE%lib!all_blocks.ShadowFreelist. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((lib!all_blocks.impl&%1.ii_shift_after_insert.? FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! insert_ai!
   ))
   :qid internal_lib!all_blocks.impl&__1.ii_shift_after_insert.?_pre_post_definition
   :skolemid skolem_internal_lib!all_blocks.impl&__1.ii_shift_after_insert.?_pre_post_definition
)))

;; Function-Specs lib::Tlsf::bitmap_wf
(declare-fun req%lib!bitmap.impl&%0.bitmap_wf. (Dcr Type Dcr Type Poly) Bool)
(declare-const %%global_location_label%%52 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
   (= (req%lib!bitmap.impl&%0.bitmap_wf. FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (=>
     %%global_location_label%%52
     (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((req%lib!bitmap.impl&%0.bitmap_wf. FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
   :qid internal_req__lib!bitmap.impl&__0.bitmap_wf._definition
   :skolemid skolem_internal_req__lib!bitmap.impl&__0.bitmap_wf._definition
)))

;; Function-Axioms lib::Tlsf::bitmap_wf
(assert
 (fuel_bool_default fuel%lib!bitmap.impl&%0.bitmap_wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!bitmap.impl&%0.bitmap_wf.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (and
      (and
       (forall ((idx$ Poly)) (!
         (=>
          (has_type idx$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
          (=>
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$)
           (= (= (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.? $ (ARRAY $ USIZE FLLEN&.
                 FLLEN&
                ) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. self!)))
               ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. idx$)))
              )
             ) 0
            ) (not (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf.
                      self!
                    ))
                   ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. idx$)))
               ))))
              ) 1
         )))))
         :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$))
         :qid user_lib__Tlsf__bitmap_wf_105
         :skolemid skolem_user_lib__Tlsf__bitmap_wf_105
       ))
       (forall ((f$ Poly)) (!
         (=>
          (has_type f$ USIZE)
          (=>
           (>= (%I f$) (const_int FLLEN&))
           (not (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf.
                     self!
                   ))
                  ) (I (%I f$))
              ))))
             ) 1
         ))))
         :pattern ((uClip SZ (bitshr (I (lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf. self!))) (
             I (%I f$)
         ))))
         :qid user_lib__Tlsf__bitmap_wf_106
         :skolemid skolem_user_lib__Tlsf__bitmap_wf_106
      )))
      (forall ((f$ Poly) (s$ Poly)) (!
        (=>
         (and
          (has_type f$ USIZE)
          (has_type s$ USIZE)
         )
         (=>
          (and
           (< (%I f$) (const_int FLLEN&))
           (>= (%I s$) (const_int SLLEN&))
          )
          (not (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (
                     vstd!view.View.view.? $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap
                       (%Poly%lib!Tlsf. self!)
                     ))
                    ) f$
                  ))
                 ) (I (%I s$))
             ))))
            ) 1
        ))))
        :pattern ((uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.?
               $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf.
                  self!
               )))
              ) f$
            ))
           ) (I (%I s$))
        )))
        :qid user_lib__Tlsf__bitmap_wf_107
        :skolemid skolem_user_lib__Tlsf__bitmap_wf_107
    ))))
    :pattern ((lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!bitmap.impl&__0.bitmap_wf.?_definition
    :skolemid skolem_internal_lib!bitmap.impl&__0.bitmap_wf.?_definition
))))

;; Function-Specs lib::Tlsf::bitmap_sync
(declare-fun req%lib!bitmap.impl&%0.bitmap_sync. (Dcr Type Dcr Type Poly) Bool)
(declare-const %%global_location_label%%53 Bool)
(declare-const %%global_location_label%%54 Bool)
(declare-const %%global_location_label%%55 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
   (= (req%lib!bitmap.impl&%0.bitmap_sync. FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (and
     (=>
      %%global_location_label%%53
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
     )))
     (=>
      %%global_location_label%%54
      (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
     )
     (=>
      %%global_location_label%%55
      (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
   )))
   :pattern ((req%lib!bitmap.impl&%0.bitmap_sync. FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
   :qid internal_req__lib!bitmap.impl&__0.bitmap_sync._definition
   :skolemid skolem_internal_req__lib!bitmap.impl&__0.bitmap_sync._definition
)))

;; Function-Axioms lib::Tlsf::bitmap_sync
(assert
 (fuel_bool_default fuel%lib!bitmap.impl&%0.bitmap_sync.)
)
(assert
 (=>
  (fuel_bool fuel%lib!bitmap.impl&%0.bitmap_sync.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (forall (
       (idx$ Poly)
      ) (!
       (=>
        (has_type idx$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (=>
         (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$)
         (= (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.?
                    $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf.
                       self!
                    )))
                   ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. idx$)))
                 ))
                ) (I (uClip SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
                    idx$
            ))))))))
           ) 1
          ) (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  self!
              ))))
             ) idx$
            )
           ) 0
       ))))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& idx$))
       :qid user_lib__Tlsf__bitmap_sync_108
       :skolemid skolem_user_lib__Tlsf__bitmap_sync_108
    )))
    :pattern ((lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!bitmap.impl&__0.bitmap_sync.?_definition
    :skolemid skolem_internal_lib!bitmap.impl&__0.bitmap_sync.?_definition
))))

;; Function-Specs lib::ordered_pointer_list::add_ghost_pointer
(declare-fun req%lib!ordered_pointer_list.add_ghost_pointer. (Poly Poly) Bool)
(declare-const %%global_location_label%%56 Bool)
(assert
 (forall ((ls! Poly) (p! Poly)) (!
   (= (req%lib!ordered_pointer_list.add_ghost_pointer. ls! p!) (=>
     %%global_location_label%%56
     (lib!ordered_pointer_list.ghost_pointer_ordered.? ls!)
   ))
   :pattern ((req%lib!ordered_pointer_list.add_ghost_pointer. ls! p!))
   :qid internal_req__lib!ordered_pointer_list.add_ghost_pointer._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.add_ghost_pointer._definition
)))

;; Function-Specs lib::Tlsf::max_block_size
(declare-fun req%lib!parameters.impl&%0.max_block_size. (Dcr Type Dcr Type) Bool)
(declare-const %%global_location_label%%57 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
   (= (req%lib!parameters.impl&%0.max_block_size. FLLEN&. FLLEN& SLLEN&. SLLEN&) (=>
     %%global_location_label%%57
     (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((req%lib!parameters.impl&%0.max_block_size. FLLEN&. FLLEN& SLLEN&. SLLEN&))
   :qid internal_req__lib!parameters.impl&__0.max_block_size._definition
   :skolemid skolem_internal_req__lib!parameters.impl&__0.max_block_size._definition
)))

;; Function-Axioms lib::Tlsf::max_block_size
(assert
 (fuel_bool_default fuel%lib!parameters.impl&%0.max_block_size.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.impl&%0.max_block_size.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
    (= (lib!parameters.impl&%0.max_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN&) (let
      ((flb$ (vstd!arithmetic.power2.pow2.? (I (nClip (Sub (Add (lib!parameters.impl&%0.granularity_log2_spec.?
              FLLEN&. FLLEN& SLLEN&. SLLEN&
             ) (const_int FLLEN&)
            ) 1
      ))))))
      (Add flb$ (Mul (Sub (const_int SLLEN&) 1) (EucDiv flb$ (const_int SLLEN&))))
    ))
    :pattern ((lib!parameters.impl&%0.max_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN&))
    :qid internal_lib!parameters.impl&__0.max_block_size.?_definition
    :skolemid skolem_internal_lib!parameters.impl&__0.max_block_size.?_definition
))))

;; Function-Specs lib::Tlsf::max_allocatable_size
(declare-fun req%lib!parameters.impl&%0.max_allocatable_size. (Dcr Type Dcr Type Poly
  Poly
 ) Bool
)
(declare-const %%global_location_label%%58 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (size! Poly) (align!
    Poly
   )
  ) (!
   (= (req%lib!parameters.impl&%0.max_allocatable_size. FLLEN&. FLLEN& SLLEN&. SLLEN&
     size! align!
    ) (=>
     %%global_location_label%%58
     (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((req%lib!parameters.impl&%0.max_allocatable_size. FLLEN&. FLLEN& SLLEN&.
     SLLEN& size! align!
   ))
   :qid internal_req__lib!parameters.impl&__0.max_allocatable_size._definition
   :skolemid skolem_internal_req__lib!parameters.impl&__0.max_allocatable_size._definition
)))

;; Function-Axioms lib::Tlsf::max_allocatable_size
(assert
 (fuel_bool_default fuel%lib!parameters.impl&%0.max_allocatable_size.)
)
(assert
 (=>
  (fuel_bool fuel%lib!parameters.impl&%0.max_allocatable_size.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (size! Poly) (align!
     Poly
    )
   ) (!
    (= (lib!parameters.impl&%0.max_allocatable_size.? FLLEN&. FLLEN& SLLEN&. SLLEN& size!
      align!
     ) (<= (Add (Add (Add (%I size!) (ite
          (>= (%I align!) (EucDiv lib!parameters.GRANULARITY.? 2))
          (Sub (%I align!) (EucDiv lib!parameters.GRANULARITY.? 2))
          0
         )
        ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
       ) (Sub lib!parameters.GRANULARITY.? 1)
      ) (lib!parameters.impl&%0.max_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
    ))
    :pattern ((lib!parameters.impl&%0.max_allocatable_size.? FLLEN&. FLLEN& SLLEN&. SLLEN&
      size! align!
    ))
    :qid internal_lib!parameters.impl&__0.max_allocatable_size.?_definition
    :skolemid skolem_internal_lib!parameters.impl&__0.max_allocatable_size.?_definition
))))

;; Function-Axioms lib::Tlsf::wf
(assert
 (fuel_bool_default fuel%lib!impl&%0.wf.)
)
(assert
 (=>
  (fuel_bool fuel%lib!impl&%0.wf.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (and
      (and
       (and
        (and
         (and
          (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
            (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. self!))
          ))
          (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
         )
         (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
        )
        (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
       )
       (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
      )
      (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    ))
    :pattern ((lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!impl&__0.wf.?_definition
    :skolemid skolem_internal_lib!impl&__0.wf.?_definition
))))

;; Function-Axioms lib::Tlsf::is_ii
(assert
 (fuel_bool_default fuel%lib!impl&%0.is_ii.)
)
(assert
 (=>
  (fuel_bool fuel%lib!impl&%0.is_ii.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! Poly)) (!
    (= (lib!impl&%0.is_ii.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!) (lib!all_blocks.is_identity_injection.?
      FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
        (%Poly%lib!Tlsf. self!)
       )
      ) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
        (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
           (%Poly%lib!Tlsf. self!)
    )))))))
    :pattern ((lib!impl&%0.is_ii.? FLLEN&. FLLEN& SLLEN&. SLLEN& self!))
    :qid internal_lib!impl&__0.is_ii.?_definition
    :skolemid skolem_internal_lib!impl&__0.is_ii.?_definition
))))

;; Function-Axioms lib::Tlsf::is_root_provenance
(assert
 (fuel_bool_default fuel%lib!impl&%0.is_root_provenance.)
)
(assert
 (=>
  (fuel_bool fuel%lib!impl&%0.is_root_provenance.)
  (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (T&. Dcr) (T& Type)
    (self! Poly) (ptr! Poly)
   ) (!
    (= (lib!impl&%0.is_root_provenance.? FLLEN&. FLLEN& SLLEN&. SLLEN& T&. T& self! ptr!)
     (let
      ((pv$ (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR T&. T&) ptr!
      )))))
      (let
       ((tmp%%$ (lib!Tlsf./Tlsf/root_provenances (%Poly%lib!Tlsf. self!))))
       (and
        (is-core!option.Option./Some tmp%%$)
        (let
         ((ex$ (%Poly%vstd!raw_ptr.IsExposed. (core!option.Option./Some/0 $ TYPE%vstd!raw_ptr.IsExposed.
             (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
         ))))
         (= (vstd!raw_ptr.impl&%9.provenance.? (Poly%vstd!raw_ptr.IsExposed. ex$)) pv$)
    )))))
    :pattern ((lib!impl&%0.is_root_provenance.? FLLEN&. FLLEN& SLLEN&. SLLEN& T&. T& self!
      ptr!
    ))
    :qid internal_lib!impl&__0.is_root_provenance.?_definition
    :skolemid skolem_internal_lib!impl&__0.is_root_provenance.?_definition
))))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (REF A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (REF A&.) A&))
   :qid internal_vstd__view__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%vstd!view.View. A&. A&)
    (tr_bound%vstd!view.View. (BOX $ TYPE%alloc!alloc.Global. A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (BOX $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_vstd__view__impl&__2_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%vstd!view.View. A&. A&)
    )
    (tr_bound%vstd!view.View. (RC $ TYPE%alloc!alloc.Global. A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (RC $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_vstd__view__impl&__4_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__4_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%vstd!view.View. A&. A&)
    )
    (tr_bound%vstd!view.View. (ARC $ TYPE%alloc!alloc.Global. A&.) A&)
   )
   :pattern ((tr_bound%vstd!view.View. (ARC $ TYPE%alloc!alloc.Global. A&.) A&))
   :qid internal_vstd__view__impl&__6_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__6_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (sized T&.)
    (tr_bound%vstd!view.View. $ (TYPE%core!option.Option. T&. T&))
   )
   :pattern ((tr_bound%vstd!view.View. $ (TYPE%core!option.Option. T&. T&)))
   :qid internal_vstd__view__impl&__14_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__14_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ TYPE%tuple%0.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 16))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 32))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (UINT 128))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ USIZE)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (SINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (SINT 16))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (SINT 32))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (SINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ (SINT 128))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ ISIZE)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!view.View. $ CHAR)
)

;; Trait-Impl-Axiom
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type)) (!
   (=>
    (and
     (sized A0&.)
     (sized A1&.)
     (tr_bound%vstd!view.View. A0&. A0&)
     (tr_bound%vstd!view.View. A1&. A1&)
    )
    (tr_bound%vstd!view.View. (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&))
   )
   :pattern ((tr_bound%vstd!view.View. (DST A1&.) (TYPE%tuple%2. A0&. A0& A1&. A1&)))
   :qid internal_vstd__view__impl&__48_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__48_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A0&. Dcr) (A0& Type) (A1&. Dcr) (A1& Type) (A2&. Dcr) (A2& Type)) (!
   (=>
    (and
     (sized A0&.)
     (sized A1&.)
     (sized A2&.)
     (tr_bound%vstd!view.View. A0&. A0&)
     (tr_bound%vstd!view.View. A1&. A1&)
     (tr_bound%vstd!view.View. A2&. A2&)
    )
    (tr_bound%vstd!view.View. (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&. A2&))
   )
   :pattern ((tr_bound%vstd!view.View. (DST A2&.) (TYPE%tuple%3. A0&. A0& A1&. A1& A2&.
      A2&
   )))
   :qid internal_vstd__view__impl&__50_trait_impl_definition
   :skolemid skolem_internal_vstd__view__impl&__50_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ BOOL $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ BOOL $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (UINT 8) $ (UINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (UINT 8) $ (UINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (SINT 8) $ (SINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (SINT 8) $ (SINT 8))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (UINT 16) $ (UINT 16))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (UINT 16) $ (UINT 16))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (SINT 16) $ (SINT 16))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (SINT 16) $ (SINT 16))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (UINT 32) $ (UINT 32))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (UINT 32) $ (UINT 32))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (SINT 32) $ (SINT 32))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (SINT 32) $ (SINT 32))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (UINT 64) $ (UINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (UINT 64) $ (UINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (SINT 64) $ (SINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (SINT 64) $ (SINT 64))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (UINT 128) $ (UINT 128))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (UINT 128) $ (UINT 128))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ (SINT 128) $ (SINT 128))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (SINT 128) $ (SINT 128))
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ USIZE $ USIZE)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ USIZE $ USIZE)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ ISIZE $ ISIZE)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ ISIZE $ ISIZE)
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (and
     (sized T&.)
     (tr_bound%core!cmp.PartialEq. T&. T& T&. T&)
    )
    (tr_bound%core!cmp.PartialEq. $ (TYPE%core!option.Option. T&. T&) $ (TYPE%core!option.Option.
      T&. T&
   )))
   :pattern ((tr_bound%core!cmp.PartialEq. $ (TYPE%core!option.Option. T&. T&) $ (TYPE%core!option.Option.
      T&. T&
   )))
   :qid internal_core__option__impl&__16_trait_impl_definition
   :skolemid skolem_internal_core__option__impl&__16_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (and
     (sized T&.)
     (tr_bound%vstd!std_specs.cmp.PartialEqSpec. T&. T& T&. T&)
    )
    (tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (TYPE%core!option.Option. T&. T&) $
     (TYPE%core!option.Option. T&. T&)
   ))
   :pattern ((tr_bound%vstd!std_specs.cmp.PartialEqSpec. $ (TYPE%core!option.Option. T&.
      T&
     ) $ (TYPE%core!option.Option. T&. T&)
   ))
   :qid internal_vstd__std_specs__option__impl&__1_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__option__impl&__1_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type) (B&. Dcr) (B& Type)) (!
   (=>
    (tr_bound%core!cmp.PartialEq. A&. A& B&. B&)
    (tr_bound%core!cmp.PartialEq. (REF A&.) A& (REF B&.) B&)
   )
   :pattern ((tr_bound%core!cmp.PartialEq. (REF A&.) A& (REF B&.) B&))
   :qid internal_core__cmp__impls__impl&__9_trait_impl_definition
   :skolemid skolem_internal_core__cmp__impls__impl&__9_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized U&.)
     (uInv SZ (const_int N&))
     (tr_bound%core!cmp.PartialEq. T&. T& U&. U&)
    )
    (tr_bound%core!cmp.PartialEq. (REF $slice) (SLICE T&. T&) $ (ARRAY U&. U& N&. N&))
   )
   :pattern ((tr_bound%core!cmp.PartialEq. (REF $slice) (SLICE T&. T&) $ (ARRAY U&. U&
      N&. N&
   )))
   :qid internal_core__array__equality__impl&__4_trait_impl_definition
   :skolemid skolem_internal_core__array__equality__impl&__4_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%core!cmp.PartialEq. (CONST_PTR $) (PTR T&. T&) (CONST_PTR $) (PTR T&. T&))
   :pattern ((tr_bound%core!cmp.PartialEq. (CONST_PTR $) (PTR T&. T&) (CONST_PTR $) (PTR
      T&. T&
   )))
   :qid internal_core__ptr__const_ptr__impl&__7_trait_impl_definition
   :skolemid skolem_internal_core__ptr__const_ptr__impl&__7_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%core!cmp.PartialEq. $ (PTR T&. T&) $ (PTR T&. T&))
   :pattern ((tr_bound%core!cmp.PartialEq. $ (PTR T&. T&) $ (PTR T&. T&)))
   :qid internal_core__ptr__mut_ptr__impl&__7_trait_impl_definition
   :skolemid skolem_internal_core__ptr__mut_ptr__impl&__7_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ TYPE%tuple%0. $ TYPE%tuple%0.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ CHAR $ CHAR)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ TYPE%core!convert.Infallible. $ TYPE%core!convert.Infallible.)
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (tr_bound%core!cmp.PartialEq. $ (TYPE%core!marker.PhantomData. T&. T&) $ (TYPE%core!marker.PhantomData.
     T&. T&
   ))
   :pattern ((tr_bound%core!cmp.PartialEq. $ (TYPE%core!marker.PhantomData. T&. T&) $
     (TYPE%core!marker.PhantomData. T&. T&)
   ))
   :qid internal_core__marker__impl&__8_trait_impl_definition
   :skolemid skolem_internal_core__marker__impl&__8_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((B&. Dcr) (B& Type) (C&. Dcr) (C& Type)) (!
   (=>
    (and
     (sized B&.)
     (sized C&.)
     (tr_bound%core!cmp.PartialEq. B&. B& B&. B&)
     (tr_bound%core!cmp.PartialEq. C&. C& C&. C&)
    )
    (tr_bound%core!cmp.PartialEq. $ (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&.
      C&
     ) $ (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)
   ))
   :pattern ((tr_bound%core!cmp.PartialEq. $ (TYPE%core!ops.control_flow.ControlFlow. B&.
      B& C&. C&
     ) $ (TYPE%core!ops.control_flow.ControlFlow. B&. B& C&. C&)
   ))
   :qid internal_core__ops__control_flow__impl&__11_trait_impl_definition
   :skolemid skolem_internal_core__ops__control_flow__impl&__11_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized U&.)
     (uInv SZ (const_int N&))
     (tr_bound%core!cmp.PartialEq. T&. T& U&. U&)
    )
    (tr_bound%core!cmp.PartialEq. $ (ARRAY T&. T& N&. N&) $ (ARRAY U&. U& N&. N&))
   )
   :pattern ((tr_bound%core!cmp.PartialEq. $ (ARRAY T&. T& N&. N&) $ (ARRAY U&. U& N&.
      N&
   )))
   :qid internal_core__array__equality__impl&__0_trait_impl_definition
   :skolemid skolem_internal_core__array__equality__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized U&.)
     (uInv SZ (const_int N&))
     (tr_bound%core!cmp.PartialEq. T&. T& U&. U&)
    )
    (tr_bound%core!cmp.PartialEq. $ (ARRAY T&. T& N&. N&) $slice (SLICE U&. U&))
   )
   :pattern ((tr_bound%core!cmp.PartialEq. $ (ARRAY T&. T& N&. N&) $slice (SLICE U&. U&)))
   :qid internal_core__array__equality__impl&__1_trait_impl_definition
   :skolemid skolem_internal_core__array__equality__impl&__1_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized U&.)
     (uInv SZ (const_int N&))
     (tr_bound%core!cmp.PartialEq. T&. T& U&. U&)
    )
    (tr_bound%core!cmp.PartialEq. $ (ARRAY T&. T& N&. N&) (REF $slice) (SLICE U&. U&))
   )
   :pattern ((tr_bound%core!cmp.PartialEq. $ (ARRAY T&. T& N&. N&) (REF $slice) (SLICE
      U&. U&
   )))
   :qid internal_core__array__equality__impl&__3_trait_impl_definition
   :skolemid skolem_internal_core__array__equality__impl&__3_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type) (N&. Dcr) (N& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized U&.)
     (uInv SZ (const_int N&))
     (tr_bound%core!cmp.PartialEq. T&. T& U&. U&)
    )
    (tr_bound%core!cmp.PartialEq. $slice (SLICE T&. T&) $ (ARRAY U&. U& N&. N&))
   )
   :pattern ((tr_bound%core!cmp.PartialEq. $slice (SLICE T&. T&) $ (ARRAY U&. U& N&. N&)))
   :qid internal_core__array__equality__impl&__2_trait_impl_definition
   :skolemid skolem_internal_core__array__equality__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (U&. Dcr) (U& Type)) (!
   (=>
    (and
     (sized T&.)
     (sized U&.)
     (tr_bound%core!cmp.PartialEq. T&. T& U&. U&)
    )
    (tr_bound%core!cmp.PartialEq. $slice (SLICE T&. T&) $slice (SLICE U&. U&))
   )
   :pattern ((tr_bound%core!cmp.PartialEq. $slice (SLICE T&. T&) $slice (SLICE U&. U&)))
   :qid internal_core__slice__cmp__impl&__0_trait_impl_definition
   :skolemid skolem_internal_core__slice__cmp__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((U&. Dcr) (U& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (sized U&.)
     (sized T&.)
     (tr_bound%core!cmp.PartialEq. U&. U& U&. U&)
     (tr_bound%core!cmp.PartialEq. T&. T& T&. T&)
    )
    (tr_bound%core!cmp.PartialEq. (DST T&.) (TYPE%tuple%2. U&. U& T&. T&) (DST T&.) (TYPE%tuple%2.
      U&. U& T&. T&
   )))
   :pattern ((tr_bound%core!cmp.PartialEq. (DST T&.) (TYPE%tuple%2. U&. U& T&. T&) (DST
      T&.
     ) (TYPE%tuple%2. U&. U& T&. T&)
   ))
   :qid internal_core__tuple__impl&__10_trait_impl_definition
   :skolemid skolem_internal_core__tuple__impl&__10_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((V&. Dcr) (V& Type) (U&. Dcr) (U& Type) (T&. Dcr) (T& Type)) (!
   (=>
    (and
     (sized V&.)
     (sized U&.)
     (sized T&.)
     (tr_bound%core!cmp.PartialEq. V&. V& V&. V&)
     (tr_bound%core!cmp.PartialEq. U&. U& U&. U&)
     (tr_bound%core!cmp.PartialEq. T&. T& T&. T&)
    )
    (tr_bound%core!cmp.PartialEq. (DST T&.) (TYPE%tuple%3. V&. V& U&. U& T&. T&) (DST T&.)
     (TYPE%tuple%3. V&. V& U&. U& T&. T&)
   ))
   :pattern ((tr_bound%core!cmp.PartialEq. (DST T&.) (TYPE%tuple%3. V&. V& U&. U& T&. T&)
     (DST T&.) (TYPE%tuple%3. V&. V& U&. U& T&. T&)
   ))
   :qid internal_core__tuple__impl&__20_trait_impl_definition
   :skolemid skolem_internal_core__tuple__impl&__20_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%core!cmp.PartialEq. T&. T& T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
    )
    (tr_bound%core!cmp.PartialEq. (BOX A&. A& T&.) T& (BOX A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!cmp.PartialEq. (BOX A&. A& T&.) T& (BOX A&. A& T&.) T&))
   :qid internal_alloc__boxed__impl&__18_trait_impl_definition
   :skolemid skolem_internal_alloc__boxed__impl&__18_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%core!cmp.PartialEq. T&. T& T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
    )
    (tr_bound%core!cmp.PartialEq. (RC A&. A& T&.) T& (RC A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!cmp.PartialEq. (RC A&. A& T&.) T& (RC A&. A& T&.) T&))
   :qid internal_alloc__rc__impl&__45_trait_impl_definition
   :skolemid skolem_internal_alloc__rc__impl&__45_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%core!cmp.PartialEq. T&. T& T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
    )
    (tr_bound%core!cmp.PartialEq. (ARC A&. A& T&.) T& (ARC A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!cmp.PartialEq. (ARC A&. A& T&.) T& (ARC A&. A& T&.) T&))
   :qid internal_alloc__sync__impl&__55_trait_impl_definition
   :skolemid skolem_internal_alloc__sync__impl&__55_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ INT $ INT)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!cmp.PartialEq. $ NAT $ NAT)
)

;; Trait-Impl-Axiom
(assert
 (forall ((A&. Dcr) (A& Type)) (!
   (=>
    (tr_bound%core!alloc.Allocator. A&. A&)
    (tr_bound%core!alloc.Allocator. (REF A&.) A&)
   )
   :pattern ((tr_bound%core!alloc.Allocator. (REF A&.) A&))
   :qid internal_core__alloc__impl&__2_trait_impl_definition
   :skolemid skolem_internal_core__alloc__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!alloc.Allocator. $ TYPE%alloc!alloc.Global.)
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%core!alloc.Allocator. T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
    )
    (tr_bound%core!alloc.Allocator. (BOX A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!alloc.Allocator. (BOX A&. A& T&.) T&))
   :qid internal_alloc__boxed__impl&__49_trait_impl_definition
   :skolemid skolem_internal_alloc__boxed__impl&__49_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%core!alloc.Allocator. T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
    )
    (tr_bound%core!alloc.Allocator. (RC A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!alloc.Allocator. (RC A&. A& T&.) T&))
   :qid internal_alloc__rc__impl&__115_trait_impl_definition
   :skolemid skolem_internal_alloc__rc__impl&__115_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (A&. Dcr) (A& Type)) (!
   (=>
    (and
     (sized A&.)
     (tr_bound%core!alloc.Allocator. T&. T&)
     (tr_bound%core!alloc.Allocator. A&. A&)
    )
    (tr_bound%core!alloc.Allocator. (ARC A&. A& T&.) T&)
   )
   :pattern ((tr_bound%core!alloc.Allocator. (ARC A&. A& T&.) T&))
   :qid internal_alloc__sync__impl&__117_trait_impl_definition
   :skolemid skolem_internal_alloc__sync__impl&__117_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type)) (!
   (=>
    (and
     (uInv SZ (const_int FLLEN&))
     (uInv SZ (const_int SLLEN&))
    )
    (tr_bound%core!cmp.PartialEq. $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
      SLLEN&
     ) $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :pattern ((tr_bound%core!cmp.PartialEq. $ (TYPE%lib!block_index.BlockIndex. FLLEN&.
      FLLEN& SLLEN&. SLLEN&
     ) $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&)
   ))
   :qid internal_lib__block_index__impl&__2_trait_impl_definition
   :skolemid skolem_internal_lib__block_index__impl&__2_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((Rhs&. Dcr) (Rhs& Type) (VERUS_SPEC__A&. Dcr) (VERUS_SPEC__A& Type)) (!
   (=>
    (tr_bound%core!cmp.PartialEq. VERUS_SPEC__A&. VERUS_SPEC__A& Rhs&. Rhs&)
    (tr_bound%vstd!std_specs.cmp.PartialEqSpec. VERUS_SPEC__A&. VERUS_SPEC__A& Rhs&. Rhs&)
   )
   :pattern ((tr_bound%vstd!std_specs.cmp.PartialEqSpec. VERUS_SPEC__A&. VERUS_SPEC__A&
     Rhs&. Rhs&
   ))
   :qid internal_vstd__std_specs__cmp__impl&__3_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__cmp__impl&__3_trait_impl_definition
)))

;; Function-Specs lib::bits::lemma_pow2_value_in_usize
(declare-fun req%lib!bits.lemma_pow2_value_in_usize. (Int) Bool)
(declare-const %%global_location_label%%59 Bool)
(declare-const %%global_location_label%%60 Bool)
(assert
 (forall ((x! Int)) (!
   (= (req%lib!bits.lemma_pow2_value_in_usize. x!) (and
     (=>
      %%global_location_label%%59
      (lib!bits.is_power_of_two.? (I x!))
     )
     (=>
      %%global_location_label%%60
      (<= x! (- (uHi SZ) 1))
   )))
   :pattern ((req%lib!bits.lemma_pow2_value_in_usize. x!))
   :qid internal_req__lib!bits.lemma_pow2_value_in_usize._definition
   :skolemid skolem_internal_req__lib!bits.lemma_pow2_value_in_usize._definition
)))
(declare-fun ens%lib!bits.lemma_pow2_value_in_usize. (Int) Bool)
(assert
 (forall ((x! Int)) (!
   (= (ens%lib!bits.lemma_pow2_value_in_usize. x!) (or
     (or
      (or
       (or
        (or
         (or
          (or
           (or
            (or
             (or
              (or
               (or
                (or
                 (or
                  (or
                   (or
                    (or
                     (or
                      (or
                       (or
                        (or
                         (or
                          (or
                           (or
                            (or
                             (or
                              (or
                               (or
                                (or
                                 (or
                                  (or
                                   (or
                                    (or
                                     (or
                                      (or
                                       (or
                                        (or
                                         (or
                                          (or
                                           (or
                                            (or
                                             (or
                                              (or
                                               (or
                                                (or
                                                 (or
                                                  (or
                                                   (or
                                                    (or
                                                     (or
                                                      (or
                                                       (or
                                                        (or
                                                         (or
                                                          (or
                                                           (or
                                                            (or
                                                             (or
                                                              (or
                                                               (or
                                                                (or
                                                                 (or
                                                                  (or
                                                                   (= x! 1)
                                                                   (= x! 2)
                                                                  )
                                                                  (= x! 4)
                                                                 )
                                                                 (= x! 8)
                                                                )
                                                                (= x! 16)
                                                               )
                                                               (= x! 32)
                                                              )
                                                              (= x! 64)
                                                             )
                                                             (= x! 128)
                                                            )
                                                            (= x! 256)
                                                           )
                                                           (= x! 512)
                                                          )
                                                          (= x! 1024)
                                                         )
                                                         (= x! 2048)
                                                        )
                                                        (= x! 4096)
                                                       )
                                                       (= x! 8192)
                                                      )
                                                      (= x! 16384)
                                                     )
                                                     (= x! 32768)
                                                    )
                                                    (= x! 65536)
                                                   )
                                                   (= x! 131072)
                                                  )
                                                  (= x! 262144)
                                                 )
                                                 (= x! 524288)
                                                )
                                                (= x! 1048576)
                                               )
                                               (= x! 2097152)
                                              )
                                              (= x! 4194304)
                                             )
                                             (= x! 8388608)
                                            )
                                            (= x! 16777216)
                                           )
                                           (= x! 33554432)
                                          )
                                          (= x! 67108864)
                                         )
                                         (= x! 134217728)
                                        )
                                        (= x! 268435456)
                                       )
                                       (= x! 536870912)
                                      )
                                      (= x! 1073741824)
                                     )
                                     (= x! 2147483648)
                                    )
                                    (= x! 4294967296)
                                   )
                                   (= x! 8589934592)
                                  )
                                  (= x! 17179869184)
                                 )
                                 (= x! 34359738368)
                                )
                                (= x! 68719476736)
                               )
                               (= x! 137438953472)
                              )
                              (= x! 274877906944)
                             )
                             (= x! 549755813888)
                            )
                            (= x! 1099511627776)
                           )
                           (= x! 2199023255552)
                          )
                          (= x! 4398046511104)
                         )
                         (= x! 8796093022208)
                        )
                        (= x! 17592186044416)
                       )
                       (= x! 35184372088832)
                      )
                      (= x! 70368744177664)
                     )
                     (= x! 140737488355328)
                    )
                    (= x! 281474976710656)
                   )
                   (= x! 562949953421312)
                  )
                  (= x! 1125899906842624)
                 )
                 (= x! 2251799813685248)
                )
                (= x! 4503599627370496)
               )
               (= x! 9007199254740992)
              )
              (= x! 18014398509481984)
             )
             (= x! 36028797018963968)
            )
            (= x! 72057594037927936)
           )
           (= x! 144115188075855872)
          )
          (= x! 288230376151711744)
         )
         (= x! 576460752303423488)
        )
        (= x! 1152921504606846976)
       )
       (= x! 2305843009213693952)
      )
      (= x! 4611686018427387904)
     )
     (= x! 9223372036854775808)
   ))
   :pattern ((ens%lib!bits.lemma_pow2_value_in_usize. x!))
   :qid internal_ens__lib!bits.lemma_pow2_value_in_usize._definition
   :skolemid skolem_internal_ens__lib!bits.lemma_pow2_value_in_usize._definition
)))

;; Function-Specs lib::bits::lemma_round_down_pow2
(declare-fun req%lib!bits.lemma_round_down_pow2. (Int Int) Bool)
(declare-const %%global_location_label%%61 Bool)
(declare-const %%global_location_label%%62 Bool)
(assert
 (forall ((x! Int) (y! Int)) (!
   (= (req%lib!bits.lemma_round_down_pow2. x! y!) (and
     (=>
      %%global_location_label%%61
      (lib!bits.is_power_of_two.? (I y!))
     )
     (=>
      %%global_location_label%%62
      (> y! 1)
   )))
   :pattern ((req%lib!bits.lemma_round_down_pow2. x! y!))
   :qid internal_req__lib!bits.lemma_round_down_pow2._definition
   :skolemid skolem_internal_req__lib!bits.lemma_round_down_pow2._definition
)))
(declare-fun ens%lib!bits.lemma_round_down_pow2. (Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int)) (!
   (= (ens%lib!bits.lemma_round_down_pow2. x! y!) (and
     (<= (uClip SZ (bitand (I x!) (I (uClip SZ (bitnot (I (uClip SZ (Sub y! 1)))))))) x!)
     (= (EucMod (uClip SZ (bitand (I x!) (I (uClip SZ (bitnot (I (uClip SZ (Sub y! 1))))))))
       y!
      ) 0
   )))
   :pattern ((ens%lib!bits.lemma_round_down_pow2. x! y!))
   :qid internal_ens__lib!bits.lemma_round_down_pow2._definition
   :skolemid skolem_internal_ens__lib!bits.lemma_round_down_pow2._definition
)))

;; Function-Specs lib::bits::lemma_round_up_pow2
(declare-fun req%lib!bits.lemma_round_up_pow2. (Int Int) Bool)
(declare-const %%global_location_label%%63 Bool)
(declare-const %%global_location_label%%64 Bool)
(declare-const %%global_location_label%%65 Bool)
(assert
 (forall ((x! Int) (y! Int)) (!
   (= (req%lib!bits.lemma_round_up_pow2. x! y!) (and
     (=>
      %%global_location_label%%63
      (lib!bits.is_power_of_two.? (I y!))
     )
     (=>
      %%global_location_label%%64
      (> y! 1)
     )
     (=>
      %%global_location_label%%65
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 (Add x! (Sub y! 1))))
        (let
         ((tmp%%$2 (- (uHi SZ) 1)))
         (and
          (<= tmp%%$ tmp%%$1)
          (<= tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!bits.lemma_round_up_pow2. x! y!))
   :qid internal_req__lib!bits.lemma_round_up_pow2._definition
   :skolemid skolem_internal_req__lib!bits.lemma_round_up_pow2._definition
)))
(declare-fun ens%lib!bits.lemma_round_up_pow2. (Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int)) (!
   (= (ens%lib!bits.lemma_round_up_pow2. x! y!) (and
     (<= x! (uClip SZ (bitand (I (uClip SZ (Add x! (Sub y! 1)))) (I (uClip SZ (bitnot (I (uClip
             SZ (Sub y! 1)
     ))))))))
     (= (EucMod (uClip SZ (bitand (I (uClip SZ (Add x! (Sub y! 1)))) (I (uClip SZ (bitnot (I (
              uClip SZ (Sub y! 1)
        ))))))
       ) y!
      ) 0
   )))
   :pattern ((ens%lib!bits.lemma_round_up_pow2. x! y!))
   :qid internal_ens__lib!bits.lemma_round_up_pow2._definition
   :skolemid skolem_internal_ens__lib!bits.lemma_round_up_pow2._definition
)))

;; Function-Specs lib::bits::granularity_is_power_of_two
(declare-fun ens%lib!bits.granularity_is_power_of_two. (Int) Bool)
(assert
 (forall ((no%param Int)) (!
   (= (ens%lib!bits.granularity_is_power_of_two. no%param) (lib!bits.is_power_of_two.?
     (I (Mul (uClip SZ (vstd!layout.size_of.? $ USIZE)) 4))
   ))
   :pattern ((ens%lib!bits.granularity_is_power_of_two. no%param))
   :qid internal_ens__lib!bits.granularity_is_power_of_two._definition
   :skolemid skolem_internal_ens__lib!bits.granularity_is_power_of_two._definition
)))

;; Function-Specs lib::bits::lemma_mod_by_multiple
(declare-fun req%lib!bits.lemma_mod_by_multiple. (Int Int Int) Bool)
(declare-const %%global_location_label%%66 Bool)
(declare-const %%global_location_label%%67 Bool)
(declare-const %%global_location_label%%68 Bool)
(assert
 (forall ((x! Int) (y! Int) (z! Int)) (!
   (= (req%lib!bits.lemma_mod_by_multiple. x! y! z!) (and
     (=>
      %%global_location_label%%66
      (= (singular_mod x! (Mul y! z!)) 0)
     )
     (=>
      %%global_location_label%%67
      (not (= (Mul y! z!) 0))
     )
     (=>
      %%global_location_label%%68
      (not (= z! 0))
   )))
   :pattern ((req%lib!bits.lemma_mod_by_multiple. x! y! z!))
   :qid internal_req__lib!bits.lemma_mod_by_multiple._definition
   :skolemid skolem_internal_req__lib!bits.lemma_mod_by_multiple._definition
)))
(declare-fun ens%lib!bits.lemma_mod_by_multiple. (Int Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int) (z! Int)) (!
   (= (ens%lib!bits.lemma_mod_by_multiple. x! y! z!) (= (singular_mod x! z!) 0))
   :pattern ((ens%lib!bits.lemma_mod_by_multiple. x! y! z!))
   :qid internal_ens__lib!bits.lemma_mod_by_multiple._definition
   :skolemid skolem_internal_ens__lib!bits.lemma_mod_by_multiple._definition
)))

;; Function-Specs lib::bits::lemma_round_up_pow2_monotonic
(declare-fun req%lib!bits.lemma_round_up_pow2_monotonic. (Int Int Int) Bool)
(declare-const %%global_location_label%%69 Bool)
(declare-const %%global_location_label%%70 Bool)
(declare-const %%global_location_label%%71 Bool)
(declare-const %%global_location_label%%72 Bool)
(declare-const %%global_location_label%%73 Bool)
(assert
 (forall ((x! Int) (y! Int) (g! Int)) (!
   (= (req%lib!bits.lemma_round_up_pow2_monotonic. x! y! g!) (and
     (=>
      %%global_location_label%%69
      (> g! 0)
     )
     (=>
      %%global_location_label%%70
      (lib!bits.is_power_of_two.? (I g!))
     )
     (=>
      %%global_location_label%%71
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 (Add x! (Sub g! 1))))
        (let
         ((tmp%%$2 (- (uHi SZ) 1)))
         (and
          (<= tmp%%$ tmp%%$1)
          (<= tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%72
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 (Add y! (Sub g! 1))))
        (let
         ((tmp%%$2 (- (uHi SZ) 1)))
         (and
          (<= tmp%%$ tmp%%$1)
          (<= tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%73
      (<= x! y!)
   )))
   :pattern ((req%lib!bits.lemma_round_up_pow2_monotonic. x! y! g!))
   :qid internal_req__lib!bits.lemma_round_up_pow2_monotonic._definition
   :skolemid skolem_internal_req__lib!bits.lemma_round_up_pow2_monotonic._definition
)))
(declare-fun ens%lib!bits.lemma_round_up_pow2_monotonic. (Int Int Int) Bool)
(assert
 (forall ((x! Int) (y! Int) (g! Int)) (!
   (= (ens%lib!bits.lemma_round_up_pow2_monotonic. x! y! g!) (<= (uClip SZ (bitand (I (uClip
         SZ (Add x! (Sub g! 1))
        )
       ) (I (uClip SZ (bitnot (I (uClip SZ (Sub g! 1))))))
      )
     ) (uClip SZ (bitand (I (uClip SZ (Add y! (Sub g! 1)))) (I (uClip SZ (bitnot (I (uClip SZ
            (Sub g! 1)
   )))))))))
   :pattern ((ens%lib!bits.lemma_round_up_pow2_monotonic. x! y! g!))
   :qid internal_ens__lib!bits.lemma_round_up_pow2_monotonic._definition
   :skolemid skolem_internal_ens__lib!bits.lemma_round_up_pow2_monotonic._definition
)))

;; Function-Specs lib::Tlsf::lemma_shadow_ptrs_nonnull_frame
(declare-fun req%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_frame. (Dcr Type
  Dcr Type lib!Tlsf. lib!Tlsf.
 ) Bool
)
(declare-const %%global_location_label%%74 Bool)
(declare-const %%global_location_label%%75 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_frame. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self!
    ) (and
     (=>
      %%global_location_label%%74
      (lib!linked_list.impl&%0.shadow_ptrs_nonnull.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%75
      (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (
        lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_frame. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_frame._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_frame._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_frame. (Dcr Type
  Dcr Type lib!Tlsf. lib!Tlsf.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_frame. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self!
    ) (lib!linked_list.impl&%0.shadow_ptrs_nonnull.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      new_self!
   )))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_frame. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_frame._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_frame._definition
)))

;; Function-Specs lib::Tlsf::lemma_shadow_ptrs_nonnull_after_pop
(declare-fun req%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_after_pop. (Dcr
  Type Dcr Type lib!Tlsf. lib!Tlsf. lib!block_index.BlockIndex.
 ) Bool
)
(declare-const %%global_location_label%%76 Bool)
(declare-const %%global_location_label%%77 Bool)
(declare-const %%global_location_label%%78 Bool)
(declare-const %%global_location_label%%79 Bool)
(declare-const %%global_location_label%%80 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_after_pop. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self! idx!
    ) (and
     (=>
      %%global_location_label%%76
      (lib!linked_list.impl&%0.shadow_ptrs_nonnull.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%77
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%78
      (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. old_self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        )
       ) 0
     ))
     (=>
      %%global_location_label%%79
      (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
         SLLEN&
        ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
         (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
            (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
         )))
        ) (Poly%lib!block_index.BlockIndex. idx!)
       ) (vstd!seq_lib.impl&%0.remove.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. old_self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        ) (I 0)
     )))
     (=>
      %%global_location_label%%80
      (forall ((bi$ Poly)) (!
        (=>
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (not (= (%Poly%lib!block_index.BlockIndex. bi$) idx!))
          )
          (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
             SLLEN&
            ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
             (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
                (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
             )))
            ) bi$
           ) (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
             SLLEN&
            ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
             (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
                (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
             )))
            ) bi$
        ))))
        :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
        :qid user_lib__Tlsf__lemma_shadow_ptrs_nonnull_after_pop_109
        :skolemid skolem_user_lib__Tlsf__lemma_shadow_ptrs_nonnull_after_pop_109
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_after_pop. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self! idx!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_after_pop._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_after_pop._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_after_pop. (Dcr
  Type Dcr Type lib!Tlsf. lib!Tlsf. lib!block_index.BlockIndex.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_after_pop. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self! idx!
    ) (lib!linked_list.impl&%0.shadow_ptrs_nonnull.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      new_self!
   )))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_shadow_ptrs_nonnull_after_pop. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self! idx!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_after_pop._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_shadow_ptrs_nonnull_after_pop._definition
)))

;; Function-Specs lib::Tlsf::lemma_nodup_get
(declare-fun req%lib!linked_list.impl&%0.lemma_nodup_get. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex. Int lib!block_index.BlockIndex. Int
 ) Bool
)
(declare-const %%global_location_label%%81 Bool)
(declare-const %%global_location_label%%82 Bool)
(declare-const %%global_location_label%%83 Bool)
(declare-const %%global_location_label%%84 Bool)
(declare-const %%global_location_label%%85 Bool)
(declare-const %%global_location_label%%86 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (i! lib!block_index.BlockIndex.) (k! Int) (j! lib!block_index.BlockIndex.) (l! Int)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_nodup_get. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i! k! j! l!
    ) (and
     (=>
      %%global_location_label%%81
      (lib!linked_list.impl&%0.shadow_freelist_nodup.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
     )))
     (=>
      %%global_location_label%%82
      (not (= (tuple%2./tuple%2 (Poly%lib!block_index.BlockIndex. i!) (I k!)) (tuple%2./tuple%2
         (Poly%lib!block_index.BlockIndex. j!) (I l!)
     ))))
     (=>
      %%global_location_label%%83
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        i!
     )))
     (=>
      %%global_location_label%%84
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        j!
     )))
     (=>
      %%global_location_label%%85
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 k!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  (Poly%lib!Tlsf. self!)
              ))))
             ) (Poly%lib!block_index.BlockIndex. i!)
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%86
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 l!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  (Poly%lib!Tlsf. self!)
              ))))
             ) (Poly%lib!block_index.BlockIndex. j!)
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_nodup_get. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i! k! j! l!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_nodup_get._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_nodup_get._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_nodup_get. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex. Int lib!block_index.BlockIndex. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (i! lib!block_index.BlockIndex.) (k! Int) (j! lib!block_index.BlockIndex.) (l! Int)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_nodup_get. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i! k! j! l!
    ) (not (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
        $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
         $ (PTR $ TYPE%lib!block.BlockHdr.)
        ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
          (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
             (Poly%lib!Tlsf. self!)
         ))))
        ) (Poly%lib!block_index.BlockIndex. i!)
       ) (I k!)
      ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
        $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
         $ (PTR $ TYPE%lib!block.BlockHdr.)
        ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
          (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
             (Poly%lib!Tlsf. self!)
         ))))
        ) (Poly%lib!block_index.BlockIndex. j!)
       ) (I l!)
   ))))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_nodup_get. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i! k! j! l!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_nodup_get._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_nodup_get._definition
)))

;; Function-Specs lib::Tlsf::lemma_size_class_after_pop
(declare-fun req%lib!linked_list.impl&%0.lemma_size_class_after_pop. (Dcr Type Dcr
  Type lib!Tlsf. lib!Tlsf. lib!block_index.BlockIndex. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%87 Bool)
(declare-const %%global_location_label%%88 Bool)
(declare-const %%global_location_label%%89 Bool)
(declare-const %%global_location_label%%90 Bool)
(declare-const %%global_location_label%%91 Bool)
(declare-const %%global_location_label%%92 Bool)
(declare-const %%global_location_label%%93 Bool)
(declare-const %%global_location_label%%94 Bool)
(declare-const %%global_location_label%%95 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.) (allocated_block! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_size_class_after_pop. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self! idx! allocated_block!
    ) (and
     (=>
      %%global_location_label%%87
      (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%88
      (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        new_self!
     )))
     (=>
      %%global_location_label%%89
      (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%90
      (lib!linked_list.impl&%0.shadow_freelist_nodup.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%91
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%92
      (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. old_self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        )
       ) 0
     ))
     (=>
      %%global_location_label%%93
      (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
         (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
           SLLEN&
          ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
           (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
              (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
           )))
          ) (Poly%lib!block_index.BlockIndex. idx!)
         ) (I 0)
        )
       ) allocated_block!
     ))
     (=>
      %%global_location_label%%94
      (lib!linked_list.impl&%0.shadow_freelist_popped_at.? FLLEN&. FLLEN& SLLEN&. SLLEN&
       (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
          (Poly%lib!Tlsf. old_self!)
        ))
       ) (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
          (Poly%lib!Tlsf. new_self!)
        ))
       ) (Poly%lib!block_index.BlockIndex. idx!)
     ))
     (=>
      %%global_location_label%%95
      (lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.? FLLEN&. FLLEN& SLLEN&.
       SLLEN& (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
          (Poly%lib!Tlsf. old_self!)
        ))
       ) (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf.
           old_self!
        )))
       ) (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf.
           new_self!
        )))
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. allocated_block!)
   ))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_size_class_after_pop. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self! idx! allocated_block!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_size_class_after_pop._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_size_class_after_pop._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_size_class_after_pop. (Dcr Type Dcr
  Type lib!Tlsf. lib!Tlsf. lib!block_index.BlockIndex. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.) (allocated_block! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_size_class_after_pop. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self! idx! allocated_block!
    ) (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      new_self!
   )))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_size_class_after_pop. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self! idx! allocated_block!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_size_class_after_pop._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_size_class_after_pop._definition
)))

;; Function-Specs lib::Tlsf::lemma_size_class_perm_change_preserved
(declare-fun req%lib!linked_list.impl&%0.lemma_size_class_perm_change_preserved. (
  Dcr Type Dcr Type lib!Tlsf. lib!Tlsf. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%96 Bool)
(declare-const %%global_location_label%%97 Bool)
(declare-const %%global_location_label%%98 Bool)
(declare-const %%global_location_label%%99 Bool)
(declare-const %%global_location_label%%100 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (changed_block! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_size_class_perm_change_preserved. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self! changed_block!
    ) (and
     (=>
      %%global_location_label%%96
      (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%97
      (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%98
      (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (
        lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%99
      (not (lib!all_blocks.impl&%1.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
         (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
        ) (Poly%ptr_mut%<lib!block.BlockHdr.>. changed_block!)
     )))
     (=>
      %%global_location_label%%100
      (lib!linked_list.impl&%0.perms_size_unchanged_for_freelist.? FLLEN&. FLLEN& SLLEN&.
       SLLEN& (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
          (Poly%lib!Tlsf. old_self!)
        ))
       ) (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf.
           old_self!
        )))
       ) (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf.
           new_self!
        )))
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. changed_block!)
   ))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_size_class_perm_change_preserved. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self! changed_block!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_size_class_perm_change_preserved._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_size_class_perm_change_preserved._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_size_class_perm_change_preserved. (
  Dcr Type Dcr Type lib!Tlsf. lib!Tlsf. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (changed_block! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_size_class_perm_change_preserved. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self! changed_block!
    ) (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      new_self!
   )))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_size_class_perm_change_preserved. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self! changed_block!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_size_class_perm_change_preserved._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_size_class_perm_change_preserved._definition
)))

;; Function-Specs lib::Tlsf::lemma_size_class_at
(declare-fun req%lib!linked_list.impl&%0.lemma_size_class_at. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex. Int
 ) Bool
)
(declare-const %%global_location_label%%101 Bool)
(declare-const %%global_location_label%%102 Bool)
(declare-const %%global_location_label%%103 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (i! Int)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_size_class_at. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx! i!
    ) (and
     (=>
      %%global_location_label%%101
      (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
     )))
     (=>
      %%global_location_label%%102
      (vstd!set.Set.contains.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
        SLLEN&
       ) (vstd!map.impl&%0.dom.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
         SLLEN&
        ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
         (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
            (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
        ))))
       ) (Poly%lib!block_index.BlockIndex. idx!)
     ))
     (=>
      %%global_location_label%%103
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  (Poly%lib!Tlsf. self!)
              ))))
             ) (Poly%lib!block_index.BlockIndex. idx!)
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_size_class_at. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! idx! i!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_size_class_at._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_size_class_at._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_size_class_at. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (i! Int)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_size_class_at. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx! i!
    ) (and
     (= idx! (lib!mapping.impl&%0.map_floor_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN& (I (uClip
         SZ (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
            $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
              (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
                 (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                   (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                     $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                      (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                         (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                      )))
                     ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                       $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                        $ (PTR $ TYPE%lib!block.BlockHdr.)
                       ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                         (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                            (Poly%lib!Tlsf. self!)
                        ))))
                       ) (Poly%lib!block_index.BlockIndex. idx!)
                      ) (I i!)
     )))))))))))))))))
     (lib!half_open_range.impl&%0.contains.? (Poly%lib!half_open_range.HalfOpenRange. (lib!block_index.impl&%7.block_size_range.?
        FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex. idx!)
       )
      ) (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
          $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
            (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
              (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
               (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                 (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                   $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                    (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                       (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                    )))
                   ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                     $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                      $ (PTR $ TYPE%lib!block.BlockHdr.)
                     ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                       (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                          (Poly%lib!Tlsf. self!)
                      ))))
                     ) (Poly%lib!block_index.BlockIndex. idx!)
                    ) (I i!)
   )))))))))))))))))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_size_class_at. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! idx! i!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_size_class_at._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_size_class_at._definition
)))

;; Function-Specs lib::Tlsf::wf_index_in_freelist
(declare-fun req%lib!linked_list.impl&%0.wf_index_in_freelist. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex.
 ) Bool
)
(declare-const %%global_location_label%%104 Bool)
(declare-const %%global_location_label%%105 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (req%lib!linked_list.impl&%0.wf_index_in_freelist. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx!
    ) (and
     (=>
      %%global_location_label%%104
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%105
      (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
   )))))
   :pattern ((req%lib!linked_list.impl&%0.wf_index_in_freelist. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! idx!
   ))
   :qid internal_req__lib!linked_list.impl&__0.wf_index_in_freelist._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.wf_index_in_freelist._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.wf_index_in_freelist. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.wf_index_in_freelist. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx!
    ) (lib!linked_list.impl&%0.freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      self!
     ) (Poly%lib!block_index.BlockIndex. idx!)
   ))
   :pattern ((ens%lib!linked_list.impl&%0.wf_index_in_freelist. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! idx!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.wf_index_in_freelist._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.wf_index_in_freelist._definition
)))

;; Function-Specs lib::Tlsf::lemma_freelist_wf_extract_wf_free_node
(declare-fun req%lib!linked_list.impl&%0.lemma_freelist_wf_extract_wf_free_node. (
  Dcr Type Dcr Type lib!Tlsf. lib!block_index.BlockIndex. Int
 ) Bool
)
(declare-const %%global_location_label%%106 Bool)
(declare-const %%global_location_label%%107 Bool)
(declare-const %%global_location_label%%108 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (n! Int)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_freelist_wf_extract_wf_free_node. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! idx! n!
    ) (and
     (=>
      %%global_location_label%%106
      (lib!linked_list.impl&%0.freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
       ) (Poly%lib!block_index.BlockIndex. idx!)
     ))
     (=>
      %%global_location_label%%107
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%108
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 n!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  (Poly%lib!Tlsf. self!)
              ))))
             ) (Poly%lib!block_index.BlockIndex. idx!)
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_freelist_wf_extract_wf_free_node. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! idx! n!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_freelist_wf_extract_wf_free_node._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_freelist_wf_extract_wf_free_node._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_freelist_wf_extract_wf_free_node. (
  Dcr Type Dcr Type lib!Tlsf. lib!block_index.BlockIndex. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (n! Int)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_freelist_wf_extract_wf_free_node. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! idx! n!
    ) (lib!linked_list.impl&%0.wf_free_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      self!
     ) (Poly%lib!block_index.BlockIndex. idx!) (I n!)
   ))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_freelist_wf_extract_wf_free_node. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! idx! n!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_freelist_wf_extract_wf_free_node._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_freelist_wf_extract_wf_free_node._definition
)))

;; Function-Specs lib::Tlsf::lemma_free_blocks_in_freelist_except_perms_frame
(declare-fun req%lib!linked_list.impl&%0.lemma_free_blocks_in_freelist_except_perms_frame.
 (Dcr Type Dcr Type lib!Tlsf. lib!Tlsf. vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)
 Bool
)
(declare-const %%global_location_label%%109 Bool)
(declare-const %%global_location_label%%110 Bool)
(declare-const %%global_location_label%%111 Bool)
(declare-const %%global_location_label%%112 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (exceptions! vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_free_blocks_in_freelist_except_perms_frame. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self! exceptions!
    ) (and
     (=>
      %%global_location_label%%109
      (lib!linked_list.impl&%0.free_blocks_in_freelist_except.? FLLEN&. FLLEN& SLLEN&. SLLEN&
       (Poly%lib!Tlsf. old_self!) (Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>. exceptions!)
     ))
     (=>
      %%global_location_label%%110
      (= (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
        ))
       ) (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
     )))))
     (=>
      %%global_location_label%%111
      (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (
        lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%112
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (let
           ((tmp%%$ 0))
           (let
            ((tmp%%$1 (%I i$)))
            (let
             ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                    (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
             )))))))
             (and
              (<= tmp%%$ tmp%%$1)
              (< tmp%%$1 tmp%%$2)
          ))))
          (= (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
              $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
               )))
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
                )))
               ) i$
            )))
           ) (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
              $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
               )))
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
                )))
               ) i$
        )))))))
        :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
           )))
          ) i$
        ))
        :qid user_lib__Tlsf__lemma_free_blocks_in_freelist_except_perms_frame_110
        :skolemid skolem_user_lib__Tlsf__lemma_free_blocks_in_freelist_except_perms_frame_110
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_free_blocks_in_freelist_except_perms_frame.
     FLLEN&. FLLEN& SLLEN&. SLLEN& old_self! new_self! exceptions!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_free_blocks_in_freelist_except_perms_frame._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_free_blocks_in_freelist_except_perms_frame._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_free_blocks_in_freelist_except_perms_frame.
 (Dcr Type Dcr Type lib!Tlsf. lib!Tlsf. vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)
 Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (exceptions! vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_free_blocks_in_freelist_except_perms_frame. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self! exceptions!
    ) (lib!linked_list.impl&%0.free_blocks_in_freelist_except.? FLLEN&. FLLEN& SLLEN&.
     SLLEN& (Poly%lib!Tlsf. new_self!) (Poly%vstd!set.Set<ptr_mut%<lib!block.BlockHdr.>.>.
      exceptions!
   )))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_free_blocks_in_freelist_except_perms_frame.
     FLLEN&. FLLEN& SLLEN&. SLLEN& old_self! new_self! exceptions!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_free_blocks_in_freelist_except_perms_frame._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_free_blocks_in_freelist_except_perms_frame._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_glue_facts
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_glue_facts. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  Int
 ) Bool
)
(declare-const %%global_location_label%%113 Bool)
(declare-const %%global_location_label%%114 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_glue_facts. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
    ) (and
     (=>
      %%global_location_label%%113
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%114
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_glue_facts. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_glue_facts._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_glue_facts._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_glue_facts. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_glue_facts. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
    ) (and
     (=>
      (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.BlockHdr./BlockHdr/prev_phys_block
             (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
                FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
                 $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                  (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                     self!
                  )))
                 ) (I i!)
         ))))))))
        ) 0
      ))
      (let
       ((tmp%%$ (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
           self!
          ) (I i!)
       )))
       (and
        (is-core!option.Option./Some tmp%%$)
        (let
         ((p$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (core!option.Option./Some/0 $ (PTR $ TYPE%lib!block.BlockHdr.)
             (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
         ))))
         (= p$ (lib!block.BlockHdr./BlockHdr/prev_phys_block (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
             (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
               self!
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   self!
                )))
               ) (I i!)
     ))))))))))
     (=>
      (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.BlockHdr./BlockHdr/prev_phys_block
            (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
               FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
                $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                    self!
                 )))
                ) (I i!)
        ))))))))
       ) 0
      )
      (is-core!option.Option./None (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN&
        SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (I i!)
     )))
     (=>
      (not (lib!block.impl&%1.is_sentinel.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
          FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
               self!
            )))
           ) (I i!)
      )))))
      (and
       (and
        (lib!block_index.impl&%7.valid_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN& (I (uClip
           SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
                (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
                  self!
                 ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                   (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                      self!
                   )))
                  ) (I i!)
             )))))
            ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
        ))))
        (< (Add (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
             (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
               self!
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   self!
                )))
               ) (I i!)
           ))))
          ) (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
            $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
             )))
            ) (I i!)
          ))
         ) (- (uHi SZ) 1)
       ))
       (is-core!option.Option./Some (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN&
         SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (I i!)
     ))))
     (=>
      (lib!block.impl&%1.is_sentinel.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
         FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              self!
           )))
          ) (I i!)
      ))))
      (and
       (and
        (= i! (Sub (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
               self!
           ))))
          ) 1
        ))
        (= (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (
               Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&.
                SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                 (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
                   (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
                  )
                 ) (I i!)
            )))))
           ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
          )
         ) 0
       ))
       (< (Add (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
               self!
            )))
           ) (I i!)
          )
         ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
        ) (- (uHi SZ) 1)
     )))
     (=>
      (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
         FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              self!
           )))
          ) (I i!)
      ))))
      (let
       ((tmp%%$ (lib!block.BlockPerm./BlockPerm/free_link_perm (%Poly%lib!block.BlockPerm. (
            vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
             )
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
              (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                 self!
              )))
             ) (I i!)
       ))))))
       (and
        (is-core!option.Option./Some tmp%%$)
        (let
         ((p$ (%Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (core!option.Option./Some/0 $
             (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.) (%Poly%core!option.Option.
              (Poly%core!option.Option. tmp%%$)
         )))))
         (= (%Poly%ptr_mut%<lib!block.FreeLink.>. (vstd!raw_ptr.PointsToData./PointsToData/ptr
            (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
               $ TYPE%lib!block.FreeLink.
              ) (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. p$)
           )))
          ) (lib!block.get_freelink_ptr_spec.? (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
            (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
             )
            ) (I i!)
     )))))))
     (lib!all_blocks.impl&%0.wf_node_glue.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       self!
      ) (I i!)
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_glue_facts. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_glue_facts._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_glue_facts._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_free_ptr_hdr_bound
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_free_ptr_hdr_bound. (Dcr Type Dcr
  Type lib!all_blocks.AllBlocks. Int
 ) Bool
)
(declare-const %%global_location_label%%115 Bool)
(declare-const %%global_location_label%%116 Bool)
(declare-const %%global_location_label%%117 Bool)
(declare-const %%global_location_label%%118 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_free_ptr_hdr_bound. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
    ) (and
     (=>
      %%global_location_label%%115
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%116
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%117
      (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
         FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              self!
           )))
          ) (I i!)
     )))))
     (=>
      %%global_location_label%%118
      (<= (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.)) lib!block_index.GRANULARITY.?)
   )))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_free_ptr_hdr_bound. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_free_ptr_hdr_bound._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_free_ptr_hdr_bound._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_free_ptr_hdr_bound. (Dcr Type Dcr
  Type lib!all_blocks.AllBlocks. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_free_ptr_hdr_bound. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
    ) (< (Add (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr.
        (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             self!
          )))
         ) (I i!)
       ))
      ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
     ) (- (uHi SZ) 1)
   ))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_free_ptr_hdr_bound. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_free_ptr_hdr_bound._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_free_ptr_hdr_bound._definition
)))

;; Function-Specs lib::block::get_freelink_ptr
(declare-fun req%lib!block.get_freelink_ptr. (ptr_mut%<lib!block.BlockHdr.>.) Bool)
(declare-const %%global_location_label%%119 Bool)
(assert
 (forall ((ptr! ptr_mut%<lib!block.BlockHdr.>.)) (!
   (= (req%lib!block.get_freelink_ptr. ptr!) (=>
     %%global_location_label%%119
     (<= (Add (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr.
         (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!)
        )
       ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
      ) (- (uHi SZ) 1)
   )))
   :pattern ((req%lib!block.get_freelink_ptr. ptr!))
   :qid internal_req__lib!block.get_freelink_ptr._definition
   :skolemid skolem_internal_req__lib!block.get_freelink_ptr._definition
)))
(declare-fun ens%lib!block.get_freelink_ptr. (ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.FreeLink.>.)
 Bool
)
(assert
 (forall ((ptr! ptr_mut%<lib!block.BlockHdr.>.) (r! ptr_mut%<lib!block.FreeLink.>.))
  (!
   (= (ens%lib!block.get_freelink_ptr. ptr! r!) (and
     (= r! (lib!block.get_freelink_ptr_spec.? (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!)))
     (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.FreeLink.) (Poly%ptr_mut%<lib!block.FreeLink.>. r!)
       ))
      ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!)
     ))))
     (= (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.FreeLink. (Poly%ptr_mut%<lib!block.FreeLink.>.
         r!
       ))
      ) (Add (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (
          Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!
        ))
       ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
   ))))
   :pattern ((ens%lib!block.get_freelink_ptr. ptr! r!))
   :qid internal_ens__lib!block.get_freelink_ptr._definition
   :skolemid skolem_internal_ens__lib!block.get_freelink_ptr._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_contains
(declare-fun req%lib!all_blocks.impl&%0.lemma_contains. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%120 Bool)
(declare-const %%global_location_label%%121 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (x! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_contains. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     x!
    ) (and
     (=>
      %%global_location_label%%120
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%121
      (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. x!)
   ))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_contains. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! x!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_contains._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_contains._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_contains. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (x! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_contains. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     x!
    ) (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
      $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
       (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          self!
      ))))
     ) (Poly%ptr_mut%<lib!block.BlockHdr.>. x!)
   ))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_contains. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! x!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_contains._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_contains._definition
)))

;; Function-Specs lib::block::null_bhdr
(declare-fun ens%lib!block.null_bhdr. (Int ptr_mut%<lib!block.BlockHdr.>.) Bool)
(assert
 (forall ((no%param Int) (r! ptr_mut%<lib!block.BlockHdr.>.)) (!
   (= (ens%lib!block.null_bhdr. no%param r!) (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData.
       (vstd!view.View.view.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>.
         r!
      )))
     ) 0
   ))
   :pattern ((ens%lib!block.null_bhdr. no%param r!))
   :qid internal_ens__lib!block.null_bhdr._definition
   :skolemid skolem_internal_ens__lib!block.null_bhdr._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_nodup
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_nodup. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.)
 Bool
)
(declare-const %%global_location_label%%122 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_nodup. FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    (=>
     %%global_location_label%%122
     (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       self!
   ))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_nodup. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_nodup._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_nodup._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_nodup. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.)
 Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_nodup. FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    (lib!ordered_pointer_list.ptrs_no_duplicates.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
      (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
         self!
   ))))))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_nodup. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_nodup._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_nodup._definition
)))

;; Function-Specs lib::ordered_pointer_list::lemma_ptrs_no_duplicates_eq_index
(declare-fun req%lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  Int Int
 ) Bool
)
(declare-const %%global_location_label%%123 Bool)
(declare-const %%global_location_label%%124 Bool)
(declare-const %%global_location_label%%125 Bool)
(declare-const %%global_location_label%%126 Bool)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (i! Int) (j! Int)) (!
   (= (req%lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index. ls! i! j!) (and
     (=>
      %%global_location_label%%123
      (lib!ordered_pointer_list.ptrs_no_duplicates.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        ls!
     )))
     (=>
      %%global_location_label%%124
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%125
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 j!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%126
      (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (I i!)
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (I j!)
   )))))
   :pattern ((req%lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index. ls! i! j!))
   :qid internal_req__lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index._definition
)))
(declare-fun ens%lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  Int Int
 ) Bool
)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (i! Int) (j! Int)) (!
   (= (ens%lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index. ls! i! j!) (= i!
     j!
   ))
   :pattern ((ens%lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index. ls! i! j!))
   :qid internal_ens__lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index._definition
   :skolemid skolem_internal_ens__lib!ordered_pointer_list.lemma_ptrs_no_duplicates_eq_index._definition
)))

;; Function-Specs lib::Tlsf::lemma_shadow_list_no_duplicates
(declare-fun req%lib!linked_list.impl&%0.lemma_shadow_list_no_duplicates. (Dcr Type
  Dcr Type lib!Tlsf.
 ) Bool
)
(declare-const %%global_location_label%%127 Bool)
(declare-const %%global_location_label%%128 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.))
  (!
   (= (req%lib!linked_list.impl&%0.lemma_shadow_list_no_duplicates. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self!
    ) (and
     (=>
      %%global_location_label%%127
      (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
     )))
     (=>
      %%global_location_label%%128
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_shadow_list_no_duplicates. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_shadow_list_no_duplicates._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_shadow_list_no_duplicates._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_shadow_list_no_duplicates. (Dcr Type
  Dcr Type lib!Tlsf.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.))
  (!
   (= (ens%lib!linked_list.impl&%0.lemma_shadow_list_no_duplicates. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self!
    ) (lib!linked_list.impl&%0.shadow_freelist_nodup.? FLLEN&. FLLEN& SLLEN&. SLLEN& (
      Poly%lib!Tlsf. self!
   )))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_shadow_list_no_duplicates. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_shadow_list_no_duplicates._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_shadow_list_no_duplicates._definition
)))

;; Function-Specs lib::Tlsf::clear_bit_for_sl
(declare-fun req%lib!bitmap.impl&%0.clear_bit_for_sl. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex.
 ) Bool
)
(declare-const %%global_location_label%%129 Bool)
(declare-const %%global_location_label%%130 Bool)
(declare-const %%global_location_label%%131 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (req%lib!bitmap.impl&%0.clear_bit_for_sl. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     idx!
    ) (and
     (=>
      %%global_location_label%%129
      (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     )
     (=>
      %%global_location_label%%130
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%131
      (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. pre%self!))
   )))
   :pattern ((req%lib!bitmap.impl&%0.clear_bit_for_sl. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     idx!
   ))
   :qid internal_req__lib!bitmap.impl&__0.clear_bit_for_sl._definition
   :skolemid skolem_internal_req__lib!bitmap.impl&__0.clear_bit_for_sl._definition
)))
(declare-fun ens%lib!bitmap.impl&%0.clear_bit_for_sl. (Dcr Type Dcr Type lib!Tlsf.
  lib!Tlsf. lib!block_index.BlockIndex.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (ens%lib!bitmap.impl&%0.clear_bit_for_sl. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     self! idx!
    ) (and
     (has_type (Poly%lib!Tlsf. self!) (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     (= (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/all_blocks
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/first_free
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/shadow_freelist
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/user_block_map
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/valid_range (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/valid_range
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (= (lib!Tlsf./Tlsf/root_provenances (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))) (lib!Tlsf./Tlsf/root_provenances
       (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
     ))
     (forall ((i$ Poly)) (!
       (=>
        (has_type i$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (=>
         (and
          (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& i$)
          (not (= (%Poly%lib!block_index.BlockIndex. i$) idx!))
         )
         (= (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.?
                    $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf.
                       (Poly%lib!Tlsf. self!)
                    )))
                   ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. i$)))
                 ))
                ) (I (uClip SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
                    i$
            ))))))))
           ) 1
          ) (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.?
                    $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf.
                       (Poly%lib!Tlsf. pre%self!)
                    )))
                   ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. i$)))
                 ))
                ) (I (uClip SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
                    i$
            ))))))))
           ) 1
       ))))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& i$))
       :qid user_lib__Tlsf__clear_bit_for_sl_111
       :skolemid skolem_user_lib__Tlsf__clear_bit_for_sl_111
     ))
     (let
      ((tmp%%$ idx!))
      (and
       (is-lib!block_index.BlockIndex./BlockIndex tmp%%$)
       (let
        ((fl$ (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             tmp%%$
        )))))
        (let
         ((sl$ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
              tmp%%$
         )))))
         (not (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (
                    vstd!view.View.view.? $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap
                      (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
                    ))
                   ) (I fl$)
                 ))
                ) (I sl$)
            ))))
           ) 1
   ))))))))
   :pattern ((ens%lib!bitmap.impl&%0.clear_bit_for_sl. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     self! idx!
   ))
   :qid internal_ens__lib!bitmap.impl&__0.clear_bit_for_sl._definition
   :skolemid skolem_internal_ens__lib!bitmap.impl&__0.clear_bit_for_sl._definition
)))

;; Function-Specs lib::Tlsf::lemma_ii_remove_for_index_ensures
(declare-fun req%lib!linked_list.impl&%0.lemma_ii_remove_for_index_ensures. (Dcr Type
  Dcr Type lib!all_blocks.ShadowFreelist. lib!all_blocks.AllBlocks. lib!block_index.BlockIndex.
  Int
 ) Bool
)
(declare-const %%global_location_label%%132 Bool)
(declare-const %%global_location_label%%133 Bool)
(declare-const %%global_location_label%%134 Bool)
(declare-const %%global_location_label%%135 Bool)
(declare-const %%global_location_label%%136 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sfl! lib!all_blocks.ShadowFreelist.)
   (all_blocks! lib!all_blocks.AllBlocks.) (bi! lib!block_index.BlockIndex.) (rm_pos!
    Int
   )
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_ii_remove_for_index_ensures. FLLEN&. FLLEN& SLLEN&.
     SLLEN& sfl! all_blocks! bi! rm_pos!
    ) (and
     (=>
      %%global_location_label%%132
      (lib!ordered_pointer_list.ptrs_no_duplicates.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           all_blocks!
     ))))))
     (=>
      %%global_location_label%%133
      (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
        sfl!
       ) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
         (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. all_blocks!))
     ))))
     (=>
      %%global_location_label%%134
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        bi!
     )))
     (=>
      %%global_location_label%%135
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 rm_pos!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. sfl!)
              )
             ) (Poly%lib!block_index.BlockIndex. bi!)
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%136
      (forall ((j$ Poly) (n$ Poly)) (!
        (=>
         (and
          (has_type j$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
          (has_type n$ INT)
         )
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& j$)
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I n$)))
             (let
              ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                  $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                   $ (PTR $ TYPE%lib!block.BlockHdr.)
                  ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                    (Poly%lib!all_blocks.ShadowFreelist. sfl!)
                   )
                  ) j$
              ))))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
          )))))
          (let
           ((tmp%%$ 0))
           (let
            ((tmp%%$4 (%I (vstd!map.impl&%0.index.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
                  FLLEN&. FLLEN& SLLEN&. SLLEN&
                 ) $ INT
                ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
                  (Poly%lib!all_blocks.ShadowFreelist. sfl!)
                 )
                ) (Poly%tuple%2. (tuple%2./tuple%2 j$ n$))
            ))))
            (let
             ((tmp%%$5 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                    all_blocks!
             )))))))
             (and
              (<= tmp%%$ tmp%%$4)
              (< tmp%%$4 tmp%%$5)
        ))))))
        :pattern ((vstd!map.impl&%0.index.? (DST $) (TYPE%tuple%2. $ (TYPE%lib!block_index.BlockIndex.
            FLLEN&. FLLEN& SLLEN&. SLLEN&
           ) $ INT
          ) $ INT (lib!all_blocks.ShadowFreelist./ShadowFreelist/pi (%Poly%lib!all_blocks.ShadowFreelist.
            (Poly%lib!all_blocks.ShadowFreelist. sfl!)
           )
          ) (Poly%tuple%2. (tuple%2./tuple%2 j$ n$))
        ))
        :qid user_lib__Tlsf__lemma_ii_remove_for_index_ensures_112
        :skolemid skolem_user_lib__Tlsf__lemma_ii_remove_for_index_ensures_112
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_ii_remove_for_index_ensures. FLLEN&. FLLEN&
     SLLEN&. SLLEN& sfl! all_blocks! bi! rm_pos!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_ii_remove_for_index_ensures._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_ii_remove_for_index_ensures._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_ii_remove_for_index_ensures. (Dcr Type
  Dcr Type lib!all_blocks.ShadowFreelist. lib!all_blocks.AllBlocks. lib!block_index.BlockIndex.
  Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sfl! lib!all_blocks.ShadowFreelist.)
   (all_blocks! lib!all_blocks.AllBlocks.) (bi! lib!block_index.BlockIndex.) (rm_pos!
    Int
   )
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_ii_remove_for_index_ensures. FLLEN&. FLLEN& SLLEN&.
     SLLEN& sfl! all_blocks! bi! rm_pos!
    ) (let
     ((new_sfl$ (lib!all_blocks.impl&%1.ii_remove_for_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
        (Poly%lib!all_blocks.ShadowFreelist. sfl!) (Poly%lib!all_blocks.AllBlocks. all_blocks!)
        (Poly%lib!block_index.BlockIndex. bi!) (I rm_pos!)
     )))
     (and
      (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
         SLLEN&
        ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
         (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. new_sfl$))
        ) (Poly%lib!block_index.BlockIndex. bi!)
       ) (vstd!seq_lib.impl&%0.remove.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. sfl!)
          )
         ) (Poly%lib!block_index.BlockIndex. bi!)
        ) (I rm_pos!)
      ))
      (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
        new_sfl$
       ) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
         (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. all_blocks!))
   ))))))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_ii_remove_for_index_ensures. FLLEN&. FLLEN&
     SLLEN&. SLLEN& sfl! all_blocks! bi! rm_pos!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_ii_remove_for_index_ensures._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_ii_remove_for_index_ensures._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_extract_node
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_extract_node. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  Int
 ) Bool
)
(declare-const %%global_location_label%%137 Bool)
(declare-const %%global_location_label%%138 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_extract_node. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
    ) (and
     (=>
      %%global_location_label%%137
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%138
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_extract_node. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_extract_node._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_extract_node._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_extract_node. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_extract_node. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
    ) (lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
     ) (I i!)
   ))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_extract_node. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_extract_node._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_extract_node._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_structural_facts
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_structural_facts. (Dcr Type Dcr Type
  lib!all_blocks.AllBlocks. Int
 ) Bool
)
(declare-const %%global_location_label%%139 Bool)
(declare-const %%global_location_label%%140 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_structural_facts. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
    ) (and
     (=>
      %%global_location_label%%139
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%140
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_structural_facts. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_structural_facts._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_structural_facts._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_structural_facts. (Dcr Type Dcr Type
  lib!all_blocks.AllBlocks. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_structural_facts. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
    ) (and
     (let
      ((tmp%%$ (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
          self!
         ) (I i!)
      )))
      (=>
       (is-core!option.Option./Some tmp%%$)
       (let
        ((next_ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (core!option.Option./Some/0 $ (PTR $
             TYPE%lib!block.BlockHdr.
            ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
        ))))
        (lib!all_blocks.impl&%0.phys_next_matches.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%ptr_mut%<lib!block.BlockHdr.>.
          next_ptr$
         ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              self!
           )))
          ) (I i!)
         ) (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
             (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
               self!
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   self!
                )))
               ) (I i!)
     ))))))))))
     (=>
      (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
         FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              self!
           )))
          ) (I i!)
      ))))
      (let
       ((tmp%%$ (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
           self!
          ) (I i!)
       )))
       (and
        (is-core!option.Option./Some tmp%%$)
        (let
         ((next_ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (core!option.Option./Some/0 $ (PTR $
              TYPE%lib!block.BlockHdr.
             ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
         ))))
         (not (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
             FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
              next_ptr$
     )))))))))
     (lib!all_blocks.impl&%0.wf_node_structural.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       self!
      ) (I i!)
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_structural_facts. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_structural_facts._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_structural_facts._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_construct_wf_node_glue
(declare-fun req%lib!all_blocks.impl&%0.lemma_construct_wf_node_glue. (Dcr Type Dcr
  Type lib!all_blocks.AllBlocks. Int
 ) Bool
)
(declare-const %%global_location_label%%141 Bool)
(declare-const %%global_location_label%%142 Bool)
(declare-const %%global_location_label%%143 Bool)
(declare-const %%global_location_label%%144 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_construct_wf_node_glue. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
    ) (and
     (=>
      %%global_location_label%%141
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%142
      (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
         (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            self!
        ))))
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            self!
         )))
        ) (I i!)
     )))
     (=>
      %%global_location_label%%143
      (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
        (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
           $ TYPE%lib!block.BlockHdr.
          ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
            (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
              $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  self!
               )))
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   self!
                )))
               ) (I i!)
     ))))))))))
     (=>
      %%global_location_label%%144
      (let
       ((ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
             (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
            )
           ) (I i!)
       ))))
       (and
        (and
         (and
          (=>
           (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.BlockHdr./BlockHdr/prev_phys_block
                  (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
                     FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
                      ptr$
              ))))))))
             ) 0
           ))
           (let
            ((tmp%%$ (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
                self!
               ) (I i!)
            )))
            (and
             (is-core!option.Option./Some tmp%%$)
             (let
              ((p$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (core!option.Option./Some/0 $ (PTR $ TYPE%lib!block.BlockHdr.)
                  (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
              ))))
              (= p$ (lib!block.BlockHdr./BlockHdr/prev_phys_block (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
                  (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
                    self!
                   ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
          )))))))))
          (=>
           (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
               $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.BlockHdr./BlockHdr/prev_phys_block
                 (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
                    FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
                     ptr$
             ))))))))
            ) 0
           )
           (is-core!option.Option./None (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN&
             SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (I i!)
         ))))
         (ite
          (lib!block.impl&%1.is_sentinel.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
             FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
              ptr$
          ))))
          (and
           (and
            (= i! (Sub (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   self!
               ))))
              ) 1
            ))
            (= (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (
                   Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&.
                    SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
                     ptr$
                )))))
               ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
              )
             ) 0
           ))
           (< (Add (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
               ptr$
              )
             ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))
            ) (- (uHi SZ) 1)
          ))
          (and
           (and
            (lib!block_index.impl&%7.valid_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN& (I (uClip
               SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
                    (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
                      self!
                     ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
                 ))))
                ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
            ))))
            (< (Add (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr.
                 (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
                   self!
                  ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
               )))
              ) (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
                ptr$
              ))
             ) (- (uHi SZ) 1)
           ))
           (is-core!option.Option./Some (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN&
             SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (I i!)
        )))))
        (=>
         (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
            FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
             ptr$
         ))))
         (let
          ((tmp%%$ (lib!block.BlockPerm./BlockPerm/free_link_perm (%Poly%lib!block.BlockPerm. (
               vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
               (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
                 (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
                )
               ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$)
          )))))
          (and
           (is-core!option.Option./Some tmp%%$)
           (let
            ((p$ (%Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. (core!option.Option./Some/0 $
                (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.) (%Poly%core!option.Option.
                 (Poly%core!option.Option. tmp%%$)
            )))))
            (= (%Poly%ptr_mut%<lib!block.FreeLink.>. (vstd!raw_ptr.PointsToData./PointsToData/ptr
               (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                  $ TYPE%lib!block.FreeLink.
                 ) (Poly%vstd!raw_ptr.PointsTo<lib!block.FreeLink.>. p$)
              )))
             ) (lib!block.get_freelink_ptr_spec.? (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$))
   ))))))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_construct_wf_node_glue. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_construct_wf_node_glue._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_construct_wf_node_glue._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_construct_wf_node_glue. (Dcr Type Dcr
  Type lib!all_blocks.AllBlocks. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_construct_wf_node_glue. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
    ) (lib!all_blocks.impl&%0.wf_node_glue.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
     ) (I i!)
   ))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_construct_wf_node_glue. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_construct_wf_node_glue._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_construct_wf_node_glue._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_construct_wf_node_structural
(declare-fun req%lib!all_blocks.impl&%0.lemma_construct_wf_node_structural. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks. Int
 ) Bool
)
(declare-const %%global_location_label%%145 Bool)
(declare-const %%global_location_label%%146 Bool)
(declare-const %%global_location_label%%147 Bool)
(declare-const %%global_location_label%%148 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_construct_wf_node_structural. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
    ) (and
     (=>
      %%global_location_label%%145
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%146
      (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
         (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            self!
        ))))
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            self!
         )))
        ) (I i!)
     )))
     (=>
      %%global_location_label%%147
      (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
        (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
           $ TYPE%lib!block.BlockHdr.
          ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
            (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
              $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  self!
               )))
              ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   self!
                )))
               ) (I i!)
     ))))))))))
     (=>
      %%global_location_label%%148
      (let
       ((ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
             (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
            )
           ) (I i!)
       ))))
       (and
        (let
         ((tmp%%$ (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
             self!
            ) (I i!)
         )))
         (=>
          (is-core!option.Option./Some tmp%%$)
          (let
           ((next_ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (core!option.Option./Some/0 $ (PTR $
                TYPE%lib!block.BlockHdr.
               ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
           ))))
           (lib!all_blocks.impl&%0.phys_next_matches.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%ptr_mut%<lib!block.BlockHdr.>.
             next_ptr$
            ) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr$) (I (lib!block.BlockHdr./BlockHdr/size
              (%Poly%lib!block.BlockHdr. (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
                 FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
                  ptr$
        ))))))))))
        (=>
         (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
            FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
             ptr$
         ))))
         (let
          ((tmp%%$ (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
              self!
             ) (I i!)
          )))
          (and
           (is-core!option.Option./Some tmp%%$)
           (let
            ((next_ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (core!option.Option./Some/0 $ (PTR $
                 TYPE%lib!block.BlockHdr.
                ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
            ))))
            (not (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
                FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
                 next_ptr$
   ))))))))))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_construct_wf_node_structural. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_construct_wf_node_structural._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_construct_wf_node_structural._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_construct_wf_node_structural. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_construct_wf_node_structural. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! i!
    ) (lib!all_blocks.impl&%0.wf_node_structural.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
     ) (I i!)
   ))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_construct_wf_node_structural. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_construct_wf_node_structural._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_construct_wf_node_structural._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_transfer_wf_node
(declare-fun req%lib!all_blocks.impl&%0.lemma_transfer_wf_node. (Dcr Type Dcr Type
  lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks. Int Int
 ) Bool
)
(declare-const %%global_location_label%%149 Bool)
(declare-const %%global_location_label%%150 Bool)
(declare-const %%global_location_label%%151 Bool)
(declare-const %%global_location_label%%152 Bool)
(declare-const %%global_location_label%%153 Bool)
(declare-const %%global_location_label%%154 Bool)
(declare-const %%global_location_label%%155 Bool)
(declare-const %%global_location_label%%156 Bool)
(declare-const %%global_location_label%%157 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.) (old_i! Int) (new_i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_transfer_wf_node. FLLEN&. FLLEN& SLLEN&. SLLEN&
     old_ab! new_ab! old_i! new_i!
    ) (and
     (=>
      %%global_location_label%%149
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        old_ab!
     )))
     (=>
      %%global_location_label%%150
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 old_i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                old_ab!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%151
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 new_i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                new_ab!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%152
      (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            old_ab!
         )))
        ) (I old_i!)
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
         )))
        ) (I new_i!)
     )))
     (=>
      %%global_location_label%%153
      (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
         (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
        ))))
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
         )))
        ) (I new_i!)
     )))
     (=>
      %%global_location_label%%154
      (= (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
        (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
          (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. old_ab!))
         )
        ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             old_ab!
          )))
         ) (I old_i!)
        )
       ) (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
        (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
          (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. new_ab!))
         )
        ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             new_ab!
          )))
         ) (I new_i!)
     ))))
     (=>
      %%global_location_label%%155
      (= (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
         old_ab!
        ) (I old_i!)
       ) (lib!all_blocks.impl&%0.phys_prev_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
         new_ab!
        ) (I new_i!)
     )))
     (=>
      %%global_location_label%%156
      (= (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
         old_ab!
        ) (I old_i!)
       ) (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
         new_ab!
        ) (I new_i!)
     )))
     (=>
      %%global_location_label%%157
      (=>
       (and
        (lib!block.impl&%1.is_free.? (Poly%lib!block.BlockHdr. (lib!all_blocks.impl&%0.value_at.?
           FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. old_ab!) (vstd!seq.Seq.index.?
            $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                old_ab!
             )))
            ) (I old_i!)
        ))))
        (is-core!option.Option./Some (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN&
          SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks. old_ab!) (I old_i!)
       )))
       (= (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
          old_ab!
         ) (core!option.Option./Some/0 $ (PTR $ TYPE%lib!block.BlockHdr.) (%Poly%core!option.Option.
           (Poly%core!option.Option. (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&.
             SLLEN& (Poly%lib!all_blocks.AllBlocks. old_ab!) (I old_i!)
         ))))
        ) (lib!all_blocks.impl&%0.value_at.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
          new_ab!
         ) (core!option.Option./Some/0 $ (PTR $ TYPE%lib!block.BlockHdr.) (%Poly%core!option.Option.
           (Poly%core!option.Option. (lib!all_blocks.impl&%0.phys_next_of.? FLLEN&. FLLEN& SLLEN&.
             SLLEN& (Poly%lib!all_blocks.AllBlocks. new_ab!) (I new_i!)
   ))))))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_transfer_wf_node. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_ab! new_ab! old_i! new_i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_transfer_wf_node._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_transfer_wf_node._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_transfer_wf_node. (Dcr Type Dcr Type
  lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks. Int Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.) (old_i! Int) (new_i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_transfer_wf_node. FLLEN&. FLLEN& SLLEN&. SLLEN&
     old_ab! new_ab! old_i! new_i!
    ) (and
     (lib!all_blocks.impl&%0.wf_node_glue.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       new_ab!
      ) (I new_i!)
     )
     (lib!all_blocks.impl&%0.wf_node_structural.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       new_ab!
      ) (I new_i!)
     )
     (lib!all_blocks.impl&%0.wf_node_ptr.? FLLEN&. FLLEN& SLLEN&. SLLEN& (vstd!seq.Seq.index.?
       $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           new_ab!
        )))
       ) (I new_i!)
     ))
     (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           new_ab!
        )))
       ) (I new_i!)
      ) (vstd!raw_ptr.PointsToData./PointsToData/ptr (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.?
         $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>.
          (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
             $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
              (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                 new_ab!
              )))
             ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
               (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  new_ab!
               )))
              ) (I new_i!)
     )))))))))
     (lib!block.impl&%2.wf.? (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
       $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
        (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           new_ab!
        )))
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
         )))
        ) (I new_i!)
   )))))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_transfer_wf_node. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_ab! new_ab! old_i! new_i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_transfer_wf_node._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_transfer_wf_node._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_pool_size_bounded_transfer
(declare-fun req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_transfer. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks.
 ) Bool
)
(declare-const %%global_location_label%%158 Bool)
(declare-const %%global_location_label%%159 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_transfer. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_ab! new_ab!
    ) (and
     (=>
      %%global_location_label%%158
      (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        old_ab!
     )))
     (=>
      %%global_location_label%%159
      (= (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          new_ab!
        ))
       ) (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          old_ab!
   )))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_transfer. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_ab! new_ab!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded_transfer._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded_transfer._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_transfer. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_transfer. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_ab! new_ab!
    ) (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      new_ab!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_transfer. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_ab! new_ab!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded_transfer._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded_transfer._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_from_nodes
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_from_nodes. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.)
 Bool
)
(declare-const %%global_location_label%%160 Bool)
(declare-const %%global_location_label%%161 Bool)
(declare-const %%global_location_label%%162 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_from_nodes. FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    (and
     (=>
      %%global_location_label%%160
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (let
           ((tmp%%$ 0))
           (let
            ((tmp%%$1 (%I i$)))
            (let
             ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                    self!
             )))))))
             (and
              (<= tmp%%$ tmp%%$1)
              (< tmp%%$1 tmp%%$2)
          ))))
          (lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
            self!
           ) i$
        )))
        :pattern ((lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
           self!
          ) i$
        ))
        :qid user_lib__all_blocks__AllBlocks__lemma_wf_from_nodes_113
        :skolemid skolem_user_lib__all_blocks__AllBlocks__lemma_wf_from_nodes_113
     )))
     (=>
      %%global_location_label%%161
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           self!
     ))))))
     (=>
      %%global_location_label%%162
      (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
   )))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_from_nodes. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_from_nodes._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_from_nodes._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_from_nodes. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.)
 Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_from_nodes. FLLEN&. FLLEN& SLLEN&. SLLEN& self!)
    (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_from_nodes. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_from_nodes._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_from_nodes._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_node_is_wf
(declare-fun req%lib!all_blocks.impl&%0.lemma_node_is_wf. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%163 Bool)
(declare-const %%global_location_label%%164 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (x! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_node_is_wf. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     x!
    ) (and
     (=>
      %%global_location_label%%163
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%164
      (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. x!)
   ))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_node_is_wf. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! x!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_node_is_wf._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_node_is_wf._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_node_is_wf. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (x! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_node_is_wf. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     x!
    ) (lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
     ) (I (lib!all_blocks.impl&%0.get_ptr_internal_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
       (Poly%lib!all_blocks.AllBlocks. self!) (Poly%ptr_mut%<lib!block.BlockHdr.>. x!)
   ))))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_node_is_wf. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! x!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_node_is_wf._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_node_is_wf._definition
)))

;; Function-Specs lib::Tlsf::freelist_nonempty
(declare-fun req%lib!linked_list.impl&%0.freelist_nonempty. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex.
 ) Bool
)
(declare-const %%global_location_label%%165 Bool)
(declare-const %%global_location_label%%166 Bool)
(declare-const %%global_location_label%%167 Bool)
(declare-const %%global_location_label%%168 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (req%lib!linked_list.impl&%0.freelist_nonempty. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     idx!
    ) (and
     (=>
      %%global_location_label%%165
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%166
      (lib!linked_list.impl&%0.freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
       ) (Poly%lib!block_index.BlockIndex. idx!)
     ))
     (=>
      %%global_location_label%%167
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
     )))
     (=>
      %%global_location_label%%168
      (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        )
       ) 0
   ))))
   :pattern ((req%lib!linked_list.impl&%0.freelist_nonempty. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx!
   ))
   :qid internal_req__lib!linked_list.impl&__0.freelist_nonempty._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.freelist_nonempty._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.freelist_nonempty. (Dcr Type Dcr Type lib!Tlsf.
  lib!block_index.BlockIndex.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.freelist_nonempty. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     idx!
    ) (and
     (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           (vstd!view.View.view.? $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&)
            (vstd!seq.Seq.index.? $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&)
             (vstd!view.View.view.? $ (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&.
                SLLEN&
               ) FLLEN&. FLLEN&
              ) (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))))
             ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
                 idx!
            )))))
           ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
               idx!
        )))))))
       ) 0
     ))
     (= (vstd!seq.impl&%0.first.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
        $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
         $ (PTR $ TYPE%lib!block.BlockHdr.)
        ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
          (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
             (Poly%lib!Tlsf. self!)
         ))))
        ) (Poly%lib!block_index.BlockIndex. idx!)
       )
      ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
        (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
         (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
          (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
          (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))))
         ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             idx!
        )))))
       ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
           idx!
     ))))))
     (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
      ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
        (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
         (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
          (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
          (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))))
         ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             idx!
        )))))
       ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
           idx!
   ))))))))
   :pattern ((ens%lib!linked_list.impl&%0.freelist_nonempty. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! idx!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.freelist_nonempty._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.freelist_nonempty._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_node_ptr
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_node_ptr. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  Int
 ) Bool
)
(declare-const %%global_location_label%%169 Bool)
(declare-const %%global_location_label%%170 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_node_ptr. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
    ) (and
     (=>
      %%global_location_label%%169
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        self!
     )))
     (=>
      %%global_location_label%%170
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                self!
         )))))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_node_ptr. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_node_ptr._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_node_ptr._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_node_ptr. (Dcr Type Dcr Type lib!all_blocks.AllBlocks.
  Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.)
   (i! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_node_ptr. FLLEN&. FLLEN& SLLEN&. SLLEN& self!
     i!
    ) (and
     (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
             (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
            )
           ) (I i!)
        )))
       ) 0
     ))
     (<= 0 (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
          (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
            (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
           )
          ) (I i!)
     )))))
     (= (EucMod (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
           (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
             (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. self!))
            )
           ) (I i!)
        )))
       ) lib!block_index.GRANULARITY.?
      ) 0
     )
     (lib!all_blocks.impl&%0.wf_node_ptr.? FLLEN&. FLLEN& SLLEN&. SLLEN& (vstd!seq.Seq.index.?
       $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           self!
        )))
       ) (I i!)
   ))))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_node_ptr. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! i!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_node_ptr._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_node_ptr._definition
)))

;; Function-Specs lib::Tlsf::link_free_block
(declare-fun req%lib!linked_list.impl&%0.link_free_block. (Dcr Type Dcr Type lib!Tlsf.
  Int ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%171 Bool)
(declare-const %%global_location_label%%172 Bool)
(declare-const %%global_location_label%%173 Bool)
(declare-const %%global_location_label%%174 Bool)
(declare-const %%global_location_label%%175 Bool)
(declare-const %%global_location_label%%176 Bool)
(declare-const %%global_location_label%%177 Bool)
(declare-const %%global_location_label%%178 Bool)
(declare-const %%global_location_label%%179 Bool)
(declare-const %%global_location_label%%180 Bool)
(declare-const %%global_location_label%%181 Bool)
(declare-const %%global_location_label%%182 Bool)
(declare-const %%global_location_label%%183 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (size! Int) (node! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!linked_list.impl&%0.link_free_block. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     size! node!
    ) (and
     (=>
      %%global_location_label%%171
      (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     )
     (=>
      %%global_location_label%%172
      (>= size! lib!parameters.GRANULARITY.?)
     )
     (=>
      %%global_location_label%%173
      (= (EucMod size! lib!parameters.GRANULARITY.?) 0)
     )
     (=>
      %%global_location_label%%174
      (lib!block_index.impl&%7.valid_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN& (I size!))
     )
     (=>
      %%global_location_label%%175
      (= (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
          $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
            (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
              (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
               (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                 (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                   $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                    (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                       (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
                    )))
                   ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
        )))))))))))
       ) size!
     ))
     (=>
      %%global_location_label%%176
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
     )))
     (=>
      %%global_location_label%%177
      (lib!linked_list.impl&%0.all_freelist_wf_weak.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        pre%self!
       ) (vstd!set.Set.insert.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!set.Set.empty.? $
         (PTR $ TYPE%lib!block.BlockHdr.)
        ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
     )))
     (=>
      %%global_location_label%%178
      (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. pre%self!))
     )
     (=>
      %%global_location_label%%179
      (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. pre%self!))
     )
     (=>
      %%global_location_label%%180
      (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        pre%self!
     )))
     (=>
      %%global_location_label%%181
      (not (lib!all_blocks.impl&%1.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
         (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
        ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
     )))
     (=>
      %%global_location_label%%182
      (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
     ))
     (=>
      %%global_location_label%%183
      (lib!block.impl&%1.is_free.? (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr.
        (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
           (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
              $ TYPE%lib!block.BlockHdr.
             ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
               (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                 $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                  (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                     (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
                  )))
                 ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
   ))))))))))))))
   :pattern ((req%lib!linked_list.impl&%0.link_free_block. FLLEN&. FLLEN& SLLEN&. SLLEN&
     pre%self! size! node!
   ))
   :qid internal_req__lib!linked_list.impl&__0.link_free_block._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.link_free_block._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.link_free_block. (Dcr Type Dcr Type lib!Tlsf.
  lib!Tlsf. Int ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (self! lib!Tlsf.) (size! Int) (node! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.link_free_block. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     self! size! node!
    ) (and
     (has_type (Poly%lib!Tlsf. self!) (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
     ))
     (= (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
         (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
       ))
      ) (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
         (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
     ))))
     (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
       $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
        (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
       ))))
      ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
     )
     (= (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
          (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
          )))
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
       ))
      ) (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
          (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
          )))
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
     ))))
     (= (lib!block.BlockPerm./BlockPerm/mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
          (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
          )))
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
       ))
      ) (lib!block.BlockPerm./BlockPerm/mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
          (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
          )))
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. node!)
     ))))
     (forall ((p$ Poly)) (!
       (=>
        (has_type p$ (PTR $ TYPE%lib!block.BlockHdr.))
        (=>
         (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
            (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
               (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
           ))))
          ) p$
         )
         (and
          (and
           (and
            (and
             (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
               $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
               ))))
              ) p$
             )
             (= (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
                 $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                  (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                     (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                  )))
                 ) p$
               ))
              ) (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
                 $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                  (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                     (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
                  )))
                 ) p$
            )))))
            (= (lib!block.BlockPerm./BlockPerm/mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
                $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                    (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                 )))
                ) p$
              ))
             ) (lib!block.BlockPerm./BlockPerm/mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
                $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                 (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                    (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
                 )))
                ) p$
           )))))
           (= (lib!block.BlockPerm./BlockPerm/overhead_mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
               $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                )))
               ) p$
             ))
            ) (lib!block.BlockPerm./BlockPerm/overhead_mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
               $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
                )))
               ) p$
          )))))
          (= (lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
              $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
               )))
              ) p$
            ))
           ) (lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
              $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
               )))
              ) p$
       )))))))
       :pattern ((vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
           (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!)))
          ))))
         ) p$
       ))
       :pattern ((vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
           (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
          ))))
         ) p$
       ))
       :qid user_lib__Tlsf__link_free_block_114
       :skolemid skolem_user_lib__Tlsf__link_free_block_114
     ))
     (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
       self!
     ))
     (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     (lib!linked_list.impl&%0.size_class_condition.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
       self!
     ))
     (let
      ((idx$ (lib!mapping.impl&%0.map_floor_spec.? FLLEN&. FLLEN& SLLEN&. SLLEN& (I size!))))
      (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
         SLLEN&
        ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
         (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
            (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
         )))
        ) (Poly%lib!block_index.BlockIndex. idx$)
       ) (vstd!seq.Seq.add.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!seq.Seq.push.? $ (PTR
          $ TYPE%lib!block.BlockHdr.
         ) (vstd!seq.Seq.empty.? $ (PTR $ TYPE%lib!block.BlockHdr.)) (Poly%ptr_mut%<lib!block.BlockHdr.>.
          node!
         )
        ) (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
          SLLEN&
         ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
          (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
             (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
          )))
         ) (Poly%lib!block_index.BlockIndex. idx$)
     ))))
     (forall ((bi$ Poly)) (!
       (=>
        (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (=>
         (and
          (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
          (not (= (%Poly%lib!block_index.BlockIndex. bi$) (lib!mapping.impl&%0.map_floor_spec.?
             FLLEN&. FLLEN& SLLEN&. SLLEN& (I size!)
         ))))
         (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
            SLLEN&
           ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
            (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
               (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
            )))
           ) bi$
          ) (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
            SLLEN&
           ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
            (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
               (%Poly%lib!Tlsf. (Poly%lib!Tlsf. pre%self!))
            )))
           ) bi$
       ))))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
       :qid user_lib__Tlsf__link_free_block_115
       :skolemid skolem_user_lib__Tlsf__link_free_block_115
   ))))
   :pattern ((ens%lib!linked_list.impl&%0.link_free_block. FLLEN&. FLLEN& SLLEN&. SLLEN&
     pre%self! self! size! node!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.link_free_block._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.link_free_block._definition
)))

;; Function-Specs lib::Tlsf::lemma_freelist_len_gt1_from_nonnull_next
(declare-fun req%lib!linked_list.impl&%0.lemma_freelist_len_gt1_from_nonnull_next.
 (Dcr Type Dcr Type lib!Tlsf. lib!block_index.BlockIndex.) Bool
)
(declare-const %%global_location_label%%184 Bool)
(declare-const %%global_location_label%%185 Bool)
(declare-const %%global_location_label%%186 Bool)
(declare-const %%global_location_label%%187 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_freelist_len_gt1_from_nonnull_next. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! idx!
    ) (and
     (=>
      %%global_location_label%%184
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%185
      (>= (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        )
       ) 1
     ))
     (=>
      %%global_location_label%%186
      (lib!linked_list.impl&%0.wf_free_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
       ) (Poly%lib!block_index.BlockIndex. idx!) (I 0)
     ))
     (=>
      %%global_location_label%%187
      (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free
             (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.FreeLink.
               (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                  (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                     $ TYPE%lib!block.FreeLink.
                    ) (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                     (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                        (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                          $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                           (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                              (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                           )))
                          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                            $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                             $ (PTR $ TYPE%lib!block.BlockHdr.)
                            ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                              (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                                 (Poly%lib!Tlsf. self!)
                             ))))
                            ) (Poly%lib!block_index.BlockIndex. idx!)
                           ) (I 0)
         ))))))))))))))))))
        ) 0
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_freelist_len_gt1_from_nonnull_next. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! idx!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_freelist_len_gt1_from_nonnull_next._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_freelist_len_gt1_from_nonnull_next._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_freelist_len_gt1_from_nonnull_next.
 (Dcr Type Dcr Type lib!Tlsf. lib!block_index.BlockIndex.) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_freelist_len_gt1_from_nonnull_next. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! idx!
    ) (>= (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
       $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
        $ (PTR $ TYPE%lib!block.BlockHdr.)
       ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
         (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
            (Poly%lib!Tlsf. self!)
        ))))
       ) (Poly%lib!block_index.BlockIndex. idx!)
      )
     ) 2
   ))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_freelist_len_gt1_from_nonnull_next. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! idx!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_freelist_len_gt1_from_nonnull_next._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_freelist_len_gt1_from_nonnull_next._definition
)))

;; Function-Specs lib::Tlsf::lemma_wf_free_node_next_addr
(declare-fun req%lib!linked_list.impl&%0.lemma_wf_free_node_next_addr. (Dcr Type Dcr
  Type lib!Tlsf. lib!block_index.BlockIndex. Int
 ) Bool
)
(declare-const %%global_location_label%%188 Bool)
(declare-const %%global_location_label%%189 Bool)
(declare-const %%global_location_label%%190 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (n! Int)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_wf_free_node_next_addr. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! idx! n!
    ) (and
     (=>
      %%global_location_label%%188
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%189
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 n!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  (Poly%lib!Tlsf. self!)
              ))))
             ) (Poly%lib!block_index.BlockIndex. idx!)
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%190
      (lib!linked_list.impl&%0.wf_free_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
       ) (Poly%lib!block_index.BlockIndex. idx!) (I n!)
   ))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_wf_free_node_next_addr. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! idx! n!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_wf_free_node_next_addr._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_wf_free_node_next_addr._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_wf_free_node_next_addr. (Dcr Type Dcr
  Type lib!Tlsf. lib!block_index.BlockIndex. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (idx! lib!block_index.BlockIndex.) (n! Int)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_wf_free_node_next_addr. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! idx! n!
    ) (and
     (=>
      (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free
             (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.FreeLink.
               (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                  (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                     $ TYPE%lib!block.FreeLink.
                    ) (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                     (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                        (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                          $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                           (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                              (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                           )))
                          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                            $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                             $ (PTR $ TYPE%lib!block.BlockHdr.)
                            ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                              (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                                 (Poly%lib!Tlsf. self!)
                             ))))
                            ) (Poly%lib!block_index.BlockIndex. idx!)
                           ) (I n!)
         ))))))))))))))))))
        ) 0
      ))
      (= (core!option.Option./Some (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free
          (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.FreeLink.
            (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
               (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                  $ TYPE%lib!block.FreeLink.
                 ) (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                  (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                     (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                       $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                        (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                           (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                        )))
                       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                          $ (PTR $ TYPE%lib!block.BlockHdr.)
                         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                              (Poly%lib!Tlsf. self!)
                          ))))
                         ) (Poly%lib!block_index.BlockIndex. idx!)
                        ) (I n!)
        ))))))))))))))))
       ) (lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN& SLLEN&. SLLEN& (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        ) (I n!)
     )))
     (=>
      (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/next_free
            (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.FreeLink.
              (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                 (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                    $ TYPE%lib!block.FreeLink.
                   ) (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                    (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                       (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                         $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                          (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                             (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                          )))
                         ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                           $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                            $ (PTR $ TYPE%lib!block.BlockHdr.)
                           ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                             (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                                (Poly%lib!Tlsf. self!)
                            ))))
                           ) (Poly%lib!block_index.BlockIndex. idx!)
                          ) (I n!)
        ))))))))))))))))))
       ) 0
      )
      (is-core!option.Option./None (lib!linked_list.impl&%0.free_next_of.? FLLEN&. FLLEN&
        SLLEN&. SLLEN& (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&.
          FLLEN& SLLEN&. SLLEN&
         ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
          (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
             (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
          )))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        ) (I n!)
   )))))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_wf_free_node_next_addr. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! idx! n!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_wf_free_node_next_addr._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_wf_free_node_next_addr._definition
)))

;; Function-Specs lib::ordered_pointer_list::lemma_add_ghost_pointer_insert_after_index
(declare-fun req%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index.
 (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. ptr_mut%<lib!block.BlockHdr.>. Int)
 Bool
)
(declare-const %%global_location_label%%191 Bool)
(declare-const %%global_location_label%%192 Bool)
(declare-const %%global_location_label%%193 Bool)
(declare-const %%global_location_label%%194 Bool)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.)
   (ins! Int)
  ) (!
   (= (req%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index. ls! p!
     ins!
    ) (and
     (=>
      %%global_location_label%%191
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        ls!
     )))
     (=>
      %%global_location_label%%192
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 ins!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%193
      (< (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           ls!
          ) (I ins!)
        ))
       ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
          p!
     )))))
     (=>
      %%global_location_label%%194
      (=>
       (< (Add ins! 1) (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
       )))
       (<= (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
           p!
         ))
        ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            ls!
           ) (I (Add ins! 1))
   ))))))))
   :pattern ((req%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index.
     ls! p! ins!
   ))
   :qid internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index._definition
)))
(declare-fun ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index.
 (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. ptr_mut%<lib!block.BlockHdr.>. Int)
 Bool
)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.)
   (ins! Int)
  ) (!
   (= (ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index. ls! p!
     ins!
    ) (and
     (= (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
       ))
      ) (nClip (Add (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
         )
        ) 1
     )))
     (forall ((k$ Poly)) (!
       (=>
        (has_type k$ INT)
        (=>
         (let
          ((tmp%%$ 0))
          (let
           ((tmp%%$1 (%I k$)))
           (let
            ((tmp%%$2 ins!))
            (and
             (<= tmp%%$ tmp%%$1)
             (<= tmp%%$1 tmp%%$2)
         ))))
         (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
              ls!
             ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
            )
           ) k$
          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            ls!
           ) k$
       ))))
       :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
         ) k$
       ))
       :qid user_lib__ordered_pointer_list__lemma_add_ghost_pointer_insert_after_index_116
       :skolemid skolem_user_lib__ordered_pointer_list__lemma_add_ghost_pointer_insert_after_index_116
     ))
     (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!ordered_pointer_list.add_ghost_pointer.?
          (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. ls!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
           p!
         ))
        ) (I (Add ins! 1))
       )
      ) p!
     )
     (forall ((k$ Poly)) (!
       (=>
        (has_type k$ INT)
        (=>
         (let
          ((tmp%%$ (Add ins! 1)))
          (let
           ((tmp%%$1 (%I k$)))
           (let
            ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                  ls!
                 ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
            )))))
            (and
             (< tmp%%$ tmp%%$1)
             (< tmp%%$1 tmp%%$2)
         ))))
         (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
              ls!
             ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
            )
           ) k$
          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            ls!
           ) (I (Sub (%I k$) 1))
       ))))
       :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            ls!
           ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
          )
         ) k$
       ))
       :qid user_lib__ordered_pointer_list__lemma_add_ghost_pointer_insert_after_index_117
       :skolemid skolem_user_lib__ordered_pointer_list__lemma_add_ghost_pointer_insert_after_index_117
   ))))
   :pattern ((ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index.
     ls! p! ins!
   ))
   :qid internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index._definition
   :skolemid skolem_internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_after_index._definition
)))

;; Function-Specs lib::Tlsf::lemma_ii_shift_after_insert_ensures
(declare-fun req%lib!linked_list.impl&%0.lemma_ii_shift_after_insert_ensures. (Dcr
  Type Dcr Type lib!all_blocks.ShadowFreelist. vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  Int ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%195 Bool)
(declare-const %%global_location_label%%196 Bool)
(declare-const %%global_location_label%%197 Bool)
(declare-const %%global_location_label%%198 Bool)
(declare-const %%global_location_label%%199 Bool)
(declare-const %%global_location_label%%200 Bool)
(declare-const %%global_location_label%%201 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sfl! lib!all_blocks.ShadowFreelist.)
   (old_ptrs! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (insert_ai! Int) (new_ptr!
    ptr_mut%<lib!block.BlockHdr.>.
   )
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_ii_shift_after_insert_ensures. FLLEN&. FLLEN&
     SLLEN&. SLLEN& sfl! old_ptrs! insert_ai! new_ptr!
    ) (and
     (=>
      %%global_location_label%%195
      (lib!ordered_pointer_list.ptrs_no_duplicates.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        old_ptrs!
     )))
     (=>
      %%global_location_label%%196
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        old_ptrs!
     )))
     (=>
      %%global_location_label%%197
      (lib!all_blocks.impl&%1.shadow_freelist_has_all_wf_index.? FLLEN&. FLLEN& SLLEN&.
       SLLEN& (Poly%lib!all_blocks.ShadowFreelist. sfl!)
     ))
     (=>
      %%global_location_label%%198
      (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
        sfl!
       ) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. old_ptrs!)
     ))
     (=>
      %%global_location_label%%199
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 insert_ai!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             old_ptrs!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%200
      (< (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           old_ptrs!
          ) (I insert_ai!)
        ))
       ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
          new_ptr!
     )))))
     (=>
      %%global_location_label%%201
      (=>
       (< (Add insert_ai! 1) (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          old_ptrs!
       )))
       (<= (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
           new_ptr!
         ))
        ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            old_ptrs!
           ) (I (Add insert_ai! 1))
   ))))))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_ii_shift_after_insert_ensures. FLLEN&.
     FLLEN& SLLEN&. SLLEN& sfl! old_ptrs! insert_ai! new_ptr!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_ii_shift_after_insert_ensures._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_ii_shift_after_insert_ensures._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_ii_shift_after_insert_ensures. (Dcr
  Type Dcr Type lib!all_blocks.ShadowFreelist. vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  Int ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sfl! lib!all_blocks.ShadowFreelist.)
   (old_ptrs! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (insert_ai! Int) (new_ptr!
    ptr_mut%<lib!block.BlockHdr.>.
   )
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_ii_shift_after_insert_ensures. FLLEN&. FLLEN&
     SLLEN&. SLLEN& sfl! old_ptrs! insert_ai! new_ptr!
    ) (lib!all_blocks.is_identity_injection.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
      (lib!all_blocks.impl&%1.ii_shift_after_insert.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.ShadowFreelist.
        sfl!
       ) (I insert_ai!)
      )
     ) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!ordered_pointer_list.add_ghost_pointer.?
       (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. old_ptrs!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
        new_ptr!
   )))))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_ii_shift_after_insert_ensures. FLLEN&.
     FLLEN& SLLEN&. SLLEN& sfl! old_ptrs! insert_ai! new_ptr!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_ii_shift_after_insert_ensures._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_ii_shift_after_insert_ensures._definition
)))

;; Function-Specs lib::Tlsf::lemma_all_freelist_wf_perms_frame
(declare-fun req%lib!linked_list.impl&%0.lemma_all_freelist_wf_perms_frame. (Dcr Type
  Dcr Type lib!Tlsf. lib!Tlsf.
 ) Bool
)
(declare-const %%global_location_label%%202 Bool)
(declare-const %%global_location_label%%203 Bool)
(declare-const %%global_location_label%%204 Bool)
(declare-const %%global_location_label%%205 Bool)
(declare-const %%global_location_label%%206 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_all_freelist_wf_perms_frame. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self!
    ) (and
     (=>
      %%global_location_label%%202
      (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%203
      (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        new_self!
     )))
     (=>
      %%global_location_label%%204
      (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (
        lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%205
      (forall ((bi$ Poly)) (!
        (=>
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (=>
          (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
          (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
             (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
              (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
               (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
               (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))))
              ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. bi$)))
             )
            ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. bi$)))
           ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
             (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
              (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
               (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
               (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))))
              ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. bi$)))
             )
            ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. bi$)))
        ))))
        :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
        :qid user_lib__Tlsf__lemma_all_freelist_wf_perms_frame_118
        :skolemid skolem_user_lib__Tlsf__lemma_all_freelist_wf_perms_frame_118
     )))
     (=>
      %%global_location_label%%206
      (forall ((bi$ Poly) (n$ Poly)) (!
        (=>
         (and
          (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
          (has_type n$ INT)
         )
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I n$)))
             (let
              ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                  $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                   $ (PTR $ TYPE%lib!block.BlockHdr.)
                  ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                    (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                       (Poly%lib!Tlsf. old_self!)
                   ))))
                  ) bi$
              ))))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
          )))))
          (= (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                 (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
             ))))
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                   (Poly%lib!Tlsf. old_self!)
               ))))
              ) bi$
             ) n$
            )
           ) (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                 (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
             ))))
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                   (Poly%lib!Tlsf. old_self!)
               ))))
              ) bi$
             ) n$
        )))))
        :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
           $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
            $ (PTR $ TYPE%lib!block.BlockHdr.)
           ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
             (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                (Poly%lib!Tlsf. old_self!)
            ))))
           ) bi$
          ) n$
        ))
        :qid user_lib__Tlsf__lemma_all_freelist_wf_perms_frame_119
        :skolemid skolem_user_lib__Tlsf__lemma_all_freelist_wf_perms_frame_119
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_all_freelist_wf_perms_frame. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_all_freelist_wf_perms_frame._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_all_freelist_wf_perms_frame._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_all_freelist_wf_perms_frame. (Dcr Type
  Dcr Type lib!Tlsf. lib!Tlsf.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_all_freelist_wf_perms_frame. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self!
    ) (and
     (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
       new_self!
     ))
     (forall ((bi$ Poly)) (!
       (=>
        (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (=>
         (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
         (lib!linked_list.impl&%0.freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
           new_self!
          ) bi$
       )))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
       :qid user_lib__Tlsf__lemma_all_freelist_wf_perms_frame_120
       :skolemid skolem_user_lib__Tlsf__lemma_all_freelist_wf_perms_frame_120
   ))))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_all_freelist_wf_perms_frame. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_all_freelist_wf_perms_frame._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_all_freelist_wf_perms_frame._definition
)))

;; Function-Specs lib::Tlsf::lemma_pop_head_preserves_wf
(declare-fun req%lib!linked_list.impl&%0.lemma_pop_head_preserves_wf. (Dcr Type Dcr
  Type lib!Tlsf. lib!Tlsf. lib!block_index.BlockIndex. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%207 Bool)
(declare-const %%global_location_label%%208 Bool)
(declare-const %%global_location_label%%209 Bool)
(declare-const %%global_location_label%%210 Bool)
(declare-const %%global_location_label%%211 Bool)
(declare-const %%global_location_label%%212 Bool)
(declare-const %%global_location_label%%213 Bool)
(declare-const %%global_location_label%%214 Bool)
(declare-const %%global_location_label%%215 Bool)
(declare-const %%global_location_label%%216 Bool)
(declare-const %%global_location_label%%217 Bool)
(declare-const %%global_location_label%%218 Bool)
(declare-const %%global_location_label%%219 Bool)
(declare-const %%global_location_label%%220 Bool)
(declare-const %%global_location_label%%221 Bool)
(declare-const %%global_location_label%%222 Bool)
(declare-const %%global_location_label%%223 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.) (next_free! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!linked_list.impl&%0.lemma_pop_head_preserves_wf. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self! idx! next_free!
    ) (and
     (=>
      %%global_location_label%%207
      (lib!linked_list.impl&%0.all_freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        old_self!
     )))
     (=>
      %%global_location_label%%208
      (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. old_self!))
     )
     (=>
      %%global_location_label%%209
      (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
        idx!
     )))
     (=>
      %%global_location_label%%210
      (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. old_self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        )
       ) 0
     ))
     (=>
      %%global_location_label%%211
      (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
         SLLEN&
        ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
         (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
            (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
         )))
        ) (Poly%lib!block_index.BlockIndex. idx!)
       ) (vstd!seq_lib.impl&%0.remove.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
         $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
          $ (PTR $ TYPE%lib!block.BlockHdr.)
         ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
           (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
              (Poly%lib!Tlsf. old_self!)
          ))))
         ) (Poly%lib!block_index.BlockIndex. idx!)
        ) (I 0)
     )))
     (=>
      %%global_location_label%%212
      (forall ((bi$ Poly)) (!
        (=>
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (not (= (%Poly%lib!block_index.BlockIndex. bi$) idx!))
          )
          (= (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
             SLLEN&
            ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
             (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
                (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
             )))
            ) bi$
           ) (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
             SLLEN&
            ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
             (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
                (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
             )))
            ) bi$
        ))))
        :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
        :qid user_lib__Tlsf__lemma_pop_head_preserves_wf_121
        :skolemid skolem_user_lib__Tlsf__lemma_pop_head_preserves_wf_121
     )))
     (=>
      %%global_location_label%%213
      (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
         (vstd!view.View.view.? $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&)
          (vstd!seq.Seq.index.? $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&)
           (vstd!view.View.view.? $ (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&.
              SLLEN&
             ) FLLEN&. FLLEN&
            ) (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))))
           ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
               idx!
          )))))
         ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             idx!
        )))))
       ) next_free!
     ))
     (=>
      %%global_location_label%%214
      (forall ((bi$ Poly)) (!
        (=>
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (not (= (%Poly%lib!block_index.BlockIndex. bi$) idx!))
          )
          (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
             (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
              (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
               (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
               (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))))
              ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. bi$)))
             )
            ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. bi$)))
           ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!view.View.view.? $
             (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!seq.Seq.index.? $
              (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) (vstd!view.View.view.? $
               (ARRAY $ (ARRAY $ (PTR $ TYPE%lib!block.BlockHdr.) SLLEN&. SLLEN&) FLLEN&. FLLEN&)
               (Poly%array%. (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))))
              ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. bi$)))
             )
            ) (I (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex. bi$)))
        ))))
        :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
        :qid user_lib__Tlsf__lemma_pop_head_preserves_wf_122
        :skolemid skolem_user_lib__Tlsf__lemma_pop_head_preserves_wf_122
     )))
     (=>
      %%global_location_label%%215
      (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        new_self!
     )))
     (=>
      %%global_location_label%%216
      (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
     )))
     (=>
      %%global_location_label%%217
      (forall ((bi$ Poly) (n$ Poly)) (!
        (=>
         (and
          (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
          (has_type n$ INT)
         )
         (=>
          (and
           (and
            (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
            (not (= (%Poly%lib!block_index.BlockIndex. bi$) idx!))
           )
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I n$)))
             (let
              ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                  $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                   $ (PTR $ TYPE%lib!block.BlockHdr.)
                  ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                    (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                       (Poly%lib!Tlsf. old_self!)
                   ))))
                  ) bi$
              ))))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
          )))))
          (= (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                 (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
             ))))
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                   (Poly%lib!Tlsf. old_self!)
               ))))
              ) bi$
             ) n$
            )
           ) (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                 (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
             ))))
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                   (Poly%lib!Tlsf. old_self!)
               ))))
              ) bi$
             ) n$
        )))))
        :pattern ((vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
          (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
            (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
               (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
           ))))
          ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
            $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
             $ (PTR $ TYPE%lib!block.BlockHdr.)
            ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
              (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                 (Poly%lib!Tlsf. old_self!)
             ))))
            ) bi$
           ) n$
        )))
        :qid user_lib__Tlsf__lemma_pop_head_preserves_wf_123
        :skolemid skolem_user_lib__Tlsf__lemma_pop_head_preserves_wf_123
     )))
     (=>
      %%global_location_label%%218
      (forall ((n$ Poly)) (!
        (=>
         (has_type n$ INT)
         (=>
          (let
           ((tmp%%$ 1))
           (let
            ((tmp%%$1 (%I n$)))
            (let
             ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
                 $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
                  $ (PTR $ TYPE%lib!block.BlockHdr.)
                 ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                   (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                      (Poly%lib!Tlsf. old_self!)
                  ))))
                 ) (Poly%lib!block_index.BlockIndex. idx!)
             ))))
             (and
              (< tmp%%$ tmp%%$1)
              (< tmp%%$1 tmp%%$2)
          ))))
          (= (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                 (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
             ))))
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                   (Poly%lib!Tlsf. old_self!)
               ))))
              ) (Poly%lib!block_index.BlockIndex. idx!)
             ) n$
            )
           ) (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm.
            (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (lib!all_blocks.AllBlocks./AllBlocks/perms
              (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. (lib!Tlsf./Tlsf/all_blocks
                 (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
             ))))
            ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
              $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
               $ (PTR $ TYPE%lib!block.BlockHdr.)
              ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
                (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                   (Poly%lib!Tlsf. old_self!)
               ))))
              ) (Poly%lib!block_index.BlockIndex. idx!)
             ) n$
        )))))
        :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
           $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
            $ (PTR $ TYPE%lib!block.BlockHdr.)
           ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
             (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                (Poly%lib!Tlsf. old_self!)
            ))))
           ) (Poly%lib!block_index.BlockIndex. idx!)
          ) n$
        ))
        :qid user_lib__Tlsf__lemma_pop_head_preserves_wf_124
        :skolemid skolem_user_lib__Tlsf__lemma_pop_head_preserves_wf_124
     )))
     (=>
      %%global_location_label%%219
      (=>
       (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
          $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
           $ (PTR $ TYPE%lib!block.BlockHdr.)
          ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
            (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
               (Poly%lib!Tlsf. old_self!)
           ))))
          ) (Poly%lib!block_index.BlockIndex. idx!)
         )
        ) 1
       )
       (and
        (and
         (and
          (and
           (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
              (vstd!map.impl&%0.index.? $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&.
                SLLEN&
               ) $ (TYPE%vstd!seq.Seq. $ (PTR $ TYPE%lib!block.BlockHdr.)) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m
                (%Poly%lib!all_blocks.ShadowFreelist. (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist
                   (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
                )))
               ) (Poly%lib!block_index.BlockIndex. idx!)
              ) (I 1)
             )
            ) next_free!
           )
           (= (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
               $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
                )))
               ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
             ))
            ) (lib!block.BlockPerm./BlockPerm/points_to (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
               $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                   (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
                )))
               ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
          )))))
          (= (lib!block.BlockPerm./BlockPerm/mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
              $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
               )))
              ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
            ))
           ) (lib!block.BlockPerm./BlockPerm/mem (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.?
              $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
               (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                  (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
               )))
              ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
         )))))
         (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
             $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. (lib!block.FreeLink./FreeLink/prev_free
               (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.FreeLink.
                 (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                    (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                       $ TYPE%lib!block.FreeLink.
                      ) (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                       (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                          (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                            $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                             (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                                (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
                             )))
                            ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
           )))))))))))))))))
          ) 0
        ))
        (= (lib!block.FreeLink./FreeLink/next_free (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0
            $ TYPE%lib!block.FreeLink. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
              (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                 (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                  (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                     (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                       $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                        (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                           (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
                        )))
                       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
          )))))))))))))
         ) (lib!block.FreeLink./FreeLink/next_free (%Poly%lib!block.FreeLink. (vstd!raw_ptr.MemContents./Init/0
            $ TYPE%lib!block.FreeLink. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
              (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                 (core!option.Option./Some/0 $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.FreeLink.)
                  (%Poly%core!option.Option. (Poly%core!option.Option. (lib!block.BlockPerm./BlockPerm/free_link_perm
                     (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                       $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                        (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                           (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
                        )))
                       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
     ))))))))))))))))))
     (=>
      %%global_location_label%%220
      (=>
       (= (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
          $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
           $ (PTR $ TYPE%lib!block.BlockHdr.)
          ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
            (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
               (Poly%lib!Tlsf. old_self!)
           ))))
          ) (Poly%lib!block_index.BlockIndex. idx!)
         )
        ) 1
       )
       (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
         ))
        ) 0
     )))
     (=>
      %%global_location_label%%221
      (=>
       (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
         ))
        ) 0
       )
       (not (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (
                  vstd!view.View.view.? $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap
                    (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))
                  ))
                 ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
                     idx!
               ))))))
              ) (I (uClip SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
                  (Poly%lib!block_index.BlockIndex. idx!)
          ))))))))
         ) 1
     ))))
     (=>
      %%global_location_label%%222
      (=>
       (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
            $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_free!)
          ))
         ) 0
       ))
       (= (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.? $ (ARRAY $ USIZE FLLEN&. FLLEN&)
          (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))))
         ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             idx!
         ))))
        ) (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.? $ (ARRAY $ USIZE FLLEN&. FLLEN&)
          (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))))
         ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. (Poly%lib!block_index.BlockIndex.
             idx!
     ))))))))
     (=>
      %%global_location_label%%223
      (forall ((bi$ Poly)) (!
        (=>
         (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
         (=>
          (and
           (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
           (not (= (%Poly%lib!block_index.BlockIndex. bi$) idx!))
          )
          (= (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.?
                     $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf.
                        (Poly%lib!Tlsf. new_self!)
                     )))
                    ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. bi$)))
                  ))
                 ) (I (uClip SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
                     bi$
             ))))))))
            ) 1
           ) (= (uClip SZ (bitand (I 1) (I (uClip SZ (bitshr (I (%I (vstd!seq.Seq.index.? $ USIZE (vstd!view.View.view.?
                     $ (ARRAY $ USIZE FLLEN&. FLLEN&) (Poly%array%. (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf.
                        (Poly%lib!Tlsf. old_self!)
                     )))
                    ) (I (lib!block_index.BlockIndex./BlockIndex/0 (%Poly%lib!block_index.BlockIndex. bi$)))
                  ))
                 ) (I (uClip SZ (lib!block_index.BlockIndex./BlockIndex/1 (%Poly%lib!block_index.BlockIndex.
                     bi$
             ))))))))
            ) 1
        ))))
        :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
        :qid user_lib__Tlsf__lemma_pop_head_preserves_wf_125
        :skolemid skolem_user_lib__Tlsf__lemma_pop_head_preserves_wf_125
   )))))
   :pattern ((req%lib!linked_list.impl&%0.lemma_pop_head_preserves_wf. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self! idx! next_free!
   ))
   :qid internal_req__lib!linked_list.impl&__0.lemma_pop_head_preserves_wf._definition
   :skolemid skolem_internal_req__lib!linked_list.impl&__0.lemma_pop_head_preserves_wf._definition
)))
(declare-fun ens%lib!linked_list.impl&%0.lemma_pop_head_preserves_wf. (Dcr Type Dcr
  Type lib!Tlsf. lib!Tlsf. lib!block_index.BlockIndex. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.) (idx! lib!block_index.BlockIndex.) (next_free! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!linked_list.impl&%0.lemma_pop_head_preserves_wf. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_self! new_self! idx! next_free!
    ) (and
     (lib!linked_list.impl&%0.wf_shadow.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
       new_self!
     ))
     (forall ((bi$ Poly)) (!
       (=>
        (has_type bi$ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&))
        (=>
         (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$)
         (lib!linked_list.impl&%0.freelist_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
           new_self!
          ) bi$
       )))
       :pattern ((lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& bi$))
       :qid user_lib__Tlsf__lemma_pop_head_preserves_wf_126
       :skolemid skolem_user_lib__Tlsf__lemma_pop_head_preserves_wf_126
     ))
     (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. new_self!))
   ))
   :pattern ((ens%lib!linked_list.impl&%0.lemma_pop_head_preserves_wf. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self! idx! next_free!
   ))
   :qid internal_ens__lib!linked_list.impl&__0.lemma_pop_head_preserves_wf._definition
   :skolemid skolem_internal_ens__lib!linked_list.impl&__0.lemma_pop_head_preserves_wf._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_phys_next_matches_intro
(declare-fun req%lib!all_blocks.impl&%0.lemma_phys_next_matches_intro. (Dcr Type Dcr
  Type ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.BlockHdr.>. Int
 ) Bool
)
(declare-const %%global_location_label%%224 Bool)
(declare-const %%global_location_label%%225 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (next_ptr! ptr_mut%<lib!block.BlockHdr.>.)
   (cur_ptr! ptr_mut%<lib!block.BlockHdr.>.) (size! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_phys_next_matches_intro. FLLEN&. FLLEN& SLLEN&.
     SLLEN& next_ptr! cur_ptr! size!
    ) (and
     (=>
      %%global_location_label%%224
      (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_ptr!)
        ))
       ) (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. cur_ptr!)
         ))
        ) (uClip SZ (bitand (I size!) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)))
     )))
     (=>
      %%global_location_label%%225
      (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_ptr!)
        ))
       ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. cur_ptr!)
   )))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_phys_next_matches_intro. FLLEN&. FLLEN&
     SLLEN&. SLLEN& next_ptr! cur_ptr! size!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_phys_next_matches_intro._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_phys_next_matches_intro._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_phys_next_matches_intro. (Dcr Type Dcr
  Type ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.BlockHdr.>. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (next_ptr! ptr_mut%<lib!block.BlockHdr.>.)
   (cur_ptr! ptr_mut%<lib!block.BlockHdr.>.) (size! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_phys_next_matches_intro. FLLEN&. FLLEN& SLLEN&.
     SLLEN& next_ptr! cur_ptr! size!
    ) (lib!all_blocks.impl&%0.phys_next_matches.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%ptr_mut%<lib!block.BlockHdr.>.
      next_ptr!
     ) (Poly%ptr_mut%<lib!block.BlockHdr.>. cur_ptr!) (I size!)
   ))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_phys_next_matches_intro. FLLEN&. FLLEN&
     SLLEN&. SLLEN& next_ptr! cur_ptr! size!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_phys_next_matches_intro._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_phys_next_matches_intro._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_phys_next_matches_elim
(declare-fun req%lib!all_blocks.impl&%0.lemma_phys_next_matches_elim. (Dcr Type Dcr
  Type ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.BlockHdr.>. Int
 ) Bool
)
(declare-const %%global_location_label%%226 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (next_ptr! ptr_mut%<lib!block.BlockHdr.>.)
   (cur_ptr! ptr_mut%<lib!block.BlockHdr.>.) (size! Int)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_phys_next_matches_elim. FLLEN&. FLLEN& SLLEN&.
     SLLEN& next_ptr! cur_ptr! size!
    ) (=>
     %%global_location_label%%226
     (lib!all_blocks.impl&%0.phys_next_matches.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%ptr_mut%<lib!block.BlockHdr.>.
       next_ptr!
      ) (Poly%ptr_mut%<lib!block.BlockHdr.>. cur_ptr!) (I size!)
   )))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_phys_next_matches_elim. FLLEN&. FLLEN&
     SLLEN&. SLLEN& next_ptr! cur_ptr! size!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_phys_next_matches_elim._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_phys_next_matches_elim._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_phys_next_matches_elim. (Dcr Type Dcr
  Type ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.BlockHdr.>. Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (next_ptr! ptr_mut%<lib!block.BlockHdr.>.)
   (cur_ptr! ptr_mut%<lib!block.BlockHdr.>.) (size! Int)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_phys_next_matches_elim. FLLEN&. FLLEN& SLLEN&.
     SLLEN& next_ptr! cur_ptr! size!
    ) (and
     (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_ptr!)
       ))
      ) (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. cur_ptr!)
        ))
       ) (uClip SZ (bitand (I size!) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)))
     ))
     (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. next_ptr!)
       ))
      ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. cur_ptr!)
   ))))))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_phys_next_matches_elim. FLLEN&. FLLEN&
     SLLEN&. SLLEN& next_ptr! cur_ptr! size!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_phys_next_matches_elim._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_phys_next_matches_elim._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_wf_node_ptr_from_facts
(declare-fun req%lib!all_blocks.impl&%0.lemma_wf_node_ptr_from_facts. (Dcr Type Dcr
  Type ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%227 Bool)
(declare-const %%global_location_label%%228 Bool)
(declare-const %%global_location_label%%229 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (ptr! ptr_mut%<lib!block.BlockHdr.>.))
  (!
   (= (req%lib!all_blocks.impl&%0.lemma_wf_node_ptr_from_facts. FLLEN&. FLLEN& SLLEN&.
     SLLEN& ptr!
    ) (and
     (=>
      %%global_location_label%%227
      (not (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!)
         ))
        ) 0
     )))
     (=>
      %%global_location_label%%228
      (<= 0 (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!)
     )))))
     (=>
      %%global_location_label%%229
      (= (EucMod (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. ptr!)
         ))
        ) lib!block_index.GRANULARITY.?
       ) 0
   ))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_wf_node_ptr_from_facts. FLLEN&. FLLEN&
     SLLEN&. SLLEN& ptr!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_wf_node_ptr_from_facts._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_wf_node_ptr_from_facts._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_wf_node_ptr_from_facts. (Dcr Type Dcr
  Type ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (ptr! ptr_mut%<lib!block.BlockHdr.>.))
  (!
   (= (ens%lib!all_blocks.impl&%0.lemma_wf_node_ptr_from_facts. FLLEN&. FLLEN& SLLEN&.
     SLLEN& ptr!
    ) (lib!all_blocks.impl&%0.wf_node_ptr.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%ptr_mut%<lib!block.BlockHdr.>.
      ptr!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_wf_node_ptr_from_facts. FLLEN&. FLLEN&
     SLLEN&. SLLEN& ptr!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_wf_node_ptr_from_facts._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_wf_node_ptr_from_facts._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_all_blocks_wf_after_replace_block_perm
(declare-fun req%lib!all_blocks.impl&%0.lemma_all_blocks_wf_after_replace_block_perm.
 (Dcr Type Dcr Type lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks. ptr_mut%<lib!block.BlockHdr.>.
  lib!block.BlockPerm.
 ) Bool
)
(declare-const %%global_location_label%%230 Bool)
(declare-const %%global_location_label%%231 Bool)
(declare-const %%global_location_label%%232 Bool)
(declare-const %%global_location_label%%233 Bool)
(declare-const %%global_location_label%%234 Bool)
(declare-const %%global_location_label%%235 Bool)
(declare-const %%global_location_label%%236 Bool)
(declare-const %%global_location_label%%237 Bool)
(declare-const %%global_location_label%%238 Bool)
(declare-const %%global_location_label%%239 Bool)
(declare-const %%global_location_label%%240 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.) (block! ptr_mut%<lib!block.BlockHdr.>.) (new_perm!
    lib!block.BlockPerm.
   )
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_all_blocks_wf_after_replace_block_perm. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_ab! new_ab! block! new_perm!
    ) (and
     (=>
      %%global_location_label%%230
      (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           old_ab!
        )))
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. block!)
     ))
     (=>
      %%global_location_label%%231
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           old_ab!
     ))))))
     (=>
      %%global_location_label%%232
      (lib!ordered_pointer_list.ptrs_no_duplicates.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           old_ab!
     ))))))
     (=>
      %%global_location_label%%233
      (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        old_ab!
     )))
     (=>
      %%global_location_label%%234
      (forall ((i$ Poly)) (!
        (=>
         (has_type i$ INT)
         (=>
          (and
           (let
            ((tmp%%$ 0))
            (let
             ((tmp%%$1 (%I i$)))
             (let
              ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
                  (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                     old_ab!
              )))))))
              (and
               (<= tmp%%$ tmp%%$1)
               (< tmp%%$1 tmp%%$2)
           ))))
           (not (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
               (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!all_blocks.AllBlocks./AllBlocks/ptrs
                 (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks. old_ab!))
                )
               ) i$
              )
             ) block!
          )))
          (lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
            old_ab!
           ) i$
        )))
        :pattern ((vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
              old_ab!
           )))
          ) i$
        ))
        :qid user_lib__all_blocks__AllBlocks__lemma_all_blocks_wf_after_replace_block_perm_127
        :skolemid skolem_user_lib__all_blocks__AllBlocks__lemma_all_blocks_wf_after_replace_block_perm_127
     )))
     (=>
      %%global_location_label%%235
      (= (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          new_ab!
        ))
       ) (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          old_ab!
     )))))
     (=>
      %%global_location_label%%236
      (= (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
          new_ab!
        ))
       ) (%Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>. (vstd!map.impl&%0.insert.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
          (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
             old_ab!
          )))
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. block!) (Poly%lib!block.BlockPerm. new_perm!)
     ))))
     (=>
      %%global_location_label%%237
      (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!raw_ptr.PointsToData./PointsToData/ptr
         (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
            $ TYPE%lib!block.BlockHdr.
           ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
             (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. new_perm!))
        )))))
       ) block!
     ))
     (=>
      %%global_location_label%%238
      (lib!block.impl&%2.wf.? (Poly%lib!block.BlockPerm. new_perm!))
     )
     (=>
      %%global_location_label%%239
      (not (lib!block.impl&%1.is_free.? (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr.
         (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
            (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
               $ TYPE%lib!block.BlockHdr.
              ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. new_perm!))
     )))))))))))
     (=>
      %%global_location_label%%240
      (lib!all_blocks.impl&%0.wf_node.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        new_ab!
       ) (I (lib!all_blocks.impl&%0.get_ptr_internal_index.? FLLEN&. FLLEN& SLLEN&. SLLEN&
         (Poly%lib!all_blocks.AllBlocks. old_ab!) (Poly%ptr_mut%<lib!block.BlockHdr.>. block!)
   ))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_all_blocks_wf_after_replace_block_perm.
     FLLEN&. FLLEN& SLLEN&. SLLEN& old_ab! new_ab! block! new_perm!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_all_blocks_wf_after_replace_block_perm._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_all_blocks_wf_after_replace_block_perm._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_all_blocks_wf_after_replace_block_perm.
 (Dcr Type Dcr Type lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks. ptr_mut%<lib!block.BlockHdr.>.
  lib!block.BlockPerm.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.) (block! ptr_mut%<lib!block.BlockHdr.>.) (new_perm!
    lib!block.BlockPerm.
   )
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_all_blocks_wf_after_replace_block_perm. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_ab! new_ab! block! new_perm!
    ) (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      new_ab!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_all_blocks_wf_after_replace_block_perm.
     FLLEN&. FLLEN& SLLEN&. SLLEN& old_ab! new_ab! block! new_perm!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_all_blocks_wf_after_replace_block_perm._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_all_blocks_wf_after_replace_block_perm._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_pool_size_bounded
(declare-fun req%lib!all_blocks.impl&%0.lemma_pool_size_bounded. (Dcr Type Dcr Type
  lib!all_blocks.AllBlocks.
 ) Bool
)
(declare-const %%global_location_label%%241 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (req%lib!all_blocks.impl&%0.lemma_pool_size_bounded. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
    ) (=>
     %%global_location_label%%241
     (lib!all_blocks.impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
       self!
   ))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_pool_size_bounded. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded. (Dcr Type Dcr Type
  lib!all_blocks.AllBlocks.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self!
    ) (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_pool_size_bounded_trivial
(declare-fun req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_trivial. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks.
 ) Bool
)
(declare-const %%global_location_label%%242 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_trivial. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self!
    ) (=>
     %%global_location_label%%242
     (< (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
           self!
       ))))
      ) 2
   )))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_trivial. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded_trivial._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded_trivial._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_trivial. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!all_blocks.AllBlocks.))
  (!
   (= (ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_trivial. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self!
    ) (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      self!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_trivial. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded_trivial._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded_trivial._definition
)))

;; Function-Specs lib::all_blocks::AllBlocks::lemma_pool_size_bounded_from_sub
(declare-fun req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_from_sub. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks.
 ) Bool
)
(declare-const %%global_location_label%%243 Bool)
(declare-const %%global_location_label%%244 Bool)
(declare-const %%global_location_label%%245 Bool)
(declare-const %%global_location_label%%246 Bool)
(declare-const %%global_location_label%%247 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.)
  ) (!
   (= (req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_from_sub. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_ab! new_ab!
    ) (and
     (=>
      %%global_location_label%%243
      (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        old_ab!
     )))
     (=>
      %%global_location_label%%244
      (>= (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            old_ab!
        ))))
       ) 2
     ))
     (=>
      %%global_location_label%%245
      (>= (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
        ))))
       ) 2
     ))
     (=>
      %%global_location_label%%246
      (= (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
         )))
        ) (I 0)
       ) (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            old_ab!
         )))
        ) (I 0)
     )))
     (=>
      %%global_location_label%%247
      (= (vstd!seq.Seq.last.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            new_ab!
        ))))
       ) (vstd!seq.Seq.last.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!all_blocks.AllBlocks./AllBlocks/ptrs (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            old_ab!
   )))))))))
   :pattern ((req%lib!all_blocks.impl&%0.lemma_pool_size_bounded_from_sub. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_ab! new_ab!
   ))
   :qid internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded_from_sub._definition
   :skolemid skolem_internal_req__lib!all_blocks.impl&__0.lemma_pool_size_bounded_from_sub._definition
)))
(declare-fun ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_from_sub. (Dcr Type
  Dcr Type lib!all_blocks.AllBlocks. lib!all_blocks.AllBlocks.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_ab! lib!all_blocks.AllBlocks.)
   (new_ab! lib!all_blocks.AllBlocks.)
  ) (!
   (= (ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_from_sub. FLLEN&. FLLEN& SLLEN&.
     SLLEN& old_ab! new_ab!
    ) (lib!all_blocks.impl&%0.pool_size_bounded.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
      new_ab!
   )))
   :pattern ((ens%lib!all_blocks.impl&%0.lemma_pool_size_bounded_from_sub. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_ab! new_ab!
   ))
   :qid internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded_from_sub._definition
   :skolemid skolem_internal_ens__lib!all_blocks.impl&__0.lemma_pool_size_bounded_from_sub._definition
)))

;; Function-Specs lib::ordered_pointer_list::lemma_ghost_pointer_ordered_index
(declare-fun req%lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  Int Int
 ) Bool
)
(declare-const %%global_location_label%%248 Bool)
(declare-const %%global_location_label%%249 Bool)
(declare-const %%global_location_label%%250 Bool)
(declare-const %%global_location_label%%251 Bool)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (i! Int) (j! Int)) (!
   (= (req%lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index. ls! i! j!) (and
     (=>
      %%global_location_label%%248
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        ls!
     )))
     (=>
      %%global_location_label%%249
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 i!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%250
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 j!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%251
      (< i! j!)
   )))
   :pattern ((req%lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index. ls! i! j!))
   :qid internal_req__lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index._definition
)))
(declare-fun ens%lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  Int Int
 ) Bool
)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (i! Int) (j! Int)) (!
   (= (ens%lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index. ls! i! j!) (<=
     (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (I i!)
      ))
     ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (I j!)
   )))))
   :pattern ((ens%lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index. ls! i! j!))
   :qid internal_ens__lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index._definition
   :skolemid skolem_internal_ens__lib!ordered_pointer_list.lemma_ghost_pointer_ordered_index._definition
)))

;; Function-Specs lib::Tlsf::lemma_checked_add_eq
(declare-fun req%lib!utils.impl&%0.lemma_checked_add_eq. (Dcr Type Dcr Type Int Int
  Int
 ) Bool
)
(declare-const %%global_location_label%%252 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x! Int) (y! Int)
   (res! Int)
  ) (!
   (= (req%lib!utils.impl&%0.lemma_checked_add_eq. FLLEN&. FLLEN& SLLEN&. SLLEN& x! y!
     res!
    ) (=>
     %%global_location_label%%252
     (= (vstd!std_specs.num.usize_specs.checked_add%returns_clause_autospec.? (I x!) (I y!))
      (core!option.Option./Some (I res!))
   )))
   :pattern ((req%lib!utils.impl&%0.lemma_checked_add_eq. FLLEN&. FLLEN& SLLEN&. SLLEN&
     x! y! res!
   ))
   :qid internal_req__lib!utils.impl&__0.lemma_checked_add_eq._definition
   :skolemid skolem_internal_req__lib!utils.impl&__0.lemma_checked_add_eq._definition
)))
(declare-fun ens%lib!utils.impl&%0.lemma_checked_add_eq. (Dcr Type Dcr Type Int Int
  Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (x! Int) (y! Int)
   (res! Int)
  ) (!
   (= (ens%lib!utils.impl&%0.lemma_checked_add_eq. FLLEN&. FLLEN& SLLEN&. SLLEN& x! y!
     res!
    ) (= res! (Add x! y!))
   )
   :pattern ((ens%lib!utils.impl&%0.lemma_checked_add_eq. FLLEN&. FLLEN& SLLEN&. SLLEN&
     x! y! res!
   ))
   :qid internal_ens__lib!utils.impl&__0.lemma_checked_add_eq._definition
   :skolemid skolem_internal_ens__lib!utils.impl&__0.lemma_checked_add_eq._definition
)))

;; Function-Specs lib::Tlsf::search_suitable_free_block_list_for_allocation
(declare-fun req%lib!search_block.impl&%0.search_suitable_free_block_list_for_allocation.
 (Dcr Type Dcr Type lib!Tlsf. Int) Bool
)
(declare-const %%global_location_label%%253 Bool)
(declare-const %%global_location_label%%254 Bool)
(declare-const %%global_location_label%%255 Bool)
(declare-const %%global_location_label%%256 Bool)
(declare-const %%global_location_label%%257 Bool)
(declare-const %%global_location_label%%258 Bool)
(declare-const %%global_location_label%%259 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (min_size! Int)
  ) (!
   (= (req%lib!search_block.impl&%0.search_suitable_free_block_list_for_allocation. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! min_size!
    ) (and
     (=>
      %%global_location_label%%253
      (lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     )
     (=>
      %%global_location_label%%254
      (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     )
     (=>
      %%global_location_label%%255
      (>= min_size! lib!parameters.GRANULARITY.?)
     )
     (=>
      %%global_location_label%%256
      (= (EucMod min_size! lib!parameters.GRANULARITY.?) 0)
     )
     (=>
      %%global_location_label%%257
      (<= min_size! (lib!parameters.impl&%0.max_block_size.? FLLEN&. FLLEN& SLLEN&. SLLEN&))
     )
     (=>
      %%global_location_label%%258
      (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     )
     (=>
      %%global_location_label%%259
      (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
   )))
   :pattern ((req%lib!search_block.impl&%0.search_suitable_free_block_list_for_allocation.
     FLLEN&. FLLEN& SLLEN&. SLLEN& self! min_size!
   ))
   :qid internal_req__lib!search_block.impl&__0.search_suitable_free_block_list_for_allocation._definition
   :skolemid skolem_internal_req__lib!search_block.impl&__0.search_suitable_free_block_list_for_allocation._definition
)))
(declare-fun ens%lib!search_block.impl&%0.search_suitable_free_block_list_for_allocation.
 (Dcr Type Dcr Type lib!Tlsf. Int core!option.Option.) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (min_size! Int) (r! core!option.Option.)
  ) (!
   (= (ens%lib!search_block.impl&%0.search_suitable_free_block_list_for_allocation. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! min_size! r!
    ) (and
     (has_type (Poly%core!option.Option. r!) (TYPE%core!option.Option. $ (TYPE%lib!block_index.BlockIndex.
        FLLEN&. FLLEN& SLLEN&. SLLEN&
     )))
     (lib!bitmap.impl&%0.bitmap_wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     (lib!bitmap.impl&%0.bitmap_sync.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
     (let
      ((tmp%%$ r!))
      (=>
       (is-core!option.Option./Some tmp%%$)
       (let
        ((idx$ (%Poly%lib!block_index.BlockIndex. (core!option.Option./Some/0 $ (TYPE%lib!block_index.BlockIndex.
             FLLEN&. FLLEN& SLLEN&. SLLEN&
            ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
        ))))
        (and
         (lib!block_index.impl&%7.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
           idx$
         ))
         (and
          (<= min_size! (lib!half_open_range.impl&%0.start.? (Poly%lib!half_open_range.HalfOpenRange.
             (lib!block_index.impl&%7.block_size_range.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!block_index.BlockIndex.
               idx$
          )))))
          (> (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.?
             $ (TYPE%lib!block_index.BlockIndex. FLLEN&. FLLEN& SLLEN&. SLLEN&) $ (TYPE%vstd!seq.Seq.
              $ (PTR $ TYPE%lib!block.BlockHdr.)
             ) (lib!all_blocks.ShadowFreelist./ShadowFreelist/m (%Poly%lib!all_blocks.ShadowFreelist.
               (Poly%lib!all_blocks.ShadowFreelist. (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf.
                  (Poly%lib!Tlsf. self!)
              ))))
             ) (Poly%lib!block_index.BlockIndex. idx$)
            )
           ) 0
   ))))))))
   :pattern ((ens%lib!search_block.impl&%0.search_suitable_free_block_list_for_allocation.
     FLLEN&. FLLEN& SLLEN&. SLLEN& self! min_size! r!
   ))
   :qid internal_ens__lib!search_block.impl&__0.search_suitable_free_block_list_for_allocation._definition
   :skolemid skolem_internal_ens__lib!search_block.impl&__0.search_suitable_free_block_list_for_allocation._definition
)))

;; Function-Specs lib::block::BlockHdr::next_phys_block
(declare-fun req%lib!block.impl&%1.next_phys_block. (ptr_mut%<lib!block.BlockHdr.>.
  lib!block.BlockPerm.
 ) Bool
)
(declare-const %%global_location_label%%260 Bool)
(declare-const %%global_location_label%%261 Bool)
(declare-const %%global_location_label%%262 Bool)
(declare-const %%global_location_label%%263 Bool)
(assert
 (forall ((block! ptr_mut%<lib!block.BlockHdr.>.) (perm! lib!block.BlockPerm.)) (!
   (= (req%lib!block.impl&%1.next_phys_block. block! perm!) (and
     (=>
      %%global_location_label%%260
      (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
        (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
           $ TYPE%lib!block.BlockHdr.
          ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
            (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. perm!))
     )))))))
     (=>
      %%global_location_label%%261
      (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!raw_ptr.PointsToData./PointsToData/ptr
         (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
            $ TYPE%lib!block.BlockHdr.
           ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
             (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. perm!))
        )))))
       ) block!
     ))
     (=>
      %%global_location_label%%262
      (not (lib!block.impl&%1.is_sentinel.? (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr.
         (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
            (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
               $ TYPE%lib!block.BlockHdr.
              ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. perm!))
     )))))))))))
     (=>
      %%global_location_label%%263
      (< (Add (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (
           Poly%ptr_mut%<lib!block.BlockHdr.>. block!
         ))
        ) (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (vstd!raw_ptr.MemContents./Init/0
           $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
             (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
               (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.BlockHdr.)
                (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                  (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. perm!))
        ))))))))))
       ) (- (uHi SZ) 1)
   ))))
   :pattern ((req%lib!block.impl&%1.next_phys_block. block! perm!))
   :qid internal_req__lib!block.impl&__1.next_phys_block._definition
   :skolemid skolem_internal_req__lib!block.impl&__1.next_phys_block._definition
)))
(declare-fun ens%lib!block.impl&%1.next_phys_block. (ptr_mut%<lib!block.BlockHdr.>.
  lib!block.BlockPerm. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((block! ptr_mut%<lib!block.BlockHdr.>.) (perm! lib!block.BlockPerm.) (r! ptr_mut%<lib!block.BlockHdr.>.))
  (!
   (= (ens%lib!block.impl&%1.next_phys_block. block! perm! r!) (and
     (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. r!)
       ))
      ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block!)
     ))))
     (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. r!)
       ))
      ) (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block!)
        ))
       ) (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr. (
             vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents.
              (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                   $ TYPE%lib!block.BlockHdr.
                  ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                    (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. perm!))
          ))))))))))
         ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
   ))))))
   :pattern ((ens%lib!block.impl&%1.next_phys_block. block! perm! r!))
   :qid internal_ens__lib!block.impl&__1.next_phys_block._definition
   :skolemid skolem_internal_ens__lib!block.impl&__1.next_phys_block._definition
)))

;; Function-Specs lib::round_up
(declare-fun req%lib!round_up. (ptr_mut%<u8.>. Int) Bool)
(declare-const %%global_location_label%%264 Bool)
(assert
 (forall ((ptr! ptr_mut%<u8.>.) (align! Int)) (!
   (= (req%lib!round_up. ptr! align!) (=>
     %%global_location_label%%264
     (lib!bits.is_power_of_two.? (I align!))
   ))
   :pattern ((req%lib!round_up. ptr! align!))
   :qid internal_req__lib!round_up._definition
   :skolemid skolem_internal_req__lib!round_up._definition
)))
(declare-fun ens%lib!round_up. (ptr_mut%<u8.>. Int ptr_mut%<u8.>.) Bool)
(assert
 (forall ((ptr! ptr_mut%<u8.>.) (align! Int) (r! ptr_mut%<u8.>.)) (!
   (= (ens%lib!round_up. ptr! align! r!) (and
     (let
      ((tmp%%$ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>. ptr!))))
      (let
       ((tmp%%$1 (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>. r!))))
       (let
        ((tmp%%$2 (Add (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>.
             ptr!
            )
           ) align!
        )))
        (and
         (<= tmp%%$ tmp%%$1)
         (< tmp%%$1 tmp%%$2)
     ))))
     (= (EucMod (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>.
          r!
        ))
       ) align!
      ) 0
     )
     (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. r!)
       ))
      ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. ptr!)
   ))))))
   :pattern ((ens%lib!round_up. ptr! align! r!))
   :qid internal_ens__lib!round_up._definition
   :skolemid skolem_internal_ens__lib!round_up._definition
)))

;; Function-Specs lib::Tlsf::lemma_join_adjacent_ranges_is_range
(declare-fun req%lib!impl&%0.lemma_join_adjacent_ranges_is_range. (Dcr Type Dcr Type
  vstd!raw_ptr.PointsToRaw. vstd!raw_ptr.PointsToRaw. Int Int Int
 ) Bool
)
(declare-const %%global_location_label%%265 Bool)
(declare-const %%global_location_label%%266 Bool)
(declare-const %%global_location_label%%267 Bool)
(declare-const %%global_location_label%%268 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (left! vstd!raw_ptr.PointsToRaw.)
   (right! vstd!raw_ptr.PointsToRaw.) (start! Int) (mid! Int) (end! Int)
  ) (!
   (= (req%lib!impl&%0.lemma_join_adjacent_ranges_is_range. FLLEN&. FLLEN& SLLEN&. SLLEN&
     left! right! start! mid! end!
    ) (and
     (=>
      %%global_location_label%%265
      (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. left!)) (vstd!raw_ptr.impl&%10.provenance.?
        (Poly%vstd!raw_ptr.PointsToRaw. right!)
     )))
     (=>
      %%global_location_label%%266
      (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. left!) (I start!)
       (I (Sub mid! start!))
     ))
     (=>
      %%global_location_label%%267
      (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. right!) (I mid!)
       (I (Sub end! mid!))
     ))
     (=>
      %%global_location_label%%268
      (let
       ((tmp%%$ start!))
       (let
        ((tmp%%$1 mid!))
        (let
         ((tmp%%$2 end!))
         (and
          (<= tmp%%$ tmp%%$1)
          (<= tmp%%$1 tmp%%$2)
   )))))))
   :pattern ((req%lib!impl&%0.lemma_join_adjacent_ranges_is_range. FLLEN&. FLLEN& SLLEN&.
     SLLEN& left! right! start! mid! end!
   ))
   :qid internal_req__lib!impl&__0.lemma_join_adjacent_ranges_is_range._definition
   :skolemid skolem_internal_req__lib!impl&__0.lemma_join_adjacent_ranges_is_range._definition
)))
(declare-fun ens%lib!impl&%0.lemma_join_adjacent_ranges_is_range. (Dcr Type Dcr Type
  vstd!raw_ptr.PointsToRaw. vstd!raw_ptr.PointsToRaw. Int Int Int vstd!raw_ptr.PointsToRaw.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (left! vstd!raw_ptr.PointsToRaw.)
   (right! vstd!raw_ptr.PointsToRaw.) (start! Int) (mid! Int) (end! Int) (joined! vstd!raw_ptr.PointsToRaw.)
  ) (!
   (= (ens%lib!impl&%0.lemma_join_adjacent_ranges_is_range. FLLEN&. FLLEN& SLLEN&. SLLEN&
     left! right! start! mid! end! joined!
    ) (and
     (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. joined!)) (
       vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. left!)
     ))
     (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. joined!) (I start!)
      (I (Sub end! start!))
   )))
   :pattern ((ens%lib!impl&%0.lemma_join_adjacent_ranges_is_range. FLLEN&. FLLEN& SLLEN&.
     SLLEN& left! right! start! mid! end! joined!
   ))
   :qid internal_ens__lib!impl&__0.lemma_join_adjacent_ranges_is_range._definition
   :skolemid skolem_internal_ens__lib!impl&__0.lemma_join_adjacent_ranges_is_range._definition
)))

;; Function-Specs lib::ordered_pointer_list::lemma_add_ghost_pointer_ensures
(declare-fun req%lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%269 Bool)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.))
  (!
   (= (req%lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures. ls! p!) (=>
     %%global_location_label%%269
     (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
       ls!
   ))))
   :pattern ((req%lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures. ls! p!))
   :qid internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures._definition
)))
(declare-fun ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.))
  (!
   (= (ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures. ls! p!) (and
     (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
       (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
     )))
     (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
       (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
       )
      ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
     )
     (forall ((e$ Poly)) (!
       (=>
        (has_type e$ (PTR $ TYPE%lib!block.BlockHdr.))
        (=>
         (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           ls!
          ) e$
         )
         (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
            ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
           )
          ) e$
       )))
       :pattern ((vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
         ) e$
       ))
       :qid user_lib__ordered_pointer_list__lemma_add_ghost_pointer_ensures_128
       :skolemid skolem_user_lib__ordered_pointer_list__lemma_add_ghost_pointer_ensures_128
   ))))
   :pattern ((ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures. ls! p!))
   :qid internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures._definition
   :skolemid skolem_internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_ensures._definition
)))

;; Function-Specs lib::Tlsf::lemma_mark_used_preserves_size_bits
(declare-fun req%lib!impl&%0.lemma_mark_used_preserves_size_bits. (Dcr Type Dcr Type
  Int
 ) Bool
)
(declare-const %%global_location_label%%270 Bool)
(declare-const %%global_location_label%%271 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sz! Int)) (!
   (= (req%lib!impl&%0.lemma_mark_used_preserves_size_bits. FLLEN&. FLLEN& SLLEN&. SLLEN&
     sz!
    ) (and
     (=>
      %%global_location_label%%270
      (= (EucMod sz! lib!parameters.GRANULARITY.?) 0)
     )
     (=>
      %%global_location_label%%271
      (lib!parameters.impl&%0.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
   )))
   :pattern ((req%lib!impl&%0.lemma_mark_used_preserves_size_bits. FLLEN&. FLLEN& SLLEN&.
     SLLEN& sz!
   ))
   :qid internal_req__lib!impl&__0.lemma_mark_used_preserves_size_bits._definition
   :skolemid skolem_internal_req__lib!impl&__0.lemma_mark_used_preserves_size_bits._definition
)))
(declare-fun ens%lib!impl&%0.lemma_mark_used_preserves_size_bits. (Dcr Type Dcr Type
  Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (sz! Int)) (!
   (= (ens%lib!impl&%0.lemma_mark_used_preserves_size_bits. FLLEN&. FLLEN& SLLEN&. SLLEN&
     sz!
    ) (and
     (= (uClip SZ (bitand (I sz!) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?))) sz!)
     (= (uClip SZ (bitand (I (uClip SZ (bitor (I sz!) (I lib!parameters.SIZE_USED.?)))) (
         I lib!parameters.SPEC_SIZE_SIZE_MASK.?
       ))
      ) sz!
   )))
   :pattern ((ens%lib!impl&%0.lemma_mark_used_preserves_size_bits. FLLEN&. FLLEN& SLLEN&.
     SLLEN& sz!
   ))
   :qid internal_ens__lib!impl&__0.lemma_mark_used_preserves_size_bits._definition
   :skolemid skolem_internal_ens__lib!impl&__0.lemma_mark_used_preserves_size_bits._definition
)))

;; Function-Specs lib::ordered_pointer_list::lemma_add_ghost_pointer_insert_point
(declare-fun req%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  ptr_mut%<lib!block.BlockHdr.>. Int
 ) Bool
)
(declare-const %%global_location_label%%272 Bool)
(declare-const %%global_location_label%%273 Bool)
(declare-const %%global_location_label%%274 Bool)
(declare-const %%global_location_label%%275 Bool)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.)
   (ins! Int)
  ) (!
   (= (req%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point. ls! p! ins!)
    (and
     (=>
      %%global_location_label%%272
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        ls!
     )))
     (=>
      %%global_location_label%%273
      (let
       ((tmp%%$ 0))
       (let
        ((tmp%%$1 ins!))
        (let
         ((tmp%%$2 (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
             ls!
         ))))
         (and
          (<= tmp%%$ tmp%%$1)
          (< tmp%%$1 tmp%%$2)
     )))))
     (=>
      %%global_location_label%%274
      (< (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
           ls!
          ) (I ins!)
        ))
       ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
          p!
     )))))
     (=>
      %%global_location_label%%275
      (=>
       (< (Add ins! 1) (vstd!seq.Seq.len.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
       )))
       (<= (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (Poly%ptr_mut%<lib!block.BlockHdr.>.
           p!
         ))
        ) (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ TYPE%lib!block.BlockHdr. (vstd!seq.Seq.index.?
           $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
            ls!
           ) (I (Add ins! 1))
   ))))))))
   :pattern ((req%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point. ls! p!
     ins!
   ))
   :qid internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point._definition
)))
(declare-fun ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  ptr_mut%<lib!block.BlockHdr.>. Int
 ) Bool
)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.)
   (ins! Int)
  ) (!
   (= (ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point. ls! p! ins!)
    (= (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!seq.Seq.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
       (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. (lib!ordered_pointer_list.add_ghost_pointer.?
         (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>. ls!) (Poly%ptr_mut%<lib!block.BlockHdr.>.
          p!
        ))
       ) (I (Add ins! 1))
      )
     ) p!
   ))
   :pattern ((ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point. ls! p!
     ins!
   ))
   :qid internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point._definition
   :skolemid skolem_internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_insert_point._definition
)))

;; Function-Specs lib::ordered_pointer_list::lemma_add_ghost_pointer_contains_old
(declare-fun req%lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(declare-const %%global_location_label%%276 Bool)
(declare-const %%global_location_label%%277 Bool)
(declare-const %%global_location_label%%278 Bool)
(declare-const %%global_location_label%%279 Bool)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.)
   (e! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (req%lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old. ls! p! e!)
    (and
     (=>
      %%global_location_label%%276
      (lib!ordered_pointer_list.ghost_pointer_ordered.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        ls!
     )))
     (=>
      %%global_location_label%%277
      (not (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
         ls!
        ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
     )))
     (=>
      %%global_location_label%%278
      (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
        (lib!ordered_pointer_list.add_ghost_pointer.? (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
          ls!
         ) (Poly%ptr_mut%<lib!block.BlockHdr.>. p!)
        )
       ) (Poly%ptr_mut%<lib!block.BlockHdr.>. e!)
     ))
     (=>
      %%global_location_label%%279
      (not (= e! p!))
   )))
   :pattern ((req%lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old. ls! p!
     e!
   ))
   :qid internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old._definition
   :skolemid skolem_internal_req__lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old._definition
)))
(declare-fun ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old. (vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
  ptr_mut%<lib!block.BlockHdr.>. ptr_mut%<lib!block.BlockHdr.>.
 ) Bool
)
(assert
 (forall ((ls! vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.) (p! ptr_mut%<lib!block.BlockHdr.>.)
   (e! ptr_mut%<lib!block.BlockHdr.>.)
  ) (!
   (= (ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old. ls! p! e!)
    (vstd!seq_lib.impl&%0.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!seq.Seq<ptr_mut%<lib!block.BlockHdr.>.>.
      ls!
     ) (Poly%ptr_mut%<lib!block.BlockHdr.>. e!)
   ))
   :pattern ((ens%lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old. ls! p!
     e!
   ))
   :qid internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old._definition
   :skolemid skolem_internal_ens__lib!ordered_pointer_list.lemma_add_ghost_pointer_contains_old._definition
)))

;; Function-Specs lib::block::UsedBlockPad::get_for_allocation
(declare-fun ens%lib!block.impl&%3.get_for_allocation. (ptr_mut%<u8.>. ptr_mut%<lib!block.UsedBlockPad.>.)
 Bool
)
(assert
 (forall ((ptr! ptr_mut%<u8.>.) (r! ptr_mut%<lib!block.UsedBlockPad.>.)) (!
   (= (ens%lib!block.impl&%3.get_for_allocation. ptr! r!) (and
     (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.UsedBlockPad.) (Poly%ptr_mut%<lib!block.UsedBlockPad.>. r!)
       ))
      ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. ptr!)
     ))))
     (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
         $ (PTR $ TYPE%lib!block.UsedBlockPad.) (Poly%ptr_mut%<lib!block.UsedBlockPad.>. r!)
       ))
      ) (vstd!std_specs.num.usize_specs.wrapping_sub%returns_clause_autospec.? (I (uClip SZ
         (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>. ptr!))
        )
       ) (I (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.UsedBlockPad.)))
     ))
     (=>
      (>= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. ptr!)
        ))
       ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.UsedBlockPad.))
      )
      (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.UsedBlockPad.) (Poly%ptr_mut%<lib!block.UsedBlockPad.>. r!)
        ))
       ) (Sub (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
           $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. ptr!)
         ))
        ) (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.UsedBlockPad.))
   )))))
   :pattern ((ens%lib!block.impl&%3.get_for_allocation. ptr! r!))
   :qid internal_ens__lib!block.impl&__3.get_for_allocation._definition
   :skolemid skolem_internal_ens__lib!block.impl&__3.get_for_allocation._definition
)))

;; Function-Specs lib::Tlsf::lemma_range_subset_of_mem_dom
(declare-fun req%lib!impl&%0.lemma_range_subset_of_mem_dom. (Dcr Type Dcr Type vstd!raw_ptr.PointsToRaw.
  Int Int Int Int
 ) Bool
)
(declare-const %%global_location_label%%280 Bool)
(declare-const %%global_location_label%%281 Bool)
(declare-const %%global_location_label%%282 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (mem! vstd!raw_ptr.PointsToRaw.)
   (mem_start! Int) (mem_end! Int) (lo! Int) (hi! Int)
  ) (!
   (= (req%lib!impl&%0.lemma_range_subset_of_mem_dom. FLLEN&. FLLEN& SLLEN&. SLLEN& mem!
     mem_start! mem_end! lo! hi!
    ) (and
     (=>
      %%global_location_label%%280
      (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. mem!) (I mem_start!)
       (I (Sub mem_end! mem_start!))
     ))
     (=>
      %%global_location_label%%281
      (<= mem_start! lo!)
     )
     (=>
      %%global_location_label%%282
      (<= hi! mem_end!)
   )))
   :pattern ((req%lib!impl&%0.lemma_range_subset_of_mem_dom. FLLEN&. FLLEN& SLLEN&. SLLEN&
     mem! mem_start! mem_end! lo! hi!
   ))
   :qid internal_req__lib!impl&__0.lemma_range_subset_of_mem_dom._definition
   :skolemid skolem_internal_req__lib!impl&__0.lemma_range_subset_of_mem_dom._definition
)))
(declare-fun ens%lib!impl&%0.lemma_range_subset_of_mem_dom. (Dcr Type Dcr Type vstd!raw_ptr.PointsToRaw.
  Int Int Int Int
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (mem! vstd!raw_ptr.PointsToRaw.)
   (mem_start! Int) (mem_end! Int) (lo! Int) (hi! Int)
  ) (!
   (= (ens%lib!impl&%0.lemma_range_subset_of_mem_dom. FLLEN&. FLLEN& SLLEN&. SLLEN& mem!
     mem_start! mem_end! lo! hi!
    ) (vstd!set.Set.subset_of.? $ INT (Poly%vstd!set.Set<int.>. (vstd!set_lib.set_int_range.?
       (I lo!) (I hi!)
      )
     ) (Poly%vstd!set.Set<int.>. (vstd!raw_ptr.impl&%10.dom.? (Poly%vstd!raw_ptr.PointsToRaw.
        mem!
   )))))
   :pattern ((ens%lib!impl&%0.lemma_range_subset_of_mem_dom. FLLEN&. FLLEN& SLLEN&. SLLEN&
     mem! mem_start! mem_end! lo! hi!
   ))
   :qid internal_ens__lib!impl&__0.lemma_range_subset_of_mem_dom._definition
   :skolemid skolem_internal_ens__lib!impl&__0.lemma_range_subset_of_mem_dom._definition
)))

;; Function-Specs lib::Tlsf::lemma_wf_preserved_after_user_block_map_update
(declare-fun req%lib!impl&%0.lemma_wf_preserved_after_user_block_map_update. (Dcr Type
  Dcr Type lib!Tlsf. lib!Tlsf.
 ) Bool
)
(declare-const %%global_location_label%%283 Bool)
(declare-const %%global_location_label%%284 Bool)
(declare-const %%global_location_label%%285 Bool)
(declare-const %%global_location_label%%286 Bool)
(declare-const %%global_location_label%%287 Bool)
(declare-const %%global_location_label%%288 Bool)
(declare-const %%global_location_label%%289 Bool)
(declare-const %%global_location_label%%290 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.)
  ) (!
   (= (req%lib!impl&%0.lemma_wf_preserved_after_user_block_map_update. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self!
    ) (and
     (=>
      %%global_location_label%%283
      (lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. old_self!))
     )
     (=>
      %%global_location_label%%284
      (= (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (lib!Tlsf./Tlsf/all_blocks
        (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%285
      (= (lib!Tlsf./Tlsf/fl_bitmap (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (lib!Tlsf./Tlsf/fl_bitmap
        (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%286
      (= (lib!Tlsf./Tlsf/sl_bitmap (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (lib!Tlsf./Tlsf/sl_bitmap
        (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%287
      (= (lib!Tlsf./Tlsf/first_free (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (lib!Tlsf./Tlsf/first_free
        (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%288
      (= (lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (
        lib!Tlsf./Tlsf/shadow_freelist (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
     )))
     (=>
      %%global_location_label%%289
      (= (lib!Tlsf./Tlsf/root_provenances (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!)))
       (lib!Tlsf./Tlsf/root_provenances (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!)))
     ))
     (=>
      %%global_location_label%%290
      (= (lib!Tlsf./Tlsf/valid_range (%Poly%lib!Tlsf. (Poly%lib!Tlsf. new_self!))) (lib!Tlsf./Tlsf/valid_range
        (%Poly%lib!Tlsf. (Poly%lib!Tlsf. old_self!))
   )))))
   :pattern ((req%lib!impl&%0.lemma_wf_preserved_after_user_block_map_update. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self!
   ))
   :qid internal_req__lib!impl&__0.lemma_wf_preserved_after_user_block_map_update._definition
   :skolemid skolem_internal_req__lib!impl&__0.lemma_wf_preserved_after_user_block_map_update._definition
)))
(declare-fun ens%lib!impl&%0.lemma_wf_preserved_after_user_block_map_update. (Dcr Type
  Dcr Type lib!Tlsf. lib!Tlsf.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (old_self! lib!Tlsf.)
   (new_self! lib!Tlsf.)
  ) (!
   (= (ens%lib!impl&%0.lemma_wf_preserved_after_user_block_map_update. FLLEN&. FLLEN&
     SLLEN&. SLLEN& old_self! new_self!
    ) (lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. new_self!))
   )
   :pattern ((ens%lib!impl&%0.lemma_wf_preserved_after_user_block_map_update. FLLEN&.
     FLLEN& SLLEN&. SLLEN& old_self! new_self!
   ))
   :qid internal_ens__lib!impl&__0.lemma_wf_preserved_after_user_block_map_update._definition
   :skolemid skolem_internal_ens__lib!impl&__0.lemma_wf_preserved_after_user_block_map_update._definition
)))

;; Function-Specs lib::Tlsf::lemma_establish_wf_dealloc_base
(declare-fun req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_base. (Dcr Type
  Dcr Type lib!Tlsf. lib!DeallocToken.
 ) Bool
)
(declare-const %%global_location_label%%291 Bool)
(declare-const %%global_location_label%%292 Bool)
(declare-const %%global_location_label%%293 Bool)
(declare-const %%global_location_label%%294 Bool)
(declare-const %%global_location_label%%295 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_base. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! tok!
    ) (and
     (=>
      %%global_location_label%%291
      (vstd!set.Set.contains.? $ (PTR $ (UINT 8)) (vstd!map.impl&%0.dom.? $ (PTR $ (UINT 8))
        $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
        )
       ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
          (Poly%lib!DeallocToken. tok!)
     )))))
     (=>
      %%global_location_label%%292
      (lib!all_blocks.impl&%0.contains.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!all_blocks.AllBlocks.
        (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
       ) (vstd!map.impl&%0.index.? $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (lib!Tlsf./Tlsf/user_block_map
          (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
         )
        ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
           (Poly%lib!DeallocToken. tok!)
     ))))))
     (=>
      %%global_location_label%%293
      (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
         (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
        ))))
       ) (vstd!map.impl&%0.index.? $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (lib!Tlsf./Tlsf/user_block_map
          (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
         )
        ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
           (Poly%lib!DeallocToken. tok!)
     ))))))
     (=>
      %%global_location_label%%294
      (not (lib!block.impl&%1.is_free.? (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr.
         (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
            (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
               $ TYPE%lib!block.BlockHdr.
              ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
                  $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
                   (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                      (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
                   )))
                  ) (vstd!map.impl&%0.index.? $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)
                   (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (lib!Tlsf./Tlsf/user_block_map
                     (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
                    )
                   ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                      (Poly%lib!DeallocToken. tok!)
     )))))))))))))))))
     (=>
      %%global_location_label%%295
      (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
             (Poly%lib!DeallocToken. tok!)
        )))))
       ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
          $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.index.? $ (PTR $ (UINT 8)) $
           (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
           ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
              (Poly%lib!DeallocToken. tok!)
   )))))))))))
   :pattern ((req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_base. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! tok!
   ))
   :qid internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_base._definition
   :skolemid skolem_internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_base._definition
)))
(declare-fun ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_base. (Dcr Type
  Dcr Type lib!Tlsf. lib!DeallocToken.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_base. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! tok!
    ) (lib!deallocate.impl&%0.wf_dealloc_base.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      self!
     ) (Poly%lib!DeallocToken. tok!)
   ))
   :pattern ((ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_base. FLLEN&. FLLEN&
     SLLEN&. SLLEN& self! tok!
   ))
   :qid internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_base._definition
   :skolemid skolem_internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_base._definition
)))

;; Function-Specs lib::Tlsf::lemma_establish_wf_dealloc_granularity_aligned
(declare-fun req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_aligned.
 (Dcr Type Dcr Type lib!Tlsf. lib!DeallocToken.) Bool
)
(declare-const %%global_location_label%%296 Bool)
(declare-const %%global_location_label%%297 Bool)
(declare-const %%global_location_label%%298 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_aligned. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! tok!
    ) (and
     (=>
      %%global_location_label%%296
      (vstd!set.Set.contains.? $ (PTR $ (UINT 8)) (vstd!map.impl&%0.dom.? $ (PTR $ (UINT 8))
        $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
        )
       ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
          (Poly%lib!DeallocToken. tok!)
     )))))
     (=>
      %%global_location_label%%297
      (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
         (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
        ))))
       ) (vstd!map.impl&%0.index.? $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (lib!Tlsf./Tlsf/user_block_map
          (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
         )
        ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
           (Poly%lib!DeallocToken. tok!)
     ))))))
     (=>
      %%global_location_label%%298
      (let
       ((block_ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!map.impl&%0.index.? $ (PTR $
            (UINT 8)
           ) $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
           ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
              (Poly%lib!DeallocToken. tok!)
       )))))))
       (let
        ((bp$ (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
            $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
             (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
             )))
            ) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
        ))))
        (let
         ((phys_size$ (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr.
                (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents.
                  (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                    (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                       $ TYPE%lib!block.BlockHdr.
                      ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                        (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
              ))))))))))
             ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
         ))))
         (let
          ((BH$ (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))))
          (let
           ((pad_size$ (vstd!layout.size_of.? $ TYPE%lib!block.UsedBlockPad.)))
           (and
            (and
             (and
              (and
               (and
                (and
                 (and
                  (> (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                      tok!
                    ))
                   ) 0
                  )
                  (>= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                      $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                         (Poly%lib!DeallocToken. tok!)
                    )))))
                   ) (Add (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                        $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                      ))
                     ) BH$
                    ) pad_size$
                 )))
                 (<= (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                      $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                         (Poly%lib!DeallocToken. tok!)
                    )))))
                   ) (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                      tok!
                   )))
                  ) (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                      $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                    ))
                   ) phys_size$
                )))
                (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/mem
                    (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
                  ))
                 ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                    $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
               )))))
               (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/mem
                  (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
                 )
                ) (I (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                        (Poly%lib!DeallocToken. tok!)
                   )))))
                  ) (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                     tok!
                 ))))
                ) (I (Sub (Sub (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                       $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                     ))
                    ) phys_size$
                   ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                      $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                         (Poly%lib!DeallocToken. tok!)
                   ))))))
                  ) (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                     tok!
              )))))))
              (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/overhead_mem
                  (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
                ))
               ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                  $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
             )))))
             (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/overhead_mem
                (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
               )
              ) (I (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                   $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                 ))
                ) BH$
               )
              ) (I (Sub (Sub (Sub (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                        (Poly%lib!DeallocToken. tok!)
                   )))))
                  ) pad_size$
                 ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                    $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                 )))
                ) BH$
            ))))
            (let
             ((tmp%%$ (lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm.
                  bp$
             )))))
             (and
              (is-core!option.Option./Some tmp%%$)
              (let
               ((pp$ (%Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. (core!option.Option./Some/0
                   $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.UsedBlockPad.) (%Poly%core!option.Option.
                    (Poly%core!option.Option. tmp%%$)
               )))))
               (and
                (and
                 (and
                  (is-vstd!raw_ptr.MemContents./Init (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                    (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                       $ TYPE%lib!block.UsedBlockPad.
                      ) (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. pp$)
                  ))))
                  (= (lib!block.UsedBlockPad./UsedBlockPad/block_hdr (%Poly%lib!block.UsedBlockPad. (vstd!raw_ptr.MemContents./Init/0
                      $ TYPE%lib!block.UsedBlockPad. (%Poly%vstd!raw_ptr.MemContents. (Poly%vstd!raw_ptr.MemContents.
                        (vstd!raw_ptr.PointsToData./PointsToData/opt_value (%Poly%vstd!raw_ptr.PointsToData.
                          (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo. $ TYPE%lib!block.UsedBlockPad.)
                           (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. pp$)
                    )))))))
                   ) block_ptr$
                 ))
                 (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ TYPE%lib!block.UsedBlockPad.) (vstd!raw_ptr.PointsToData./PointsToData/ptr
                      (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                         $ TYPE%lib!block.UsedBlockPad.
                        ) (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. pp$)
                   )))))
                  ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                        (Poly%lib!DeallocToken. tok!)
                ))))))))
                (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                    $ (PTR $ TYPE%lib!block.UsedBlockPad.) (vstd!raw_ptr.PointsToData./PointsToData/ptr
                     (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                        $ TYPE%lib!block.UsedBlockPad.
                       ) (Poly%vstd!raw_ptr.PointsTo<lib!block.UsedBlockPad.>. pp$)
                  )))))
                 ) (Sub (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                        (Poly%lib!DeallocToken. tok!)
                   )))))
                  ) pad_size$
   )))))))))))))))
   :pattern ((req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_aligned.
     FLLEN&. FLLEN& SLLEN&. SLLEN& self! tok!
   ))
   :qid internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_aligned._definition
   :skolemid skolem_internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_aligned._definition
)))
(declare-fun ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_aligned.
 (Dcr Type Dcr Type lib!Tlsf. lib!DeallocToken.) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_aligned. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! tok!
    ) (lib!deallocate.impl&%0.wf_dealloc_granularity_aligned.? FLLEN&. FLLEN& SLLEN&.
     SLLEN& (Poly%lib!Tlsf. self!) (Poly%lib!DeallocToken. tok!)
   ))
   :pattern ((ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_aligned.
     FLLEN&. FLLEN& SLLEN&. SLLEN& self! tok!
   ))
   :qid internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_aligned._definition
   :skolemid skolem_internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_aligned._definition
)))

;; Function-Specs lib::Tlsf::lemma_establish_wf_dealloc_granularity_unaligned
(declare-fun req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_unaligned.
 (Dcr Type Dcr Type lib!Tlsf. lib!DeallocToken.) Bool
)
(declare-const %%global_location_label%%299 Bool)
(declare-const %%global_location_label%%300 Bool)
(declare-const %%global_location_label%%301 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_unaligned. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! tok!
    ) (and
     (=>
      %%global_location_label%%299
      (vstd!set.Set.contains.? $ (PTR $ (UINT 8)) (vstd!map.impl&%0.dom.? $ (PTR $ (UINT 8))
        $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
         (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
        )
       ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
          (Poly%lib!DeallocToken. tok!)
     )))))
     (=>
      %%global_location_label%%300
      (vstd!set.Set.contains.? $ (PTR $ TYPE%lib!block.BlockHdr.) (vstd!map.impl&%0.dom.?
        $ (PTR $ TYPE%lib!block.BlockHdr.) $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
         (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
            (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
        ))))
       ) (vstd!map.impl&%0.index.? $ (PTR $ (UINT 8)) $ (PTR $ TYPE%lib!block.BlockHdr.)
        (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>. (lib!Tlsf./Tlsf/user_block_map
          (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!))
         )
        ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
           (Poly%lib!DeallocToken. tok!)
     ))))))
     (=>
      %%global_location_label%%301
      (let
       ((block_ptr$ (%Poly%ptr_mut%<lib!block.BlockHdr.>. (vstd!map.impl&%0.index.? $ (PTR $
            (UINT 8)
           ) $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%vstd!map.Map<ptr_mut%<u8.>./ptr_mut%<lib!block.BlockHdr.>.>.
            (lib!Tlsf./Tlsf/user_block_map (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
           ) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
              (Poly%lib!DeallocToken. tok!)
       )))))))
       (let
        ((bp$ (%Poly%lib!block.BlockPerm. (vstd!map.impl&%0.index.? $ (PTR $ TYPE%lib!block.BlockHdr.)
            $ TYPE%lib!block.BlockPerm. (Poly%vstd!map.Map<ptr_mut%<lib!block.BlockHdr.>./lib!block.BlockPerm.>.
             (lib!all_blocks.AllBlocks./AllBlocks/perms (%Poly%lib!all_blocks.AllBlocks. (Poly%lib!all_blocks.AllBlocks.
                (lib!Tlsf./Tlsf/all_blocks (%Poly%lib!Tlsf. (Poly%lib!Tlsf. self!)))
             )))
            ) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
        ))))
        (let
         ((phys_size$ (uClip SZ (bitand (I (lib!block.BlockHdr./BlockHdr/size (%Poly%lib!block.BlockHdr.
                (vstd!raw_ptr.MemContents./Init/0 $ TYPE%lib!block.BlockHdr. (%Poly%vstd!raw_ptr.MemContents.
                  (Poly%vstd!raw_ptr.MemContents. (vstd!raw_ptr.PointsToData./PointsToData/opt_value
                    (%Poly%vstd!raw_ptr.PointsToData. (vstd!view.View.view.? $ (TYPE%vstd!raw_ptr.PointsTo.
                       $ TYPE%lib!block.BlockHdr.
                      ) (Poly%vstd!raw_ptr.PointsTo<lib!block.BlockHdr.>. (lib!block.BlockPerm./BlockPerm/points_to
                        (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
              ))))))))))
             ) (I lib!parameters.SPEC_SIZE_SIZE_MASK.?)
         ))))
         (let
          ((BH$ (uClip SZ (vstd!layout.size_of.? $ TYPE%lib!block.BlockHdr.))))
          (and
           (and
            (and
             (and
              (and
               (and
                (> (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                    tok!
                  ))
                 ) 0
                )
                (<= (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                        (Poly%lib!DeallocToken. tok!)
                   )))))
                  ) (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                     tok!
                  )))
                 ) (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                   ))
                  ) phys_size$
               )))
               (= (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                   $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                 ))
                ) (Sub (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                    $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                       (Poly%lib!DeallocToken. tok!)
                  )))))
                 ) (EucDiv lib!parameters.GRANULARITY.? 2)
              )))
              (= (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/mem
                  (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
                ))
               ) (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                  $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
             )))))
             (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/mem
                (%Poly%lib!block.BlockPerm. (Poly%lib!block.BlockPerm. bp$))
               )
              ) (I (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                   $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                      (Poly%lib!DeallocToken. tok!)
                 )))))
                ) (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                   tok!
               ))))
              ) (I (Sub (Sub (Add (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                     $ (PTR $ TYPE%lib!block.BlockHdr.) (Poly%ptr_mut%<lib!block.BlockHdr.>. block_ptr$)
                   ))
                  ) phys_size$
                 ) (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                    $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. (lib!DeallocToken./DeallocToken/ptr (%Poly%lib!DeallocToken.
                       (Poly%lib!DeallocToken. tok!)
                 ))))))
                ) (lib!DeallocToken./DeallocToken/user_size (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
                   tok!
            )))))))
            (vstd!set_lib.impl&%0.is_empty.? $ INT (Poly%vstd!set.Set<int.>. (vstd!raw_ptr.impl&%10.dom.?
               (Poly%vstd!raw_ptr.PointsToRaw. (lib!block.BlockPerm./BlockPerm/overhead_mem (%Poly%lib!block.BlockPerm.
                  (Poly%lib!block.BlockPerm. bp$)
           )))))))
           (is-core!option.Option./None (lib!block.BlockPerm./BlockPerm/pad_perm (%Poly%lib!block.BlockPerm.
              (Poly%lib!block.BlockPerm. bp$)
   )))))))))))
   :pattern ((req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_unaligned.
     FLLEN&. FLLEN& SLLEN&. SLLEN& self! tok!
   ))
   :qid internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_unaligned._definition
   :skolemid skolem_internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_unaligned._definition
)))
(declare-fun ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_unaligned.
 (Dcr Type Dcr Type lib!Tlsf. lib!DeallocToken.) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_unaligned. FLLEN&.
     FLLEN& SLLEN&. SLLEN& self! tok!
    ) (lib!deallocate.impl&%0.wf_dealloc_granularity_unaligned.? FLLEN&. FLLEN& SLLEN&.
     SLLEN& (Poly%lib!Tlsf. self!) (Poly%lib!DeallocToken. tok!)
   ))
   :pattern ((ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc_granularity_unaligned.
     FLLEN&. FLLEN& SLLEN&. SLLEN& self! tok!
   ))
   :qid internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_unaligned._definition
   :skolemid skolem_internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc_granularity_unaligned._definition
)))

;; Function-Specs lib::Tlsf::lemma_establish_wf_dealloc
(declare-fun req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc. (Dcr Type Dcr Type
  lib!Tlsf. lib!DeallocToken.
 ) Bool
)
(declare-const %%global_location_label%%302 Bool)
(declare-const %%global_location_label%%303 Bool)
(declare-const %%global_location_label%%304 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! tok!
    ) (and
     (=>
      %%global_location_label%%302
      (lib!deallocate.impl&%0.wf_dealloc_base.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
        self!
       ) (Poly%lib!DeallocToken. tok!)
     ))
     (=>
      %%global_location_label%%303
      (=>
       (>= (lib!DeallocToken./DeallocToken/align (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
           tok!
         ))
        ) lib!parameters.GRANULARITY.?
       )
       (lib!deallocate.impl&%0.wf_dealloc_granularity_aligned.? FLLEN&. FLLEN& SLLEN&. SLLEN&
        (Poly%lib!Tlsf. self!) (Poly%lib!DeallocToken. tok!)
     )))
     (=>
      %%global_location_label%%304
      (=>
       (< (lib!DeallocToken./DeallocToken/align (%Poly%lib!DeallocToken. (Poly%lib!DeallocToken.
           tok!
         ))
        ) lib!parameters.GRANULARITY.?
       )
       (lib!deallocate.impl&%0.wf_dealloc_granularity_unaligned.? FLLEN&. FLLEN& SLLEN&.
        SLLEN& (Poly%lib!Tlsf. self!) (Poly%lib!DeallocToken. tok!)
   )))))
   :pattern ((req%lib!deallocate.impl&%0.lemma_establish_wf_dealloc. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! tok!
   ))
   :qid internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc._definition
   :skolemid skolem_internal_req__lib!deallocate.impl&__0.lemma_establish_wf_dealloc._definition
)))
(declare-fun ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc. (Dcr Type Dcr Type
  lib!Tlsf. lib!DeallocToken.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (self! lib!Tlsf.)
   (tok! lib!DeallocToken.)
  ) (!
   (= (ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc. FLLEN&. FLLEN& SLLEN&. SLLEN&
     self! tok!
    ) (lib!deallocate.impl&%0.wf_dealloc.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
      self!
     ) (Poly%lib!DeallocToken. tok!)
   ))
   :pattern ((ens%lib!deallocate.impl&%0.lemma_establish_wf_dealloc. FLLEN&. FLLEN& SLLEN&.
     SLLEN& self! tok!
   ))
   :qid internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc._definition
   :skolemid skolem_internal_ens__lib!deallocate.impl&__0.lemma_establish_wf_dealloc._definition
)))

;; Function-Specs lib::Tlsf::allocate
(declare-fun req%lib!allocate.impl&%0.allocate. (Dcr Type Dcr Type lib!Tlsf. Int Int)
 Bool
)
(declare-const %%global_location_label%%305 Bool)
(declare-const %%global_location_label%%306 Bool)
(declare-const %%global_location_label%%307 Bool)
(declare-const %%global_location_label%%308 Bool)
(declare-const %%global_location_label%%309 Bool)
(declare-const %%global_location_label%%310 Bool)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (size! Int) (align! Int)
  ) (!
   (= (req%lib!allocate.impl&%0.allocate. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self! size!
     align!
    ) (and
     (=>
      %%global_location_label%%305
      (lib!block_index.impl&%7.parameter_validity.? FLLEN&. FLLEN& SLLEN&. SLLEN&)
     )
     (=>
      %%global_location_label%%306
      (lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. pre%self!))
     )
     (=>
      %%global_location_label%%307
      (lib!bits.is_power_of_two.? (I align!))
     )
     (=>
      %%global_location_label%%308
      (< align! (Mul (vstd!arithmetic.power2.pow2.? (I (const_int FLLEN&))) lib!parameters.GRANULARITY.?))
     )
     (=>
      %%global_location_label%%309
      (> size! 0)
     )
     (=>
      %%global_location_label%%310
      (lib!parameters.impl&%0.max_allocatable_size.? FLLEN&. FLLEN& SLLEN&. SLLEN& (I size!)
       (I align!)
   ))))
   :pattern ((req%lib!allocate.impl&%0.allocate. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     size! align!
   ))
   :qid internal_req__lib!allocate.impl&__0.allocate._definition
   :skolemid skolem_internal_req__lib!allocate.impl&__0.allocate._definition
)))
(declare-fun ens%lib!allocate.impl&%0.allocate. (Dcr Type Dcr Type lib!Tlsf. lib!Tlsf.
  Int Int core!option.Option.
 ) Bool
)
(assert
 (forall ((FLLEN&. Dcr) (FLLEN& Type) (SLLEN&. Dcr) (SLLEN& Type) (pre%self! lib!Tlsf.)
   (self! lib!Tlsf.) (size! Int) (align! Int) (r! core!option.Option.)
  ) (!
   (= (ens%lib!allocate.impl&%0.allocate. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self! self!
     size! align! r!
    ) (and
     (has_type (Poly%core!option.Option. r!) (TYPE%core!option.Option. (DST (TRACKED $))
       (TYPE%tuple%3. $ (PTR $ (UINT 8)) (TRACKED $) TYPE%vstd!raw_ptr.PointsToRaw. (TRACKED
         $
        ) TYPE%lib!DeallocToken.
     )))
     (has_type (Poly%lib!Tlsf. self!) (TYPE%lib!Tlsf. FLLEN&. FLLEN& SLLEN&. SLLEN&))
     (let
      ((tmp%%$ r!))
      (=>
       (and
        (is-core!option.Option./Some tmp%%$)
        (is-tuple%3./tuple%3 (%Poly%tuple%3. (core!option.Option./Some/0 (DST (TRACKED $)) (
            TYPE%tuple%3. $ (PTR $ (UINT 8)) (TRACKED $) TYPE%vstd!raw_ptr.PointsToRaw. (TRACKED
             $
            ) TYPE%lib!DeallocToken.
           ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
       ))))
       (let
        ((ptr$ (%Poly%ptr_mut%<u8.>. (tuple%3./tuple%3/0 (%Poly%tuple%3. (core!option.Option./Some/0
              (DST (TRACKED $)) (TYPE%tuple%3. $ (PTR $ (UINT 8)) (TRACKED $) TYPE%vstd!raw_ptr.PointsToRaw.
               (TRACKED $) TYPE%lib!DeallocToken.
              ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
        ))))))
        (let
         ((points_to$ (%Poly%vstd!raw_ptr.PointsToRaw. (tuple%3./tuple%3/1 (%Poly%tuple%3. (core!option.Option./Some/0
               (DST (TRACKED $)) (TYPE%tuple%3. $ (PTR $ (UINT 8)) (TRACKED $) TYPE%vstd!raw_ptr.PointsToRaw.
                (TRACKED $) TYPE%lib!DeallocToken.
               ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
         ))))))
         (let
          ((tok$ (%Poly%lib!DeallocToken. (tuple%3./tuple%3/2 (%Poly%tuple%3. (core!option.Option./Some/0
                (DST (TRACKED $)) (TYPE%tuple%3. $ (PTR $ (UINT 8)) (TRACKED $) TYPE%vstd!raw_ptr.PointsToRaw.
                 (TRACKED $) TYPE%lib!DeallocToken.
                ) (%Poly%core!option.Option. (Poly%core!option.Option. tmp%%$))
          ))))))
          (and
           (and
            (and
             (and
              (lib!deallocate.impl&%0.wf_dealloc.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf.
                self!
               ) (Poly%lib!DeallocToken. tok$)
              )
              (= (vstd!raw_ptr.PtrData./PtrData/provenance (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                  $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. ptr$)
                ))
               ) (vstd!raw_ptr.impl&%10.provenance.? (Poly%vstd!raw_ptr.PointsToRaw. points_to$))
             ))
             (and
              (not (vstd!set_lib.impl&%0.is_empty.? $ INT (Poly%vstd!set.Set<int.>. (vstd!raw_ptr.impl&%10.dom.?
                  (Poly%vstd!raw_ptr.PointsToRaw. points_to$)
              ))))
              (exists ((s$ Poly)) (!
                (and
                 (has_type s$ INT)
                 (and
                  (>= (%I s$) size!)
                  (vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. points_to$) (I (uClip
                     SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>. ptr$))
                    )
                   ) s$
                )))
                :pattern ((vstd!raw_ptr.impl&%10.is_range.? (Poly%vstd!raw_ptr.PointsToRaw. points_to$)
                  (I (uClip SZ (vstd!raw_ptr.spec_cast_ptr_to_usize.? $ (UINT 8) (Poly%ptr_mut%<u8.>. ptr$))))
                  s$
                ))
                :qid user_lib__Tlsf__allocate_129
                :skolemid skolem_user_lib__Tlsf__allocate_129
            ))))
            (= (EucMod (vstd!raw_ptr.PtrData./PtrData/addr (%Poly%vstd!raw_ptr.PtrData. (vstd!view.View.view.?
                 $ (PTR $ (UINT 8)) (Poly%ptr_mut%<u8.>. ptr$)
               ))
              ) align!
             ) 0
           ))
           (lib!impl&%0.is_root_provenance.? FLLEN&. FLLEN& SLLEN&. SLLEN& $ (UINT 8) (Poly%lib!Tlsf.
             self!
            ) (Poly%ptr_mut%<u8.>. ptr$)
     )))))))
     (let
      ((tmp%%$ r!))
      (=>
       (is-core!option.Option./None tmp%%$)
       (= pre%self! self!)
     ))
     (lib!impl&%0.wf.? FLLEN&. FLLEN& SLLEN&. SLLEN& (Poly%lib!Tlsf. self!))
   ))
   :pattern ((ens%lib!allocate.impl&%0.allocate. FLLEN&. FLLEN& SLLEN&. SLLEN& pre%self!
     self! size! align! r!
   ))
   :qid internal_ens__lib!allocate.impl&__0.allocate._definition
   :skolemid skolem_internal_ens__lib!allocate.impl&__0.allocate._definition
)))

;; Function-Def lib::Tlsf::allocate
;; src/allocate.rs:525:25: 525:31 (#0)
(set-option :sat.euf true)
(set-option :tactic.default_tactic sat)
(set-option :smt.ematching false)
(set-option :smt.case_split 0)
(get-info :all-statistics)
(declare-const p@ (_ BitVec 64))
(declare-const align! (_ BitVec 64))
(declare-const tmp$$$$bitvectmp1 (_ BitVec 64))
(assert
 (= (let
   ((tmp$$$$bitvectmp0 align!))
   (ite
    (= tmp$$$$bitvectmp0 (_ bv0 64))
    tmp$$$$bitvectmp1
    (bvurem p@ tmp$$$$bitvectmp0)
   )
  ) ((_ zero_extend 63) (_ bv0 1))
))
(assert
 (bvugt align! ((_ zero_extend 63) (_ bv0 1)))
)
(assert
 (= (let
   ((tmp$$$$bitvectmp0 (_ bv16 5)))
   (ite
    (= tmp$$$$bitvectmp0 (_ bv0 5))
    tmp$$$$bitvectmp1
    (bvurem align! ((_ zero_extend 59) tmp$$$$bitvectmp0))
   )
  ) ((_ zero_extend 63) (_ bv0 1))
))
;; bitvector assertion not satisfied
(declare-const %%location_label%%0 Bool)
(assert
 (not (=>
   %%location_label%%0
   (= (let
     ((tmp$$$$bitvectmp0 (_ bv16 5)))
     (ite
      (= tmp$$$$bitvectmp0 (_ bv0 5))
      tmp$$$$bitvectmp1
      (bvurem p@ ((_ zero_extend 59) tmp$$$$bitvectmp0))
     )
    ) ((_ zero_extend 63) (_ bv0 1))
))))
(get-info :all-statistics)
(get-info :version)
(set-option :rlimit 3000000000)
(check-sat)
(set-option :rlimit 0)
(get-info :all-statistics)
