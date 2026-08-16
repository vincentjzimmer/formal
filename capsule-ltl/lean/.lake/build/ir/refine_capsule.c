// Lean compiler output
// Module: refine_capsule
// Imports: Init ltl_capsule
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_UefiCapsuleLTL_advance(lean_object*);
LEAN_EXPORT lean_object* l_UefiCapsuleLTL_detRun___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UefiCapsuleLTL_detRun(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UefiCapsuleLTL_advance(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_3 = lean_box(x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
return x_1;
}
case 1:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
uint8_t x_5; uint8_t x_6; 
x_5 = 2;
x_6 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_5);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 3, x_6);
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
lean_inc(x_9);
lean_inc(x_7);
lean_dec(x_1);
x_11 = 2;
x_12 = 1;
x_13 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_11);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 1, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 2, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*2 + 3, x_12);
return x_13;
}
}
case 2:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = 3;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_15);
return x_1;
}
else
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_inc(x_18);
lean_inc(x_16);
lean_dec(x_1);
x_21 = 3;
x_22 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set_uint8(x_22, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 1, x_17);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 2, x_19);
lean_ctor_set_uint8(x_22, sizeof(void*)*2 + 3, x_20);
return x_22;
}
}
case 3:
{
uint8_t x_23; 
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
uint8_t x_25; uint8_t x_26; 
x_25 = 5;
x_26 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_25);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 1, x_26);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_1);
x_30 = 5;
x_31 = 0;
x_32 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_30);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 2, x_23);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 3, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_nat_dec_lt(x_34, x_35);
if (x_36 == 0)
{
uint8_t x_37; uint8_t x_38; 
x_37 = 5;
x_38 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_37);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 1, x_38);
return x_1;
}
else
{
uint8_t x_39; 
lean_dec(x_34);
x_39 = 4;
lean_inc(x_35);
lean_ctor_set(x_1, 0, x_35);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_39);
return x_1;
}
}
else
{
lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_42 = lean_ctor_get(x_1, 1);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 3);
lean_inc(x_42);
lean_inc(x_40);
lean_dec(x_1);
x_44 = lean_nat_dec_lt(x_40, x_42);
if (x_44 == 0)
{
uint8_t x_45; uint8_t x_46; lean_object* x_47; 
x_45 = 5;
x_46 = 0;
x_47 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_47, 0, x_40);
lean_ctor_set(x_47, 1, x_42);
lean_ctor_set_uint8(x_47, sizeof(void*)*2, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 1, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 2, x_23);
lean_ctor_set_uint8(x_47, sizeof(void*)*2 + 3, x_43);
return x_47;
}
else
{
uint8_t x_48; lean_object* x_49; 
lean_dec(x_40);
x_48 = 4;
lean_inc(x_42);
x_49 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_49, 0, x_42);
lean_ctor_set(x_49, 1, x_42);
lean_ctor_set_uint8(x_49, sizeof(void*)*2, x_48);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 1, x_41);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 2, x_23);
lean_ctor_set_uint8(x_49, sizeof(void*)*2 + 3, x_43);
return x_49;
}
}
}
}
default: 
{
uint8_t x_50; 
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
uint8_t x_51; uint8_t x_52; 
x_51 = 0;
x_52 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_51);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 1, x_52);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 3, x_52);
return x_1;
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_1, 0);
x_54 = lean_ctor_get(x_1, 1);
x_55 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_1);
x_56 = 0;
x_57 = 0;
x_58 = lean_alloc_ctor(0, 2, 4);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_54);
lean_ctor_set_uint8(x_58, sizeof(void*)*2, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 1, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 2, x_55);
lean_ctor_set_uint8(x_58, sizeof(void*)*2 + 3, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_UefiCapsuleLTL_detRun(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_UefiCapsuleLTL_detRun(x_1, x_6);
lean_dec(x_6);
x_8 = l_UefiCapsuleLTL_advance(x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_UefiCapsuleLTL_detRun___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_UefiCapsuleLTL_detRun(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_ltl__capsule(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_refine__capsule(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ltl__capsule(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
