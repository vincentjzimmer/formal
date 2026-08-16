// Lean compiler output
// Module: AbstractAdvance
// Imports: Init AuthVarInstance SecureBootInstance
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
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_UefiAuthVar_advance(lean_object*);
LEAN_EXPORT lean_object* l_UefiSecureBoot_advance(lean_object*);
LEAN_EXPORT lean_object* l_UefiAuthVar_advance(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
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
uint8_t x_5; 
x_5 = 2;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_12 = 2;
x_13 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_9);
lean_ctor_set(x_13, 3, x_10);
lean_ctor_set_uint8(x_13, sizeof(void*)*4, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*4 + 1, x_8);
lean_ctor_set_uint8(x_13, sizeof(void*)*4 + 2, x_11);
return x_13;
}
}
case 2:
{
uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 2);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; 
x_16 = 4;
x_17 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_16);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 1, x_17);
return x_1;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = 4;
x_23 = 0;
x_24 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*4, x_22);
lean_ctor_set_uint8(x_24, sizeof(void*)*4 + 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*4 + 2, x_14);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_ctor_get(x_1, 2);
x_29 = lean_ctor_get(x_1, 3);
x_30 = lean_nat_dec_lt(x_26, x_28);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; 
x_31 = 4;
x_32 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_31);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 1, x_32);
return x_1;
}
else
{
uint8_t x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_33 = 3;
lean_inc(x_29);
lean_inc(x_28);
lean_ctor_set(x_1, 1, x_29);
lean_ctor_set(x_1, 0, x_28);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_33);
return x_1;
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 1);
x_37 = lean_ctor_get(x_1, 2);
x_38 = lean_ctor_get(x_1, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_39 = lean_nat_dec_lt(x_34, x_37);
if (x_39 == 0)
{
uint8_t x_40; uint8_t x_41; lean_object* x_42; 
x_40 = 4;
x_41 = 0;
x_42 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_42, 0, x_34);
lean_ctor_set(x_42, 1, x_35);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*4, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 2, x_14);
return x_42;
}
else
{
uint8_t x_43; lean_object* x_44; 
lean_dec(x_35);
lean_dec(x_34);
x_43 = 3;
lean_inc(x_38);
lean_inc(x_37);
x_44 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_38);
lean_ctor_set(x_44, 2, x_37);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 1, x_36);
lean_ctor_set_uint8(x_44, sizeof(void*)*4 + 2, x_14);
return x_44;
}
}
}
}
default: 
{
uint8_t x_45; 
lean_dec(x_3);
x_45 = !lean_is_exclusive(x_1);
if (x_45 == 0)
{
uint8_t x_46; uint8_t x_47; 
x_46 = 0;
x_47 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 1, x_47);
return x_1;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_1, 0);
x_49 = lean_ctor_get(x_1, 1);
x_50 = lean_ctor_get(x_1, 2);
x_51 = lean_ctor_get(x_1, 3);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 2);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_1);
x_53 = 0;
x_54 = 0;
x_55 = lean_alloc_ctor(0, 4, 3);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_49);
lean_ctor_set(x_55, 2, x_50);
lean_ctor_set(x_55, 3, x_51);
lean_ctor_set_uint8(x_55, sizeof(void*)*4, x_53);
lean_ctor_set_uint8(x_55, sizeof(void*)*4 + 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*4 + 2, x_52);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_UefiSecureBoot_advance(lean_object* x_1) {
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
uint8_t x_5; 
x_5 = 2;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_5);
return x_1;
}
else
{
lean_object* x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
lean_inc(x_8);
lean_inc(x_6);
lean_dec(x_1);
x_10 = 2;
x_11 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set_uint8(x_11, sizeof(void*)*2, x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*2 + 1, x_7);
lean_ctor_set_uint8(x_11, sizeof(void*)*2 + 2, x_9);
return x_11;
}
}
case 2:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_1);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = 4;
x_15 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_14);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 1, x_15);
return x_1;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_1);
x_18 = 4;
x_19 = 0;
x_20 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 2, x_12);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
x_24 = l_List_appendTR___rarg(x_22, x_23);
x_25 = 3;
lean_ctor_set(x_1, 0, x_24);
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_25);
return x_1;
}
else
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_26);
lean_dec(x_1);
lean_inc(x_28);
x_29 = l_List_appendTR___rarg(x_26, x_28);
x_30 = 3;
x_31 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_12);
return x_31;
}
}
}
default: 
{
uint8_t x_32; 
lean_dec(x_3);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; 
x_33 = 0;
x_34 = 0;
lean_ctor_set_uint8(x_1, sizeof(void*)*2, x_33);
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 1, x_34);
return x_1;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_1, 0);
x_36 = lean_ctor_get(x_1, 1);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_1);
x_38 = 0;
x_39 = 0;
x_40 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 1, x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 2, x_37);
return x_40;
}
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_AuthVarInstance(uint8_t builtin, lean_object*);
lean_object* initialize_SecureBootInstance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_AbstractAdvance(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_AuthVarInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_SecureBootInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
