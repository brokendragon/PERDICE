 

#include <stdio.h>
#include "pub_tool_basics.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_mallocfree.h"
#include "po.h"
#include "valgrind.h"
#include "pub_tool_vki.h"
#include "pub_tool_libcfile.h"

#define FFF 	VG_(free)(lquery);\
	VG_(free)(rquery);\
	VG_(free)(tmpbuf);\
	VG_(free)(tmpbuf1);\

extern int varcount;
//extern Bool firstcmp;
extern char* vars_file_name;
/* borrowed from priv/ir/irdefs.c: ppIROp() */
void IROp_to_str(IROp op, Char *buffer) {
    HChar* str;
    IROp    base;
    switch (op) {
        case Iop_Add8 ... Iop_Add64:
            str = "Add"; base = Iop_Add8; break;
        case Iop_Sub8 ... Iop_Sub64:
            str = "Sub"; base = Iop_Sub8; break;
        case Iop_Mul8 ... Iop_Mul64:
            str = "Mul"; base = Iop_Mul8; break;
        case Iop_Or8 ... Iop_Or64:
            str = "Or"; base = Iop_Or8; break;
        case Iop_And8 ... Iop_And64:
            str = "And"; base = Iop_And8; break;
        case Iop_Xor8 ... Iop_Xor64:
            str = "Xor"; base = Iop_Xor8; break;
        case Iop_Shl8 ... Iop_Shl64:
            str = "Shl"; base = Iop_Shl8; break;
        case Iop_Shr8 ... Iop_Shr64:
            str = "Shr"; base = Iop_Shr8; break;
        case Iop_Sar8 ... Iop_Sar64:
            str = "Sar"; base = Iop_Sar8; break;
        case Iop_CmpEQ8 ... Iop_CmpEQ64:
            str = "CmpEQ"; base = Iop_CmpEQ8; break;
        case Iop_CmpNE8 ... Iop_CmpNE64:
            str = "CmpNE"; base = Iop_CmpNE8; break;
		/*
        case Iop_CasCmpEQ8 ... Iop_CasCmpEQ64:
            str = "CasCmpEQ"; base = Iop_CasCmpEQ8; break;
        case Iop_CasCmpNE8 ... Iop_CasCmpNE64:
            str = "CasCmpNE"; base = Iop_CasCmpNE8; break;
		*/
        case Iop_Not8 ... Iop_Not64:
            str = "Not"; base = Iop_Not8; break;
        /* other cases must explicitly "return;" */
         case Iop_8Uto16:    VG_(strcpy)(buffer, "8Uto16");  return;
         case Iop_8Uto32:    VG_(strcpy)(buffer, "8Uto32");  return;
         case Iop_16Uto32:  VG_(strcpy)(buffer, "16Uto32"); return;
         case Iop_8Sto16:    VG_(strcpy)(buffer, "8Sto16");  return;
         case Iop_8Sto32:    VG_(strcpy)(buffer, "8Sto32");  return;
         case Iop_16Sto32:  VG_(strcpy)(buffer, "16Sto32"); return;
         case Iop_32Sto64:  VG_(strcpy)(buffer, "32Sto64"); return;
         case Iop_32Uto64:  VG_(strcpy)(buffer, "32Uto64"); return;
         case Iop_32to8:     VG_(strcpy)(buffer, "32to8");    return;
         case Iop_16Uto64:  VG_(strcpy)(buffer, "16Uto64"); return;
         case Iop_16Sto64:  VG_(strcpy)(buffer, "16Sto64"); return;
         case Iop_8Uto64:    VG_(strcpy)(buffer, "8Uto64"); return;
         case Iop_8Sto64:    VG_(strcpy)(buffer, "8Sto64"); return;
         case Iop_64to16:    VG_(strcpy)(buffer, "64to16"); return;
         case Iop_64to8:     VG_(strcpy)(buffer, "64to8");  return;

         case Iop_Not1:      VG_(strcpy)(buffer, "Not1");     return;
         case Iop_32to1:     VG_(strcpy)(buffer, "32to1");    return;
         case Iop_64to1:     VG_(strcpy)(buffer, "64to1");    return;
         case Iop_1Uto8:     VG_(strcpy)(buffer, "1Uto8");    return;
         case Iop_1Uto32:    VG_(strcpy)(buffer, "1Uto32");  return;
         case Iop_1Uto64:    VG_(strcpy)(buffer, "1Uto64");  return;
         case Iop_1Sto8:     VG_(strcpy)(buffer, "1Sto8");  return;
         case Iop_1Sto16:    VG_(strcpy)(buffer, "1Sto16");  return;
         case Iop_1Sto32:    VG_(strcpy)(buffer, "1Sto32");  return;
         case Iop_1Sto64:    VG_(strcpy)(buffer, "1Sto64");  return;

         case Iop_MullS8:    VG_(strcpy)(buffer, "MullS8");  return;
         case Iop_MullS16:  VG_(strcpy)(buffer, "MullS16"); return;
         case Iop_MullS32:  VG_(strcpy)(buffer, "MullS32"); return;
         case Iop_MullS64:  VG_(strcpy)(buffer, "MullS64"); return;
         case Iop_MullU8:    VG_(strcpy)(buffer, "MullU8");  return;
         case Iop_MullU16:  VG_(strcpy)(buffer, "MullU16"); return;
         case Iop_MullU32:  VG_(strcpy)(buffer, "MullU32"); return;
         case Iop_MullU64:  VG_(strcpy)(buffer, "MullU64"); return;

         case Iop_Clz64:     VG_(strcpy)(buffer, "Clz64"); return;
         case Iop_Clz32:     VG_(strcpy)(buffer, "Clz32"); return;
         case Iop_Ctz64:     VG_(strcpy)(buffer, "Ctz64"); return;
         case Iop_Ctz32:     VG_(strcpy)(buffer, "Ctz32"); return;

         case Iop_CmpLT32S: VG_(strcpy)(buffer, "CmpLT32S"); return;
         case Iop_CmpLE32S: VG_(strcpy)(buffer, "CmpLE32S"); return;
         case Iop_CmpLT32U: VG_(strcpy)(buffer, "CmpLT32U"); return;
         case Iop_CmpLE32U: VG_(strcpy)(buffer, "CmpLE32U"); return;

         case Iop_CmpLT64S: VG_(strcpy)(buffer, "CmpLT64S"); return;
         case Iop_CmpLE64S: VG_(strcpy)(buffer, "CmpLE64S"); return;
         case Iop_CmpLT64U: VG_(strcpy)(buffer, "CmpLT64U"); return;
         case Iop_CmpLE64U: VG_(strcpy)(buffer, "CmpLE64U"); return;

         case Iop_CmpNEZ8:  VG_(strcpy)(buffer, "CmpNEZ8"); return;
         case Iop_CmpNEZ16: VG_(strcpy)(buffer, "CmpNEZ16"); return;
         case Iop_CmpNEZ32: VG_(strcpy)(buffer, "CmpNEZ32"); return;
         case Iop_CmpNEZ64: VG_(strcpy)(buffer, "CmpNEZ64"); return;

         case Iop_CmpwNEZ32: VG_(strcpy)(buffer, "CmpwNEZ32"); return;
         case Iop_CmpwNEZ64: VG_(strcpy)(buffer, "CmpwNEZ64"); return;

         case Iop_Left8:  VG_(strcpy)(buffer, "Left8"); return;
         case Iop_Left16: VG_(strcpy)(buffer, "Left16"); return;
         case Iop_Left32: VG_(strcpy)(buffer, "Left32"); return;
         case Iop_Left64: VG_(strcpy)(buffer, "Left64"); return;
         case Iop_Max32U: VG_(strcpy)(buffer, "Max32U"); return;

         case Iop_CmpORD32U: VG_(strcpy)(buffer, "CmpORD32U"); return;
         case Iop_CmpORD32S: VG_(strcpy)(buffer, "CmpORD32S"); return;

         case Iop_CmpORD64U: VG_(strcpy)(buffer, "CmpORD64U"); return;
         case Iop_CmpORD64S: VG_(strcpy)(buffer, "CmpORD64S"); return;

         case Iop_DivU32: VG_(strcpy)(buffer, "DivU32"); return;
         case Iop_DivS32: VG_(strcpy)(buffer, "DivS32"); return;
         case Iop_DivU64: VG_(strcpy)(buffer, "DivU64"); return;
         case Iop_DivS64: VG_(strcpy)(buffer, "DivS64"); return;
         case Iop_DivU64E: VG_(strcpy)(buffer, "DivU64E"); return;
         case Iop_DivS64E: VG_(strcpy)(buffer, "DivS64E"); return;
         case Iop_DivU32E: VG_(strcpy)(buffer, "DivU32E"); return;
         case Iop_DivS32E: VG_(strcpy)(buffer, "DivS32E"); return;

         case Iop_DivModU64to32: VG_(strcpy)(buffer, "DivModU64to32"); return;
         case Iop_DivModS64to32: VG_(strcpy)(buffer, "DivModS64to32"); return;

         case Iop_DivModU128to64: VG_(strcpy)(buffer, "DivModU128to64"); return;
         case Iop_DivModS128to64: VG_(strcpy)(buffer, "DivModS128to64"); return;

         case Iop_DivModS64to64: VG_(strcpy)(buffer, "DivModS64to64"); return;
         case Iop_16HIto8:  VG_(strcpy)(buffer, "16HIto8"); return;
         case Iop_16to8:     VG_(strcpy)(buffer, "16to8");    return;
         case Iop_8HLto16:  VG_(strcpy)(buffer, "8HLto16"); return;

         case Iop_32HIto16: VG_(strcpy)(buffer, "32HIto16"); return;
         case Iop_32to16:    VG_(strcpy)(buffer, "32to16");    return;
         case Iop_16HLto32: VG_(strcpy)(buffer, "16HLto32"); return;

         case Iop_64HIto32: VG_(strcpy)(buffer, "64HIto32"); return;
         case Iop_64to32:    VG_(strcpy)(buffer, "64to32");    return;
         case Iop_32HLto64: VG_(strcpy)(buffer, "32HLto64"); return;

         case Iop_128HIto64: VG_(strcpy)(buffer, "128HIto64"); return;
         case Iop_128to64:    VG_(strcpy)(buffer, "128to64");    return;
         case Iop_64HLto128: VG_(strcpy)(buffer, "64HLto128"); return;

         case Iop_CmpF32:    VG_(strcpy)(buffer, "CmpF32");    return;
         case Iop_F32toI16S: VG_(strcpy)(buffer, "F32toI16S");  return;
         case Iop_F32toI32S: VG_(strcpy)(buffer, "F32toI32S");  return;
         case Iop_F32toI64S: VG_(strcpy)(buffer, "F32toI64S");  return;
         case Iop_I16StoF32: VG_(strcpy)(buffer, "I16StoF32");  return;
         case Iop_I32StoF32: VG_(strcpy)(buffer, "I32StoF32");  return;
         case Iop_I64StoF32: VG_(strcpy)(buffer, "I64StoF32");  return;
         case Iop_AddF64:     VG_(strcpy)(buffer, "AddF64"); return;
         case Iop_SubF64:     VG_(strcpy)(buffer, "SubF64"); return;
         case Iop_MulF64:     VG_(strcpy)(buffer, "MulF64"); return;
         case Iop_DivF64:     VG_(strcpy)(buffer, "DivF64"); return;
         case Iop_AddF64r32: VG_(strcpy)(buffer, "AddF64r32"); return;
         case Iop_SubF64r32: VG_(strcpy)(buffer, "SubF64r32"); return;
         case Iop_MulF64r32: VG_(strcpy)(buffer, "MulF64r32"); return;
         case Iop_DivF64r32: VG_(strcpy)(buffer, "DivF64r32"); return;
         case Iop_AddF32:    VG_(strcpy)(buffer, "AddF32"); return;
         case Iop_SubF32:    VG_(strcpy)(buffer, "SubF32"); return;
         case Iop_MulF32:    VG_(strcpy)(buffer, "MulF32"); return;
         case Iop_DivF32:    VG_(strcpy)(buffer, "DivF32"); return;

         case Iop_ScaleF64:        VG_(strcpy)(buffer, "ScaleF64"); return;
         case Iop_AtanF64:         VG_(strcpy)(buffer, "AtanF64"); return;
         case Iop_Yl2xF64:         VG_(strcpy)(buffer, "Yl2xF64"); return;
         case Iop_Yl2xp1F64:      VG_(strcpy)(buffer, "Yl2xp1F64"); return;
         case Iop_PRemF64:         VG_(strcpy)(buffer, "PRemF64"); return;
         case Iop_PRemC3210F64:  VG_(strcpy)(buffer, "PRemC3210F64"); return;
         case Iop_PRem1F64:        VG_(strcpy)(buffer, "PRem1F64"); return;
         case Iop_PRem1C3210F64: VG_(strcpy)(buffer, "PRem1C3210F64"); return;
         case Iop_NegF64:        VG_(strcpy)(buffer, "NegF64"); return;
         case Iop_AbsF64:        VG_(strcpy)(buffer, "AbsF64"); return;
         case Iop_NegF32:        VG_(strcpy)(buffer, "NegF32"); return;
         case Iop_AbsF32:        VG_(strcpy)(buffer, "AbsF32"); return;
         case Iop_SqrtF64:       VG_(strcpy)(buffer, "SqrtF64"); return;
         case Iop_SqrtF32:       VG_(strcpy)(buffer, "SqrtF32"); return;
         case Iop_SinF64:     VG_(strcpy)(buffer, "SinF64"); return;
         case Iop_CosF64:     VG_(strcpy)(buffer, "CosF64"); return;
         case Iop_TanF64:     VG_(strcpy)(buffer, "TanF64"); return;
         case Iop_2xm1F64:    VG_(strcpy)(buffer, "2xm1F64"); return;

         case Iop_MAddF64:     VG_(strcpy)(buffer, "MAddF64"); return;
         case Iop_MSubF64:     VG_(strcpy)(buffer, "MSubF64"); return;
         case Iop_MAddF64r32: VG_(strcpy)(buffer, "MAddF64r32"); return;
         case Iop_MSubF64r32: VG_(strcpy)(buffer, "MSubF64r32"); return;

         case Iop_Est5FRSqrt:     VG_(strcpy)(buffer, "Est5FRSqrt"); return;
         case Iop_TruncF64asF32: VG_(strcpy)(buffer, "TruncF64asF32"); return;
         case Iop_CalcFPRF:        VG_(strcpy)(buffer, "CalcFPRF"); return;

         case Iop_CmpF64:     VG_(strcpy)(buffer, "CmpF64"); return;

         case Iop_F64toI16S: VG_(strcpy)(buffer, "F64toI16S"); return;
         case Iop_F64toI32S: VG_(strcpy)(buffer, "F64toI32S"); return;
         case Iop_F64toI64S: VG_(strcpy)(buffer, "F64toI64S"); return;
         case Iop_F64toI64U: VG_(strcpy)(buffer, "F64toI64U"); return;

         case Iop_F64toI32U: VG_(strcpy)(buffer, "F64toI32U"); return;

         case Iop_I16StoF64: VG_(strcpy)(buffer, "I16StoF64"); return;
         case Iop_I32StoF64: VG_(strcpy)(buffer, "I32StoF64"); return;
         case Iop_I64StoF64: VG_(strcpy)(buffer, "I64StoF64"); return;
         case Iop_I64UtoF64: VG_(strcpy)(buffer, "I64UtoF64"); return;
         case Iop_I64UtoF32: VG_(strcpy)(buffer, "I64UtoF32"); return;

         case Iop_I32UtoF64: VG_(strcpy)(buffer, "I32UtoF64"); return;

         case Iop_F32toF64: VG_(strcpy)(buffer, "F32toF64"); return;
         case Iop_F64toF32: VG_(strcpy)(buffer, "F64toF32"); return;
        
         case Iop_RoundF64toInt: VG_(strcpy)(buffer, "RoundF64toInt"); return;
         case Iop_RoundF64toF32: VG_(strcpy)(buffer, "RoundF64toF32"); return;

         case Iop_ReinterpF64asI64: VG_(strcpy)(buffer, "ReinterpF64asI64"); return;
         case Iop_ReinterpI64asF64: VG_(strcpy)(buffer, "ReinterpI64asF64"); return;
         case Iop_ReinterpF32asI32: VG_(strcpy)(buffer, "ReinterpF32asI32"); return;
         case Iop_ReinterpI32asF32: VG_(strcpy)(buffer, "ReinterpI32asF32"); return;

         case Iop_I32UtoFx4: VG_(strcpy)(buffer, "Iop_I32UtoFx4"); return;
         case Iop_I32StoFx4: VG_(strcpy)(buffer, "Iop_I32StoFx4"); return;

         case Iop_QFtoI32Ux4_RZ: VG_(strcpy)(buffer, "Iop_QFtoI32Ux4_RZ"); return;
         case Iop_QFtoI32Sx4_RZ: VG_(strcpy)(buffer, "Iop_QFtoI32Sx4_RZ"); return;

         case Iop_RoundF32x4_RM: VG_(strcpy)(buffer, "Iop_RoundF32x4_RM"); return;
         case Iop_RoundF32x4_RP: VG_(strcpy)(buffer, "Iop_RoundF32x4_RP"); return;
         case Iop_RoundF32x4_RN: VG_(strcpy)(buffer, "Iop_RoundF32x4_RN"); return;
         case Iop_RoundF32x4_RZ: VG_(strcpy)(buffer, "Iop_RoundF32x4_RZ"); return;

         case Iop_Add8x8: VG_(strcpy)(buffer, "Add8x8"); return;
         case Iop_Add16x4: VG_(strcpy)(buffer, "Add16x4"); return;
         case Iop_Add32x2: VG_(strcpy)(buffer, "Add32x2"); return;
         case Iop_QAdd8Ux8: VG_(strcpy)(buffer, "QAdd8Ux8"); return;
         case Iop_QAdd16Ux4: VG_(strcpy)(buffer, "QAdd16Ux4"); return;
         case Iop_QAdd32Ux2: VG_(strcpy)(buffer, "QAdd32Ux2"); return;
         case Iop_QAdd64Ux1: VG_(strcpy)(buffer, "QAdd64Ux1"); return;
         case Iop_QAdd8Sx8: VG_(strcpy)(buffer, "QAdd8Sx8"); return;
         case Iop_QAdd16Sx4: VG_(strcpy)(buffer, "QAdd16Sx4"); return;
         case Iop_QAdd32Sx2: VG_(strcpy)(buffer, "QAdd32Sx2"); return;
         case Iop_QAdd64Sx1: VG_(strcpy)(buffer, "QAdd64Sx1"); return;
         case Iop_Sub8x8: VG_(strcpy)(buffer, "Sub8x8"); return;
         case Iop_Sub16x4: VG_(strcpy)(buffer, "Sub16x4"); return;
         case Iop_Sub32x2: VG_(strcpy)(buffer, "Sub32x2"); return;
         case Iop_QSub8Ux8: VG_(strcpy)(buffer, "QSub8Ux8"); return;
         case Iop_QSub16Ux4: VG_(strcpy)(buffer, "QSub16Ux4"); return;
         case Iop_QSub8Sx8: VG_(strcpy)(buffer, "QSub8Sx8"); return;
         case Iop_QSub16Sx4: VG_(strcpy)(buffer, "QSub16Sx4"); return;
         case Iop_Mul16x4: VG_(strcpy)(buffer, "Mul16x4"); return;
         case Iop_Mul32x2: VG_(strcpy)(buffer, "Mul32x2"); return;
         case Iop_MulHi16Ux4: VG_(strcpy)(buffer, "MulHi16Ux4"); return;
         case Iop_MulHi16Sx4: VG_(strcpy)(buffer, "MulHi16Sx4"); return;
         case Iop_Avg8Ux8: VG_(strcpy)(buffer, "Avg8Ux8"); return;
         case Iop_Avg16Ux4: VG_(strcpy)(buffer, "Avg16Ux4"); return;
         case Iop_Max16Sx4: VG_(strcpy)(buffer, "Max16Sx4"); return;
         case Iop_Max8Ux8: VG_(strcpy)(buffer, "Max8Ux8"); return;
         case Iop_Min16Sx4: VG_(strcpy)(buffer, "Min16Sx4"); return;
         case Iop_Min8Ux8: VG_(strcpy)(buffer, "Min8Ux8"); return;
         case Iop_CmpEQ8x8: VG_(strcpy)(buffer, "CmpEQ8x8"); return;
         case Iop_CmpEQ16x4: VG_(strcpy)(buffer, "CmpEQ16x4"); return;
         case Iop_CmpEQ32x2: VG_(strcpy)(buffer, "CmpEQ32x2"); return;
         case Iop_CmpGT8Sx8: VG_(strcpy)(buffer, "CmpGT8Sx8"); return;
         case Iop_CmpGT16Sx4: VG_(strcpy)(buffer, "CmpGT16Sx4"); return;
         case Iop_CmpGT32Sx2: VG_(strcpy)(buffer, "CmpGT32Sx2"); return;
         case Iop_ShlN8x8: VG_(strcpy)(buffer, "ShlN8x8"); return;
         case Iop_ShlN16x4: VG_(strcpy)(buffer, "ShlN16x4"); return;
         case Iop_ShlN32x2: VG_(strcpy)(buffer, "ShlN32x2"); return;
         case Iop_ShrN16x4: VG_(strcpy)(buffer, "ShrN16x4"); return;
         case Iop_ShrN32x2: VG_(strcpy)(buffer, "ShrN32x2"); return;
         case Iop_SarN8x8: VG_(strcpy)(buffer, "SarN8x8"); return;
         case Iop_SarN16x4: VG_(strcpy)(buffer, "SarN16x4"); return;
         case Iop_SarN32x2: VG_(strcpy)(buffer, "SarN32x2"); return;
         case Iop_QNarrowBin16Sto8Ux8: VG_(strcpy)(buffer, "QNarrowBin16Sto8Ux8"); return;
         case Iop_QNarrowBin16Sto8Sx8: VG_(strcpy)(buffer, "QNarrowBin16Sto8Sx8"); return;
         case Iop_QNarrowBin32Sto16Sx4: VG_(strcpy)(buffer, "QNarrowBin32Sto16Sx4"); return;
         case Iop_NarrowBin16to8x8: VG_(strcpy)(buffer, "NarrowBin16to8x8"); return;
         case Iop_NarrowBin32to16x4: VG_(strcpy)(buffer, "NarrowBin32to16x4"); return;
         case Iop_InterleaveHI8x8: VG_(strcpy)(buffer, "InterleaveHI8x8"); return;
         case Iop_InterleaveHI16x4: VG_(strcpy)(buffer, "InterleaveHI16x4"); return;
         case Iop_InterleaveHI32x2: VG_(strcpy)(buffer, "InterleaveHI32x2"); return;
         case Iop_InterleaveLO8x8: VG_(strcpy)(buffer, "InterleaveLO8x8"); return;
         case Iop_InterleaveLO16x4: VG_(strcpy)(buffer, "InterleaveLO16x4"); return;
         case Iop_InterleaveLO32x2: VG_(strcpy)(buffer, "InterleaveLO32x2"); return;
         case Iop_CatOddLanes8x8: VG_(strcpy)(buffer, "CatOddLanes8x8"); return;
         case Iop_CatOddLanes16x4: VG_(strcpy)(buffer, "CatOddLanes16x4"); return;
         case Iop_CatEvenLanes8x8: VG_(strcpy)(buffer, "CatEvenLanes8x8"); return;
         case Iop_CatEvenLanes16x4: VG_(strcpy)(buffer, "CatEvenLanes16x4"); return;
         case Iop_Perm8x8: VG_(strcpy)(buffer, "Iop_Perm8x8"); return;

         case Iop_CmpNEZ32x2: VG_(strcpy)(buffer, "CmpNEZ32x2"); return;
         case Iop_CmpNEZ16x4: VG_(strcpy)(buffer, "CmpNEZ16x4"); return;
         case Iop_CmpNEZ8x8:  VG_(strcpy)(buffer, "CmpNEZ8x8"); return;

         case Iop_Add32Fx4:  VG_(strcpy)(buffer, "Add32Fx4"); return;
         case Iop_Add32Fx2:  VG_(strcpy)(buffer, "Add32Fx2"); return;
         case Iop_Add32F0x4: VG_(strcpy)(buffer, "Add32F0x4"); return;
         case Iop_Add64Fx2:  VG_(strcpy)(buffer, "Add64Fx2"); return;
         case Iop_Add64F0x2: VG_(strcpy)(buffer, "Add64F0x2"); return;

         case Iop_Div32Fx4:  VG_(strcpy)(buffer, "Div32Fx4"); return;
         case Iop_Div32F0x4: VG_(strcpy)(buffer, "Div32F0x4"); return;
         case Iop_Div64Fx2:  VG_(strcpy)(buffer, "Div64Fx2"); return;
         case Iop_Div64F0x2: VG_(strcpy)(buffer, "Div64F0x2"); return;

         case Iop_Max32Fx4:  VG_(strcpy)(buffer, "Max32Fx4"); return;
         case Iop_Max32F0x4: VG_(strcpy)(buffer, "Max32F0x4"); return;
         case Iop_Max64Fx2:  VG_(strcpy)(buffer, "Max64Fx2"); return;
         case Iop_Max64F0x2: VG_(strcpy)(buffer, "Max64F0x2"); return;

         case Iop_Min32Fx4:  VG_(strcpy)(buffer, "Min32Fx4"); return;
         case Iop_Min32F0x4: VG_(strcpy)(buffer, "Min32F0x4"); return;
         case Iop_Min64Fx2:  VG_(strcpy)(buffer, "Min64Fx2"); return;
         case Iop_Min64F0x2: VG_(strcpy)(buffer, "Min64F0x2"); return;

         case Iop_Mul32Fx4:  VG_(strcpy)(buffer, "Mul32Fx4"); return;
         case Iop_Mul32F0x4: VG_(strcpy)(buffer, "Mul32F0x4"); return;
         case Iop_Mul64Fx2:  VG_(strcpy)(buffer, "Mul64Fx2"); return;
         case Iop_Mul64F0x2: VG_(strcpy)(buffer, "Mul64F0x2"); return;

         case Iop_Recip32Fx4:  VG_(strcpy)(buffer, "Recip32Fx4"); return;
         case Iop_Recip32F0x4: VG_(strcpy)(buffer, "Recip32F0x4"); return;
         case Iop_Recip64Fx2:  VG_(strcpy)(buffer, "Recip64Fx2"); return;
         case Iop_Recip64F0x2: VG_(strcpy)(buffer, "Recip64F0x2"); return;

         case Iop_RSqrt32Fx4:  VG_(strcpy)(buffer, "RSqrt32Fx4"); return;
         case Iop_RSqrt32F0x4: VG_(strcpy)(buffer, "RSqrt32F0x4"); return;
         case Iop_RSqrt64Fx2:  VG_(strcpy)(buffer, "RSqrt64Fx2"); return;
         case Iop_RSqrt64F0x2: VG_(strcpy)(buffer, "RSqrt64F0x2"); return;

         case Iop_Sqrt32Fx4:  VG_(strcpy)(buffer, "Sqrt32Fx4"); return;
         case Iop_Sqrt32F0x4: VG_(strcpy)(buffer, "Sqrt32F0x4"); return;
         case Iop_Sqrt64Fx2:  VG_(strcpy)(buffer, "Sqrt64Fx2"); return;
         case Iop_Sqrt64F0x2: VG_(strcpy)(buffer, "Sqrt64F0x2"); return;

         case Iop_Sub32Fx4:  VG_(strcpy)(buffer, "Sub32Fx4"); return;
         case Iop_Sub32Fx2:  VG_(strcpy)(buffer, "Sub32Fx2"); return;
         case Iop_Sub32F0x4: VG_(strcpy)(buffer, "Sub32F0x4"); return;
         case Iop_Sub64Fx2:  VG_(strcpy)(buffer, "Sub64Fx2"); return;
         case Iop_Sub64F0x2: VG_(strcpy)(buffer, "Sub64F0x2"); return;

         case Iop_CmpEQ32Fx4: VG_(strcpy)(buffer, "CmpEQ32Fx4"); return;
         case Iop_CmpLT32Fx4: VG_(strcpy)(buffer, "CmpLT32Fx4"); return;
         case Iop_CmpLE32Fx4: VG_(strcpy)(buffer, "CmpLE32Fx4"); return;
         case Iop_CmpGT32Fx4: VG_(strcpy)(buffer, "CmpGT32Fx4"); return;
         case Iop_CmpGE32Fx4: VG_(strcpy)(buffer, "CmpGE32Fx4"); return;
         case Iop_CmpUN32Fx4: VG_(strcpy)(buffer, "CmpUN32Fx4"); return;
         case Iop_CmpEQ64Fx2: VG_(strcpy)(buffer, "CmpEQ64Fx2"); return;
         case Iop_CmpLT64Fx2: VG_(strcpy)(buffer, "CmpLT64Fx2"); return;
         case Iop_CmpLE64Fx2: VG_(strcpy)(buffer, "CmpLE64Fx2"); return;
         case Iop_CmpUN64Fx2: VG_(strcpy)(buffer, "CmpUN64Fx2"); return;
         case Iop_CmpGT32Fx2: VG_(strcpy)(buffer, "CmpGT32Fx2"); return;
         case Iop_CmpEQ32Fx2: VG_(strcpy)(buffer, "CmpEQ32Fx2"); return;
         case Iop_CmpGE32Fx2: VG_(strcpy)(buffer, "CmpGE32Fx2"); return;

         case Iop_CmpEQ32F0x4: VG_(strcpy)(buffer, "CmpEQ32F0x4"); return;
         case Iop_CmpLT32F0x4: VG_(strcpy)(buffer, "CmpLT32F0x4"); return;
         case Iop_CmpLE32F0x4: VG_(strcpy)(buffer, "CmpLE32F0x4"); return;
         case Iop_CmpUN32F0x4: VG_(strcpy)(buffer, "CmpUN32F0x4"); return;
         case Iop_CmpEQ64F0x2: VG_(strcpy)(buffer, "CmpEQ64F0x2"); return;
         case Iop_CmpLT64F0x2: VG_(strcpy)(buffer, "CmpLT64F0x2"); return;
         case Iop_CmpLE64F0x2: VG_(strcpy)(buffer, "CmpLE64F0x2"); return;
         case Iop_CmpUN64F0x2: VG_(strcpy)(buffer, "CmpUN64F0x2"); return;

         case Iop_V128to64:    VG_(strcpy)(buffer, "V128to64");    return;
         case Iop_V128HIto64: VG_(strcpy)(buffer, "V128HIto64"); return;
         case Iop_64HLtoV128: VG_(strcpy)(buffer, "64HLtoV128"); return;

         case Iop_64UtoV128:    VG_(strcpy)(buffer, "64UtoV128"); return;
         case Iop_SetV128lo64: VG_(strcpy)(buffer, "SetV128lo64"); return;

         case Iop_32UtoV128:    VG_(strcpy)(buffer, "32UtoV128"); return;
         case Iop_V128to32:     VG_(strcpy)(buffer, "V128to32"); return;
         case Iop_SetV128lo32: VG_(strcpy)(buffer, "SetV128lo32"); return;

         case Iop_Dup8x16: VG_(strcpy)(buffer, "Dup8x16"); return;
         case Iop_Dup16x8: VG_(strcpy)(buffer, "Dup16x8"); return;
         case Iop_Dup32x4: VG_(strcpy)(buffer, "Dup32x4"); return;

         case Iop_NotV128:     VG_(strcpy)(buffer, "NotV128"); return;
         case Iop_AndV128:     VG_(strcpy)(buffer, "AndV128"); return;
         case Iop_OrV128:      VG_(strcpy)(buffer, "OrV128");  return;
         case Iop_XorV128:     VG_(strcpy)(buffer, "XorV128"); return;

         case Iop_CmpNEZ8x16: VG_(strcpy)(buffer, "CmpNEZ8x16"); return;
         case Iop_CmpNEZ16x8: VG_(strcpy)(buffer, "CmpNEZ16x8"); return;
         case Iop_CmpNEZ32x4: VG_(strcpy)(buffer, "CmpNEZ32x4"); return;
         case Iop_CmpNEZ64x2: VG_(strcpy)(buffer, "CmpNEZ64x2"); return;

         case Iop_Add8x16:    VG_(strcpy)(buffer, "Add8x16"); return;
         case Iop_Add16x8:    VG_(strcpy)(buffer, "Add16x8"); return;
         case Iop_Add32x4:    VG_(strcpy)(buffer, "Add32x4"); return;
         case Iop_Add64x2:    VG_(strcpy)(buffer, "Add64x2"); return;
         case Iop_QAdd8Ux16: VG_(strcpy)(buffer, "QAdd8Ux16"); return;
         case Iop_QAdd16Ux8: VG_(strcpy)(buffer, "QAdd16Ux8"); return;
         case Iop_QAdd32Ux4: VG_(strcpy)(buffer, "QAdd32Ux4"); return;
         case Iop_QAdd8Sx16: VG_(strcpy)(buffer, "QAdd8Sx16"); return;
         case Iop_QAdd16Sx8: VG_(strcpy)(buffer, "QAdd16Sx8"); return;
         case Iop_QAdd32Sx4: VG_(strcpy)(buffer, "QAdd32Sx4"); return;

         case Iop_Sub8x16:    VG_(strcpy)(buffer, "Sub8x16"); return;
         case Iop_Sub16x8:    VG_(strcpy)(buffer, "Sub16x8"); return;
         case Iop_Sub32x4:    VG_(strcpy)(buffer, "Sub32x4"); return;
         case Iop_Sub64x2:    VG_(strcpy)(buffer, "Sub64x2"); return;
         case Iop_QSub8Ux16: VG_(strcpy)(buffer, "QSub8Ux16"); return;
         case Iop_QSub16Ux8: VG_(strcpy)(buffer, "QSub16Ux8"); return;
         case Iop_QSub32Ux4: VG_(strcpy)(buffer, "QSub32Ux4"); return;
         case Iop_QSub8Sx16: VG_(strcpy)(buffer, "QSub8Sx16"); return;
         case Iop_QSub16Sx8: VG_(strcpy)(buffer, "QSub16Sx8"); return;
         case Iop_QSub32Sx4: VG_(strcpy)(buffer, "QSub32Sx4"); return;

         case Iop_Mul16x8:     VG_(strcpy)(buffer, "Mul16x8"); return;
         case Iop_MulHi16Ux8: VG_(strcpy)(buffer, "MulHi16Ux8"); return;
         case Iop_MulHi32Ux4: VG_(strcpy)(buffer, "MulHi32Ux4"); return;
         case Iop_MulHi16Sx8: VG_(strcpy)(buffer, "MulHi16Sx8"); return;
         case Iop_MulHi32Sx4: VG_(strcpy)(buffer, "MulHi32Sx4"); return;

         case Iop_MullEven8Ux16: VG_(strcpy)(buffer, "MullEven8Ux16"); return;
         case Iop_MullEven16Ux8: VG_(strcpy)(buffer, "MullEven16Ux8"); return;
         case Iop_MullEven8Sx16: VG_(strcpy)(buffer, "MullEven8Sx16"); return;
         case Iop_MullEven16Sx8: VG_(strcpy)(buffer, "MullEven16Sx8"); return;

         case Iop_Avg8Ux16: VG_(strcpy)(buffer, "Avg8Ux16"); return;
         case Iop_Avg16Ux8: VG_(strcpy)(buffer, "Avg16Ux8"); return;
         case Iop_Avg32Ux4: VG_(strcpy)(buffer, "Avg32Ux4"); return;
         case Iop_Avg8Sx16: VG_(strcpy)(buffer, "Avg8Sx16"); return;
         case Iop_Avg16Sx8: VG_(strcpy)(buffer, "Avg16Sx8"); return;
         case Iop_Avg32Sx4: VG_(strcpy)(buffer, "Avg32Sx4"); return;

         case Iop_Max8Sx16: VG_(strcpy)(buffer, "Max8Sx16"); return;
         case Iop_Max16Sx8: VG_(strcpy)(buffer, "Max16Sx8"); return;
         case Iop_Max32Sx4: VG_(strcpy)(buffer, "Max32Sx4"); return;
         case Iop_Max8Ux16: VG_(strcpy)(buffer, "Max8Ux16"); return;
         case Iop_Max16Ux8: VG_(strcpy)(buffer, "Max16Ux8"); return;
         case Iop_Max32Ux4: VG_(strcpy)(buffer, "Max32Ux4"); return;

         case Iop_Min8Sx16: VG_(strcpy)(buffer, "Min8Sx16"); return;
         case Iop_Min16Sx8: VG_(strcpy)(buffer, "Min16Sx8"); return;
         case Iop_Min32Sx4: VG_(strcpy)(buffer, "Min32Sx4"); return;
         case Iop_Min8Ux16: VG_(strcpy)(buffer, "Min8Ux16"); return;
         case Iop_Min16Ux8: VG_(strcpy)(buffer, "Min16Ux8"); return;
         case Iop_Min32Ux4: VG_(strcpy)(buffer, "Min32Ux4"); return;

         case Iop_CmpEQ8x16:  VG_(strcpy)(buffer, "CmpEQ8x16"); return;
         case Iop_CmpEQ16x8:  VG_(strcpy)(buffer, "CmpEQ16x8"); return;
         case Iop_CmpEQ32x4:  VG_(strcpy)(buffer, "CmpEQ32x4"); return;
         case Iop_CmpEQ64x2:  VG_(strcpy)(buffer, "CmpEQ64x2"); return;
         case Iop_CmpGT8Sx16: VG_(strcpy)(buffer, "CmpGT8Sx16"); return;
         case Iop_CmpGT16Sx8: VG_(strcpy)(buffer, "CmpGT16Sx8"); return;
         case Iop_CmpGT32Sx4: VG_(strcpy)(buffer, "CmpGT32Sx4"); return;
         case Iop_CmpGT64Sx2: VG_(strcpy)(buffer, "CmpGT64Sx2"); return;
         case Iop_CmpGT8Ux16: VG_(strcpy)(buffer, "CmpGT8Ux16"); return;
         case Iop_CmpGT16Ux8: VG_(strcpy)(buffer, "CmpGT16Ux8"); return;
         case Iop_CmpGT32Ux4: VG_(strcpy)(buffer, "CmpGT32Ux4"); return;

         case Iop_Cnt8x16: VG_(strcpy)(buffer, "Cnt8x16"); return;
         case Iop_Clz8Sx16: VG_(strcpy)(buffer, "Clz8Sx16"); return;
         case Iop_Clz16Sx8: VG_(strcpy)(buffer, "Clz16Sx8"); return;
         case Iop_Clz32Sx4: VG_(strcpy)(buffer, "Clz32Sx4"); return;
         case Iop_Cls8Sx16: VG_(strcpy)(buffer, "Cls8Sx16"); return;
         case Iop_Cls16Sx8: VG_(strcpy)(buffer, "Cls16Sx8"); return;
         case Iop_Cls32Sx4: VG_(strcpy)(buffer, "Cls32Sx4"); return;
         case Iop_ShlV128: VG_(strcpy)(buffer, "ShlV128"); return;
         case Iop_ShrV128: VG_(strcpy)(buffer, "ShrV128"); return;

         case Iop_ShlN8x16: VG_(strcpy)(buffer, "ShlN8x16"); return;
         case Iop_ShlN16x8: VG_(strcpy)(buffer, "ShlN16x8"); return;
         case Iop_ShlN32x4: VG_(strcpy)(buffer, "ShlN32x4"); return;
         case Iop_ShlN64x2: VG_(strcpy)(buffer, "ShlN64x2"); return;
         case Iop_ShrN8x16: VG_(strcpy)(buffer, "ShrN8x16"); return;
         case Iop_ShrN16x8: VG_(strcpy)(buffer, "ShrN16x8"); return;
         case Iop_ShrN32x4: VG_(strcpy)(buffer, "ShrN32x4"); return;
         case Iop_ShrN64x2: VG_(strcpy)(buffer, "ShrN64x2"); return;
         case Iop_SarN8x16: VG_(strcpy)(buffer, "SarN8x16"); return;
         case Iop_SarN16x8: VG_(strcpy)(buffer, "SarN16x8"); return;
         case Iop_SarN32x4: VG_(strcpy)(buffer, "SarN32x4"); return;

         case Iop_Shl8x16: VG_(strcpy)(buffer, "Shl8x16"); return;
         case Iop_Shl16x8: VG_(strcpy)(buffer, "Shl16x8"); return;
         case Iop_Shl32x4: VG_(strcpy)(buffer, "Shl32x4"); return;
         case Iop_Shr8x16: VG_(strcpy)(buffer, "Shr8x16"); return;
         case Iop_Shr16x8: VG_(strcpy)(buffer, "Shr16x8"); return;
         case Iop_Shr32x4: VG_(strcpy)(buffer, "Shr32x4"); return;
         case Iop_Shr64x2: VG_(strcpy)(buffer, "Shr64x2"); return;
         case Iop_Sar8x16: VG_(strcpy)(buffer, "Sar8x16"); return;
         case Iop_Sar16x8: VG_(strcpy)(buffer, "Sar16x8"); return;
         case Iop_Sar32x4: VG_(strcpy)(buffer, "Sar32x4"); return;
         case Iop_Sar64x2: VG_(strcpy)(buffer, "Sar64x2"); return;
         case Iop_Sal8x16: VG_(strcpy)(buffer, "Sal8x16"); return;
         case Iop_Sal16x8: VG_(strcpy)(buffer, "Sal16x8"); return;
         case Iop_Sal32x4: VG_(strcpy)(buffer, "Sal32x4"); return;
         case Iop_Sal64x2: VG_(strcpy)(buffer, "Sal64x2"); return;
         case Iop_Rol8x16: VG_(strcpy)(buffer, "Rol8x16"); return;
         case Iop_Rol16x8: VG_(strcpy)(buffer, "Rol16x8"); return;
         case Iop_Rol32x4: VG_(strcpy)(buffer, "Rol32x4"); return;

         case Iop_NarrowBin16to8x16:    VG_(strcpy)(buffer, "NarrowBin16to8x16"); return;
         case Iop_NarrowBin32to16x8:    VG_(strcpy)(buffer, "NarrowBin32to16x8"); return;
         case Iop_QNarrowBin16Uto8Ux16: VG_(strcpy)(buffer, "QNarrowBin16Uto8Ux16"); return;
         case Iop_QNarrowBin32Sto16Ux8: VG_(strcpy)(buffer, "QNarrowBin32Sto16Ux8"); return;
         case Iop_QNarrowBin16Sto8Ux16: VG_(strcpy)(buffer, "QNarrowBin16Sto8Ux16"); return;
         case Iop_QNarrowBin32Uto16Ux8: VG_(strcpy)(buffer, "QNarrowBin32Uto16Ux8"); return;
         case Iop_QNarrowBin16Sto8Sx16: VG_(strcpy)(buffer, "QNarrowBin16Sto8Sx16"); return;
         case Iop_QNarrowBin32Sto16Sx8: VG_(strcpy)(buffer, "QNarrowBin32Sto16Sx8"); return;
         case Iop_NarrowUn16to8x8:     VG_(strcpy)(buffer, "NarrowUn16to8x8");  return;
         case Iop_NarrowUn32to16x4:    VG_(strcpy)(buffer, "NarrowUn32to16x4"); return;
         case Iop_NarrowUn64to32x2:    VG_(strcpy)(buffer, "NarrowUn64to32x2"); return;
         case Iop_QNarrowUn16Uto8Ux8:  VG_(strcpy)(buffer, "QNarrowUn16Uto8Ux8");  return;
         case Iop_QNarrowUn32Uto16Ux4: VG_(strcpy)(buffer, "QNarrowUn32Uto16Ux4"); return;
         case Iop_QNarrowUn64Uto32Ux2: VG_(strcpy)(buffer, "QNarrowUn64Uto32Ux2"); return;
         case Iop_QNarrowUn16Sto8Sx8:  VG_(strcpy)(buffer, "QNarrowUn16Sto8Sx8");  return;
         case Iop_QNarrowUn32Sto16Sx4: VG_(strcpy)(buffer, "QNarrowUn32Sto16Sx4"); return;
         case Iop_QNarrowUn64Sto32Sx2: VG_(strcpy)(buffer, "QNarrowUn64Sto32Sx2"); return;
         case Iop_QNarrowUn16Sto8Ux8:  VG_(strcpy)(buffer, "QNarrowUn16Sto8Ux8");  return;
         case Iop_QNarrowUn32Sto16Ux4: VG_(strcpy)(buffer, "QNarrowUn32Sto16Ux4"); return;
         case Iop_QNarrowUn64Sto32Ux2: VG_(strcpy)(buffer, "QNarrowUn64Sto32Ux2"); return;
         case Iop_Widen8Uto16x8:  VG_(strcpy)(buffer, "Widen8Uto16x8");  return;
         case Iop_Widen16Uto32x4: VG_(strcpy)(buffer, "Widen16Uto32x4"); return;
         case Iop_Widen32Uto64x2: VG_(strcpy)(buffer, "Widen32Uto64x2"); return;
         case Iop_Widen8Sto16x8:  VG_(strcpy)(buffer, "Widen8Sto16x8");  return;
         case Iop_Widen16Sto32x4: VG_(strcpy)(buffer, "Widen16Sto32x4"); return;
         case Iop_Widen32Sto64x2: VG_(strcpy)(buffer, "Widen32Sto64x2"); return;

         case Iop_InterleaveHI8x16: VG_(strcpy)(buffer, "InterleaveHI8x16"); return;
         case Iop_InterleaveHI16x8: VG_(strcpy)(buffer, "InterleaveHI16x8"); return;
         case Iop_InterleaveHI32x4: VG_(strcpy)(buffer, "InterleaveHI32x4"); return;
         case Iop_InterleaveHI64x2: VG_(strcpy)(buffer, "InterleaveHI64x2"); return;
         case Iop_InterleaveLO8x16: VG_(strcpy)(buffer, "InterleaveLO8x16"); return;
         case Iop_InterleaveLO16x8: VG_(strcpy)(buffer, "InterleaveLO16x8"); return;
         case Iop_InterleaveLO32x4: VG_(strcpy)(buffer, "InterleaveLO32x4"); return;
         case Iop_InterleaveLO64x2: VG_(strcpy)(buffer, "InterleaveLO64x2"); return;

        case Iop_Perm8x16: VG_(strcpy)(buffer, "Perm8x16"); return;

        default: 
			buffer[0]=11;
            return;
            VG_(tool_panic)("ppIROp(1)");
    }

    VG_(strcpy)(buffer, str);
    switch (op - base) {
        case 0:
            VG_(strcat)(buffer, "8");
            break;
        case 1:
            VG_(strcat)(buffer, "16");
            break;
        case 2:
            VG_(strcat)(buffer, "32");
            break;
        case 3:
            VG_(strcat)(buffer, "64");
            break;
        default:
            VG_(tool_panic)("IROp_to_str(2)");
    }
}
Opij get_opij(IROp op)
{
    Opij opij;
    IROp    base;
    opij.i = -1;
    opij.j = -1;
    opij.type = -1;
    opij.sign = 0;
    switch(op){
        case Iop_Add8 ... Iop_Add64:
             base = Iop_Add8; break;
        case Iop_Sub8 ... Iop_Sub64:
             base = Iop_Sub8; break;
        case Iop_Mul8 ... Iop_Mul64:
             base = Iop_Mul8; break;
        case Iop_Or8 ... Iop_Or64:
             base = Iop_Or8; break;
        case Iop_And8 ... Iop_And64:
             base = Iop_And8; break;
        case Iop_Xor8 ... Iop_Xor64:
             base = Iop_Xor8; break;
        case Iop_Shl8 ... Iop_Shl64:
             base = Iop_Shl8; break;
        case Iop_Shr8 ... Iop_Shr64:
             base = Iop_Shr8; break;
        case Iop_Sar8 ... Iop_Sar64:
             base = Iop_Sar8; break;
        case Iop_CmpEQ8 ... Iop_CmpEQ64:
             base = Iop_CmpEQ8; break;
        case Iop_CmpNE8 ... Iop_CmpNE64:
             base = Iop_CmpNE8; break;
        case Iop_Not8 ... Iop_Not64:
             base = Iop_Not8; break;
        case Iop_8Uto16:    {opij.i=8; opij.j=16; opij.sign=0;} return opij;
        case Iop_8Uto32:    {opij.i=8; opij.j=32; opij.sign=0;} return opij;
        case Iop_16Uto32:   {opij.i=16; opij.j=32; opij.sign=0;} return opij;
        case Iop_8Sto16:    {opij.i=8; opij.j=16; opij.sign=1;} return opij;
        case Iop_8Sto32:    {opij.i=8; opij.j=32; opij.sign=1;} return opij;
        case Iop_16Sto32:    {opij.i=16; opij.j=32; opij.sign=1;} return opij;
        case Iop_32Sto64:    {opij.i=32; opij.j=64; opij.sign=1;} return opij;
        case Iop_32Uto64:    {opij.i=32; opij.j=64; opij.sign=0;} return opij;
        case Iop_32to8:    {opij.i=32; opij.j=8;} return opij;
        case Iop_16Uto64:    {opij.i=16; opij.j=64; opij.sign=0;} return opij;
        case Iop_16Sto64:    {opij.i=16; opij.j=64; opij.sign=1;} return opij;
        case Iop_8Uto64:    {opij.i=8; opij.j=64; opij.sign=0;} return opij;
        case Iop_8Sto64:    {opij.i=8; opij.j=64; opij.sign=1;} return opij;
        case Iop_64to16:    {opij.i=64; opij.j=16;} return opij;
        case Iop_64to8:    {opij.i=64; opij.j=8;} return opij;   
        case Iop_Not1:     {opij.j=1;}     return opij;
        case Iop_32to1:    {opij.i=32; opij.j=1;} return opij;
        case Iop_64to1:    {opij.i=64; opij.j=1;} return opij;
        case Iop_1Uto8:    {opij.i=1; opij.j=8; opij.sign=0;} return opij;
        case Iop_1Uto32:   {opij.i=1; opij.j=32; opij.sign=0;} return opij;
        case Iop_1Uto64:   {opij.i=1; opij.j=64; opij.sign=0;} return opij;
        case Iop_1Sto8:    {opij.i=1; opij.j=8; opij.sign=1;} return opij;
        case Iop_1Sto16:   {opij.i=1; opij.j=16; opij.sign=1;} return opij;
        case Iop_1Sto32:   {opij.i=1; opij.j=32; opij.sign=1;} return opij;
        case Iop_1Sto64:   {opij.i=1; opij.j=64; opij.sign=1;} return opij;
        case Iop_MullS8:   {opij.j=8; opij.sign=1;} return opij;
        case Iop_MullS16:  {opij.j=16; opij.sign=1;} return opij;
        case Iop_MullS32:  {opij.j=32; opij.sign=1;} return opij;
        case Iop_MullS64:  {opij.j=64; opij.sign=1;} return opij;
        case Iop_MullU8:   {opij.j=8; opij.sign=0;} return opij;
        case Iop_MullU16:  {opij.j=16; opij.sign=0;} return opij;
        case Iop_MullU32:  {opij.j=32; opij.sign=0;} return opij;
        case Iop_MullU64:  {opij.j=64; opij.sign=0;} return opij;
        case Iop_Clz64:    {opij.j=64;} return opij;
        case Iop_Clz32:    {opij.j=32;} return opij;
        case Iop_Ctz64:    {opij.j=64;} return opij;
        case Iop_Ctz32:    {opij.j=32;} return opij;
        case Iop_CmpLT32S: {opij.j=32; opij.type=1;opij.sign=1;} return opij;
        case Iop_CmpLE32S: {opij.j=32; opij.type=0;opij.sign=1;} return opij;
        case Iop_CmpLT32U: {opij.j=32; opij.type=1;opij.sign=0;} return opij;
        case Iop_CmpLE32U: {opij.j=32; opij.type=0;opij.sign=0;} return opij;
        case Iop_CmpLT64S: {opij.j=64; opij.type=1;opij.sign=1;} return opij;
        case Iop_CmpLE64S: {opij.j=64; opij.type=0;opij.sign=1;} return opij;
        case Iop_CmpLT64U: {opij.j=64; opij.type=1;opij.sign=0;} return opij;
        case Iop_CmpLE64U: {opij.j=32; opij.type=0;opij.sign=0;} return opij;
/*
        case Iop_CmpNEZ8:  VG_(strcpy)(buffer, "CmpNEZ8"); return;
        case Iop_CmpNEZ16: VG_(strcpy)(buffer, "CmpNEZ16"); return;
        case Iop_CmpNEZ32: VG_(strcpy)(buffer, "CmpNEZ32"); return;
        case Iop_CmpNEZ64: VG_(strcpy)(buffer, "CmpNEZ64"); return;

        case Iop_CmpwNEZ32: VG_(strcpy)(buffer, "CmpwNEZ32"); return;
        case Iop_CmpwNEZ64: VG_(strcpy)(buffer, "CmpwNEZ64"); return;
*/
        case Iop_Left8:  {opij.j=8;} return opij;
        case Iop_Left16: {opij.j=16;} return opij;
        case Iop_Left32: {opij.j=32;} return opij;
        case Iop_Left64: {opij.j=64;} return opij;
/*
        case Iop_CmpORD32U: VG_(strcpy)(buffer, "CmpORD32U"); return;
        case Iop_CmpORD32S: VG_(strcpy)(buffer, "CmpORD32S"); return;

        case Iop_CmpORD64U: VG_(strcpy)(buffer, "CmpORD64U"); return;
        case Iop_CmpORD64S: VG_(strcpy)(buffer, "CmpORD64S"); return;
*/
        case Iop_DivU32: {opij.j=32; opij.sign=0;} return opij;
        case Iop_DivS32: {opij.j=32; opij.sign=1;} return opij;
        case Iop_DivU64: {opij.j=64; opij.sign=0;} return opij;
        case Iop_DivS64: {opij.j=64; opij.sign=1;} return opij;

        case Iop_DivModU64to32: {opij.i=64; opij.j=32; opij.sign=0;} return opij;
        case Iop_DivModS64to32: {opij.i=64; opij.j=32; opij.sign=1;} return opij;

        case Iop_DivModU128to64: {opij.i=128; opij.j=64; opij.sign=0;} return opij;
        case Iop_DivModS128to64: {opij.i=128; opij.j=64; opij.sign=1;} return opij;

        case Iop_16HIto8:  {opij.i=16; opij.j=8;} return opij;
        case Iop_16to8:    {opij.i=16; opij.j=8;} return opij;
        case Iop_8HLto16:  {opij.i=8; opij.j=16;} return opij;

        case Iop_32HIto16: {opij.i=32; opij.j=16;} return opij;
        case Iop_32to16:   {opij.i=32; opij.j=16;} return opij;
        case Iop_16HLto32: {opij.i=16; opij.j=32;} return opij;

        case Iop_64HIto32: {opij.i=64; opij.j=32;} return opij;
        case Iop_64to32:   {opij.i=64; opij.j=32;} return opij;
        case Iop_32HLto64: {opij.i=32; opij.j=64;} return opij;

        case Iop_128HIto64: {opij.i=128; opij.j=64;} return opij;
        case Iop_128to64:   {opij.i=128; opij.j=64;} return opij;
        case Iop_64HLto128: {opij.i=64; opij.j=128;} return opij;
        default :
              return opij;
    } 
    switch (op - base) {
        case 0:
            opij.j = 8;
            break;
        case 1:
            opij.j = 16;
            break;
        case 2:
            opij.j = 32;
            break;
        case 3:
            opij.j = 64;
            break;
        default:
            VG_(tool_panic)("get_opij wrong");
    }
    return opij;
}

//in simplify there are some sitution like this:
//*****  8Uto64(32to8(a)) ---> 32Uto64(a)
//in this we need to get the opertion(32Uto64) after simplify.
IROp getIRop(int i , int j)
{
    IROp op = -1;
    switch(i){
        case 1: 
            if(j == 8) op = Iop_1Uto8;
            else if(j == 32) op = Iop_1Uto32;
            else if(j == 64) op = Iop_1Uto64;
            break;
        case 8:
            if(j == 16) op = Iop_8Uto16;
            else if(j == 32) op = Iop_8Uto32;
            else if(j == 64) op = Iop_8Uto64;           
            break;
        case 16:
            if(j == 32) op = Iop_16Uto32;
            else if(j == 64) op = Iop_16Uto64;
            else if(j == 8) op = Iop_16to8;
            break;
        case 32:
            if(j == 64) op = Iop_32Uto64;
            else if(j == 16) op = Iop_32to16;
            else if(j == 8) op = Iop_32to8;
            else if(j == 1) op = Iop_32to1;
            break;
        case 64:
            if(j == 32) op = Iop_64to32;
            else if(j == 16) op = Iop_64to16;
            else if(j == 8) op = Iop_64to8;
            else if(j == 1) op = Iop_64to1;
            break;
        default: break;
    }
    return op;
}


//x86g_calculate_condition.
Dep* x86g_parse(Dep* dep, UInt cc_op, UInt cond)
{
    Dep* ptmp1 = NULL, *ptmp2=NULL,*ptmp3 = NULL,*ptmp4 = NULL;
    int tmpsize;
    if(dep == NULL || dep->left == NULL || dep->right == NULL)
    {
        dep->left = NULL;
        dep->right = NULL;
        return NULL; 
    }

    switch(cond){
        case 2:  //X86CondB
        case 4:  //X86CondZ
        case 6:  //X86CondBE
        case 7:  //X86CondNBE
        case 12: //X86CondL
        case 14: //X86CondLE
            break;
        default: return NULL;     
    }

    if(cc_op>39 || cc_op<1)
    {
        dep->left = NULL;
        dep->right = NULL;
        return NULL; 
    }
    switch(cc_op%3)
    {
        case 1: tmpsize = 8; break;
        case 2: 
			tmpsize = 16; 
			if(cond != 2 && cond != 6) 
			{
				dep->left = NULL;
				dep->right = NULL;
				return NULL; 
			}
			break;
        case 0: 
			tmpsize = 32; 
			if(cond != 2 && cond != 4 && cond != 6 && cond != 12 && cond != 14) 		
			{
				dep->left = NULL;
				dep->right = NULL;
				return NULL; 
			} 
			break;
    }

    if(tmpsize==8)
    {
        ptmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp4 == NULL) return NULL;
        ptmp4->left = dep->left;
        ptmp4->right = NULL;
        ptmp4->op = unop;
        //ptmp4->buop = Iop_32to8;
        ptmp4->size = 32;
		ptmp4->father = 1;

        ptmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp3 == NULL) return NULL;
        ptmp3->left = dep->right;
        ptmp3->right = NULL;
        ptmp3->op = unop;
        //ptmp3->buop = Iop_8Sto32;
        ptmp3->size = 32;
		ptmp3->father = 1;
        
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = ptmp4;
        ptmp2->right = ptmp3;
        ptmp2->op = binop;
        //ptmp2->buop = Iop_CmpEQ8;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {
            case 4:
                ptmp4->buop = Iop_32to8;
                ptmp3->buop = Iop_32to8;
                ptmp4->size = 8;
                ptmp3->size = 8;
                ptmp2->buop = Iop_CmpEQ8;
                break;
            case 14:
                ptmp4->buop = Iop_8Sto32;
                ptmp3->buop = Iop_8Sto32;
                ptmp2->buop = Iop_CmpLE32S;
                break;
            case 12:
                ptmp4->buop = Iop_8Sto32;
                ptmp3->buop = Iop_8Sto32;
                ptmp2->buop = Iop_CmpLT32S;
                break;
            case 2:
                ptmp4->buop = Iop_8Uto32;
                ptmp3->buop = Iop_8Uto32;
                ptmp2->buop = Iop_CmpLT32U;
                break;
            case 6:
                ptmp4->buop = Iop_8Uto32;
                ptmp3->buop = Iop_8Uto32;
                ptmp2->buop = Iop_CmpLE32U;
                break;
            case 7:
                ptmp4->buop = Iop_8Uto32;
                ptmp3->buop = Iop_8Uto32;
                ptmp2->buop = Iop_CmpLT32U;
                break;
        }
    }  
    else if(tmpsize==16)
    {   
        ptmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp4 == NULL) return NULL;
        ptmp4->left = dep->left;
        ptmp4->right = NULL;
        ptmp4->op = unop;
        //ptmp4->buop = Iop_32to8;
        ptmp4->size = 32;
		ptmp4->father = 1;

        ptmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp3 == NULL) return NULL;
        ptmp3->left = dep->right;
        ptmp3->right = NULL;
        ptmp3->op = unop;
        //ptmp3->buop = Iop_32to8;
        ptmp3->size = 32;
		ptmp3->father = 1;
        
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = ptmp4;
        ptmp2->right = ptmp3;
        ptmp2->op = binop;
        //ptmp2->buop = Iop_CmpEQ8;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {

            case 2:
                ptmp4->buop = Iop_16Uto32;
                ptmp3->buop = Iop_16Uto32;
                ptmp2->buop = Iop_CmpLT32U;
                break;
            case 6:
                ptmp4->buop = Iop_16Uto32;
                ptmp3->buop = Iop_16Uto32;
                ptmp2->buop = Iop_CmpLE32U;
                break;
            default:
                dep->left = NULL;
                dep->right = NULL;
                return NULL; 
        }                 
    }
    else
    {
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = dep->left;
        ptmp2->right = dep->right;
        ptmp2->op = binop;
        //ptmp2->buop = Iop_CmpEQ8;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {
            case 4:
                ptmp2->buop = Iop_CmpEQ32;
                break;
            case 14:
                ptmp2->buop = Iop_CmpLE32S;
                break;
            case 12:
                ptmp2->buop = Iop_CmpLT32S;
                break;
            case 2:
                ptmp2->buop = Iop_CmpLT32U;
                break;
            case 6:
                ptmp2->buop = Iop_CmpLE32U;
                break;
            default : 
                dep->left = NULL;
                dep->right = NULL;
                return NULL; 
        }
        
    }             
    dep->left = ptmp2;
    dep->right = NULL;
    dep->op = unop;
    dep->buop = Iop_1Uto32;
    dep->size = 32; 
    return dep;            

}


//amd64g_calculate_condition .
Dep* amd64g_parse(Dep* dep, UInt cc_op, UInt cond)
{
    Dep* ptmp1, *ptmp2,*ptmp3,*ptmp4;
    int tmpsize;
    if(dep == NULL || dep->left == NULL || dep->right == NULL) 
    {
        dep->left = NULL;
        dep->right = NULL;
        return NULL; 
    }


    switch(cond){
        case 2:  //Amd64CondB
        case 4:  //Amd64CondZ
        case 6:  //Amd64CondBE
        case 7:  //Amd64CondNBE
        case 12: //Amd64CondL
        case 14: //Amd64CondLE
            break;
        default: 
            dep->left = NULL;
            dep->right = NULL;
            return NULL;     
    }

    if(cc_op>52 || cc_op<1)
    {
        dep->left = NULL;
        dep->right = NULL;
        return NULL; 
    }
    switch(cc_op%4)
    {
        case 1: tmpsize = 8; break;
        case 2: 
			tmpsize = 16; 
			if(cond != 2 && cond != 6) 
			{
				dep->left = NULL;
				dep->right = NULL;
				return NULL; 
			}
			break;
        case 3: 
			tmpsize = 32; 
			if(cond != 2 && cond != 6 && cond != 12 && cond != 14) 		
			{
				dep->left = NULL;
				dep->right = NULL;
				return NULL; 
			} 
			break;
        case 0: 
			tmpsize = 64; 
		     if(cond != 2 && cond != 4 && cond != 6 && cond != 12 && cond != 14) 
		    {
		        dep->left = NULL;
		        dep->right = NULL;
		        return NULL; 
		    }
			break;
    }

    if(tmpsize==8)
    {
        ptmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp4 == NULL) return NULL;
        ptmp4->left = dep->left;
        ptmp4->right = NULL;
        ptmp4->op = unop;
        ptmp4->size = 64;
		ptmp4->father = 1;

        ptmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp3 == NULL) return NULL;
        ptmp3->left = dep->right;
        ptmp3->right = NULL;
        ptmp3->op = unop;
        ptmp3->size = 64;
		ptmp3->father = 1;
        
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = ptmp4;
        ptmp2->right = ptmp3;
        ptmp2->op = binop;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {
            case 4:
                ptmp4->buop = Iop_64to8;
                ptmp3->buop = Iop_64to8;
                ptmp4->size = 8;
                ptmp3->size = 8;
                ptmp2->buop = Iop_CmpEQ8;
                break;
            case 14:
                ptmp4->buop = Iop_8Sto64;
                ptmp3->buop = Iop_8Sto64;
                ptmp2->buop = Iop_CmpLE64S;
                break;
            case 12:
                ptmp4->buop = Iop_8Sto64;
                ptmp3->buop = Iop_8Sto64;
                ptmp2->buop = Iop_CmpLT64S;
                break;
            case 2:
                ptmp4->buop = Iop_8Uto64;
                ptmp3->buop = Iop_8Uto64;
                ptmp2->buop = Iop_CmpLT64U;
                break;
            case 6:
                ptmp4->buop = Iop_8Uto64;
                ptmp3->buop = Iop_8Uto64;
                ptmp2->buop = Iop_CmpLE64U;
                break;
            case 7:
                ptmp4->buop = Iop_8Uto64;
                ptmp3->buop = Iop_8Uto64;
                ptmp2->buop = Iop_CmpLT64U;
                break;
        }
    }  
    else if(tmpsize==16)
    {   
        ptmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp4 == NULL) return NULL;
        ptmp4->left = dep->left;
        ptmp4->right = NULL;
        ptmp4->op = unop;
        ptmp4->size = 64;
		ptmp4->father = 1;

        ptmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp3 == NULL) return NULL;
        ptmp3->left = dep->right;
        ptmp3->right = NULL;
        ptmp3->op = unop;
        ptmp3->size = 64;
		ptmp3->father = 1;
        
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = ptmp4;
        ptmp2->right = ptmp3;
        ptmp2->op = binop;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {

            case 2:
                ptmp4->buop = Iop_16Uto64;
                ptmp3->buop = Iop_16Uto64;
                ptmp2->buop = Iop_CmpLT64U;
                break;
            case 6:
                ptmp4->buop = Iop_16Uto64;
                ptmp3->buop = Iop_16Uto64;
                ptmp2->buop = Iop_CmpLE64U;
                break;
            default: 
                dep->left = NULL;
                dep->right = NULL;
                return NULL; 
        }                 

    }
    else if(tmpsize==32)
    {   
        ptmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp4 == NULL) return NULL;
        ptmp4->left = dep->left;
        ptmp4->right = NULL;
        ptmp4->op = unop;
        ptmp4->size = 64;
		ptmp4->father = 1;

        ptmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp3 == NULL) return NULL;
        ptmp3->left = dep->right;
        ptmp3->right = NULL;
        ptmp3->op = unop;
        ptmp3->size = 64;
		ptmp3->father = 1;
        
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = ptmp4;
        ptmp2->right = ptmp3;
        ptmp2->op = binop;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {
            case 14:
                ptmp4->buop = Iop_32Uto64;
                ptmp3->buop = Iop_32Uto64;
                ptmp2->buop = Iop_CmpLE64S;
                break;
            case 12:
                ptmp4->buop = Iop_32Uto64;
                ptmp3->buop = Iop_32Uto64;
                ptmp2->buop = Iop_CmpLT64S;
                break;
            case 2:
                ptmp4->buop = Iop_32Uto64;
                ptmp3->buop = Iop_32Uto64;
                ptmp2->buop = Iop_CmpLT64U;
                break;
            case 6:
                ptmp4->buop = Iop_32Uto64;
                ptmp3->buop = Iop_32Uto64;
                ptmp2->buop = Iop_CmpLE64U;
                break;
            default: 
                dep->left = NULL;
                dep->right = NULL;
                return NULL; 
        }                 

    }
    else
    {
        ptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(ptmp2 == NULL) return NULL;
        ptmp2->left = dep->left;
        ptmp2->right = dep->right;
        ptmp2->op = binop;
        ptmp2->size = 1;
		ptmp2->father = 1;
        switch(cond)
        {
            case 4:
                ptmp2->buop = Iop_CmpEQ64;
                break;
            case 14:
                ptmp2->buop = Iop_CmpLE64S;
                break;
            case 12:
                ptmp2->buop = Iop_CmpLT64S;
                break;
            case 2:
                ptmp2->buop = Iop_CmpLT64U;
                break;
            case 6:
                ptmp2->buop = Iop_CmpLE64U;
                break;
            default : 
                dep->left = NULL;
                dep->right = NULL;
                return NULL; 
        }
        
    }           

    dep->left = ptmp2;
    dep->right = NULL;
    dep->op = unop;
    dep->buop = Iop_1Uto64;
    dep->size = 64; 

    return dep;            

}



void add_father(Dep* dep)
{
	if(dep->left != NULL) dep->left->father += 1;
	if(dep->right != NULL) dep->right->father += 1;
}

void dep_copy(Dep* des,Dep* src)
{
	if(des == NULL || src == NULL) return;
    des->op = src->op;
    des->buop = src->buop;
    des->size = src->size;
    des->opval = src->opval;
    des->cond = src->cond;
    des->value.addr = src->value.addr;
    des->left = src->left;
    des->right = src->right;
}

//simplify the tree.
//for example: translate things like 32to1(1to32(a)) to (a)
Bool simplify(Dep* dep)
{
    Bool changed = False;
    Opij opij,opij_child;
    Dep* ptmp;
    Dep* lptmp;
    Dep* rptmp;
    IROp optmp;
    if(dep == NULL) return False;
	if(dep->left == NULL && dep->right == NULL) return False;
    switch(dep->op){
        case rdtmp:
        case mux0x:
        case loadI:
            ptmp = dep->left;
			dep_copy(dep,ptmp);
			add_father(dep);
			ptmp->father -= 1;
            simplify(dep);
            changed = True;
            break;
        case unop:        
            if(dep->left->op == unop)
            {
                opij = get_opij(dep->buop); 
                opij_child = get_opij(dep->left->buop);
                if(opij.sign != 1)
                {
                    if((opij.i == opij_child.j)&&(opij.j == opij_child.i)&&(opij.i != -1)&&(opij.j != -1))
                    {
						if(dep->left->left == NULL) break;
						if(dep->left->left->size != opij_child.i) break;
                        ptmp = dep->left->left;
						lptmp = dep->left;
						dep_copy(dep,ptmp);
						add_father(dep);
						lptmp->father -= 1;
                        simplify(dep);
                        changed = True;
                    }
                    else if(opij.i == opij_child.j && opij.i != -1)
                    { 
                        optmp = getIRop(opij_child.i,opij.j);
                        if(optmp == -1) break;
                        ptmp = dep->left->left;
						lptmp = dep->left;
                        dep->op = unop;
                        dep->buop = optmp;
                        dep->left = ptmp;
						add_father(dep);
						lptmp->father -= 1;
                        simplify(dep);
                        changed = True;
                    }
					else simplify(dep->left);
                }else simplify(dep->left);
            }
			else simplify(dep->left);
            break;
        case load:
            if(dep->left->op == store)
            {
                if(dep->left->left->op == load)
                {
                    ptmp = dep->left->left->left;
					lptmp = dep->left;
                    dep->left = ptmp;
					add_father(dep);
					lptmp->father -= 1;
                    simplify(dep);
                    changed = True;
                }
                else
                {
                    if(dep->size == dep->left->size)
                    {
						if(dep->left->left == NULL) break;
                        ptmp = dep->left->left;
						lptmp = dep->left;
						dep_copy(dep,ptmp);
						add_father(dep);
						lptmp->father -= 1;
						simplify(dep); 
						changed = True;
                    }else{
                        optmp = getIRop(dep->left->size,dep->size);
                        if(optmp == -1) break;
                        ptmp = dep->left->left;
						lptmp = dep->left;
                        dep->op = unop;
                        dep->buop = optmp;
                        dep->left = ptmp;
						add_father(ptmp);
						lptmp->father -= 1;
                        simplify(dep);
                        changed = True;
                    }

                } 
            }
            else {simplify(dep->left);}
            break;
        case get:
            if(dep->left->op = put)
            { 
                if(dep->size == dep->left->size)
                {
					if(dep->left->left == NULL) break;
                    ptmp = dep->left->left;
					lptmp = dep->left;
					dep_copy(dep,ptmp);
					add_father(dep);
					lptmp->father -= 1;
					changed = True;
					simplify(dep);
                }
                else{
                    optmp = getIRop(dep->left->size,dep->size);
                    if(optmp == -1) break;
                    ptmp = dep->left->left;
					lptmp = dep->left;
                    dep->op = unop;
                    dep->buop = optmp;
                    dep->left = ptmp;
					add_father(dep);
					lptmp->father -= 1;
                    simplify(dep);
                    changed = True;
                }
            }
            else simplify(dep->left);
            break;
        case binop:
            if(dep->left != NULL)simplify(dep->left);
            if(dep->right != NULL) simplify(dep->right);
            break;
        case x86g:
			if(dep->left == NULL || dep->right == NULL) break;
            if(x86g_parse(dep, dep->opval, dep->cond)== NULL) 
			{
				dep->left = NULL;
				dep->right = NULL; 
				break;
			}
            simplify(dep->left);
            changed = True;
            break;
        case amd64g:
			if(dep->left == NULL || dep->right == NULL) break;
            if(amd64g_parse(dep, dep->opval, dep->cond) == NULL)
			{
				dep->left = NULL;
				dep->right = NULL; 
				break;
			}
            simplify(dep->left);
            changed = True; 
            break;       
        case store:
            if(dep->left != NULL)simplify(dep->left);
            if(dep->right != NULL) simplify(dep->right);
            break;
        case put:
            if(dep->left != NULL)simplify(dep->left);
            if(dep->right != NULL) simplify(dep->right);
            break;
		case modu:
		case mods:
		case cat:
			if(dep->left != NULL)simplify(dep->left);
            if(dep->right != NULL) simplify(dep->right);
			break;
        default: break;
    }
    return changed;
}



char* s_function(char* buf,Sop op,int size, char* arg0, char* arg1)
{
    switch(op){
        case S_bvnot:
              VG_(snprintf)(buf,XXX_MAX_BUF,"~(%s)", arg0);break;
        case S_not:
              VG_(snprintf)(buf,XXX_MAX_BUF,"NOT(%s)", arg0);break;
        case S_cat:
              VG_(snprintf)(buf,XXX_MAX_BUF,"(%s@%s)", arg0, arg1);break;
        case S_and:
              VG_(snprintf)(buf,XXX_MAX_BUF,"(%s & %s)", arg0, arg1);break;
        case S_equal:
              VG_(snprintf)(buf,XXX_MAX_BUF,"(%s = %s)", arg0, arg1);break;
        case S_or:
              VG_(snprintf)(buf,XXX_MAX_BUF,"(%s | %s)", arg0, arg1);break;
        case S_bvle:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVLE(%s,%s)",arg0, arg1);break; 
        case S_sbvle:
              VG_(snprintf)(buf,XXX_MAX_BUF,"SBVLE(%s,%s)",arg0, arg1);break; 
        case S_bvlt:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVLT(%s,%s)",arg0, arg1);break; 
        case S_sbvlt:
              VG_(snprintf)(buf,XXX_MAX_BUF,"SBVLT(%s,%s)",arg0, arg1);break; 
        case S_bvxor:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVXOR(%s,%s)",arg0, arg1);break;  
        case S_bvsub:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVSUB(%d,%s,%s)",size,arg0, arg1);break;
        case S_bvplus:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVPLUS(%d,%s,%s)",size,arg0, arg1);break;
        case S_bvmult:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVMULT(%d,%s,%s)",size,arg0, arg1);break;
        case S_bvmod:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVMOD(%d,%s,%s)",size,arg0, arg1);break;
        case S_sbvmod:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVSMOD(%d,%s,%s)",size,arg0, arg1);break;
        case S_bvdiv:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVDIV(%d,%s,%s)",size,arg0, arg1);break;
        case S_sbvdiv:
              VG_(snprintf)(buf,XXX_MAX_BUF,"SBVDIV(%d,%s,%s)",size,arg0, arg1);break;
        case S_shr:
              VG_(snprintf)(buf,XXX_MAX_BUF,"(%s >> %s)",arg0, arg1);break;
        case S_shl:
              VG_(snprintf)(buf,XXX_MAX_BUF,"(%s << %s)",arg0, arg1);break;
        case S_bvsx:
              VG_(snprintf)(buf,XXX_MAX_BUF,"BVSX(%s,%d)", arg0, arg1);break;
        default :
            VG_(tool_panic)("op default");
    }
    return buf;
}

//operation of cat need extend the width.
char* solver_const(int sign, int value)
{
    char* val = (char*)VG_(malloc)("\x00",66);
	if(val == NULL) VG_(tool_panic)("malloc failed in solver_const!");
    int i;
	if(sign == 0)
	{
		switch(value)
		{
			case 7: VG_(snprintf)(val,10,"0b0000000");break;
			case 8: VG_(snprintf)(val,5,"0h00");break;
			case 16: VG_(snprintf)(val,7,"0h0000");break;
			case 24: VG_(snprintf)(val,9,"0h000000");break;
			case 32: VG_(snprintf)(val,12,"0h00000000");break;
			case 48: VG_(snprintf)(val,15,"0h000000000000");break;
			case 31: VG_(snprintf)(val,34,"0b0000000000000000000000000000000");break;
			case 56: VG_(snprintf)(val,17,"0h00000000000000");break;
			case 63: VG_(snprintf)(val,66,"0b000000000000000000000000000000000000000000000000000000000000000",value);break;
			case 64: VG_(snprintf)(val,67,"0h0000000000000000");break;
			default: 
				VG_(printf)("value: %d\n",value);
				VG_(tool_panic)("solver_const wrong\n");
		}
	}
	else
	{
		switch(value)
		{
			case 7: VG_(snprintf)(val,10,"0b1111111");break;
			case 8: VG_(snprintf)(val,5,"0hff");break;
			case 16: VG_(snprintf)(val,7,"0hffff");break;
			case 24: VG_(snprintf)(val,9,"0hffffff");break;
			case 32: VG_(snprintf)(val,11,"0hffffffff");break;
			case 48: VG_(snprintf)(val,15,"0hffffffffffff");break;
			case 31: VG_(snprintf)(val,34,"0b1111111111111111111111111111111");break;
			case 56: VG_(snprintf)(val,17,"0hffffffffffffff");break;
			case 63: VG_(snprintf)(val,66,"0b111111111111111111111111111111111111111111111111111111111111111");break;
			case 64: VG_(snprintf)(val,67,"0hffffffffffffffff");break;
			default: 
				VG_(printf)("value: %d\n",value);
				VG_(tool_panic)("solver_const wrong\n");
		}
	}
    return val;
}

Bool dirty_patch_size(Dep* fdep,Dep* cdep,Bool sign,char* query,char* buf)
{
	Opij opij;
	UInt fsize;
	UInt csize;
	csize = cdep->size;
	opij = get_opij(fdep->buop);
	if(opij.i != -1) fsize = opij.i;
	else if(opij.j != -1) fsize = opij.j;
	else
	{
		VG_(snprintf)(buf,XXX_MAX_BUF,"%s",query);
		return False;
	}
	if(fdep->op == binop)
	{
		switch(fdep->buop)
		{
	        case Iop_MullS8:    
            case Iop_MullS16:  
            case Iop_MullS32:  
            case Iop_MullS64:  
            case Iop_MullU8:  
            case Iop_MullU16:  
            case Iop_MullU32:  
            case Iop_MullU64:
				fsize = 2*fsize;
				break;
			default:
				break;
		}
	}
	if(fsize == csize) 
	{
		VG_(snprintf)(buf,XXX_MAX_BUF,"%s",query);
		return False;
	}
	if(csize != 0)
	{
		if(cdep->op != Iconst)
		{
			if(sign == True )
			{
				if(fsize > csize) VG_(snprintf)(buf,XXX_MAX_BUF,"BVSX(%s,%d)",query,fsize);
				else if(fsize < csize) VG_(snprintf)(buf,XXX_MAX_BUF,"((%s)[%d:0])",query,fsize -1);
				return True;
			}
			else
			{
				if(fsize> csize) VG_(snprintf)(buf,XXX_MAX_BUF,"(%s@%s)",solver_const(0,fsize - csize),query);
				else if(fsize < csize) VG_(snprintf)(buf,XXX_MAX_BUF,"((%s)[%d:0])",query,csize-1);
				return True;
			}
		}
		else 
		{
			switch(fsize)
			{
				case 8:
					VG_(snprintf)( buf,XXX_MAX_BUF,"0h%02x",cdep->opval);
					break;
				case 16:
					VG_(snprintf)( buf,XXX_MAX_BUF,"0h%04x",cdep->opval);
					break;
				case 32:
					VG_(snprintf)( buf,XXX_MAX_BUF,"0h%08x",cdep->opval);
					break;
				case 64:
					VG_(snprintf)( buf,XXX_MAX_BUF,"0h%016x",cdep->opval);
					break;
				case 128:
					VG_(snprintf)( buf,XXX_MAX_BUF,"0h%032x",cdep->opval);
					break;
				default :
					VG_(tool_panic)("const size wrong !");
			}
			return True;
		}
	}
	return False;
}

// search the tree to get the constraint.in stp form.
char* fz_solver(Dep* dep,char* query)
{
    int i,j;
    int fd;
    SysRes res;
    char* wtmpbuf ;//= (char*)VG_(malloc)("\x00",20);
    Sop sop;
    Opij opij;
    Opij opij_child;
    int zero;
    int mask32[5];
    long long mask64[5];
    char* args[6];
    char* a ,*b ,*bvle,*ne,*cond,*nz;
	char* sconst;
	char* ret;
	Bool fc = False;
	int shift = 0;
    char* lquery = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
	if(lquery == NULL){return NULL;}
    char* rquery = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
	if(rquery == NULL){VG_(free)(lquery);return NULL;}
    char* tmpbuf = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
	if(tmpbuf == NULL){VG_(free)(lquery);VG_(free)(rquery);return NULL;}
	char* tmpbuf1 = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
	if(tmpbuf1 == NULL){VG_(free)(lquery);VG_(free)(rquery);VG_(free)(tmpbuf);return NULL;}

    if(dep == NULL) {FFF; return NULL;}

    switch(dep->op){
        case symbol:
            VG_(snprintf)( query,XXX_MAX_BUF,"x%d",dep->opval);
            if(dep->opval > varcount)
			{
				// for(i=varcount+1; i<= dep->opval; i++)
				// {
					// VG_(printf)("\nVars:x%d : BITVECTOR(8);\n",i);
				// }
				varcount = dep->opval;
			}
			FFF;
            return query;
        case Iconst:
            if(dep->size == 8)
                VG_(snprintf)( query,XXX_MAX_BUF,"0h%02x",dep->opval);
            else if(dep->size == 16)
                VG_(snprintf)( query,XXX_MAX_BUF,"0h%04x",dep->opval);
            else if(dep->size == 32)
                VG_(snprintf)( query,XXX_MAX_BUF,"0h%08x",dep->opval);
            else if(dep->size == 64)
                VG_(snprintf)( query,XXX_MAX_BUF,"0h%016x",dep->opval);
            else if(dep->size == 128)
                VG_(snprintf)( query,XXX_MAX_BUF,"0h%032x",dep->opval);
            else VG_(tool_panic)("const size");
			FFF;
            return query;

        case load:
            if(dep->left == NULL) { FFF;return NULL;}          
            if(fz_solver(dep->left,lquery) == NULL) {FFF; return NULL;}     
            VG_(snprintf)( query,XXX_MAX_BUF,"%s",lquery);
			FFF;
			return query;
        case unop:
            if(dep->left == NULL ) {FFF; return NULL;}
            if(fz_solver(dep->left,lquery) == NULL){FFF; return NULL;}
            opij = get_opij(dep->buop);
            switch(dep->buop){
                case Iop_Not8 ... Iop_Not64:
					dirty_patch_size(dep,dep->left,0,lquery,tmpbuf);
                    VG_(snprintf)( query,XXX_MAX_BUF,"NOT(%s)",tmpbuf);
					FFF;
                    return query;
                case Iop_1Sto8:   case Iop_1Sto16: case Iop_8Sto16: case Iop_1Sto32:  case Iop_8Sto32:
                case Iop_16Sto32: case Iop_1Sto64: case Iop_8Sto64: case Iop_16Sto64: case Iop_32Sto64:
					if(dep->size == dep->left->size) VG_(snprintf)(query,XXX_MAX_BUF,"%s",lquery);
                    else VG_(snprintf)( query,XXX_MAX_BUF,"BVSX(%s,%d)",lquery,opij.j); 
					FFF;
                    return query;                       
                case Iop_32to1:  case Iop_64to1:  case Iop_16to8: case Iop_32to8: 
                case Iop_64to8: case Iop_32to16: case Iop_64to16: case Iop_64to32: 
					if(opij.i != dep->left->size){FFF;return NULL;}
                    VG_(snprintf)( query,XXX_MAX_BUF,"((%s)[%d:0])",lquery,opij.j-1);
					FFF;
                    return query;
                case Iop_1Uto8: case Iop_1Uto32: case Iop_1Uto64: case Iop_8Uto16: case Iop_8Uto32:
                case Iop_8Uto64: case Iop_16Uto32: case Iop_16Uto64: case Iop_32Uto64:
                	if(opij.i != dep->left->size){FFF;return NULL;}
						sconst = solver_const(0,dep->size - dep->left->size);
		                VG_(snprintf)( query,XXX_MAX_BUF,"(%s@%s)",sconst,lquery);
						VG_(free)(sconst);
					FFF;
                    return query;
                case Iop_Left8: 
                case Iop_Left16: 
                case Iop_Left32: 
                case Iop_Left64:  
                    VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"BVSUB(%d,0,%s)",opij.j,lquery);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(%s | %s)",lquery,tmpbuf);
					FFF;
                    return query;
                case Iop_16HIto8:
                case Iop_32HIto16:
                case Iop_64HIto32:
                case Iop_128HIto64:
                	if(opij.i != dep->left->size){FFF;return NULL;}
                    VG_(snprintf)( query,XXX_MAX_BUF,"((%s)[%d:%d])",lquery,opij.i-1,opij.j);
					FFF;
                    return query;
                case Iop_Clz32: 
                    zero = 0;
                    mask32[0] = 0xAAAAAAAA;
                    mask32[1] = 0xCCCCCCCC;
                    mask32[2] = 0xF0F0F0F0;
                    mask32[3] = 0xFF00FF00;
                    mask32[4] = 0xFFFF0000;
                    a = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(a == NULL) {FFF;return NULL;}
                    b = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(b == NULL) {FFF;VG_(free)(a);return NULL;}
                    bvle = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(bvle == NULL) {FFF;VG_(free)(a);VG_(free)(b);return NULL;}
                    nz = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(nz == NULL) {FFF;VG_(free)(a);VG_(free)(b);VG_(free)(bvle);return NULL;}
                    cond = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(cond == NULL) {FFF;VG_(free)(a);VG_(free)(b);VG_(free)(bvle);VG_(free)(nz);return NULL;}
                    for(i = 0; i<=4 ; i++)
                    {
                        VG_(snprintf)(a,XXX_MAX_BUF,"(%s & 0h%08x)",lquery,mask32[i]);  
                        VG_(snprintf)(b,XXX_MAX_BUF,"(%s & 0h%08x)",lquery,(~mask32[i])); 
                        VG_(snprintf)(bvle,XXX_MAX_BUF,"%s(%s %s)",a,b);
                        args[i] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
						if(args[i] == NULL)
						{
							FFF;
							VG_(free)(a);
							VG_(free)(b);
							VG_(free)(bvle);
							VG_(free)(nz);
							VG_(free)(cond);
							for(j=0;j<i;j++)
								VG_(free)(args[j]);
							return NULL;
						}
                        VG_(snprintf)(args[i],XXX_MAX_BUF,"(IF (%s) THEN (0h%08x) ELSE (0h%08x) ENDIF)",bvle,1<<i,zero);
                    }
                    VG_(snprintf)(nz,XXX_MAX_BUF,"BVPLUS(32,%s,%s,%s,%s,%s)",args[0],args[1],args[2],args[3],args[4]);
                    VG_(snprintf)(cond,XXX_MAX_BUF,"(%s = 0h%08x)",lquery,zero);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(IF (%s) THEN (0h%08x) ELSE (%s) ENDIF)",cond,zero,nz);
					for(i=0;i<=4;i++)
					{
						VG_(free)(args[i]);
					}
					VG_(free)(a);
					VG_(free)(b);
					VG_(free)(bvle);
					VG_(free)(nz);
					VG_(free)(cond);
					FFF;
                    return query;
                case Iop_Clz64:
                    zero = 0;
                    mask64[0] = 0xAAAAAAAAAAAAAAAA;
                    mask64[1] = 0xCCCCCCCCCCCCCCCC;
                    mask64[2] = 0xF0F0F0F0F0F0F0F0;
                    mask64[3] = 0xFF00FF00FF00FF00;
                    mask64[4] = 0xFFFF0000FFFF0000;
                    mask64[5] = 0xFFFFFFFF00000000;
                    a = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(a == NULL) {FFF;return NULL;}
                    b = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(b == NULL) {FFF;VG_(free)(a);return NULL;}
                    bvle = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(bvle == NULL) {FFF;VG_(free)(a);VG_(free)(b);return NULL;}
                    nz = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(nz == NULL) {FFF;VG_(free)(a);VG_(free)(b);VG_(free)(bvle);return NULL;}
                    cond = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(cond == NULL) {FFF;VG_(free)(a);VG_(free)(b);VG_(free)(bvle);VG_(free)(nz);return NULL;}
                    for(i = 0; i<=5 ; i++)
                    {
                        VG_(snprintf)(a,XXX_MAX_BUF,"(%s & 0h%016x)",lquery,mask64[i]);  
                        VG_(snprintf)(b,XXX_MAX_BUF,"(%s & 0h%016x)",lquery,(~mask64[i])); 
                        VG_(snprintf)(bvle,XXX_MAX_BUF,"%s(%s %s)",a,b);
                        args[i] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
						if(args[i] == NULL)
						{
							FFF;
							VG_(free)(a);
							VG_(free)(b);
							VG_(free)(bvle);
							VG_(free)(nz);
							VG_(free)(cond);
							for(j=0;j<i;j++)
								VG_(free)(args[j]);
							return NULL;
						}
                        VG_(snprintf)(args[i],XXX_MAX_BUF,"(IF (%s) THEN (0h%016x) ELSE (0h%016x) ENDIF)",bvle,1<<i,zero);
                    }
                    VG_(snprintf)(nz,XXX_MAX_BUF,"BVPLUS(64,%s,%s,%s,%s,%s)",args[0],args[1],args[2],args[3],args[4],args[5]);
                    VG_(snprintf)(cond,XXX_MAX_BUF,"(%s = 0h%016x)",lquery,zero);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(IF (%s) THEN (0h%016x) ELSE (%s) ENDIF)",cond,zero,nz);
					for(i=0;i<=5;i++)
					{
						VG_(free)(args[i]);
					}
					VG_(free)(a);
					VG_(free)(b);
					VG_(free)(bvle);
					VG_(free)(nz);
					VG_(free)(cond);
					FFF;
                    return query;
                case Iop_Ctz64:
                    zero = 0;
                    mask64[0] = 0xAAAAAAAAAAAAAAAA;
                    mask64[1] = 0xCCCCCCCCCCCCCCCC;
                    mask64[2] = 0xF0F0F0F0F0F0F0F0;
                    mask64[3] = 0xFF00FF00FF00FF00;
                    mask64[4] = 0xFFFF0000FFFF0000;
                    mask64[5] = 0xFFFFFFFF00000000;
					if(b == NULL) {FFF;return NULL;}
                    ne = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(b == NULL) {FFF;VG_(free)(b);return NULL;}
                    nz = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(bvle == NULL) {FFF;VG_(free)(b);VG_(free)(ne);return NULL;}
                    cond = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(cond == NULL) {FFF;VG_(free)(b);VG_(free)(ne);VG_(free)(nz);return NULL;}
                    for(i = 0; i<=5 ; i++)
                    {
                        VG_(snprintf)(b,XXX_MAX_BUF,"(%s & 0h%016x)",lquery,(~mask64[i])); 
                        VG_(snprintf)(ne,XXX_MAX_BUF,"(%s = 0h%016x)",b,zero);
                        args[i] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
						if(args[i] == NULL)
						{
							FFF;
							VG_(free)(b);
							VG_(free)(ne);
							VG_(free)(nz);
							VG_(free)(cond);
							for(j=0;j<i;j++)
								VG_(free)(args[j]);
							return NULL;
						}
                        VG_(snprintf)(args[i],XXX_MAX_BUF,"(IF (%s) THEN (0h%016x) ELSE (0h%016x) ENDIF)",ne,zero,1<<i);
                    }
                    VG_(snprintf)(nz,XXX_MAX_BUF,"BVPLUS(64,%s,%s,%s,%s,%s)",args[0],args[1],args[2],args[3],args[4],args[5]);
                    VG_(snprintf)(cond,XXX_MAX_BUF,"(%s = 0h%016x)",lquery,zero);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(IF (%s) THEN (0h%016x) ELSE (%s) ENDIF)",cond,zero,nz);
					for(i=0;i<=5;i++)
					{
						VG_(free)(args[i]);
					}
					VG_(free)(ne);
					VG_(free)(b);
					VG_(free)(nz);
					VG_(free)(cond);
					FFF;
                    return query;
                default:{FFF; return NULL;}            
        }
      
        case binop:
            if((dep->left == NULL) || (dep->right == NULL)) {FFF; return NULL;}
            if((fz_solver(dep->left,lquery) == NULL) || (fz_solver(dep->right,rquery) == NULL)) {FFF;return NULL;}
            opij = get_opij(dep->buop);
            switch(dep->buop)
            {
                case Iop_CmpEQ8 ... Iop_CmpEQ64:
					dirty_patch_size(dep,dep->left,0,lquery,tmpbuf);
					dirty_patch_size(dep,dep->right,0,rquery,tmpbuf1);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(IF (%s = %s) THEN (0b1) ELSE (0b0) ENDIF)",tmpbuf,tmpbuf1);
					FFF;
                    return query;
                case Iop_CmpNE8 ... Iop_CmpNE64:
					dirty_patch_size(dep,dep->left,0,lquery,tmpbuf);
					dirty_patch_size(dep,dep->right,0,rquery,tmpbuf1);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(IF (NOT(%s = %s)) THEN (0b1) ELSE (0b0) ENDIF)",tmpbuf,tmpbuf1);
					FFF;
                    return query;                
                case Iop_CmpLT32S:
                case Iop_CmpLE32S: 
                case Iop_CmpLT32U: 
                case Iop_CmpLE32U: 
                case Iop_CmpLT64S:
                case Iop_CmpLE64S: 
                case Iop_CmpLT64U: 
                case Iop_CmpLE64U: 
                    if(opij.type == 0){ 
                        if(opij.sign == 0) VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"BVLE(%s,%s)",lquery,rquery);
                        else VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"SBVLE(%s,%s)",lquery,rquery); 
                    }
                    else
					{ 
						if(opij.sign == 1) VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"SBVLT(%s,%s)",lquery,rquery);
                        else VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"BVLT(%s,%s)",lquery,rquery);
					}
                    VG_(snprintf)(query,XXX_MAX_BUF,"(IF %s THEN (0b1) ELSE (0b0) ENDIF)",tmpbuf);
					FFF;
                    return query;
                    break;
                case Iop_And8 ... Iop_And64:
					dirty_patch_size(dep,dep->left,0,lquery,tmpbuf);
					dirty_patch_size(dep,dep->right,0,rquery,tmpbuf1);
                    sop = S_and;
                    s_function(query,sop,dep->size,tmpbuf,tmpbuf1);
					FFF;
                    return query;
                case Iop_Xor8 ... Iop_Xor64:
                    sop = S_bvxor;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query;
                case Iop_Or8 ... Iop_Or64:
                    sop = S_or;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query;
                case Iop_Add8 ... Iop_Add64:
                    sop = S_bvplus;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query;
                case Iop_Sub8 ... Iop_Sub64:
                    sop = S_bvsub;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query; 
                case Iop_Mul8 ... Iop_Mul64:
                    sop = S_bvmult;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query;              
                case Iop_MullS8:    
                case Iop_MullS16:  
                case Iop_MullS32:  
                case Iop_MullS64:  
                case Iop_MullU8:  
                case Iop_MullU16:  
                case Iop_MullU32:  
                case Iop_MullU64:
                        sop = S_bvmult;
						dirty_patch_size(dep,dep->left,0,lquery,tmpbuf);
						dirty_patch_size(dep,dep->right,0,rquery,tmpbuf1);
                        s_function(query,sop,dep->size,tmpbuf,tmpbuf1);
						FFF;
                        return query;
                case Iop_Shl8 ... Iop_Shl64:
                    tl_assert(dep->right->op == Iconst || dep->left->op == Iconst);
                    sop = S_shl;
					if(dep->right->op == Iconst)
					{
		                if(dep->right->opval != 0)
						{
							shift = dep->right->opval;
							dirty_patch_size(dep,dep->left,True,lquery,tmpbuf);
							VG_(snprintf)(lquery,XXX_MAX_BUF,"((%s)[%d:0])",tmpbuf,opij.j - shift -1);
			                VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"%d",shift);
			                s_function(query,sop,dep->size,lquery,tmpbuf1);
						}
		                else  VG_(snprintf)(query,XXX_MAX_BUF,"%s",lquery);
					}
					else
					{
						FFF;
						return NULL;
					}
					FFF;
                    return query;
                case Iop_Shr8 ... Iop_Shr64:
                    tl_assert(dep->right->op == Iconst);
                    sop = S_shr;
                    if(dep->right->opval != 0)
					{
						shift = dep->right->opval;
	                    VG_(snprintf)(rquery,XXX_MAX_BUF,"%d",shift);
	                    s_function(query,sop,dep->size,lquery,rquery);
					}
                    else VG_(snprintf)(query,XXX_MAX_BUF,"%s",lquery);
					FFF;
                    return query;
                case Iop_Sar8 ... Iop_Sar64:
                    tl_assert(dep->right->op == Iconst);
                    if(dep->right->opval != 0){
						shift = dep->right->opval;
                        VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"BVSX(%s,%d)",lquery,dep->left->size+1);
                        args[0] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                        VG_(snprintf)(args[0],XXX_MAX_BUF,"(%s >> %d)",tmpbuf,shift);
                        VG_(snprintf)( query,XXX_MAX_BUF,"((%s)[%d:0])",args[0],opij.j-1);
                    }
                    else  VG_(snprintf)(query,XXX_MAX_BUF,"%s",lquery);
					FFF;
                    return query;         
                case Iop_DivU32:
                case Iop_DivU64:
                    sop = S_bvdiv;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query;  
                case Iop_DivS32:
                case Iop_DivS64:
                    sop = S_sbvdiv;
                    s_function(query,sop,dep->size,lquery,rquery);
					FFF;
                    return query;  
                case Iop_8HLto16:
                case Iop_16HLto32:
                case Iop_32HLto64:
                case Iop_64HLto128:
					if(dep->left->size + dep->right->size == dep->size)
                    	VG_(snprintf)(query,XXX_MAX_BUF,"(%s@%s)",lquery,rquery);
					else if(dep->left->size + dep->right->size < dep->size)
					{
						VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"(%s@%s)",lquery,rquery);
						VG_(snprintf)(query,XXX_MAX_BUF,"BVSX(%s,%d)",tmpbuf,dep->size);
					}
					FFF;
                    return query;
                case Iop_DivModU64to32:
                case Iop_DivModU128to64:
                    args[1] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                    args[2] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                    args[3] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                    args[4] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(dep->left->size < dep->size)
					{
						if(dep->left->op != Iconst)
							VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"%s@%s",solver_const(0,opij.i-dep->left->size),lquery);
						else
						{
							if(opij.i == 64)
								VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"0h%016x",opij.i);
							else VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"0h%032x",opij.i);
						}
					}
					else VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"%s",lquery);

					if(dep->right->size < dep->size)
					{
						if(dep->right->op != Iconst)
							VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"%s@%s",solver_const(0,opij.i - dep->right->size),rquery);
						else
						{
							if(opij.i == 64)
								VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"0h%016x",opij.i);
							else VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"0h%032x",opij.i);
						}
					}
					else VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"%s",rquery);

                    VG_(snprintf)(args[1],XXX_MAX_BUF,"BVDIV(%d,%s,%s)",opij.i,tmpbuf,tmpbuf1);
                    VG_(snprintf)(args[2],XXX_MAX_BUF,"BVMOD(%d,%s,%s)",opij.i,tmpbuf,tmpbuf1);
                    VG_(snprintf)(args[3],XXX_MAX_BUF,"((%s)[%d:0])",args[1],opij.j-1);
                    VG_(snprintf)(args[4],XXX_MAX_BUF,"((%s)[%d:0])",args[2],opij.j-1);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(%s@%s)",args[3],args[4]);
					for(i=1;i<=4;i++)
					{
						VG_(free)(args[i]);
					}
					FFF;
                    return query;
                case Iop_DivModS64to32:
                case Iop_DivModS128to64:
                    args[1] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                    args[2] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                    args[3] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
                    args[4] = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(dep->left->size < dep->size)
					{
						if(dep->left->op != Iconst)
							VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"BVSX(%s,%d)",lquery,opij.i);
						else
						{
							if(opij.i == 64)
								VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"0h%016x",opij.i);
							else VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"0h%032x",opij.i);
						}
					}
					else VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"%s",lquery);

					if(dep->right->size < dep->size)
					{
						if(dep->right->op != Iconst)
							VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"BVSX(%s,%d)",lquery,opij.i);
						else
						{
							if(opij.i == 64)
								VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"0h%016x",opij.i);
							else VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"0h%032x",opij.i);
						}
					}
					else VG_(snprintf)(tmpbuf1,XXX_MAX_BUF,"%s",rquery);

                    VG_(snprintf)(args[1],XXX_MAX_BUF,"SBVDIV(%d,%s,%s)",opij.i,tmpbuf,tmpbuf1);
                    VG_(snprintf)(args[2],XXX_MAX_BUF,"SBVMOD(%d,%s,%s)",opij.i,tmpbuf,tmpbuf1);
                    VG_(snprintf)(args[3],XXX_MAX_BUF,"((%s)[%d:0])",args[1],opij.j-1);
                    VG_(snprintf)(args[4],XXX_MAX_BUF,"((%s)[%d:0])",args[2],opij.j-1);
                    VG_(snprintf)( query,XXX_MAX_BUF,"(%s@%s)",args[3],args[4]);
					for(i=1;i<=4;i++)
					{
						VG_(free)(args[i]);
					}
					FFF;
                    return query;
                default:{FFF;return NULL;} 
            }
            break;
		case modu:
            if(dep->left == NULL || dep->right == NULL){FFF;return NULL;}
            if(fz_solver(dep->left,lquery) == NULL || fz_solver(dep->right,rquery) == NULL)
            {
				FFF;
                return NULL;
            }
            VG_(snprintf)( query, XXX_MAX_BUF, "BVMOD(%d,%s,%s)",dep->size,lquery,rquery);
			FFF;
            return query;	
		case mods:
            if(dep->left == NULL || dep->right == NULL){FFF;return NULL;}
            if(fz_solver(dep->left,lquery) == NULL || fz_solver(dep->right,rquery) == NULL)
            {
				FFF;
                return NULL;
            }
            VG_(snprintf)( query, XXX_MAX_BUF, "SBVMOD(%d,%s,%s)",dep->size,lquery,rquery);
			FFF;
            return query;		
        case cat:  
     
            if(dep->left == NULL || dep->right == NULL){FFF;return NULL;}  
            if(fz_solver(dep->left,lquery) == NULL || fz_solver(dep->right,rquery) == NULL)
            {
				FFF;
                return NULL;
            }
            VG_(snprintf)( query, XXX_MAX_BUF, "(%s@%s)",rquery,lquery);
			FFF;
            return query;

        case rdtmp:
            if(dep->left == NULL ){FFF;return NULL;}
            fz_solver(dep->left,lquery);
             VG_(snprintf)( query,XXX_MAX_BUF,"%s",lquery);
			FFF;
            return query;
        case loadI:
            if(dep->left == NULL ){	FFF; return NULL;}
            fz_solver(dep->left,lquery);
              VG_(snprintf)( query,XXX_MAX_BUF,"%s",lquery);
			FFF;
            return query;
        case mux0x:
            if(dep->left == NULL ){ FFF;return NULL;}
               fz_solver(dep->left,lquery);
              VG_(snprintf)( query,XXX_MAX_BUF,"%s",lquery);
			FFF;
            return query;
        default:
        {
			FFF;
            return NULL;
        } 
        }
	FFF;
    return NULL;              
}


char* fz_treesearch(Dep* dep,char *buf)
{
    char lbuffer[XXX_MAX_BUF];
    char rbuffer[XXX_MAX_BUF];
    char *Lbuf = lbuffer;
    char *Rbuf = rbuffer;
    char OP_buf[100];
    #if defined(VGA_x86)
    int value;
#elif defined(VGA_amd64)
    long value;
#endif 
    if(dep == NULL) return NULL;
    switch(dep->op){
        case symbol:
                VG_(snprintf)(buf,XXX_MAX_BUF,"input(%d)",dep->opval);
            break;
        case Iconst:
                VG_(snprintf)(buf,XXX_MAX_BUF,"0x%x:I%d",dep->opval,dep->size);
            break;
        case put:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf) != NULL)
                VG_(snprintf)(buf, XXX_MAX_BUF, "PUT(%s)",Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;
        case get:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf)!= NULL)
                VG_(snprintf)(buf, XXX_MAX_BUF, "GET:I%d(%s)",dep->size,Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;
        case load:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf) != NULL )
                VG_(snprintf)(buf, XXX_MAX_BUF, "LDle:I%d(%s)", dep->size, Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;
        case unop:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf))
            {
                IROp_to_str(dep->buop,OP_buf);
                VG_(snprintf)(buf, XXX_MAX_BUF, "%s(%s)",OP_buf,Lbuf);
            }
            else
            {
                buf = NULL;
                return NULL;
            } 
            break;       
        case binop:
            if((dep->left != NULL) && (dep->right != NULL) && fz_treesearch(dep->left,Lbuf)!= NULL && fz_treesearch(dep->right,Rbuf) != NULL)
            {
                IROp_to_str(dep->buop,OP_buf);
                VG_(snprintf)(buf, XXX_MAX_BUF, "%s(%s,%s)", OP_buf,Lbuf,Rbuf);
            }
            else
            {
                buf = NULL;
                return NULL;
            } 
            break;
 
        case store:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf) != NULL)
                VG_(snprintf)(buf, XXX_MAX_BUF, "STle(%s)",Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;

        case loadI:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf) != NULL)
                VG_(snprintf)(buf, XXX_MAX_BUF, "%s", Lbuf); 
            else
            {
                buf = NULL;
                return NULL;
            }
            break;

        case cat:
            if(dep->left != NULL && dep->right != NULL && fz_treesearch(dep->left,Lbuf)!= NULL && fz_treesearch(dep->right,Rbuf) != NULL)
            VG_(snprintf)(buf, XXX_MAX_BUF, "Cat%d(%s,%s)",dep->size,Rbuf,Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;

        case rdtmp:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf) != NULL)
                VG_(snprintf)(buf, XXX_MAX_BUF,"%s",Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;
        case mux0x:
            if(dep->left != NULL && fz_treesearch(dep->left,Lbuf) != NULL)
                VG_(snprintf)(buf, XXX_MAX_BUF,"%s",Lbuf);
            else
            {
                buf = NULL;
                return NULL;
            }
            break;
        case x86g:
            if(dep->left != NULL && dep->right != NULL && fz_treesearch(dep->left,Lbuf)!= NULL)
            {
                VG_(snprintf)(buf,XXX_MAX_BUF,"%s",fz_treesearch(dep->left,Lbuf));
            }
            else
            {
                buf = NULL;
                return NULL;
            }
            break;

        case amd64g:
            if(dep->left != NULL && dep->right != NULL && fz_treesearch(dep->left,Lbuf)!= NULL && fz_treesearch(dep->right,Rbuf)!= NULL)
            {
                VG_(snprintf)(buf,XXX_MAX_BUF,"amd64(%s,%s)",Lbuf,Rbuf);
            }
            else
            {
                buf = NULL;
                return NULL;
            }
            break;
        default:
        {
             buf = NULL;
             return NULL;
        } 
        }
    return buf;              
}

void del_dep(Dep* dep)
{
	Dep* ltmp;
	Dep* rtmp;
	if(dep == NULL) return;
	if(dep->father == 0)
	{
		ltmp = dep->left;
		rtmp = dep->right;
		dep->dirty = Fdirty;
		dep->left = NULL;
		dep->right = NULL;		
		VG_(free)(dep);
		if(ltmp != NULL) 
		{
			ltmp->father -= 1; 
			del_dep(ltmp);
		}		
		if(rtmp != NULL) 
		{
			rtmp->father -= 1; 
			del_dep(rtmp);
		}
	} 
}
