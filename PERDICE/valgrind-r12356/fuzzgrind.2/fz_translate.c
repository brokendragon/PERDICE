/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 *
 *  Based heavily on Flayer by redpig@dataspill.org
 *  Copyright (C) 2006,2007 Will Drewry <redpig@dataspill.org>
 *  Some portions copyright (C) 2007 Google Inc.
 *
 *  Based heavily on MemCheck by jseward@acm.org
 *  MemCheck: Copyright (C) 2000-2007 Julian Seward
 *  jseward@acm.org
 *
 *
 *  This program is free software; you can redistribute it and/or
 *  modify it under the terms of the GNU General Public License as
 *  published by the Free Software Foundation; either version 2 of the
 *  License, or (at your option) any later version.
 *  This program is distributed in the hope that it will be useful, but
 *  WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 *  General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA
 *  02111-1307, USA.
 *
 *  The GNU General Public License is contained in the file LICENCE.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>
//#include <dir.h>

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
#include "fz.h"
#include "pub_tool_vki.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_libcfile.h"


//#include "../coregrind/pub_core_xarray.h"
//#include"../coregrind/m_debuginfo/priv_tytypes.h"
//#include"../coregrind/m_debuginfo/priv_storage.h"
#include "pub_tool_libcsetjmp.h"
#include "../coregrind/pub_core_basics.h"
#include "../coregrind/pub_core_vki.h"
#include "../coregrind/pub_core_vkiscnums.h"
#include "../coregrind/pub_core_threadstate.h"


#define Debug_jin 1

#define VER_0.9

#define FZ_DEBUG
#undef FZ_DEBUG

#define MAX_FILE_SIZE 256

//add by luo for x64 symbolize
#if defined(VGA_x86)
#  define GP_COUNT 8
#elif defined(VGA_amd64)
#  define GP_COUNT 16
#elif defined(VGA_ppc32) || defined(VGA_ppc64)
#  define GP_COUNT 34
#else
#  error Unknown arch
#endif





//in catch : global
int *addrp;
static int flag=0;
static int count=0;
extern char fn_buf[200];
extern char buf[100];
extern char run_times;

// for selective synbolic execution

static  unsigned long func_ebp = 0,main_ebp = 0;
static Bool    is_in_func = False;
static Bool    is_in_obj = False;
static Addr    ret_addr = 0;


//Debug flag
//Print info flag
Bool fengflag=False;
Bool debugflag=False;
//site
Bool fengSwitchFlag=False;//for switch in fz_instrument
Bool fengHelperEnterFlag=False;//for helper_xx enter
Bool feng8664Flag=False;//for x86_xx and amd64_xx

//parameters
Bool fengHelperPara=False;//for helper parameters

//behavior
Bool fengDepFlag=False;//for xx_dependency_xx
Bool fengDirtyFlag=False;//for add dirty
Bool fengBinopFlag=False;//for binop parameters


Bool fengRetFlag=False;//for return
Bool fengConsFlag=False;//for constraint print

//size
Bool fengSizeHelpercFlag=False;//for size in helperc
Bool fengSizeFlag=False;//for size
Bool fengSizeDepFlag=False;//for size in dep

Bool fengAddTmp=False;//flag before add dep tmp
Bool fengAddFlag=False;//flag before add dep

//data
Bool fengTmpFlag=False;//for temp debug
Bool fengAddrFlag=False;//for addr print

//assert
Bool fengAssertFlag=False;

//selective debug!
Bool jinAssertObjFlag = False;
Bool jinAssertFlag = False;




typedef struct {
    UWord args[GP_COUNT];
    UInt used;
} GuestArgs;

// VG_(N_THREADS) - do threads actually run concurrently here too?

static GuestArgs guest_args[VG_N_THREADS];
//static Bool is_in_obj_lists(Addr addr);
//static Bool is_in_function();

#if defined(VGA_x86)
static void populate_guest_args(ThreadId tid) {
  /* This is legacy.  I was using apply_GPs callback,
   * but it isn't threadsafe.  So for now, we bind to
   * the ThreadState functions for the specific x86 arch
   */
    ThreadState *ts =  VG_(get_ThreadState) (tid);
    guest_args[tid].args[1] = ts->arch.vex.guest_ECX;
    guest_args[tid].args[2] = ts->arch.vex.guest_EDX;
    guest_args[tid].args[3] = ts->arch.vex.guest_EBP;
    
    guest_args[tid].used = 3;
}
#elif defined(VGA_amd64)
static void populate_guest_args(ThreadId tid) {
    ThreadState *ts =  VG_(get_ThreadState) (tid);
    guest_args[tid].args[1] = ts->arch.vex.guest_RDI;
    guest_args[tid].args[2] = ts->arch.vex.guest_RSI;
    guest_args[tid].args[3] = ts->arch.vex.guest_RBP;
    guest_args[tid].args[4] = ts->arch.vex.guest_RSP;
    guest_args[tid].used = 4;
}

#endif

//#define VGA_amd64
#if defined(VGA_amd64)
#define FENG_AMD64
#endif // defined(VGA_amd64)
//Feng:here, we should change all type into 64bit? do it by #define
//Feng:I add all types here to support 64bit which can be seen in switch case
//Feng:but now we still use 32 env type
#ifdef FENG_AMD64
static IRExpr *assignNew(IRSB *bb, IRExpr *e) {
	IRTemp t = newIRTemp(bb->tyenv, Ity_I64);

	if(fengSwitchFlag){VG_(printf)("feng:type of ir expr:%d\n",typeOfIRExpr(bb->tyenv, e));}
	switch (typeOfIRExpr(bb->tyenv, e)) {
	case Ity_I1:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_1Uto64, e)));
		break;
	case Ity_I8:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_8Uto64, e)));
		break;
	case Ity_I16:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_16Uto64, e)));
		break;
	case Ity_I32:
		//return e;
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_32Uto64, e)));
		break;
	case Ity_I64:
		return e;
		break;
	//Feng:add
	case Ity_I128:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_128to64, e)));
		break;
	//case Ity_F32:
		return NULL;
		//addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F32toI64S, e)));
		break;
	//case Ity_F64:
		return NULL;
		//addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F64toI64S, e)));
		break;
	//case Ity_F128:
		//if(fengSwitchFlag){VG_(printf)("feng:switch f128\n");}
		return NULL;
		//addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F128toI64S, e)));
		break;
	case Ity_V128:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_V128to64, e)));
		break;
	default:
		if(fengSwitchFlag){VG_(printf)("feng:switch default\n");}
		VG_(tool_panic)("assignNew");
	}
	return IRExpr_RdTmp(t);
}
#else
static IRExpr *assignNew(IRSB *bb, IRExpr *e) {
	IRTemp t = newIRTemp(bb->tyenv, Ity_I32);

	if(fengSwitchFlag){VG_(printf)("feng:type of ir expr:%d\n",typeOfIRExpr(bb->tyenv, e));}
	switch (typeOfIRExpr(bb->tyenv, e)) {
	case Ity_I1:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_1Uto32, e)));
		break;
	case Ity_I8:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_8Uto32, e)));
		break;
	case Ity_I16:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_16Uto32, e)));
		break;
	case Ity_I32:
		return e;
	case Ity_I64:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_64to32, e)));
		break;
		//Feng:add
		//case Ity_I128:
		//	if(fengSwitchFlag){VG_(printf)("feng:switch i128\n");}
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_128to64, e)));
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_64to32, e)));
		//	break;
		//case Ity_F32:
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F32toI32S, e)));
		//	break;
		//case Ity_F64:
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F64toI32S, e)));
		//	break;
		//case Ity_F128:
		//	if(fengSwitchFlag){VG_(printf)("feng:switch f128\n");}
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F128toF32, e)));
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F32toI32S, e)));
		//	break;
		//case Ity_V128:
		//	if(fengSwitchFlag){VG_(printf)("feng:switch v128\n");}
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_V128to32, e)));
		//	break;
	default:
		if(fengSwitchFlag){VG_(printf)("feng:switch default\n");}
		VG_(tool_panic)("assignNew");
	}
	return IRExpr_RdTmp(t);
}
#endif // FENG_AMD64

#ifdef FZ_DEBUG
static void ppDepReg(Dep* reg) {
	//VG_(printf)("    reg    = %d\n", reg->value.reg);
	VG_(printf)("    size   = %d\n", reg->size);
	VG_(printf)("    constr = %s\n", reg->cons);
}
static void ppDepTmp(Dep* tmp) {
	VG_(printf)("    size   = %d\n", tmp->size);
	VG_(printf)("    constr = %s\n", tmp->cons);
}
static void ppDepAddr(Dep* addr) {
	VG_(printf)("    addr   = 0x%08x\n", (UInt)addr->value.addr);
	VG_(printf)("    size   = %d\n", addr->size);
	VG_(printf)("    constr = %s\n", addr->cons);
}
#else
#define ppDepReg(x)
#define ppDepTmp(x)
#define ppDepAddr(x)
#endif
/*
* Check that the size of the constraint buffer is large enough to contain the
* new string. If not, reallocate the buffer.
*/

static void realloc_cons_buf(Dep* d, UInt new_size) {
	d->cons_size *= 2;
	tl_assert(new_size < d->cons_size);

	if (d->cons == d->buf) {
		d->cons = VG_(malloc)("fz.rcb.1", d->cons_size);
	}
	else {
		d->cons = VG_(realloc)("fz.rcb.2", d->cons, d->cons_size);
	}

	tl_assert(d->cons != NULL);
}
static void free_cons_buf(Dep* d) {
	if (d->cons != d->buf) {
		VG_(free)(d->cons);
		d->cons = d->buf;
		d->cons_size = XXX_MAX_BUF;
	}
	d->cons[0] = '\x00';
}

#define SPRINTF_CONS(d, fmt, ...) do {                                                 \
	UInt res_snprintf;                                                                 \
	Bool ok = True;                                                                    \
	do {                                                                               \
	/*VG_(printf)("SPRINTF_CONS:");*/													\
	/*VG_(printf)((fmt),__VA_ARGS__);	*/												\
	/*VG_(printf)("\n");*/													\
	res_snprintf = VG_(snprintf)((d).cons, (d).cons_size, (fmt), __VA_ARGS__);     \
	if (res_snprintf >= (d).cons_size - 1) { /* valgrind's buggy snprintf... */    \
	realloc_cons_buf(&(d), res_snprintf);                                      \
	res_snprintf = VG_(snprintf)((d).cons, (d).cons_size, (fmt), __VA_ARGS__); \
	ok = (res_snprintf < (d).cons_size - 1);                                   \
	}                                                                              \
	} while (!ok);                                                                     \
} while (0)


static UInt add_dependency_reg(Reg reg, UInt size) {
	if(fengDepFlag || fengSizeDepFlag){VG_(printf)("feng:entered add_dependency_reg with reg=%d size=%d\n",reg,size);}


	// 	tl_assert(reg >= 0 && reg < MAX_DEP);
	// 	tl_assert(size != 0);
	if (reg < 0)
	{
		VG_(printf)("Feng:depend of reg=%d\n",reg);
		VG_(tool_panic)("feng:depend of reg: invalid reg !");
	}

	if (reg > depreg.count){
		return INVALID_TMP;
	}

	if (size==1 || size==8 || size==16 || size==32 ||size==64 || size==128)
	{
		//only these size valid
	}else{
		VG_(printf)("Feng:dep reg size=%d\n", size);
		VG_(tool_panic)("Feng: no handled size\n");
	}

	Dep* preg=getDep(&depreg,reg);
	if (preg==NULL){
		return INVALID_TMP;
	}
	preg->size=size;

	//feng:update count
	if (depreg.count<reg){
		depreg.count=reg;
	}

#ifdef FZ_DEBUG
	VG_(printf)("[+] dependency_reg[%d]\n", reg);
#endif

	if(fengRetFlag)VG_(printf)("feng:return\n");
	return reg;
}


static UInt add_dependency_tmp(Tmp tmp, UInt size) {
	if(fengDepFlag){VG_(printf)("feng:entered add_dependency_tmp with size:%d tmp:%d\n",size,tmp);}

	//tl_assert(tmp >= 0 && tmp < MAX_DEP);
	//防止DEP无约束扩展
	if (tmp < 0)
	{
		VG_(printf)("Feng:depend of tmp=%d\n",tmp);
		VG_(tool_panic)("feng:depend of reg: invalid reg !");
	}

	if (tmp > deptmp.count){
		return INVALID_TMP;
	}

	if (size==1 || size==8 || size==16 || size==32 ||size==64 || size==128)
	{
		//Feng:size 必须符号规定
	}else{
		VG_(printf)("Feng:dep tmp size=%d\n", size);
		VG_(tool_panic)("Feng: no handled size\n");
	}



	Dep* ptmp=getDep(&deptmp,tmp);
	if (ptmp==NULL){
		return INVALID_TMP;
	}
	

	ptmp->size=size;

	//feng:update count
	if (deptmp.count<tmp){
		deptmp.count=tmp;
	}


#ifdef FZ_DEBUG
	VG_(printf)("[+] dependency_tmp[%d]\n", tmp);
#endif

	if(fengRetFlag)VG_(printf)("feng:return\n");
	return tmp;
}

//Feng:ok
UInt add_dependency_addr(Addr addr, UInt size) {
	if(fengDepFlag || fengSizeDepFlag){VG_(printf)("feng:entered add_dependency_addr with addr:%d size:%d\n",addr,size);}

	UInt i;
	DepExt *depaddr = SELECT_DEPADDR(size);
	UInt *depaddr_count = SELECT_DEPADDR_COUNT(size);
	Dep *preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;
	Dep* pi=NULL;
	Dep* pj=NULL;

	if (size==1 || size==8 || size==16 || size==32 ||size==64 || size==128)
	{
		//feng:size 应当在此范围内
	}else{
		VG_(printf)("Feng:dep addr size=%d\n", size);
		VG_(tool_panic)("Feng: no handled size\n");
	}

	/* search for an existing dependency and replace it */
	for (i = 0; i < *depaddr_count; i++) {
		paddr=getDep(depaddr,i);
		if (paddr->value.addr == addr) {
			break;
		}
	}

	//tl_assert(i < MAX_DEP);
	//VG_(printf)("Feng:i=%d ? depaddr count=%d\n",i,*depaddr_count);
	if (i == *depaddr_count) {
		paddr=getDep(depaddr,i);
		paddr->value.addr=addr;
		*depaddr_count += 1;
		//VG_(printf)("Feng:depaddr count=%d with addr=0x%x\n",*depaddr_count,addr);
	}
	tl_assert(size != 0);

	paddr->size=size;
#ifdef FZ_DEBUG
	VG_(printf)("[+] dependency_addr[%d]\n", i);
#endif

	if(fengRetFlag)VG_(printf)("feng:return\n");

	return i;
}

//Feng:ok
static void del_dependency_tmp(Tmp tmp) {
	if(fengDepFlag){VG_(printf)("feng:entered del_dependency_tmp with tmp=%d\n",tmp);}

	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;

	tl_assert(tmp >= 0 && tmp < MAX_DEP);
	ptmp=getDep(&deptmp,tmp);
	if (ptmp->cons[0]!='\x00')
	{
		free_cons_buf(ptmp);
	}
}

static void del_dependency_reg(Reg reg) {
	if(fengDepFlag){VG_(printf)("feng:entered del_dependency_reg\n");}
	if(fengDepFlag){VG_(printf)("Feng:del dep reg=%d\n",reg);}

	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;

	tl_assert(reg >= 0 && reg < MAX_DEP);
	preg=getDep(&depreg,reg);
	if (preg->cons[0]!='\x00')
	{
		free_cons_buf(preg);
	}
}

//Feng:may ok
void del_dependency_addr(Addr addr, UInt size) {
	if(fengDepFlag){VG_(printf)("feng:entered del_dependency_addr\n");}
	if(fengDepFlag){VG_(printf)("Feng:del dep addr=%d\n",addr);}

	DepExt *depaddr = SELECT_DEPADDR(size);
	UInt *depaddr_count = SELECT_DEPADDR_COUNT(size);
	UInt i, j = *depaddr_count - 1;
	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;
	Dep* pi=NULL;
	Dep* pj=NULL;

	for (i = 0; i < *depaddr_count; i++) {
		pi=getDep(depaddr,i);
		if (pi->value.addr == addr) {
#ifdef FZ_DEBUG
			VG_(printf)("[+] removing dependency_addr[%d]\n", i);
			ppDepAddr(pi);
#endif
			free_cons_buf(pi);
			//VG_(printf)("Feng:i=%d ? j=%d ? depaddr count=%d\n",i,j,*depaddr_count);
			if (i < j) {
				pj=getDep(depaddr,j);
				pi->value.addr = pj->value.addr;
				pi->size = pj->size;
				SPRINTF_CONS(*pi, "%s", pj->cons);
				free_cons_buf(pj);
				if(fengflag){VG_(printf)("feng:delete dep addr=%llu\n",addr);}//temp debug
			}

			*depaddr_count -= 1;
			//VG_(printf)("Feng:depaddr count=%d\n",*depaddr_count);
			break;
		}

	}

}


char * depend_on_addr(Addr addr, UInt size) {
	UInt i;
	DepExt *depaddr = SELECT_DEPADDR(size);
	UInt *depaddr_count = SELECT_DEPADDR_COUNT(size);

	Dep* paddr=NULL;
	Dep* pi=NULL;

	/* search for an existing dependency and replace it */
	for (i = 0; i < *depaddr_count; i++) {
		pi=getDep(depaddr,i);
		if (pi->value.addr == addr) {
			return pi->cons;
		}
	}

	return NULL;
}

static UInt depend_of_reg(Reg reg) {
	if(fengDepFlag){VG_(printf)("Feng:enter depend of reg=%d\n",reg);}

	//tl_assert(reg >= 0 && reg < MAX_DEP);
	if (reg < 0)
	{
		VG_(printf)("Feng:depend of reg=%d\n",reg);
		VG_(tool_panic)("feng:depend of reg: invalid reg !");
	}

	if (reg > depreg.count){
		return False;
	}


	return getDep(&depreg,reg)->cons[0] != '\x00';
}

static UInt depend_of_tmp(Tmp tmp) {
	if(fengDepFlag){VG_(printf)("Feng:depend of tmp=%d\n",tmp);}

	//tl_assert(tmp >= 0 && tmp < MAX_DEP);
	if (tmp < 0)
	{
		{VG_(printf)("Feng:depend of tmp=%d\n",tmp);}
		VG_(tool_panic)("feng:depend of tmp: invalid tmp !");

	}

	if (tmp > deptmp.count){
		return False;
	}

	return getDep(&deptmp,tmp)->cons[0] != '\x00';;
}
/*
* Write a value to a register
* tmp is invalid if it's a constant
*/
//Feng:ok
static VG_REGPARM(0) void helperc_put(Tmp tmp, Reg offset) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc\n");}
	UInt j;

	Dep* ptmp=NULL;
	Dep *pj=NULL;

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("put returned!\n ");
		return;
	}

	if (tmp != INVALID_TMP) {
		if (depend_of_tmp(tmp)) {
			ptmp=getDep(&deptmp,tmp);
			if(fengSizeHelpercFlag){VG_(printf)("feng:in helper_put ptmp->%d\n",ptmp->size);}
			j = add_dependency_reg(offset, ptmp->size);
			if (j==INVALID_TMP){
				return;
			}


			pj=getDep(&depreg,j);
			SPRINTF_CONS(*pj, "PUT(%s)", ptmp->cons);
			ppDepReg(pj);
			return;
		}

	}
	/* delete an eventually dependency to the offset if:
	* - the value to write is a constant
	* - or we don't depend of the tmp */
	del_dependency_reg(offset);
}
/*
* Valgrind does implicit size conversion between PUT and GET, so we can't rely
* on the dependency's size. For example : GET:I32(PUT(1Uto8(a))).
*/
//Feng:ok
static VG_REGPARM(0) void helperc_get(Reg offset, Tmp tmp, UInt size) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_get with size:%d\n",size);}
	UInt j;

	Dep* preg=NULL;
	Dep* ptmp=NULL;
	Dep* pj=NULL;

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("get returned!\n ");
		return;
	}

	if (depend_of_reg(offset)) {
		if(fengSizeHelpercFlag){VG_(printf)("feng:in helper_get offset size %d\n",size);}
		if (fengAddTmp){VG_(printf)("Feng:in helperc_get add dependency tmp\n");}

		preg=getDep(&depreg,offset);

		j = add_dependency_tmp(tmp, size);
		if (j==INVALID_TMP){del_dependency_tmp(tmp);}

		pj=getDep(&deptmp,j);
		SPRINTF_CONS(*pj, "GET:I%d(%s)", size, preg->cons);
		ppDepTmp(pj);

		return;
	}
	del_dependency_tmp(tmp);
}

static VG_REGPARM(0) void helperc_load(Addr addr, Tmp tmp, Tmp tmp_to, UInt size) {
	if(fengTmpFlag){VG_(printf)("feng:entered helperc_load with addr:%llu\n",addr);}
	UInt a, b, c;
	UInt d,e,f,g;
	UInt i, j, pos;
	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;
	Dep* pi=NULL;
	Dep* pj=NULL;
	Dep* paddr8=NULL,*paddr16=NULL,*paddr32=NULL,*paddr64=NULL;
	Dep* pa=NULL,*pb=NULL,*pc=NULL;
	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("load returned!\n ");
		return;
	}

	if (addr != INVALID_ADDR) {

		//if(fengflag){VG_(printf)("feng:load valid\n");}//temp debug

		if(fengSizeHelpercFlag){VG_(printf)("feng:do helperc_load with size:%d\n",size);}
		if (size == 8) {
			for (i = 0; i < depaddr8.count; i++) {
				paddr8=getDep(&depaddr8,i);

				if (paddr8->value.addr != addr){
					continue;
				}

				if(fengAddrFlag){VG_(printf)("feng:do helper_load depaddr8[%d]=%llu ? %llu\n",i,paddr8->value.addr,addr);}
				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr8->value.addr,addr);}//temp debug

				if (VG_(strncmp)(paddr8->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr8->cons, "ST", 2) != 0) {
						break;
				}

				if (fengAddTmp){VG_(printf)("Feng:helperc_load");}

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);

				if(fengSizeHelpercFlag){VG_(printf)("feng:in helperc_load add dep 8\n");}
				if(fengConsFlag){VG_(printf)("feng:in helper_load addr constraint:%s\n",paddr8->cons);}

				SPRINTF_CONS(*pj, "LDle:I%d(%s)", size, paddr8->cons);

				if(fengConsFlag){VG_(printf)("feng:in helper_load tmp constraint:%s\n",pj->cons);}

				ppDepTmp(pj);

				return;
			}

			for (i = 0; i < depaddr16.count; i++) {
				paddr16=getDep(&depaddr16,i);

				//Feng: address exceed - continue
				//Feng: 16 = 8 * 2, addr8 +0 +1
				if (! (addr >= paddr16->value.addr
					&& addr <= paddr16->value.addr + 1) ){
						continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr16[%d]=%llu ? %llu\n",size,i,paddr16->value.addr,addr);}//temp debug

				pos = addr - paddr16->value.addr;
				if (VG_(strncmp)(paddr16->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr16->cons, "ST", 2) != 0) {
						break;
				}

				if (fengAddTmp){VG_(printf)("Feng:helperc_load");}
				if(fengSizeHelpercFlag){VG_(printf)("feng:in helperc_load add dep 8\n");}

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);


#ifdef FENG_AMD64
				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);
				SPRINTF_CONS(*pj,
					"64to8(And64(Shr64(8Uto64(LDle:I8(%s)),0x%x:I64),0xff:I64))",
					paddr16->cons, 8 * pos);
#else
				SPRINTF_CONS(*pj,
					"32to8(And32(Shr32(8Uto32(LDle:I8(%s)),0x%x:I32),0xff:I32))",
					paddr16->cons, 8 * pos);
#endif // FENG_AMD64
				ppDepTmp(pj);
				return;
			}

			for (i = 0; i < depaddr32.count; i++) {
				paddr32=getDep(&depaddr32,i);

				//Feng: address exceed - continue
				//Feng: 32 = 8 * 4, addr8 + 0 +1 +2 +3
				if ( ! (addr >= paddr32->value.addr
					&& addr <= paddr32->value.addr + 3) ){
						continue;
				}


				pos = addr - paddr32->value.addr;
				if (VG_(strncmp)(paddr32->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr32->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 8\n");}

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);


#ifdef FENG_AMD64
				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);
				SPRINTF_CONS(*pj,
					"64to8(And64(Shr64(8Uto64(LDle:I8(%s)),0x%x:I64),0xff:I64))",
					paddr32->cons, 8 * pos);
#else
				SPRINTF_CONS(*pj,
					"32to8(And32(Shr32(8Uto32(LDle:I8(%s)),0x%x:I32),0xff:I32))",
					paddr32->cons, 8 * pos);
#endif // FENG_AMD64

				ppDepTmp(pj);

				return;
			}

#ifdef FENG_AMD64
			for (i = 0; i < depaddr64.count; i++) {
				paddr64=getDep(&depaddr64,i);

				//Feng: address exceed - continue
				//Feng: 64= 8 * 8, addr8 +0 +1 +2 +3 +4 +5 +6 +7
				if ( ! (addr >= paddr64->value.addr
					&& addr <= paddr64->value.addr + 7 )){
						continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr64->value.addr,addr);}//temp debug

				pos = addr - paddr64->value.addr;
				if (VG_(strncmp)(paddr64->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr64->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 8\n");}

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);


				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);

				SPRINTF_CONS(*pj,
					"64to8(And64(Shr64(8Uto64(LDle:I8(%s)),0x%x:I64),0xff:I64))",
					paddr64->cons, 8 * pos);

				ppDepTmp(pj);

				return;
			}
#endif // FENG_AMD64
		}
		else if (size == 16) {


			for (i = 0; i < depaddr16.count; i++) {
				paddr16=getDep(&depaddr16,i);

				if (paddr16->value.addr != addr){
					continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr8->value.addr,addr);}//temp debug

				if (VG_(strncmp)(paddr16->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr16->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 16\n");}

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);

				SPRINTF_CONS(*pj, "LDle:I%d(%s)", size, paddr16->cons);
				ppDepTmp(pj);

				return;
			}

			for (i = 0; i < depaddr32.count; i++) {
				paddr32=getDep(&depaddr32,i);

				//Feng: may wrong here
				//Feng: address exceed - continue
				//Feng: 32 = 16 * 2, addr16 +0 +1 +2
				//Feng: addr range may wrong
				if ( ! (addr >= paddr32->value.addr
					&& addr <= paddr32->value.addr + 2 )) {
						continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr8->value.addr,addr);}//temp debug

				pos = addr - paddr32->value.addr;
				if (VG_(strncmp)(paddr32->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr32->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 16\n");}

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);


#ifdef FENG_AMD64
				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);
				SPRINTF_CONS(*pj,
					"64to16(And64(Shr64(16Uto64(LDle:I16(%s)),0x%x:I64),0xffff:I64))",
					paddr32->cons, 8 * pos);
#else
				SPRINTF_CONS(*pj,
					"32to16(And32(Shr32(16Uto32(LDle:I16(%s)),0x%x:I32),0xffff:I32))",
					paddr32->cons, 8 * pos);
#endif // FENG_AMD64

				ppDepTmp(pj);

				return;
			}

#ifdef FENG_AMD64
			for (i = 0; i < depaddr64.count; i++) {
				paddr64=getDep(&depaddr64,i);

				//Feng: address exceed - continue+6
				//Feng: 64=16 * 4, addr16 +0 +1 +2 +3 +4 +5 +6
				if ( ! (addr >= paddr64->value.addr
					&& addr <= paddr64->value.addr + 6)){
						continue;
				}

				pos = addr - paddr64->value.addr;
				if (VG_(strncmp)(paddr64->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr64->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 16\n");}

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);


				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);
				SPRINTF_CONS(*pj,
					"64to16(And64(Shr64(16Uto64(LDle:I16(%s)),0x%x:I64),0xffff:I64))",
					paddr64->cons, 8 * pos);
				ppDepTmp(pj);


				return;
			}
#endif // FENG_AMD64

			for (i = 0; i < depaddr8.count; i++) {
				paddr8=getDep(&depaddr8,i);

				if (paddr8->value.addr != addr){
					continue;
				}

				if(fengflag){VG_(printf)("feng:load i depaddr8[%d]=%llu ? %llu\n",i,paddr8->value.addr,addr);}//temp debug

				for (a = 0; a < depaddr8.count; a++) {
					paddr8=getDep(&depaddr8,a);
					if (paddr8->value.addr == addr + 1) {
						if(fengflag){VG_(printf)("feng:load a depaddr8[%d]=%llu ? %llu\n",a,paddr8->value.addr,addr);}//temp debug
						break;
					}
				}

				//tl_assert(a!=depaddr8.count);
				if(a == depaddr8.count){
					continue;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 16\n");}

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);


				SPRINTF_CONS(*pj, "Cat16(LDle:I8(%s),LDle:I8(%s))", getDep(&depaddr8,a)->cons, getDep(&depaddr8,i)->cons);
				ppDepTmp(pj);

				return;
			}
		}
		else if (size == 32) {


			for (i = 0; i < depaddr32.count; i++) {
				paddr32=getDep(&depaddr32,i);
				if (paddr32->value.addr != addr) {
					continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr8->value.addr,addr);}//temp debug

				if (VG_(strncmp)(paddr32->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr32->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 32\n");}

				j = add_dependency_tmp(tmp_to, 32);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);

				SPRINTF_CONS(*pj, "LDle:I32(%s)", paddr32->cons);
				ppDepTmp(pj);

				return;

			}

#ifdef FENG_AMD64
			for (i = 0; i < depaddr64.count; i++) {
				paddr64=getDep(&depaddr64,i);

				//Feng: address exceed - continue
				//Feng: 64=32 * 2, addr32 +0 +1 +2 +3 +4
				if (! (addr >= paddr64->value.addr
					&& addr <= paddr64->value.addr + 4)){
						continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr64->value.addr,addr);}//temp debug

				pos = addr - paddr64->value.addr;
				if (VG_(strncmp)(paddr64->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr64->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 32\n");}

				j = add_dependency_tmp(tmp_to, 32);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);

				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);

				SPRINTF_CONS(*pj,
					"64to32(And64(Shr64(32Uto64(LDle:I32(%s)),0x%x:I64),0xffffffff:I64))",
					paddr64->cons, 8 * pos);
				ppDepTmp(pj);

				return;
			}
#endif // FENG_AMD64

			for (i = 0; i < depaddr8.count; i++) {
				paddr8=getDep(&depaddr8,i);
				if (paddr8->value.addr == addr) {
					//VG_(printf)("feng: find i:%d\n",i);

					for (a = 0; a < depaddr8.count; a++) {
						paddr8=getDep(&depaddr8,a);
						if (paddr8->value.addr == addr + 1) {
							//VG_(printf)("feng: find a:%d\n",a);
							break;
						}
					}
					for (b = 0; b < depaddr8.count; b++) {
						paddr8=getDep(&depaddr8,b);
						if (paddr8->value.addr == addr + 2) {
							//VG_(printf)("feng: find b:%d\n",b);
							break;
						}
					}
					for (c = 0; c < depaddr8.count; c++) {
						paddr8=getDep(&depaddr8,c);
						if (paddr8->value.addr == addr + 3) {
							//VG_(printf)("feng: find c:%d\n",c);
							break;
						}
					}
					// XXX
					//tl_assert(a != depaddr8.count && b != depaddr8.count && c != depaddr8.count);
					if (a == depaddr8.count || b == depaddr8.count || c == depaddr8.count) {
						continue;
					}

					if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 32\n");}
					j = add_dependency_tmp(tmp_to, 32);
					if (j==INVALID_TMP){break;}

					pj=getDep(&deptmp,j);


					SPRINTF_CONS(*pj,
						"Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s))))",
						getDep(&depaddr8,c)->cons,
						getDep(&depaddr8,b)->cons,
						getDep(&depaddr8,a)->cons,
						getDep(&depaddr8,i)->cons);
					ppDepTmp(pj);

					return;
				}
			}
		}
		else if (size == 64) {

			// feng:we support it now
#ifdef FENG_AMD64
			//Feng:change site, edit here for 64bit
			for (i = 0; i < depaddr64.count; i++) {
				paddr64=getDep(&depaddr64,i);
				if (paddr64->value.addr != addr) {
					continue;
				}

				if(fengflag){VG_(printf)("feng:load size=%d depaddr8[%d]=%llu ? %llu\n",size,i,paddr8->value.addr,addr);}//temp debug

				if (VG_(strncmp)(paddr64->cons, "input", 5) != 0
					&& VG_(strncmp)(paddr64->cons, "ST", 2) != 0) {
						break;
				}

				if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 64\n");}

				j = add_dependency_tmp(tmp_to, 64);
				if (j==INVALID_TMP){break;}

				pj=getDep(&deptmp,j);

				SPRINTF_CONS(*pj, "LDle:I64(%s)", paddr64->cons);
				ppDepTmp(pj);
				return;

			}

			for (i = 0; i < depaddr8.count; i++) {
				paddr8=getDep(&depaddr8,i);
				if (paddr8->value.addr == addr) {
					//VG_(printf)("feng: find i:%d\n",i);

					for (a = 0; a < depaddr8.count; a++) {
						paddr8=getDep(&depaddr8,a);
						if (paddr8->value.addr == addr + 1) {
							//VG_(printf)("feng: find a:%d\n",a);
							break;
						}
					}
					for (b = 0; b < depaddr8.count; b++) {
						paddr8=getDep(&depaddr8,b);
						if (paddr8->value.addr == addr + 2) {
							//VG_(printf)("feng: find b:%d\n",b);
							break;
						}
					}
					for (c = 0; c < depaddr8.count; c++) {
						paddr8=getDep(&depaddr8,c);
						if (paddr8->value.addr == addr + 3) {
							//VG_(printf)("feng: find c:%d\n",c);
							break;
						}
					}
					for (d = 0; d < depaddr8.count; d++) {
						paddr8=getDep(&depaddr8,d);
						if (paddr8->value.addr == addr + 4) {
							//VG_(printf)("feng: find d:%d\n",d);
							break;
						}
					}
					for (e = 0; e < depaddr8.count; e++) {
						paddr8=getDep(&depaddr8,e);
						if (paddr8->value.addr == addr + 5) {
							//VG_(printf)("feng: find e:%d\n",e);
							break;
						}
					}
					for (f = 0; f < depaddr8.count; f++) {
						paddr8=getDep(&depaddr8,f);
						if (paddr8->value.addr == addr + 6) {
							//VG_(printf)("feng: find f:%d\n",f);
							break;
						}
					}
					for (g = 0; g < depaddr8.count; g++) {
						paddr8=getDep(&depaddr8,g);
						if (paddr8->value.addr == addr + 7) {
							//VG_(printf)("feng: find g:%d\n",g);
							break;
						}
					}

					// XXX
					//tl_assert(a != depaddr8.count && b != depaddr8.count && c != depaddr8.count);
					//tl_assert(d != depaddr8.count && e != depaddr8.count && f != depaddr8.count && g != depaddr8.count);
					if (a == depaddr8.count || b == depaddr8.count || c == depaddr8.count) {
						continue;
					}
					if (d == depaddr8.count || e == depaddr8.count || f == depaddr8.count || g == depaddr8.count) {
						continue;
					}

					if(fengAddFlag){VG_(printf)("feng:in helper_load add dep 64\n");}

					j = add_dependency_tmp(tmp_to, 64);
					if (j==INVALID_TMP){break;}

					pj=getDep(&deptmp,j);

					SPRINTF_CONS(*pj,
						//"Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s))))",
						"Cat64(Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s)))),Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s)))))",
						/*"Cat64(LDle:I8(%s),Cat56(LDle:I8(%s),Cat48(LDle:I8(%s),Cat40(LDle:I8(%s),Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s))))))))",*/
						getDep(&depaddr8,g)->cons,
						getDep(&depaddr8,f)->cons,
						getDep(&depaddr8,e)->cons,
						getDep(&depaddr8,d)->cons,
						getDep(&depaddr8,c)->cons,
						getDep(&depaddr8,b)->cons,
						getDep(&depaddr8,a)->cons,
						getDep(&depaddr8,i)->cons);
					ppDepTmp(pj);
					return;
				}
			}
#else
			//if(fengflag){}//temp debug
			// XXX - currently not supported...
#endif // FENG_AMD64
		}
		else if (size == 128) {

			//return;
		}
		else {
			//if (fengSizeHelpercFlag){VG_(printf)("oops, size = %d\n",size);}

			//Feng:size no handle error happend there
			VG_(printf)("size = %d\n", size);
			VG_(tool_panic)("helperc_load: invalid size !");
		}
	}

	// we can depend either on the temporary number or the temporary value
	// (which is an address)
	if (tmp != INVALID_TMP) {
		if (depend_of_tmp(tmp)) {
			ptmp=getDep(&deptmp,tmp);
			// we don't track pointer: just load previous stored value and input
			if (VG_(strncmp)(ptmp->cons, "input", 5) != 0
				&& VG_(strncmp)(ptmp->cons, "ST", 2) != 0) {
					VG_(printf)("[-] Losing dependency\n");
					//VG_(printf)("feng:%s\n",ptmp->cons);
			}
			else {
				if (fengAddTmp){VG_(printf)("Feng:helperc_load add tmp size=%d",ptmp->size);}

				ptmp=getDep(&deptmp,tmp);

				j = add_dependency_tmp(tmp_to, ptmp->size);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);}

				pj=getDep(&deptmp,j);

				SPRINTF_CONS(*pj, "LDle:%d(%s)", ptmp->size, ptmp->cons);
				ppDepTmp(pj);

				return;
			}
		}
	}

	del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_rdtmp(Tmp tmp, Tmp tmp_to) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc\n");}
	UInt j;

	Dep* ptmp=NULL;
	Dep* pj=NULL;

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("rdtmp returned!\n ");
		return;
	}

	if (tmp != INVALID_TMP) {
		if (depend_of_tmp(tmp)) {
			if (fengAddTmp){VG_(printf)("Feng:in helperc_rdtmp add dependency tmp\n");}

			ptmp=getDep(&deptmp,tmp);

			j = add_dependency_tmp(tmp_to, ptmp->size);
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);}

			pj=getDep(&deptmp,j);

			SPRINTF_CONS(*pj, "%s", ptmp->cons);
			ppDepTmp(pj);

			return;
		}
	}

	del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_unop(Tmp tmp, Tmp tmp_to, UInt size, UInt op) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_unop with size:%d\n",size);}
	UInt j;
	char buffer[XXX_MAX_BUF];

	Dep* ptmp=NULL;
	Dep* pj=NULL;

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("unop returned!\n ");
		return;
	}

	if (tmp != INVALID_TMP) {
		if (depend_of_tmp(tmp)) {
			if(fengTmpFlag){VG_(printf)("feng:in helperc_unop after if tmp:%d\n",tmp);}
			if (fengAddTmp){VG_(printf)("Feng:in helperc_unop add dep tmp size=%d",size);}

			ptmp=getDep(&deptmp,tmp);

			// We must use size, because some expressions change the dependency
			// size. For example: 8Uto32(a).

			j = add_dependency_tmp(tmp_to, size);
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);}

			pj=getDep(&deptmp,j);

			IROp_to_str(op, buffer);
			SPRINTF_CONS(*pj, "%s(%s)", buffer, ptmp->cons);
			ppDepTmp(pj);
			return;
		}
	}

	del_dependency_tmp(tmp_to);
}

#ifdef FENG_AMD64
static VG_REGPARM(0) void helperc_binop(Tmp tmp1, Tmp tmp2, BinopData *data, UInt tmp1_value, UInt tmp2_value) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_binop\n");}

	UInt tmp_to=data->tmp_to;
	UInt op=data->op;
	UInt end_size=data->end_size;
#else
static VG_REGPARM(0) void helperc_binop(Tmp tmp1, Tmp tmp2, Tmp tmp_to, UInt op, UInt tmp1_value, UInt tmp2_value, UInt end_size) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_binop\n");}
#endif // FENG_AMD64
	UInt j1 = 0, j2 = 0;
	Bool b1 = False, b2 = False;
	char *p=NULL;
	char buffer[XXX_MAX_BUF]={0};
	char type;
	int size=0;

	Dep* ptmp1=NULL;
	Dep* ptmp2=NULL;
	Dep* pj1=NULL;
	Dep* pj2=NULL;

	if(fengSizeHelpercFlag){VG_(printf)("feng:binop size=%lld\n",end_size);}

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("binop returned!\n ");
		return;
	}
	if(jinAssertFlag) VG_(printf)("binop not returned!\n ");
	if (tmp1 != INVALID_TMP || tmp2 != INVALID_TMP) {
		//IROp_to_str(op, buffer);
		//VG_(printf)("op=%010s\n",buffer);
		if(fengBinopFlag){
			VG_(printf)("tmp1=%d tmp2=%d tmp_to=%d op=0x%x v1=%d v2=%d end_size=%d ", tmp1,tmp2,tmp_to,op,tmp1_value,tmp2_value,end_size);
			IROp_to_str(op, buffer);
			VG_(printf)("op=%010s\n",buffer);
		}

		if (tmp1 != INVALID_TMP) {
			if (depend_of_tmp(tmp1)) {
				//VG_(printf)("add dep tmp j1=%d\n",j1);
				j1 = add_dependency_tmp(tmp_to, end_size);
				pj1=getDep(&deptmp,j1);
				b1 = True;
			}
		}

		if (tmp2 != INVALID_TMP) {
			if (depend_of_tmp(tmp2)) {
				//VG_(printf)("add dep tmp j2=%d\n",j2);
				j2 = add_dependency_tmp(tmp_to, end_size);
				pj2=getDep(&deptmp,j2);
				b2 = True;
			}
		}

		if (b1 || b2) {
			IROp_to_str(op, buffer);//CT:may return error - ok,pass
			type = 'I';
			p = &buffer[VG_(strlen)(buffer) - 1]; // CmpEQ32
			if (*p < '0' || *p > '9') {           // CmpEQ32S
				p--;
			}

			switch (op) {
			case Iop_Shl8 ... Iop_Sar64:
				size = 8;
				break;
			default:
				switch (*p) {
				case '8': size = 8;  break;
				case '6': size = 16; break;
				case '2': size = 32; break;
				case '4': size = 64; break;
				default:
					VG_(printf)("buffer = : %s\b", buffer);
					VG_(tool_panic)("helperc_binop");
				}
			}

			if (b1 && b2) {
				SPRINTF_CONS(*pj2, "%s(%s,%s)",
					buffer, getDep(&deptmp,tmp1)->cons, getDep(&deptmp,tmp2)->cons);
				ppDepTmp(pj2);
			}
			else if (b1) {
#ifdef FENG_AMD64
				tmp2_value &= (0xffffffffffffffff >> (64 - size));
#else
				tmp2_value &= (0xffffffff >> (32 - size));
#endif // FENG_AMD64

				SPRINTF_CONS(*pj1, "%s(%s,0x%x:%c%d)",
					buffer, getDep(&deptmp,tmp1)->cons, tmp2_value, type, size);
				ppDepTmp(pj1);
			}
			else if (b2) {
#ifdef FENG_AMD64
				tmp1_value &= (0xffffffffffffffff >> (64 - size));
#else
				tmp1_value &= (0xffffffff >> (32 - size));
#endif // FENG_AMD64

				SPRINTF_CONS(*pj2, "%s(0x%x:%c%d,%s)",
					buffer, tmp1_value, type, size, getDep(&deptmp,tmp2)->cons);
				ppDepTmp(pj2);
			}

#ifdef FENG_AMD64
			data->used=False;
#endif // FENG_AMD64

			return;
		}
	}

#ifdef FENG_AMD64
	data->used=False;
#endif // FENG_AMD64
	del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_mux0x(
	Tmp cond_tmp, UInt cond_value,
	Tmp expr0, Tmp exprX, Tmp tmp_to)
{
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_mux0x\n");}
	UInt j;
	Tmp t = (cond_value) ? exprX : expr0;

	Dep* ptmp=NULL;
	Dep* pj=NULL;

	// XXX
	/*
	if (depend_of_tmp(cond_tmp)) {
	VG_(printf)("[+] 0x%08x depending of input: if (8to1(%s)) => %d\n", 0x12345678, deptmp[cond_tmp].cons, cond_value);
	}
	*/

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("mux0x returned!\n ");
		return;
	}

	if (t != INVALID_TMP) {
		if (depend_of_tmp(t)) {

			if(fengSizeHelpercFlag){
				VG_(printf)("feng:in helper_mux0x ptmp->%d\n",ptmp->size);
			}

			ptmp=getDep(&deptmp,t);
			j = add_dependency_tmp(tmp_to, ptmp->size);
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);}

			pj=getDep(&deptmp,j);

			SPRINTF_CONS(*pj, "%s", ptmp->cons);
			ppDepTmp(pj);
			return;
		}
	}

	del_dependency_tmp(tmp_to);
}

static VG_REGPARM(0) void helperc_store(Addr addr, Tmp tmp) {
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_store\n");}
	UInt j;

	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;
	Dep* pi=NULL;
	Dep* pj=NULL;

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("store returned!\n ");
		return;
	}

	if (tmp != INVALID_TMP) {
		if (depend_of_tmp(tmp)) {
			ptmp=getDep(&deptmp,tmp);

			if(fengHelperEnterFlag){VG_(printf)("feng:in helper_store with ptmp->%d\n",ptmp->size);}

			// XXX - we're asserting that values don't overlap
#ifdef FENG_AMD64
			//Feng:add for 64bit
			if (ptmp->size==64){
				j = add_dependency_addr(addr, 64);
				pj=getDep(&depaddr64,j);
				SPRINTF_CONS(*pj, "STle(%s)", ptmp->cons);
				ppDepAddr(pj);

				// delete any dependency stored at this address
				//Feng: addr range may wrong
				for (j = 0; j < depaddr32.count; j++) {
					pj=getDep(&depaddr32,j);

					//addr32 +0 +1 +2 +3 +4
					if (pj->value.addr >= addr && pj->value.addr <= addr + 4) {
						del_dependency_addr(pj->value.addr, 32);
					}
				}

				for (j = 0; j < depaddr16.count; j++) {
					pj=getDep(&depaddr16,j);

					//addr16 +0 +1 +2 +3 +4 +5 +6
					if (pj->value.addr >= addr && pj->value.addr <= addr + 6) {
						del_dependency_addr(pj->value.addr, 16);
					}
				}

				for (j = 0; j < depaddr8.count; j++) {
					pj=getDep(&depaddr8,j);

					//addr8 +0 ~ +7
					if (pj->value.addr >= addr && pj->value.addr <= addr + 7) {
						del_dependency_addr(pj->value.addr, 8);
					}
				}


				return;
			}
#endif // FENG_AMD64
			if (ptmp->size == 32) {
				// XXX - we're asserting that values don't overlap
				// add dependency to the 32 bit value
				j = add_dependency_addr(addr, 32);
				pj=getDep(&depaddr32,j);
				SPRINTF_CONS(*pj, "STle(%s)", ptmp->cons);
				ppDepAddr(pj);

				// delete any dependency stored at this address
				//Feng: addr range may wrong
				for (j = 0; j < depaddr16.count; j++) {
					pj=getDep(&depaddr16,j);

					//addr16 +0 ~ +2
					if (pj->value.addr >= addr && pj->value.addr <= addr + 2) {
						del_dependency_addr(pj->value.addr, 16);
					}
				}

				for (j = 0; j < depaddr8.count; j++) {
					pj=getDep(&depaddr8,j);

					//addr8 +0 ~ +3
					if (pj->value.addr >= addr && pj->value.addr <= addr + 3) {
						del_dependency_addr(pj->value.addr, 8);
					}
				}
			}
			else if (ptmp->size == 16) {
				j = add_dependency_addr(addr, 16);
				pj=getDep(&depaddr16,j);
				SPRINTF_CONS(*pj, "STle(%s)", ptmp->cons);
				ppDepAddr(pj);

				for (j = 0; j < depaddr8.count; j++) {
					pj=getDep(&depaddr8,j);

					//addr8 +0 ~ +1
					if (pj->value.addr >= addr && pj->value.addr <= addr + 1) {
						del_dependency_addr(pj->value.addr, 8);
					}
				}
			}
			else if (ptmp->size == 8) {
				// add dependency to the 8 bit value
				j = add_dependency_addr(addr, 8);
				pj=getDep(&depaddr8,j);
				SPRINTF_CONS(*pj, "STle(%s)", ptmp->cons);
				ppDepAddr(pj);

				// if it overwrite a longer bits value like 32 or 16 bits value, just fragment them
			}
			else {
				VG_(printf)("deptmp[%d].size = %d\n", tmp, ptmp->size);
				VG_(printf)("deptmp[%d].cons = %s", tmp, ptmp->cons);
				VG_(tool_panic)("helperc_store: dependency size not handled");
			}


			return;
		}
	}

	// XXX !
	del_dependency_addr(addr, 64);
	del_dependency_addr(addr, 32);
	del_dependency_addr(addr, 16);
	del_dependency_addr(addr, 8);
}


static VG_REGPARM(0) void helperc_exit(Tmp guard, Addr addr, UInt taken){
	if(fengHelperEnterFlag){VG_(printf)("feng:entered helperc_exit\n");}

#ifdef VER_0.9

	unsigned long rbp;
	UInt linenum = 0,tid;
	Bool dirname_available;
	char filename[MAX_FILE_SIZE], dirname[MAX_FILE_SIZE];
	static char objname[MAX_FILE_SIZE];

	Bool named;

	named = VG_(get_objname)(addr, objname, MAX_FILE_SIZE);
	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("exit returned!\n ");
		return;
	}
	if (depend_of_tmp(guard))
	{

		VG_(printf)("[+] 0x%08x depending of input: if (%s) => %d\n",
			(UInt)addr, getDep(&deptmp,guard)->cons, taken);
		VG_(printf)("depending path %d\n",taken);
		if (VG_(get_filename_linenum)(addr, filename, MAX_FILE_SIZE, dirname, MAX_FILE_SIZE, &dirname_available, &linenum) == True)
			VG_(printf)("[-]path:%d depending file linenum => file-> %s || line-> %d\n",taken, filename, linenum);
		if(named)
		{
			VG_(printf)("branch is in obj %s\n",objname);
		}
		return;
	}
	else
	{
		if (VG_(get_filename_linenum)(addr, filename, MAX_FILE_SIZE, dirname, MAX_FILE_SIZE, &dirname_available, &linenum) == True)
		{
			if(VG_(strcmp)(filename,"elf-init.c") == 0)
				return;
			if(!taken)
				VG_(printf)("depending path 2\n");  //false
			else
				VG_(printf)("depending path 3\n");  //true
			VG_(printf)("[+]branch file linenum => file-> %s || line-> %d\n", filename, linenum);
		}
		return ;
	}
#else
#ifdef FENG_AMD64
	if (depend_of_tmp(guard)) {
		VG_(printf)("[+] 0x%08x depending of input: if (%s) => %d\n",
			(ULong)addr, getDep(&deptmp,guard)->cons, taken);
		return;
	}
#else
	if (depend_of_tmp(guard)) {
		VG_(printf)("[+] 0x%08x depending of input: if (%s) => %d\n",
			(UInt)addr, getDep(&deptmp,guard)->cons, taken);
		return;
	}
#endif // FENG_AMD64
#endif //VER_0.9
}

void printDepTmp(){
	int i=0;
	Dep* ptmp=NULL;
	for (i=0;i<MAX_DEP;i++)
	{
		ptmp=getDep(&deptmp,i);
		if (ptmp->cons[0]!='\x00')
		{
			VG_(printf)("tmp[%d]=%s\t",i,ptmp->cons);
		}
	}

	VG_(printf)("\n\n");
}

void printDepAddr(){
	int i=0;
	Dep* paddr=NULL;
	for (i=0;i<depaddr8.count;i++)
	{
		paddr=getDep(&depaddr8,i);
		if (paddr->cons[0]!='\x00')
		{
			VG_(printf)("addr8[%d]=%s\t",i,paddr->cons);
		}
	}

	for (i=0;i<depaddr16.count;i++)
	{
		paddr=getDep(&depaddr16,i);
		if (paddr->cons[0]!='\x00')
		{
			VG_(printf)("addr16[%d]=%s\t",i,paddr->cons);
		}
	}

	for (i=0;i<depaddr32.count;i++)
	{
		paddr=getDep(&depaddr32,i);
		if (paddr->cons[0]!='\x00')
		{
			VG_(printf)("addr32[%d]=%s\t",i,paddr->cons);
		}
	}

	for (i=0;i<depaddr64.count;i++)
	{
		paddr=getDep(&depaddr64,i);
		if (paddr->cons[0]!='\x00')
		{
			VG_(printf)("addr64[%d]=%s\t",i,paddr->cons);
		}
	}

	VG_(printf)("\n\n");
}

//Feng:ok
//static VG_REGPARM(0) void helperc_amd64g_calculate_condition(
//	Tmp tmp_to,
//	UInt cond, UInt cc_op,
//	Tmp cc_dep1, Tmp cc_dep2,
//	UInt cc_dep1_value, UInt cc_dep2_value)
static VG_REGPARM(0) void helperc_amd64g_calculate_condition(
	UInt cc_op,
	UInt cc_dep1_value, UInt cc_dep2_value,
	CalcData *data)
{

	UInt cond=data->cond;
	Tmp tmp_to=data->tmp_to;
	Tmp cc_dep1=data->cc_dep1;
	Tmp cc_dep2=data->cc_dep2;

	if(feng8664Flag){VG_(printf)("feng:entered helperc_amd64\n");}
	UInt j1 = 0, j2 = 0;
	Bool b1 = False, b2 = False;
	char type = 'I';
	int size = 64;

	Dep* pcc1=NULL,*pcc2=NULL,*pj1=NULL,*pj2=NULL;


	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("amd64 calculate returned!\n ");
		return;
	}

	if (depend_of_tmp(cc_dep1) || depend_of_tmp(cc_dep2)){
		if(feng8664Flag){VG_(printf)("feng:ready depend amd64g : cond=0x%x op=%d tmp1=%d tmp2=%d tmp1_val=%d tmp2_val=%d\n",
			cond,cc_op,cc_dep1,cc_dep2,cc_dep1_value,cc_dep2_value);}



		if (depend_of_tmp(cc_dep1)) {
			pcc1=getDep(&deptmp,cc_dep1);
			j1 = add_dependency_tmp(tmp_to, pcc1->size);
			b1 = True;

			if(feng8664Flag){VG_(printf)("feng:depend amd64g : op=%d tmp1=%d\n",cc_op,cc_dep1);}
		}




		if (depend_of_tmp(cc_dep2)) {
			pcc2=getDep(&deptmp,cc_dep2);
			j2 = add_dependency_tmp(tmp_to, pcc2->size);
			b2 = True;

			if(feng8664Flag){VG_(printf)("feng:depend amd64g : op=%d tmp2=%d\n",cc_op,cc_dep2);}
		}


		if (b1 || b2) {
			if (b1 && b2) {
				//pj1=getDep(&deptmp,j1);		
				pj2=getDep(&deptmp,j2);
				pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				SPRINTF_CONS(*pj2,
					"amd64g_calculate_condition(0x%x:I64,0x%x:I64,%s,%s)",
					cond, cc_op, pcc1->cons, pcc2->cons);
				ppDepTmp(pj2);
			}
			else if (b1) {
				pj1=getDep(&deptmp,j1);		
				//pj2=getDep(&deptmp,j2);
				pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				SPRINTF_CONS(*pj1,
					"amd64g_calculate_condition(0x%x:I64,0x%x:I64,%s,0x%x:%c%d)",
					cond, cc_op, pcc1->cons, cc_dep2_value, type, size);
				ppDepTmp(pj1);
			}
			else if (b2) {
				//pj1=getDep(&deptmp,j1);		
				pj2=getDep(&deptmp,j2);
				//pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				SPRINTF_CONS(*pj2,
					"amd64g_calculate_condition(0x%x:I64,0x%x:I64,0x%x:%c%d,%s)",
					cond, cc_op, cc_dep1_value, type, size, pcc2->cons);
				ppDepTmp(pj2);
			}


			data->used=False;
			return;
		}
	}

	//add_dirty2(helperc_rdtmp,mkIRExpr_HWord(INVALID_TMP),mkIRExpr_HWord(tmp_to));

	data->used=False;
	del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_x86g_calculate_condition(
	Tmp tmp_to,
	UInt cond, UInt cc_op,
	Tmp cc_dep1, Tmp cc_dep2,
	UInt cc_dep1_value, UInt cc_dep2_value)
{
	// static VG_REGPARM(0) void helperc_x86g_calculate_condition(
	// 	Tmp tmp_to,
	// 	Tmp cc_dep1, Tmp cc_dep2,
	//	CalcData *data)
	//{
	//	UInt cond=data->cond;
	//	UInt cc_op=data->cc_op;
	//	UInt cc_dep1_value=data->cc_dep1_value;
	//	UInt cc_dep2_value=data->cc_dep2_value;

	if(feng8664Flag){VG_(printf)("feng:entered helperc_x86\n");}
	UInt j1 = 0, j2 = 0;
	Bool b1 = False, b2 = False;
	char type = 'I';
	int size = 32;
	Dep* pcc1=NULL,*pcc2=NULL,*pj1=NULL,*pj2=NULL;
	char buffer[1024]={0};

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		return;
	}

	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("x86 calculate returned!\n ");
		return;
	}

	//printDepAddr();
	//printDepTmp();

	if (depend_of_tmp(cc_dep1) || depend_of_tmp(cc_dep2)){

		if(feng8664Flag){VG_(printf)("feng:ready depend x86g : cond=0x%x op=%d tmp1=%d tmp2=%d tmp1_val=%d tmp2_val=%d\n",
			cond,cc_op,cc_dep1,cc_dep2,cc_dep1_value,cc_dep2_value);}


		if (depend_of_tmp(cc_dep1)) {
			pcc1=getDep(&deptmp,cc_dep1);
			j1 = add_dependency_tmp(tmp_to, pcc1->size);
			b1 = True;

			if(feng8664Flag){VG_(printf)("feng:depend x86g : op=%d tmp1=%d\n",cc_op,cc_dep1);}
		}



		if (depend_of_tmp(cc_dep2)) {
			pcc2=getDep(&deptmp,cc_dep2);
			j2 = add_dependency_tmp(tmp_to, pcc2->size);
			b2 = True;

			if(feng8664Flag){VG_(printf)("feng:depend x86g : op=%d tmp2=%d\n",cc_op,cc_dep2);}
		}



		if (b1 || b2) {
			if (b1 && b2) {
				//pj1=getDep(&deptmp,j1);		
				pj2=getDep(&deptmp,j2);
				pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				SPRINTF_CONS(*pj2,
					"x86g_calculate_condition(0x%x:I32,0x%x:I32,%s,%s)",
					cond, cc_op, pcc1->cons, pcc2->cons);
				ppDepTmp(pj2);
			}
			else if (b1) {
				pj1=getDep(&deptmp,j1);		
				//pj2=getDep(&deptmp,j2);
				pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				SPRINTF_CONS(*pj1,
					"x86g_calculate_condition(0x%x:I32,0x%x:I32,%s,0x%x:%c%d)",
					cond, cc_op, pcc1->cons, cc_dep2_value, type, size);
				ppDepTmp(pj1);
			}
			else if (b2) {
				//pj1=getDep(&deptmp,j1);		
				pj2=getDep(&deptmp,j2);
				//pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				SPRINTF_CONS(*pj2,
					"x86g_calculate_condition(0x%x:I32,0x%x:I32,0x%x:%c%d,%s)",
					cond, cc_op, cc_dep1_value, type, size, pcc2->cons);
				ppDepTmp(pj2);
			}

			return;
		}
	}

	//add_dirty2(helperc_rdtmp,mkIRExpr_HWord(INVALID_TMP),mkIRExpr_HWord(tmp_to));
	del_dependency_tmp(tmp_to);
}


//Luo added for symbolize
static VG_REGPARM(0) void helperc_catch(UInt addr)

{


	int i,j,k;
	int size;
	Dep* pdepaddr=NULL;
	Bool Symbol_ready = False;
	UInt tid;
	ULong param1;
	ULong param2;
	int *addr_param1=NULL;
	int *addr_param2=NULL;
	int *ebp = NULL;

	int fd;
	int fd1;
	SysRes res;
	SysRes res1;
	char *tempch;

	tid= VG_(get_running_tid)();

#if defined(VGA_x86)
	populate_guest_args(tid);
	param1= guest_args[tid].args[3];
	ebp=(int*)param1;
	addr_param1=(int*)(param1+8);
	addr_param2=(int*)(param1+12);
	if(flag==0)
	{
		addrp=ebp;
		flag=1;
	}
	else if(flag==1)
	{
		if(addrp!=ebp)
		{
			flag=2;
			size=*addr_param2;
			for(i=0;i<size;i++)
			{
				for(k=0;k<depaddr8.count;k++)
				{
					pdepaddr=getDep(&depaddr8,k);
					if((*addr_param1)+i==pdepaddr->value.addr) Symbol_ready=True;
				}
				if(Symbol_ready==False) for(k=0;k<depaddr16.count;k++)
				{
					pdepaddr=getDep(&depaddr16,k);
					if((*addr_param1)+i==pdepaddr->value.addr) Symbol_ready=True;
				}
				if(Symbol_ready==False) for(k=0;k<depaddr32.count;k++)
				{
					pdepaddr=getDep(&depaddr32,k);
					if((*addr_param1)+i==pdepaddr->value.addr) Symbol_ready=True;
				}

				if(Symbol_ready == False)
				{
					tempch=(char*)((*addr_param1)+i);
					if(run_times != '1') res=VG_(open)(fn_buf,VKI_O_WRONLY,0);
					if(!sr_isError(res))
					{
						fd = sr_Res(res);
						VG_(lseek)(fd,count,SEEK_SET);
						VG_(write)(fd,tempch,1);
						VG_(close)(fd);
					}
					if(run_times == '1') *tempch=buf[count];
					j=add_dependency_addr((Addr)((*addr_param1)+i), 8);
					VG_(snprintf)(getDep(&depaddr8,j)->cons, XXX_MAX_BUF, "input(%d)",j);
					count=j+1;
				}
			}
		}
	}
	else if(flag==2)
	{
		flag=0;
	}


#elif defined(VGA_amd64)
	populate_guest_args(tid);
	param1 = guest_args[tid].args[1];
	param2 = guest_args[tid].args[2];
	for(i=0;i<param2;i++)
	{
		for(k=0;k<depaddr8.count;k++)
		{
			pdepaddr=getDep(&depaddr8,k);
			if(param1+i==pdepaddr->value.addr) Symbol_ready=True;
		}
		if(Symbol_ready==False) for(k=0;k<depaddr16.count;k++)
		{
			pdepaddr=getDep(&depaddr16,k);
			if(param1+i==pdepaddr->value.addr) Symbol_ready=True;
		}
		if(Symbol_ready==False) for(k=0;k<depaddr32.count;k++)
		{
			pdepaddr=getDep(&depaddr32,k);
			if(param1+i==pdepaddr->value.addr) Symbol_ready=True;

		}
		if(Symbol_ready==False) for(k=0;k<depaddr64.count;k++)
		{
			pdepaddr=getDep(&depaddr64,k);
			if(param1+i==pdepaddr->value.addr) Symbol_ready=True;
		}

		if(Symbol_ready == False)
		{
			tempch=(char*)(param1+i);
			if(run_times != '1') res=VG_(open)(fn_buf,VKI_O_WRONLY,0);
			if(!sr_isError(res))
			{
				fd = sr_Res(res);
				VG_(lseek)(fd,count,SEEK_SET);
				VG_(write)(fd,tempch,1);
				VG_(close)(fd);
			}
			if(run_times == '1') *tempch=buf[count];
			j=add_dependency_addr((ULong)(param1+i), 8);
			VG_(snprintf)(getDep(&depaddr8,j)->cons, XXX_MAX_BUF, "input(%d)",j);
			count=j+1;
		}
	}
#endif
	return;
}

//Jin add a function ,determin wherther a helperc_func need to be executed or not!

/*
static Bool is_in_function()
{
//return False;
unsigned long rbp;
UInt tid;

tid= VG_(get_running_tid)();
populate_guest_args(tid);
rbp=(unsigned long )(guest_args[tid].args[3]);
if(jinAssertFlag)VG_(printf)("need or not : current rbp is %08x \n",rbp);
if(jinAssertFlag)VG_(printf)("              current func_ebp is %08x\n",func_ebp);
//if(is_in_func) VG_(printf)("is_in_func is true!\n");
//if(just_module_sym) VG_(printf)("just module sym true!\n");
if(is_in_func)
{
if(rbp <= func_ebp)  // not in the current function
{
//VG_(printf)("return True!\n");
return True;
}
if(rbp > func_ebp)
{
//VG_(printf)("out of function\n");
is_in_func  = False;
return False;
}
VG_(printf)("why here?\n");
}


return False;
}
*/

//Jin add a function ,determin whether an instruction is in the objects we are willing to symbolic execution

static Bool is_in_obj_lists(Addr addr)
{
	static char objname[MAX_FILE_SIZE];
	Char *tmp,*name;
	Bool named,in_obj_lists;
	UInt i = 0;
	named = VG_(get_objname)(addr, objname, MAX_FILE_SIZE);
	if(named)
	{
		tmp = VG_(strtok)(objname,"/");
		while(tmp != NULL)
		{
			tmp = VG_(strtok)(NULL,"/");
			if(tmp != NULL)
				name = tmp;
		}
		for(i=0;i<obj_num;i++)
		{
			if(jinAssertObjFlag) VG_(printf)("obj name is %s\n compare with %s\n",name,object_lists[i]);
			if(jinAssertObjFlag) VG_(printf)("obj_num is %d\n",obj_num);
			in_obj_lists = VG_(strcmp)(object_lists[i],name)==0;
			if(in_obj_lists)
			{
				if(jinAssertObjFlag) VG_(printf)("obj is in %s\n",object_lists[i]);
				return True;
			}
		}
	}
	return False;
}


static VG_REGPARM(0) void helperc_get_ret(UInt addr,const char *fname)
{
	if(ret_addr != 0)
		return;

	int tid;
	UInt nips;
	Addr ips[VG_(clo_backtrace_size)];
	Addr sps[VG_(clo_backtrace_size)];
	Addr fps[VG_(clo_backtrace_size)];
	unsigned long rbp;
	unsigned long *re;
	Bool named = False,is_begain = False;
	char fnname[MAX_FILE_SIZE];

	/*
	nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);

	named = VG_(get_fnname)(addr, fnname, MAX_FILE_SIZE);
	if(named)
	VG_(printf)("\n@@ Inst is in func %s\n",fnname);
	*/
	is_begain = VG_(get_fnname_if_entry)(addr,fnname,MAX_FILE_SIZE);
	if(is_begain)
	{
		if(jinAssertFlag)VG_(printf)("func %s\n\n",fnname);

		if(VG_(strcmp)(fnname,fname) == 0)
		{
			nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);
			VG_(printf)("ips is %x fps is %x sps is %x\n",ips[0],fps[0],sps[0]);
			re = (void*)(sps[0]);
			ret_addr = *re;
			is_in_func = True;
			VG_(printf)("sp content is %x\n",*re);
			/*           
			tid= VG_(get_running_tid)();
			populate_guest_args(tid);
			rbp=(unsigned long )(guest_args[tid].args[3]);
			main_ebp = rbp;
			VG_(printf)("SP  is %x\n",(unsigned long )(guest_args[tid].args[4])); 
			VG_(printf)("before push ebp; func %s caller rbp is: %08x current addr is %08x\n",fnname,rbp,addr);
			*/
		}
	}

}
/*
static VG_REGPARM(0) void helperc_get_func_rbp(UInt addr)
{
int tid;
unsigned long rbp;
unsigned long *ret,*ret2;
if(main_ebp == 0)
return ;
if(func_ebp == 0)
{
tid= VG_(get_running_tid)();
populate_guest_args(tid);
rbp=(unsigned long )(guest_args[tid].args[3]);
if(rbp == main_ebp)
return;
else
{
func_ebp = rbp;
ret_addr = (void*)(func_ebp+8);
VG_(printf)("return addr is %08x\n",*ret);
is_in_func = True;
}

ret = (void*)(func_ebp+8);
//ret2 = (void*)(func_ebp+16);
VG_(printf)("func ebp: %08x   main ebp: %08x\n \n",func_ebp,main_ebp);
//ret_addr = (Addr)(*ret);
//VG_(printf)("return addr is %08x\n",*ret2);
}
}

*/

static VG_REGPARM(0) void helperc_imark(UInt addr)
{
	if(ret_addr == 0)
		return;
	if(is_in_func && addr == ret_addr)
	{
		is_in_func = False;
		VG_(printf)("not in func ever!  addr is %08x\n",addr);
	}
}

static VG_REGPARM(0) void helperc_in_objs(UInt addr)
{
	is_in_obj = is_in_obj_lists(addr);
}

/*
static VG_REGPARM(0) void helperc_rbp(UInt addr)
{
int tid;
unsigned long rbp;
unsigned long dflag;
UInt nips;
Addr ips[VG_(clo_backtrace_size)];
Addr sps[VG_(clo_backtrace_size)];
Addr fps[VG_(clo_backtrace_size)];

tid= VG_(get_running_tid)();
populate_guest_args(tid);
rbp=(unsigned long )(guest_args[tid].args[3]);
dflag = (unsigned long )(guest_args[tid].args[4]);
if(is_in_func)
{
if(rbp == main_ebp)
is_in_func = False;
}

if(is_in_obj_lists(addr))
is_in_obj = True;
else
is_in_obj = False;

nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);

VG_(printf)("ips is %x\nfps is %x\nsps is %x\n",ips[0],fps[0],sps[0]);

VG_(printf)("\ncurrent addr : %p  \n",addr);
VG_(printf)("current_dirty rbp : %08x\n",rbp);
VG_(printf)("current main_ebp is %08x\n",main_ebp);
VG_(printf)("current func_ebp is %08x\n",func_ebp);

//rbp=(unsigned long *)(guest_args[tid].args[8]);


}

*/

//Feng:change site
//Feng:warning, fuzz will crash here because of the differ between 32 and 64
//Feng:crashed here now we know
IRSB* fz_instrument ( VgCallbackClosure* closure,
					 IRSB* bb_in,
					 VexGuestLayout* layout,
					 VexGuestExtents* vge,
					 IRType gWordTy, IRType hWordTy )
{
	if(fengHelperEnterFlag){VG_(printf)("feng:entered fz_instrument\n");}

	Addr current_addr = 0,inst_addr = 0;
	IRSB*   bb=NULL;
	Int     i=0, j=0;
	Bool is_first_Imark = True;
	Bool named = False;

	char fnname[MAX_FILE_SIZE];



	//Feng：数据word不匹配处理，暂时未支持
	if (gWordTy != hWordTy) {
		/* We don't currently support this case. */
		VG_(tool_panic)("host/guest word size mismatch");
	}
	//VG_(printf)("feng:fz_instrument word match\n");


	//Feng:初始化bb
	/* Set up SB */
	bb = deepCopyIRSBExceptStmts(bb_in);
	//VG_(printf)("feng:fz_instrument bb init\n");

	//Feng:逐个复制 第一个imark前 的 ir 前置同步码
	// Copy verbatim any IR preamble preceding the first IMark
	i = 0;
	while (i < bb_in->stmts_used && bb_in->stmts[i]->tag != Ist_IMark) {
		addStmtToIRSB(bb, bb_in->stmts[i]);
		i++;
	}
	//VG_(printf)("feng:fz_instrument IR preamble\n");

	//Feng:迭代解析剩余stmts 并生成指令
	// Iterate over the remaining stmts to generate instrumentation.
	tl_assert(bb_in->stmts_used > 0);
	tl_assert(i >= 0);
	tl_assert(i < bb_in->stmts_used);
	tl_assert(bb_in->stmts[i]->tag == Ist_IMark);

	//if(fengflag){VG_(printf)("feng:fz_instrument begin iterate stmts\n");}
	//Feng:i 的游标值续接，不重新定义：前部分的使用为?
	//Feng:可以确定问题出现在了这一个循环中，其中部分代码存在未对64经过实现或者测试的功能，导致崩溃
	for (/*use current i*/; i < bb_in->stmts_used; i++) {
		IRStmt* st = bb_in->stmts[i];
		IRExpr *addr, *data, **args, *arg, *e1, *e2;
		IRTemp to = 0; /* gcc warning */
		IRDirty *di;
		UInt size = 0;//Feng Jin:uint is not good for 64, we change it to uword

		if (!st || st->tag == Ist_NoOp) {
			continue;
		}

		//module symbolic and not the first Imark and the first Imark is not in the function,just add the bb into the SB

		if(st->tag == Ist_IMark && just_module_sym)
		{
			inst_addr = st->Ist.IMark.addr;
			//VG_(printf)("first Imark, addr is %08x\n",inst_addr);
			add_dirty2(helperc_get_ret,mkIRExpr_HWord(inst_addr),mkIRExpr_HWord(FZ_(module_name)));
			add_dirty1(helperc_in_objs,mkIRExpr_HWord(inst_addr));
			//is_in_obj = is_in_obj_lists(inst_addr);
		}

		if (FZ_(verbose)) {
			VG_(printf)("-> ");
			ppIRStmt(st);
			VG_(printf)("\n");
		}

		if(True)
		{
			//VG_(printf)("instrumented\n");
			switch (st->tag) {
				//Feng:crashed here now we know
				//Feng:imark标记
			case Ist_IMark:
				if(fengSwitchFlag){VG_(printf)("feng:switch imark\n");}
				//判断是否退出函数
				current_addr = st->Ist.IMark.addr;
				add_dirty1(helperc_imark,mkIRExpr_HWord(current_addr));

				named = VG_(get_fnname)(current_addr, fnname, MAX_FILE_SIZE);
				if((VG_(strcmp)(fnname,"Symbolize_LLL")==0 ) && (named == True))
				{
					add_dirty1(helperc_catch,mkIRExpr_HWord(current_addr));
					VG_(printf)("\n++++++++++++++Symbolize has found~\n");
				}
				//VG_(printf)("instrumented\n");
				break;

				//Feng:put传递参数
			case Ist_Put:
				if(fengSwitchFlag){VG_(printf)("feng:switch put\n");}
				tl_assert(isIRAtom(st->Ist.Put.data));
				if (st->Ist.Put.data->tag == Iex_RdTmp) {
					add_dirty2(helperc_put,
						mkIRExpr_HWord(st->Ist.Put.data->Iex.RdTmp.tmp),
						mkIRExpr_HWord(st->Ist.Put.offset));
				}
				else {
					add_dirty2(helperc_put,
						mkIRExpr_HWord(INVALID_TMP),
						mkIRExpr_HWord(st->Ist.Put.offset));
				}
				break;

				//Feng:写临时
			case Ist_WrTmp:
				//if (fengSwitchDebug){break;}
				//Feng:crashed here now we know
				if(fengSwitchFlag){VG_(printf)("feng:switch wrtmp\n");}
				switch (st->Ist.WrTmp.data->tag) {
					//Feng:常量
				case Iex_Const:
					if(fengSwitchFlag){VG_(printf)("feng:switch switch const\n");}
					to = st->Ist.WrTmp.tmp;
					add_dirty2(helperc_rdtmp,
						mkIRExpr_HWord(INVALID_TMP),
						mkIRExpr_HWord(to));
					break;

					//Feng:读临时
				case Iex_RdTmp:
					//if(fengSwitchFlag){VG_(printf)("feng:switch switch rdtmp\n");}
					to = st->Ist.WrTmp.tmp;
					add_dirty2(helperc_rdtmp,
						mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.RdTmp.tmp),
						mkIRExpr_HWord(to));
					break;

					//Feng:扩展加载
				case Iex_Load:
					//Feng:error happened here
					//if(fengSwitchFlag){VG_(printf)("feng:switch switch load\n");}
					addr = st->Ist.WrTmp.data->Iex.Load.addr;
					to = st->Ist.WrTmp.tmp;

					tl_assert(isIRAtom(addr));

					j = st->Ist.WrTmp.data->Iex.Load.ty;
					size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
					//VG_(printf)("feng:load size:%d\n",size);

#ifdef FENG_AMD64
					if (addr->tag == Iex_Const) {
						add_dirty4(helperc_load,
							mkIRExpr_HWord(addr->Iex.Const.con->Ico.U64),
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(to),
							mkIRExpr_HWord(size));
					}
					else if (addr->tag == Iex_RdTmp) {
						add_dirty4(helperc_load,
							addr,
							mkIRExpr_HWord(addr->Iex.RdTmp.tmp),
							mkIRExpr_HWord(to),
							mkIRExpr_HWord(size));
					}
#else
					if (addr->tag == Iex_Const) {
						add_dirty4(helperc_load,
							mkIRExpr_HWord(addr->Iex.Const.con->Ico.U32),
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(to),
							mkIRExpr_HWord(size));
					}
					else if (addr->tag == Iex_RdTmp) {
						add_dirty4(helperc_load,
							addr,
							mkIRExpr_HWord(addr->Iex.RdTmp.tmp),
							mkIRExpr_HWord(to),
							mkIRExpr_HWord(size));
					}
#endif // FENG_AMD64
					break;

					//Feng:获取
				case Iex_Get:
					if(fengSwitchFlag){VG_(printf)("feng:switch switch get\n");}
					j = st->Ist.WrTmp.data->Iex.Get.ty;
					size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
					add_dirty3(helperc_get,
						mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Get.offset),
						mkIRExpr_HWord(st->Ist.WrTmp.tmp),
						mkIRExpr_HWord(size));
					break;

					//Feng:单元素操作
				case Iex_Unop:
					if(fengSwitchFlag){VG_(printf)("feng:switch switch unop\n");}
					arg = st->Ist.WrTmp.data->Iex.Unop.arg;
					to = st->Ist.WrTmp.tmp;

					tl_assert(isIRAtom(arg));

					if (arg->tag == Iex_RdTmp) {
						size = (bb->tyenv->types[to] != Ity_I1) ? sizeofIRType(bb->tyenv->types[to]) * 8 : 1;
						add_dirty4(helperc_unop,
							mkIRExpr_HWord(arg->Iex.RdTmp.tmp),
							mkIRExpr_HWord(to),
							mkIRExpr_HWord(size),
							mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Unop.op));
					}
					else {
						add_dirty4(helperc_unop,
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(to),
							mkIRExpr_HWord(size),
							mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Unop.op));

					}
					break;

					//Feng:双元素操作
				case Iex_Binop:
					//break;//Feng:truncation code
					//Feng:crashed here now we know
					if(fengSwitchFlag){VG_(printf)("feng:switch switch binop\n");}
					j = 0;
					switch (st->Ist.WrTmp.data->Iex.Binop.op) {
					case Iop_AddF64 ... Iop_CalcFPRF:
						j = 1;
						break;
					default:
						break;
					}

					e1 = st->Ist.WrTmp.data->Iex.Binop.arg1;
					e2 = st->Ist.WrTmp.data->Iex.Binop.arg2;

					//Feng:assert may crash
					tl_assert(isIRAtom(e1));
					tl_assert(isIRAtom(e2));

					size = (bb->tyenv->types[st->Ist.WrTmp.tmp] != Ity_I1) ? sizeofIRType(bb->tyenv->types[st->Ist.WrTmp.tmp]) * 8 : 1;

					if(fengSizeHelpercFlag){VG_(printf)("feng:binop size=%d\n",size);}
					if (size==1 || size==8 || size==16 || size==32 ||size==64 || size==128){
						//Feng:size 必须符合规定
					}else{
						VG_(printf)("Feng:will be used size=%d\n", size);
						VG_(tool_panic)("Feng:no handled size\n");
					}

					//Feng: 选取临时数据空间
					BinopData *data=NULL;
					data=&binopData[binopDataSite];
					while (data->used)
					{
						binopDataSite=(binopDataSite+1)%MAX_DATA_BUF_LEN;
						data=&binopData[binopDataSite];
					}
					data->used=True;
					binopDataSite=(binopDataSite+1)%MAX_DATA_BUF_LEN;


					// this is a floating point operation, we don't care about it
					// remove the dependency to the destination register
					if (j == 1) {
						if(fengDirtyFlag){VG_(printf)("feng:64 binop if adddir5 with argv5=data=0x%x and size=%d\n",data,data->end_size);}
#ifdef FENG_AMD64
						data->tmp_to=st->Ist.WrTmp.tmp;
						data->op=0;
						data->end_size=0;
						data->used=True;

						add_dirty5(helperc_binop,
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(data),
							mkIRExpr_HWord(0),
							mkIRExpr_HWord(0));
#else
						add_dirty7(helperc_binop,
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(st->Ist.WrTmp.tmp),
							mkIRExpr_HWord(0),
							mkIRExpr_HWord(0),
							mkIRExpr_HWord(0),
							mkIRExpr_HWord(0));
#endif // FENG_AMD64

						break;
					}

					//Feng:crashed here now we know
					if(fengSwitchFlag){VG_(printf)("feng:binop adddir7\n");}
					if(fengDirtyFlag){VG_(printf)("feng:64 binop if adddir5 with argv5=data=0x%x and size=%d\n",data,data->end_size);}
					//VG_(printf)("feng:64 binop if adddir5 with argv5=data=0x%x and size=%d\n",data,data->end_size);
#ifdef FENG_AMD64
					data->tmp_to=st->Ist.WrTmp.tmp;
					data->op=st->Ist.WrTmp.data->Iex.Binop.op;
					data->end_size=size;
					data->used=True;

					if(fengDirtyFlag){VG_(printf)("feng:64 binop if adddir5 with argv5=size=%d\n",size);}
					add_dirty5(helperc_binop,
						mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord(data),
						(e1->tag == Iex_RdTmp) ? assignNew(bb, e1) : mkIRExpr_HWord(e1->Iex.Const.con->Ico.U64),
						(e2->tag == Iex_RdTmp) ? assignNew(bb, e2) : mkIRExpr_HWord(e2->Iex.Const.con->Ico.U64));
#else
					if(fengDirtyFlag){VG_(printf)("feng:32 binop if adddir7 with argv7=size=%d\n",size);}
					add_dirty7(helperc_binop,
						mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord(st->Ist.WrTmp.tmp),
						mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Binop.op),
						(e1->tag == Iex_RdTmp) ? assignNew(bb, e1) : mkIRExpr_HWord(e1->Iex.Const.con->Ico.U32),
						(e2->tag == Iex_RdTmp) ? assignNew(bb, e2) : mkIRExpr_HWord(e2->Iex.Const.con->Ico.U32),
						mkIRExpr_HWord(size));
#endif // FENG_AMD64
					break;

					//Feng:多元操作
				case Iex_Mux0X:
					if(fengSwitchFlag){VG_(printf)("feng:switch switch muxox\n");}
					e1 = st->Ist.WrTmp.data->Iex.Mux0X.expr0;
					e2 = st->Ist.WrTmp.data->Iex.Mux0X.exprX;

					tl_assert(st->Ist.WrTmp.data->Iex.Mux0X.cond->tag == Iex_RdTmp);
					tl_assert(isIRAtom(e1));
					tl_assert(isIRAtom(e2));

					add_dirty5(helperc_mux0x,
						mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Mux0X.cond->Iex.RdTmp.tmp),
						assignNew(bb, st->Ist.WrTmp.data->Iex.Mux0X.cond),
						mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord(st->Ist.WrTmp.tmp));

					break;

					//Feng:三元素操作
				case Iex_Triop: // only used by floating point operations
					if(fengSwitchFlag){VG_(printf)("feng:switch switch triop\n");}
					break;

					//Feng:
				case Iex_GetI:  // only used by floating point operations
					if(fengSwitchFlag){VG_(printf)("feng:switch switch geti\n");}
					break;

					//Feng:call函数
					//Feng:why we need helper amd64 and helper x86 calculate condition
				case Iex_CCall:
					// XXX - x86g_calculate_condition
					// look at guest_x86_spechelper
					// encounterd when IR optimization failed
					//Feng:优化失败时会触发这一部分代码
					if(fengSwitchFlag){VG_(printf)("feng:switch switch ccall\n");}
					if(feng8664Flag)VG_(printf)("feng:ccall name=%s\n",st->Ist.WrTmp.data->Iex.CCall.cee->name);

#ifdef FENG_AMD64		
					if (VG_(strcmp)(st->Ist.WrTmp.data->Iex.CCall.cee->name, "amd64g_calculate_condition") == 0) {
						args = st->Ist.WrTmp.data->Iex.CCall.args;
						tl_assert(args[0]->tag == Iex_Const && args[0]->Iex.Const.con->tag == Ico_U64);
						//tl_assert(args[1]->tag == Iex_RdTmp);
						/*if (args[1]->tag == Iex_RdTmp) {
						tl_assert(args[2]->tag == Iex_RdTmp);
						tl_assert(args[3]->tag == Iex_RdTmp);
						tl_assert(args[4]->tag == Iex_RdTmp);*/

						CalcData *data=&calcData[calcDataSite];
						while (data->used){
							calcDataSite=(calcDataSite+1)%MAX_DATA_BUF_LEN;
							data=&calcData[calcDataSite];
						}
						data->used=True;						
						calcDataSite=(calcDataSite+1)%MAX_DATA_BUF_LEN;					
						data->cond=args[0]->Iex.Const.con->Ico.U64;
						data->tmp_to=st->Ist.WrTmp.tmp;
						data->cc_dep1=args[2]->Iex.RdTmp.tmp;
						data->cc_dep2=args[3]->Iex.RdTmp.tmp;

						add_dirty4(helperc_amd64g_calculate_condition,
							args[1],				//cc_op
							args[2],          // cc_dep1 value
							args[3],          // cc_dep2 value
							mkIRExpr_HWord(data));
						//add_dirty7(helperc_x86g_calculate_condition,
						//	mkIRExpr_HWord(st->Ist.WrTmp.tmp),               // to
						//	mkIRExpr_HWord(args[0]->Iex.Const.con->Ico.U32), // cond
						//	args[1],                                         // cc_op
						//	mkIRExpr_HWord(args[2]->Iex.RdTmp.tmp),          // cc_dep1
						//	mkIRExpr_HWord(args[3]->Iex.RdTmp.tmp),          // cc_dep2
						//	args[2],                                         // cc_dep1
						//	args[3]);                                        // cc_dep2

						//}else {
						//	//VG_(printf)("oops, we depend of amd64_calculate_condition: %d, %d\n", args[0]->Iex.Const.con->Ico.U32, args[1]->Iex.Const.con->Ico.U32);
						//	//VG_(tool_panic)("");
						//	// just remove the dependency
						//	add_dirty2(helperc_rdtmp,
						//		mkIRExpr_HWord(INVALID_TMP),
						//		mkIRExpr_HWord(st->Ist.WrTmp.tmp));
						//}
					}
#else
					if (VG_(strcmp)(st->Ist.WrTmp.data->Iex.CCall.cee->name, "x86g_calculate_condition") == 0) {
						args = st->Ist.WrTmp.data->Iex.CCall.args;

						tl_assert(args[0]->tag == Iex_Const && args[0]->Iex.Const.con->tag == Ico_U32);
						//tl_assert(args[1]->tag == Iex_RdTmp);
						// 					if (args[1]->tag == Iex_RdTmp) {
						// 						tl_assert(args[2]->tag == Iex_RdTmp);
						// 						tl_assert(args[3]->tag == Iex_RdTmp);
						// 						tl_assert(args[4]->tag == Iex_RdTmp);

						if(feng8664Flag){VG_(printf)("feng:call helperc_x86g_calculate_condition\n");}
						add_dirty7(helperc_x86g_calculate_condition,
							mkIRExpr_HWord(st->Ist.WrTmp.tmp),               // to
							mkIRExpr_HWord(args[0]->Iex.Const.con->Ico.U32), // cond
							args[1],                                         // cc_op
							mkIRExpr_HWord(args[2]->Iex.RdTmp.tmp),          // cc_dep1
							mkIRExpr_HWord(args[3]->Iex.RdTmp.tmp),          // cc_dep2
							args[2],                                         // cc_dep1
							args[3]);                                        // cc_dep2
						//}else {
						//	//VG_(printf)("oops, we depend of x86g_calculate_condition: %d, %d\n", args[0]->Iex.Const.con->Ico.U32, args[1]->Iex.Const.con->Ico.U32);
						//	//VG_(tool_panic)("");
						//	// just remove the dependency
						//	add_dirty2(helperc_rdtmp,
						//		mkIRExpr_HWord(INVALID_TMP),
						//		mkIRExpr_HWord(st->Ist.WrTmp.tmp));
						//}
					}
#endif // FENG_AMD64
					else{
						// just remove the dependency
						add_dirty2(helperc_rdtmp,
							mkIRExpr_HWord(INVALID_TMP),
							mkIRExpr_HWord(st->Ist.WrTmp.tmp));
					}
					break;

					//case Iex_Binder:
					//    break;

					//case Iex_Qop:
					//    break;

				default:
					if(fengSwitchFlag){VG_(printf)("feng:switch switch others\n");}
					ppIRStmt(st);
					VG_(tool_panic)("Ist_WrTmp: data->tag not handled");
					break;
				}
				break;

				//Feng:数据存储
			case Ist_Store:
				if(fengSwitchFlag){VG_(printf)("feng:switch store\n");}
				data = st->Ist.Store.data;
				tl_assert(isIRAtom(data));
				tl_assert(isIRAtom(st->Ist.Store.addr));

				if (data->tag == Iex_RdTmp) {
					j = bb->tyenv->types[data->Iex.RdTmp.tmp];
					size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
				}
				else { // data->tag == Iex_Const
					j = typeOfIRConst(data->Iex.Const.con);
					size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
				}

#ifdef FENG_AMD64
				add_dirty2(helperc_store,
					(st->Ist.Store.addr->tag == Iex_Const) ? mkIRExpr_HWord(st->Ist.Store.addr->Iex.Const.con->Ico.U64) : st->Ist.Store.addr,
					mkIRExpr_HWord((data->tag == Iex_RdTmp) ? data->Iex.RdTmp.tmp : INVALID_TMP));
				break;
#else
				add_dirty2(helperc_store,
					(st->Ist.Store.addr->tag == Iex_Const) ? mkIRExpr_HWord(st->Ist.Store.addr->Iex.Const.con->Ico.U32) : st->Ist.Store.addr,
					mkIRExpr_HWord((data->tag == Iex_RdTmp) ? data->Iex.RdTmp.tmp : INVALID_TMP));
				break;
#endif // FENG_AMD64

				//Feng:退出
			case Ist_Exit:
				if(fengSwitchFlag){VG_(printf)("feng:switch exit\n");}
				tl_assert(st->Ist.Exit.guard->tag == Iex_RdTmp);
				add_dirty3(helperc_exit,
					mkIRExpr_HWord(st->Ist.Exit.guard->Iex.RdTmp.tmp),
					mkIRExpr_HWord(current_addr),
					assignNew(bb, st->Ist.Exit.guard));
				break;

			case Ist_PutI:
				if(fengSwitchFlag){VG_(printf)("feng:switch puti\n");}
				//VG_(printf)("oops, tag Ist_PutI not handled at 0x%08x\n", current_addr);
				break;
			case Ist_NoOp:
			case Ist_AbiHint:
			case Ist_MBE:
			case Ist_Dirty:
			default:
				if(fengSwitchFlag){VG_(printf)("feng:switch others\n");}
				break;
			}
		}

		/* must be after the switch, otherwise Ist_Exit can jump causing helper
		not to be called */
		//Feng:code强制置于switch后，防止Ist_Exit跳转导致helper无法调用？目前没看出来强制跳转在哪儿。
		addStmtToIRSB(bb, st);
	}
	//if(fengflag){VG_(printf)("feng:fz_instrument end iterate stmts\n");}

	if(fengflag){VG_(printf)("feng:return fz_instrument\n");}
	//return bb_in;//Feng:add,truncation code
	return bb;//Feng:crashed here now we know

}
