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
*
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
#include "pub_tool_basics.h"
#include "pub_tool_vki.h"
#include "pub_tool_vkiscnums.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcsetjmp.h"
#include "pub_tool_machine.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_aspacemgr.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_vkiscnums.h"

#include "valgrind.h"

/* Pulled in to get the threadstate */
#include "../coregrind/pub_core_basics.h"
#include "../coregrind/pub_core_vki.h"
#include "../coregrind/pub_core_vkiscnums.h"
#include "../coregrind/pub_core_threadstate.h"
#include "fz.h"

Bool fengSysFlag=False;//debug info in fz_syswrap.c
Bool fengDepExtFlag=False;

extern Bool fengAssertFlag;

//#define VGA_amd64
#if defined(VGA_amd64)
#define FENG_AMD64
#define TEST_FENG_AMD64
#endif // defined(VGA_amd64)

#if defined(VGA_x86)
#  define GP_COUNT 8
#elif defined(VGA_amd64)
#  define GP_COUNT 16
#elif defined(VGA_ppc32) || defined(VGA_ppc64)
#  define GP_COUNT 34
#else
#  error Unknown arch
#endif

typedef struct {
	UWord args[GP_COUNT];
	UInt used;
} GuestArgs;

// VG_(N_THREADS) - do threads actually run concurrently here too?
static GuestArgs guest_args[VG_N_THREADS];

// Set up GuestArgs prior to arg_collector
//static void populate_guest_args(ThreadId tid) {
//  /* This is legacy.  I was using apply_GPs callback,
//   * but it isn't threadsafe.  So for now, we bind to 
//   * the ThreadState functions for the specific x86 arch
//   */
//    ThreadState *ts =  VG_(get_ThreadState) (tid);
//    guest_args[tid].args[1] = ts->arch.vex.guest_ECX;
//    guest_args[tid].args[2] = ts->arch.vex.guest_EDX;
//    guest_args[tid].args[3] = ts->arch.vex.guest_EBX;
//    guest_args[tid].args[4] = ts->arch.vex.guest_ESI;
//    guest_args[tid].args[5] = ts->arch.vex.guest_EDI;
//    guest_args[tid].args[6] = ts->arch.vex.guest_EBP;
//    guest_args[tid].args[7] = ts->arch.vex.guest_EAX;
//    guest_args[tid].used = 8;
//}
#define MAX_PATH    256
static void resolve_fd(Int fd, Char *path, Int max) {
	//VG_(printf)("feng:entered resolve_fd\n");
	Char src[MAX_PATH]; // be lazy and use their max
	Int len = 0;
	// TODO: Cache resolved fds by also catching open()s and close()s
	VG_(sprintf)(src, "/proc/%d/fd/%d", VG_(getpid)(), fd);
	len = VG_(readlink)(src, path, max);
	// Just give emptiness on error.
	if (len == -1) {
		len = 0;
	}
	path[len] = '\0';
}
// TODO: copy linked list setup for allocated_fds in clo_track_fds.
//       or see if they will patch it to allow tools to access it.
/* enforce an arbitrary maximum */
#define MAXIMUM_FDS 256
static Bool tainted_fds[VG_N_THREADS][MAXIMUM_FDS];
static UInt position_fds[VG_N_THREADS][MAXIMUM_FDS];
void FZ_(setup_tainted_map)(void) {
	if(fengSysFlag){VG_(printf)("feng:entered setup_tainted_map\n");}
	ThreadId t = 0;
	VG_(memset)(tainted_fds, False, sizeof(tainted_fds));
	VG_(memset)(position_fds, 0, sizeof(position_fds));

	/* Taint stdin if specified */
	if (FZ_(clo_taint_stdin)) {
		for(t = 0; t < VG_N_THREADS; t++) {
			tainted_fds[t][0] = True;
		}
	}
}
	
void printArgs(UWord *args,UInt n,const char *name){
	/*
	int i=0;
	for (i=0;i<n;i++)
	{
		VG_(printf)("feng:in %s with arg[%d]=0x%x\n",name,i,args[i]);
	}
	*/
}

void FZ_(syscall_open)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_open\n");}
	printArgs(args,nArgs,"open");
	Char fdpath[MAX_PATH]={0};
	Int fd = sr_Res(res);

	// Nothing to do if no file tainting
	// But, if stdin tainting, always taint fd 0...
	if (!FZ_(clo_taint_file)/* && (fd != 0 || !FL_(clo_taint_stdin))*/) {
		return;
	}

	//populate_guest_args(tid);
	if (!sr_isError(res) && fd < MAXIMUM_FDS) {
		resolve_fd(fd, fdpath, MAX_PATH-1);
		tainted_fds[tid][sr_Res(res)] = (VG_(strncmp)(fdpath, FZ_(clo_file_filter), VG_(strlen)(FZ_(clo_file_filter))) == 0);
		VG_(printf)("[?] tid %d open(%d) fdpath=%s clo_file_filter=%s\n", tid, fd, fdpath, FZ_(clo_file_filter));
		if (tainted_fds[tid][sr_Res(res)]) {
			VG_(printf)("[+] tid %d open(%d)\n", tid, fd);
			position_fds[tid][sr_Res(res)] = 0;
		}
		/*if (tainted_fds[tid][sr_Res(res)]) {
		VG_(printf)("tainting file %d\n", sr_Res(res));
		}
		else {
		VG_(printf)("not tainting file %d\n", sr_Res(res));
		}*/
	}
}

Dep *paddr=NULL,*pj=NULL;

void FZ_(syscall_read)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_read\n");}
	printArgs(args,nArgs,"read");
	UInt i, j, k;
	Int fd = -1;
	Char *data = NULL;
	//populate_guest_args(tid);

	fd = ((Int)args[0])/*guest_args[tid].args[3]*/;
	data = (Char *)(args[1]/*guest_args[tid].args[1]*/);

	//VG_(printf)("[?] tid %d read(%d) tainted %d\n", tid, fd, tainted_fds[tid][fd]);
	if (fd < 0 || sr_isError(res) || !tainted_fds[tid][fd]) {
		return;
	}

	k = position_fds[tid][fd];
	for (i = 0; i < sr_Res(res); i++) {
#ifdef FENG_AMD64
		if(fengSysFlag){VG_(printf)("feng:addr:%llu\n",((ULong)data + i));}
		j = add_dependency_addr((Addr)((ULong)data + i), 8);
		//VG_(printf)("[+] tid %d read(%d) tainting byte %d (0x%08x)\n",
		//	tid, fd, k + i, (ULong)(data + i));
		pj=getDep(&depaddr8,j);
		VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", k + i);
#else
		if(fengSysFlag){VG_(printf)("feng:addr:%llu\n",((UInt)data + i));}
		j = add_dependency_addr((Addr)(UInt)(data + i), 8);
		//VG_(printf)("[+] tid %d read(%d) tainting byte %d (0x%08x)\n",
		//	tid, fd, k + i, (UInt)(data + i));
		pj=getDep(&depaddr8,j);
		VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", k + i);
#endif // FENG_AMD64
	}
	position_fds[tid][fd] += sr_Res(res);
}

void FZ_(syscall_write)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_write\n");}
	printArgs(args,nArgs,"write");
	UInt i, k;
	Int fd = -1;
	Char *data = NULL;
	//populate_guest_args(tid);

	fd = ((Int)args[0])/*guest_args[tid].args[3]*/;
	data = (Char *)(args[1]/*guest_args[tid].args[1]*/);

	if (fd < 0 || sr_isError(res)) {
		return;
	}
	k = position_fds[tid][fd];
	for (i = 0; i < sr_Res(res); i++) {
#ifdef FENG_AMD64
		char * cons = depend_on_addr((Addr)(ULong)(data + i), 8);
		VG_(printf)("[+] tid %d write(%d) tainted byte %d (0x%08x) %s\n",
			tid, fd, k + i, (Addr)(ULong)(data + i), cons);
#else
		char * cons = depend_on_addr((Addr)(UInt)(data + i), 8);
		VG_(printf)("[+] tid %d write(%d) tainted byte %d (0x%08x) %s\n",
			tid, fd, k + i, (Addr)(UInt)(data + i), cons);
#endif // FENG_AMD64


	}
}

void FZ_(syscall_mmap2)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if (fengSysFlag){VG_(printf)("feng:entered syscall_mmap2\n");}
	printArgs(args,nArgs,"mmap2");
	UInt i, j, length, offset;
	Int fd = -1;
	Char *data = NULL;
	//populate_guest_args(tid);

	fd = ((Int)args[4])/*guest_args[tid].args[5]*/;
	length = ((UInt)args[1])/*guest_args[tid].args[1]*/;
	data = ((Char *)args[0]);
	offset = ((UInt)args[5])/*guest_args[tid].args[6]*/;

	//VG_(printf)("[+] mmap2(0x%08x, 0x%x, 0x%x, 0x%x, 0x%x, 0x%x) = 0x%08x\n", guest_args[tid].args[3], length, guest_args[tid].args[2], guest_args[tid].args[4], fd, offset, data);

	if (fd < 0 || sr_isError(res) || !tainted_fds[tid][fd]) {
		return;
	}

	for (i = 0; i < length; i++) {
#ifdef FENG_AMD64
		if(fengSysFlag){VG_(printf)("feng:addr:%x\n",((ULong)data + i));}
		j = add_dependency_addr((Addr)((ULong)data + i), 8);
		VG_(printf)("[+] mmap2() tainting byte %d (0x%08x)\n", offset + i, (ULong)(data + i));
		pj=getDep(&depaddr8,j);
		VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", offset + i);
#else
		if(fengSysFlag){VG_(printf)("feng:addr:%x\n",((UInt)data + i));}
		j = add_dependency_addr((Addr)((UInt)data + i), 8);
		VG_(printf)("[+] mmap2() tainting byte %d (0x%08x)\n", offset + i, (UInt)(data + i));
		pj=getDep(&depaddr8,j);
		VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", offset + i);
#endif // FENG_AMD64
	}
}

void FZ_(syscall_munmap)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_munmap\n");}
	printArgs(args,nArgs,"munmap");
	UInt i, start, length;
	//populate_guest_args(tid);

	length = ((UInt)args[1])/*guest_args[tid].args[1]*/;
	start = ((UInt)args[0])/*guest_args[tid].args[2]*/;

	//VG_(printf)("[+] munmap(0x%08x, 0x%x)\n", start, length);

	if (sr_isError(res)) {
		return;
	}

	for (i = 0; i < depaddr8.count; i++) {
		paddr=getDep(&depaddr8,i);
		if (paddr->value.addr == start) {
			break;
		}
	}

	if (i == depaddr8.count) {
		return;
	}

	for (i = 0; i < length; i++) {
		del_dependency_addr(start + i, 8);
	}
}


void FZ_(syscall_lseek)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_lseek\n");}
	printArgs(args,nArgs,"lseek");
	Int fd;
	//populate_guest_args(tid);

	fd = ((Int)args[0])/*guest_args[tid].args[3]*/;

	if (fd < 0 || sr_isError(res) || !tainted_fds[tid][fd]) {
		return;
	}

	position_fds[tid][fd] = sr_Res(res);

    //// Nothing to do if no file tainting
    //// But, if stdin tainting, always taint fd 0...	/*
    //if (!FZ_(clo_taint_file)/* && (fd != 0 || !FL_(clo_taint_stdin))*/) {
    //    return;
    //}

    //if (fd > -1 && fd < MAXIMUM_FDS) {
    //    resolve_fd(fd, fdpath, MAX_PATH-1);
    //    tainted_fds[tid][res.res] = (VG_(strncmp)(fdpath, FZ_(clo_file_filter), VG_(strlen)(FZ_(clo_file_filter))) == 0);
    //    if (tainted_fds[tid][res.res]) {
    //        position_fds[tid][res.res] = 0;
    //    }
    //    /*if (tainted_fds[tid][res.res]) {
    //        VG_(printf)("tainting file %d\n", res.res);
    //    }
    //    else {
    //        VG_(printf)("not tainting file %d\n", res.res);
    //    }*/
    //}
}

void FZ_(syscall_close)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_close\n");}
	printArgs(args,nArgs,"close");
	Int fd = -1;
	//populate_guest_args(tid);
	fd = ((Int)args[0])/*guest_args[tid].args[1]*/;
	if (fd > -1 && fd < MAXIMUM_FDS) {
		VG_(printf)("[+] tid %d close(%d)\n", tid, fd);
		tainted_fds[tid][fd] = False;
		position_fds[tid][fd] = 0;
	}
}
 

//feng: create new dep( auto extending)
int extendDep(DepExt *depext){
	UInt i;

	depext->last->next=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	depext->last=depext->last->next;
	depext->last->next=NULL;
	depext->total+=DEP_BLOCK_SIZE;

	for (i = 0; i < DEP_BLOCK_SIZE; i++) {
		depext->last->dep[i].cons = depext->last->dep[i].buf;
		depext->last->dep[i].cons[0] = '\x00';
		depext->last->dep[i].cons_size = XXX_MAX_BUF;
	}
	
	return 1;
}


#define DEP_EXT_TIMES 0

//feng: get dep by 2-level index
Dep*  getDep( DepExt *depext, UInt id )
{
	if (id<0)
	{
		if (fengDepExtFlag)	{VG_(printf)("feng:DepExt return NULL\n");}
		return NULL;
	}

	if (id){
	}

	UInt loop=id/DEP_BLOCK_SIZE;//feng: get level 1 block index
	UInt site=id%DEP_BLOCK_SIZE;//feng: get level 2 block index
	//if (fengDepExtFlag)	{VG_(printf)("feng:entered DepExt id:%d loop:%d site:%d\n",id,loop,site);}

	
	Dep* rnt=NULL;
	DepBlock* pblock=depext->first;

	//if (depext == &depaddr8 || depext == &depaddr16 || depext == &depaddr32 || depext == &depaddr64) 
	//if (depext == &depreg || depext == &deptmp) 
	//if (depext != &deptmp)
	{
		if (loop>DEP_EXT_TIMES) {
			if (pblock->next==NULL)
			{
				extendDep(depext);//feng : no such level 1 , extend(create)
				if(fengDepExtFlag){VG_(printf)("feng:extended id:%d total:%d\n",id,depext->total);}
			}
			pblock=pblock->next;
			loop--;
		}
	}

	if (loop>DEP_EXT_TIMES){
		return NULL;
	}

	rnt=&pblock->dep[site];
	if(rnt==NULL){
		VG_(tool_panic)("feng:getDep return NULL\n");
	}
	return rnt;//feng : return level 2 dep
}


//Feng:初始化 各个dep块：大小，计数器，初始化值，内存空间
void initDepExt(void){
	if(fengDepExtFlag){VG_(printf)("feng:entered initDepExt\n");}

	UInt i;
	deptmp.first=NULL;
	depreg.first=NULL;
	depaddr8.first=NULL;
	depaddr16.first=NULL;
	depaddr32.first=NULL;
	depaddr64.first=NULL;

	deptmp.first=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	//VG_(printf)("Feng:malloc %x\n",deptmp.first);
	deptmp.last=deptmp.first;
	deptmp.count=DEP_BLOCK_SIZE;
	deptmp.total=DEP_BLOCK_SIZE;

	depreg.first=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	//VG_(printf)("Feng:malloc %x\n",depreg.first);
	depreg.last=depreg.first;
	depreg.count=DEP_BLOCK_SIZE;
	depreg.total=DEP_BLOCK_SIZE;

	depaddr8.first=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	//VG_(printf)("Feng:malloc %x\n",depaddr8.first);
	depaddr8.last=depaddr8.first;
	depaddr8.count=0;
	depaddr8.total=DEP_BLOCK_SIZE;

	depaddr16.first=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	//VG_(printf)("Feng:malloc %x\n",depaddr16.first);
	depaddr16.last=depaddr16.first;
	depaddr16.count=0;
	depaddr16.total=DEP_BLOCK_SIZE;

	depaddr32.first=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	//VG_(printf)("Feng:malloc %x\n",depaddr32.first);
	depaddr32.last=depaddr32.first;
	depaddr32.count=0;
	depaddr32.total=DEP_BLOCK_SIZE;

	depaddr64.first=(DepBlock *)VG_(malloc)("\x00",sizeof(DepBlock));
	//VG_(printf)("Feng:malloc %x\n",depaddr64.first);
	depaddr64.last=depaddr64.first;
	depaddr64.count=0;
	depaddr64.total=DEP_BLOCK_SIZE;


	//feng:memory init
	VG_(memset)(deptmp.first, 0, sizeof(DepBlock));
	VG_(memset)(depreg.first, 0, sizeof(DepBlock));
	VG_(memset)(depaddr8.first, 0, sizeof(DepBlock));
	VG_(memset)(depaddr16.first, 0, sizeof(DepBlock));
	VG_(memset)(depaddr32.first, 0, sizeof(DepBlock));
	VG_(memset)(depaddr64.first, 0, sizeof(DepBlock));


	if(fengDepExtFlag){VG_(printf)("feng:begin init value\n");}
	//Feng:初始化值：constraint约束，cons_size长度，buffer串
	for (i = 0; i < DEP_BLOCK_SIZE; i++) {
		deptmp.first->dep[i].cons = deptmp.first->dep[i].buf;
		deptmp.first->dep[i].cons[0] = '\x00';
		depreg.first->dep[i].cons = depreg.first->dep[i].buf;
		depreg.first->dep[i].cons[0] = '\x00';

		depaddr8.first->dep[i].cons = depaddr8.first->dep[i].buf;
		depaddr16.first->dep[i].cons = depaddr16.first->dep[i].buf;
		depaddr32.first->dep[i].cons = depaddr32.first->dep[i].buf;
		depaddr64.first->dep[i].cons=depaddr64.first->dep[i].buf;
		depaddr8.first->dep[i].cons[0] = '\x00';
		depaddr16.first->dep[i].cons[0] = '\x00';
		depaddr32.first->dep[i].cons[0] = '\x00';
		depaddr64.first->dep[i].cons[0] = '\x00';

		deptmp.first->dep[i].cons_size = XXX_MAX_BUF;
		depreg.first->dep[i].cons_size = XXX_MAX_BUF;

		depaddr8.first->dep[i].cons_size = XXX_MAX_BUF;
		depaddr16.first->dep[i].cons_size = XXX_MAX_BUF;
		depaddr32.first->dep[i].cons_size = XXX_MAX_BUF;
		depaddr64.first->dep[i].cons_size=XXX_MAX_BUF;
	}
	if(fengDepExtFlag){VG_(printf)("feng:end init value\n");}

	if(fengDepExtFlag){VG_(printf)("feng:return initDepExt\n");}
}
