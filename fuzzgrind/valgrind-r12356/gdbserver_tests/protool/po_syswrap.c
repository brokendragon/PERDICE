

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
#include "po.h"

//debug info in fz_syswrap.c
Bool fengSysFlag=False;
Bool fengDepExtFlag=False;
Bool fengAddrFlag=False;
Bool PrintFlag=False;
Bool tidPrintFlag=False;
extern Bool fengAssertFlag;
Bool firstTested=False;

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
	
	int i=0;
	for (i=0;i<n;i++)
	{
		if(PrintFlag) {VG_(printf)("feng:in %s with arg[%d]=0x%x\n",name,i,args[i]);}
	}
	
}

void FZ_(syscall_socketcall)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(firstTested){
		//return;
	}
	if(fengSysFlag){VG_(printf)("feng:entered syscall_socketcall\n");}
	//VG_(printf)("feng:will exit\n");
	//VG_(exit)(0);
	printArgs(args,nArgs,"socket");
	Char fdpath[MAX_PATH]={0};
	Int fd = sr_Res(res);
	// Nothing to do if no file tainting
	// But, if stdin tainting, always taint fd 0...
	// if not network_tainted ,return
	if(!FZ_(clo_taint_network))
	{
		VG_(printf)("####tainted_network false. return");
		return;	
	}
	if(fengSysFlag){VG_(printf)("feng: will mark fd: %d\n",fd);}
	//populate_guest_args(tid);
	if (!sr_isError(res) && fd < MAXIMUM_FDS) {
		resolve_fd(fd, fdpath, MAX_PATH-1);
		tainted_fds[tid][sr_Res(res)] = 1;
		//VG_(printf)("[?] tid %d open(%d) fdpath=%s clo_file_filter=%s\n", tid, fd, fdpath, FZ_(clo_file_filter));
		if(tidPrintFlag){
			VG_(printf)("[?] tid %d open(%d) fdpath=%s clo_file_filter=network\n", tid, fd, fdpath);
		}
		if (tainted_fds[tid][sr_Res(res)]) {
			if(tidPrintFlag){
				VG_(printf)("[+] tid %d open(%d)\n", tid, fd);
			}
			position_fds[tid][sr_Res(res)] = 0;
		}
	}
}
void FZ_(syscall_socket)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_socket\n");}
	printArgs(args,nArgs,"socket");
	Char fdpath[MAX_PATH]={0};
	Int fd = sr_Res(res);
	// Nothing to do if no file tainting
	// But, if stdin tainting, always taint fd 0...
	// if (!FZ_(clo_taint_file)/* && (fd != 0 || !FL_(clo_taint_stdin))*/) {
		// return;
	// }
	if(!FZ_(clo_taint_network))
	{
		VG_(printf)("####tainted_network false. return");
		return;	
	}
	//populate_guest_args(tid);
	if (!sr_isError(res) && fd < MAXIMUM_FDS) {
		resolve_fd(fd, fdpath, MAX_PATH-1);
		tainted_fds[tid][sr_Res(res)] = 1;
		//VG_(printf)("[?] tid %d open(%d) fdpath=%s clo_file_filter=%s\n", tid, fd, fdpath, FZ_(clo_file_filter));
		if(tidPrintFlag){
			VG_(printf)("[?] tid %d open(%d) fdpath=%s clo_file_filter=network\n", tid, fd, fdpath);
		}
		if (tainted_fds[tid][sr_Res(res)]) {
			if(tidPrintFlag) {VG_(printf)("[+] tid %d open(%d)\n", tid, fd);}
			position_fds[tid][sr_Res(res)] = 0;
		}
	}
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
		if(tidPrintFlag){VG_(printf)("[?] tid %d open(%d) fdpath=%s clo_file_filter=%s\n", tid, fd, fdpath, FZ_(clo_file_filter));}
		if (tainted_fds[tid][sr_Res(res)]) {
			if(tidPrintFlag){VG_(printf)("[+] tid %d open(%d)\n", tid, fd);}
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
/* 
void FZ_(syscall_recv)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_recv\n");}
	VG_(exit)(0);
	printArgs(args,nArgs,"recv");
	UInt i, j, k;
	Int fd = -1;
	Char *data = NULL;
	//populate_guest_args(tid);

	fd = ((Int)args[0]); //guest_args[tid].args[3];
	data = (Char *)(args[1]); ///*guest_args[tid].args[1];
	//VG_(printf)("[?] tid %d read(%d) tainted %d\n", tid, fd, tainted_fds[tid][fd]);
	if (fd < 0 || sr_isError(res) || !tainted_fds[tid][fd]) {
		return;
	}
	k = position_fds[tid][fd];
	for (i = 0; i < sr_Res(res); i++) {
#ifdef FENG_AMD64
		//if(fengAddrFlag){VG_(printf)("feng:addr:%llu\n",((ULong)data + i));}
		j = add_dependency_addr((Addr)((ULong)data + i), 8);
		if(PrintFlag){VG_(printf)("[+] tid %d recv(%d) tainting byte %d (0x%08x)\n",
		tid, fd, k + i, (ULong)(data + i));}
		pj=getDep(&depaddr8,j);
		VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", k + i);
#else
		//if(fengAddrFlag){VG_(printf)("feng:addr:%llu\n",((UInt)data + i));}
		j = add_dependency_addr((Addr)(UInt)(data + i), 8);
		if(PrintFlag){VG_(printf)("[+] tid %d recv(%d) tainting byte %d (0x%08x)\n",
		tid, fd, k + i, (ULong)(data + i));}
		pj=getDep(&depaddr8,j);
		VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", k + i);
#endif // FENG_AMD64
	}
	position_fds[tid][fd] += sr_Res(res);
}
 */
void FZ_(syscall_read)(ThreadId tid, UWord *args, UInt nArgs, SysRes res) {
	if(fengSysFlag){VG_(printf)("feng:entered syscall_read\n");}
	printArgs(args,nArgs,"read");
	UInt i, j, k;
	Int fd = -1;
	Int test_fd = -1;
	static Int packet_num = 0;
	Int recv_data_len = 0;
	Char *data = NULL;
	char *cwd = NULL;
	Char map_data[MAX_LINE];
	SysRes res_test;	
	//populate_guest_args(tid);

	fd = ((Int)args[0]);				//guest_args[tid].args[3];
	data = (Char *)(args[1]);			//guest_args[tid].args[1];

	if(tidPrintFlag){VG_(printf)("[?] tid %d read(%d) tainted %d\n", tid, fd, tainted_fds[tid][fd]);}
	if (fd < 0 || sr_isError(res) || !tainted_fds[tid][fd]) {
		if(fengSysFlag){
			VG_(printf)("feng:can not be taints\n");
		}	
		return;
	}
	if(fengSysFlag){VG_(printf)("feng:tainted_fds:%d\n",tainted_fds[tid][fd]);}
	if(fengSysFlag){VG_(printf)("*****feng:data lenth:%d\n",sr_Res(res));}
	if(fengSysFlag){VG_(printf)("*****jin:packet_num:%d\n",FZ_(clo_packet_num));}
	// if(fengSysFlag){VG_(printf)("*****jin:first round:%d\n",(int)(FZ_(clo_first_round)));}
	if(fengSysFlag){if (FZ_(clo_first_round)) VG_(printf)("*****feng:first round\n");}
	recv_data_len = (Int)sr_Res(res);
	if(fengSysFlag){VG_(printf)("*****feng:data lenth:%d\n",recv_data_len);}
	//if revcived data but not the packet data we want to taint ,return and increase packet_num
	if(recv_data_len < 200){
		VG_(printf)("####not the payload, will return\n");
		for (i = 0; i < sr_Res(res); i++) {
			if(fengSysFlag){VG_(printf)("*****jin:data [%d]:%x\n",i,*(Char *)(data+i));}

		}
		return;
	}
	else{
		VG_(printf)("####add current packet num\n");
		packet_num++;
		if(fengSysFlag){VG_(printf)("*****jin:current num:%d\n",packet_num);}
	}
	if(packet_num != FZ_(clo_packet_num)){
		VG_(printf)("####not the packet need to taint. will return\n");
		return ;
	}
	if(FZ_(clo_first_round)){
		VG_(printf)("####write input model file!\n");
		if(fengSysFlag){VG_(printf)("*****jin:packet_num:%d\n",FZ_(clo_packet_num));}
		if(fengSysFlag){VG_(printf)("*****jin:current num:%d\n",packet_num);}
		res_test = VG_(open)("/tmp/peach_input.txt", VKI_O_RDWR, 0);
		if (!sr_isError(res_test)){
			test_fd = sr_Res(res_test);
			for (i = 0; i < sr_Res(res); i++) {
				VG_(write)(test_fd, data+i, 1);
			}		
		}
		else{
			VG_(printf)("####open peach_input file failed\n");
		}
	}
	for (i = 0; i < sr_Res(res); i++) {
		if(fengSysFlag){VG_(printf)("*****feng:data [%d]:%x\n",i,*(Char *)(data+i));}
	}
	k = position_fds[tid][fd];
	for (i = 0; i < sr_Res(res); i++) {
#ifdef FENG_AMD64
		//if(fengAddrFlag){VG_(printf)("feng:addr:%x\n",((ULong)data + i));}
		j = add_dependency_addr((Addr)((ULong)data + i), 8);
		if(tidPrintFlag){VG_(printf)("[+] tid %d read(%d) tainting byte %d (0x%08x)\n",
		tid, fd, k + i, (ULong)(data + i));}
		if(j == INVALID_ADDR){return;};
		pj=getDep(&depaddr8,j);
		if(pj == NULL) return ;
	//	VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", k + i);
        pj->op = symbol;
        pj->opval = k+i; 
		pj->left = NULL;
		pj->right = NULL;
#if defined(Debug_Luo)
                VG_(printf)("\n\n This is in helperc_symbol_read \n");
                fz_treesearch(pj,buf);
                VG_(printf)("\n\n");
#endif
#else
		//if(fengAddrFlag){VG_(printf)("feng:addr:%x\n",((UInt)data + i));}
		j = add_dependency_addr((Addr)(UInt)(data + i), 8);
		if(tidPrintFlag){VG_(printf)("[+] tid %d read(%d) tainting byte %d (0x%08x)\n",
		tid, fd, k + i, (ULong)(data + i));}
		if(j == INVALID_ADDR){
			VG_(printf)("????add_dependency_addr failed\n");
			return;
		};
		pj=getDep(&depaddr8,j);
		if(pj == NULL) return;
	//	VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", k + i);
        pj->op = symbol;
        pj->opval = k+i;
		pj->left = NULL;
		pj->right = NULL;
#if defined(Debug_Luo)
                VG_(printf)("\n\n This is in helperc_symbol_read \n");
                fz_treesearch(pj,buf);
                VG_(printf)("\n\n");
#endif
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
/* 	for (i = 0; i < sr_Res(res); i++) {
#ifdef FENG_AMD64
		char * cons = depend_on_addr((Addr)(ULong)(data + i), 8);
		if (cons != NULL){
			if(tidPrintFlag){VG_(printf)("[+] tid %d write(%d) tainted byte %d (0x%08x) %s\n",tid, fd, k + i, (Addr)(ULong)(data + i), cons);}
		}
#else
		char * cons = depend_on_addr((Addr)(UInt)(data + i), 8);
		if (cons != NULL){
			if(tidPrintFlag){VG_(printf)("[+] tid %d write(%d) tainted byte %d (0x%08x) %s\n",tid, fd, k + i, (Addr)(ULong)(data + i), cons);}
		}
#endif // FENG_AMD64

	} */
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
		if(fengAddrFlag){VG_(printf)("feng:addr:%x\n",((ULong)data + i));}
		j = add_dependency_addr((Addr)((ULong)data + i), 8);
		if(PrintFlag){
		VG_(printf)("[+] mmap2() tainting byte %d (0x%08x)\n", offset + i, (ULong)(data + i));
		}
		if(j == INVALID_ADDR){return;}
		pj=getDep(&depaddr8,j);
		//VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", offset + i);
        pj->op = symbol;
        pj->opval = offset+i; 
		pj->left = NULL;
		pj->right = NULL;
#if defined(Debug_Luo)
                VG_(printf)("\n\n This is in helperc_symbol_read_mmap2 \n");
                fz_treesearch(pj,buf);
                VG_(printf)("\n\n");
#endif
#else
		if(fengAddrFlag){VG_(printf)("feng:addr:%x\n",((UInt)data + i));}
		j = add_dependency_addr((Addr)((UInt)data + i), 8);
		if(PrintFlag){
		VG_(printf)("[+] mmap2() tainting byte %d (0x%08x)\n", offset + i, (UInt)(data + i));
		}
		if(j == INVALID_ADDR){return;};
		pj=getDep(&depaddr8,j);
		//VG_(snprintf)(pj->cons, XXX_MAX_BUF, "input(%d)", offset + i);
        pj->op = symbol;
        pj->opval = offset+i;
		pj->left = NULL;
		pj->right = NULL; 
#if defined(Debug_Luo)
                VG_(printf)("\n\n This is in helperc_symbol_read_mmap2 \n");
                fz_treesearch(pj,buf);
                VG_(printf)("\n\n");
#endif
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


	

#define DEP_EXT_TIMES 0

//feng: get dep by 2-level index
Dep*  getDep_for_depend( DepExt *depext, UInt id )
{

	if (id < 0 || id >= DEP_BLOCK_SIZE)
	{
		if (fengDepExtFlag)	{VG_(printf)("feng:DepExt return NULL\n");}
		return NULL;
	}
	return depext->dep[id];//feng : return level 2 dep
}
//feng: get dep by 2-level index


Dep*  getDep( DepExt *depext, UInt id )
{

	if (id < 0 || id >= DEP_BLOCK_SIZE)
	{
		if (fengDepExtFlag)	{VG_(printf)("feng:DepExt return NULL\n");}
		return NULL;
	}

	if(depext->dep[id] == NULL)
	{
		depext->dep[id] = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
		if(depext->dep[id] == NULL) return NULL;
		depext->dep[id]->dirty = Fdirty;
		depext->dep[id]->father = 1;
		depext->dep[id]->left = NULL;
		depext->dep[id]->right = NULL;
	}

	return depext->dep[id];//feng : return level 2 dep
}


Dep*  getDep_for_malloc( DepExt *depext, UInt id )
{


	if (id < 0 || id >= DEP_BLOCK_SIZE)
	{
		if (fengDepExtFlag)	{VG_(printf)("feng:DepExt return NULL\n");}
		return NULL;
	}

	depext->dep[id] = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
	if(depext->dep[id] == NULL) return NULL;
	depext->dep[id]->dirty = Fdirty;
	depext->dep[id]->father = 1;
	depext->dep[id]->left = NULL;
	depext->dep[id]->right = NULL;
	

	//VG_(printf)("------------in getDep_for_malloc:	%ld \n",tv_end.tv_usec - tv_begin.tv_usec);
	return depext->dep[id];//feng : return level 2 dep
}





//Feng:初始化 各个dep块：大小，计数器，初始化值，内存空间
void initDepExt(void){
	if(fengDepExtFlag){VG_(printf)("feng:entered initDepExt\n");}


	UInt i;
	//VG_(printf)("Feng:malloc %x\n",deptmp.first);
	deptmp.count=0;
	deptmp.total=DEP_BLOCK_SIZE;

	//VG_(printf)("Feng:malloc %x\n",depreg.first);
	depreg.count=0;
	depreg.total=DEP_BLOCK_SIZE;

	//VG_(printf)("Feng:malloc %x\n",depaddr8.first);
	depaddr8.count=0;
	depaddr8.total=DEP_BLOCK_SIZE;

	//VG_(printf)("Feng:malloc %x\n",depaddr16.first);
	depaddr16.count=0;
	depaddr16.total=DEP_BLOCK_SIZE;

	//VG_(printf)("Feng:malloc %x\n",depaddr32.first);
	depaddr32.count=0;
	depaddr32.total=DEP_BLOCK_SIZE;


	//VG_(printf)("Feng:malloc %x\n",depaddr64.first);
	depaddr64.count=0;
	depaddr64.total=DEP_BLOCK_SIZE;

	//feng:memory init

	for (i = 0; i < DEP_BLOCK_SIZE; i++) {	
		deptmp.dep[i] = NULL;
		depreg.dep[i] = NULL;
		depaddr8.dep[i] = NULL;
		depaddr16.dep[i] = NULL;
		depaddr32.dep[i] = NULL;
		depaddr64.dep[i] = NULL;
	}


	//Feng:初始化值：constraint约束，cons_size长度，buffer串
	if(fengDepExtFlag){VG_(printf)("feng:end init value\n");}

	if(fengDepExtFlag){VG_(printf)("feng:return initDepExt\n");}
}
