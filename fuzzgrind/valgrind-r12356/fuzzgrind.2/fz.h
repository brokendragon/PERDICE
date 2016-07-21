/*  This file is part of Fuzzgrind.
 *  Copyright (C) 2009 Gabriel Campana
 *
 *  This work is licensed under the terms of the GNU GPL, version 3.
 *  See the LICENSE file in the top-level directory.
 */

#ifndef FZ_H
#define FZ_H

//#define VGA_amd64
#if defined(VGA_amd64)
#define FENG_AMD64
#define TEST_FENG_AMD64
#endif // defined(VGA_amd64)


#define FZ_(str)    VGAPPEND(vgFuzzGrind_, str)

#define MAX_OBJ_NUM 20
#define MAX_OBJ_SIZE 256

extern Char*         FZ_(clo_file_filter);
extern Bool          FZ_(clo_taint_file);
extern Bool          FZ_(verbose);
extern Bool          FZ_(clo_taint_stdin);
extern Char*         FZ_(module_name);
extern Char*         FZ_(obj_list);
extern Char object_lists[MAX_OBJ_NUM][MAX_OBJ_SIZE];
extern Bool          FZ_(is_symbolize);
//add for module symbolic execution

extern Bool          just_module_sym;
extern UInt          obj_num;
static int check_module_exist = 0;
//indicate all the program should be DSE

#ifdef FENG_AMD64
typedef UInt Tmp;
typedef UInt Reg;
//typedef HWord Addr;
#else
typedef UInt Tmp;
typedef UInt Reg;
//typedef HWord Addr;
#endif //FENG_AMD64


/*
 * Structures which represent the dependency to the input
 * For example, the first byte of a little endian temporary value may depend of
 * the 6th byte of the input
 */
 
#define INVALID_TMP       -1
#define INVALID_ADDR      -1
//#define IS_INVALID(i, n)  (i & (1 << n))
//#define SET_INVALID(i, n) do { i |= (1 << n); } while (0)
#define XXX_POS_MAX       100
#define MAX_DEP           4096
#define XXX_MAX_BUF       1024

//Feng : extend dep, 这一大小决定了每一个dependency扩展块大小，直接影响效能
#define DEP_BLOCK_SIZE 4096

typedef struct s_dependency {
    union {
        //Tmp tmp;
        //Reg reg;
        Addr addr;
    } value;
    unsigned int size;      /* dependency size, in bits */
    char *cons;             /* pointing to buf while cons_size <= XXX_MAX_BUF */
    char buf[XXX_MAX_BUF];
    unsigned int cons_size;
} Dep;

typedef struct s_dependency_block{
	Dep dep[DEP_BLOCK_SIZE];
	struct s_dependency_block *next;
}DepBlock;

typedef struct s_dependency_ext{
	UInt total;
	UInt count;
	DepBlock* first;
	DepBlock* last;
}DepExt;

typedef struct BinopData{
	UInt tmp_to;
	UInt op;
	UInt end_size;
	Bool used;
}BinopData;

typedef struct CalcData
{
	UInt cond;
	Tmp tmp_to;
	Tmp cc_dep1;
	Tmp cc_dep2;
	Bool used;
}CalcData;


extern DepExt deptmp;
extern DepExt depreg;
extern DepExt depaddr8;
extern DepExt depaddr16;
extern DepExt depaddr32;
extern DepExt depaddr64;

//Feng Jin:这一缓冲区的大小设定不合理，可能导致程序严重的错误
#define MAX_DATA_BUF_LEN 15000

extern BinopData binopData[MAX_DATA_BUF_LEN];
extern CalcData calcData[MAX_DATA_BUF_LEN];
extern int binopDataSite;
extern int calcDataSite;



//Feng:change site
//Feng:if we edit here, then all function need to support 64bit!
#ifdef FENG_AMD64
	#define SELECT_DEPADDR(size) \
		(size == 64) ? &depaddr64 : ((size == 32) ? &depaddr32 : ((size == 8) ? &depaddr8 : &depaddr16))
	#define SELECT_DEPADDR_COUNT(size) \
		(size == 64) ? &depaddr64.count : ((size == 32) ? &depaddr32.count : ((size == 8) ? &depaddr8.count : &depaddr16.count))
#else
	#define SELECT_DEPADDR(size) \
		(size == 32) ? &depaddr32 : ((size == 8) ? &depaddr8 : &depaddr16)
	#define SELECT_DEPADDR_COUNT(size) \
		(size == 32) ? &depaddr32.count : ((size == 8) ? &depaddr8.count : &depaddr16.count)
#endif // FENG_AMD64



#define TO_STR(x) #x

#define add_dirty1(fun, a) do {                               \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_1((a))               \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty2(fun, a, b) do {                               \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_2((a), (b))               \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty3(fun, a, b, c) do {                            \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_3((a), (b), (c))          \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty4(fun, a, b, c, d) do {                         \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_4((a), (b), (c), (d))     \
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty5(fun, a, b, c, d, e) do {                      \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_5((a), (b), (c), (d), (e))\
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty6(fun, a, b, c, d, e, f) do {                   \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_6((a), (b), (c), (d), (e), (f))\
    );                                                           \
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)

#define add_dirty7(fun, a, b, c, d, e, f, g) do {                   \
    di = unsafeIRDirty_0_N(0,                                    \
                           "FL_(" TO_STR(fun) ")",               \
                           VG_(fnptr_to_fnentry)(&(fun)),        \
                           mkIRExprVec_7((a), (b), (c), (d), (e), (f), (g))\
    );                                                           \
	/*VG_(printf)("feng:a=0x%x b=0x%x c==0x%x d=0x%x e=0x%x f=0x%x g=0x%x\n",a,b,c,d,e,f,g);*/\
    addStmtToIRSB(bb, IRStmt_Dirty(di));                         \
} while (0)


/* prototypes */

extern UInt add_dependency_addr(Addr, UInt);
extern void del_dependency_addr(Addr, UInt);
extern char * depend_on_addr(Addr, UInt);

extern void FZ_(setup_tainted_map)(void);

extern void FZ_(syscall_open)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void FZ_(syscall_read)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void FZ_(syscall_write)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void FZ_(syscall_mmap2)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void FZ_(syscall_munmap)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void FZ_(syscall_close)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void FZ_(syscall_lseek)(ThreadId tid, UWord* args, UInt nArgs, SysRes res);
extern void IROp_to_str(IROp op, Char *buffer);

extern IRSB* fz_instrument(VgCallbackClosure*, IRSB*, VexGuestLayout*, 
                           VexGuestExtents*, IRType, IRType);


//feng: create new dep( auto extending)
extern int extendDep(DepExt *depext);
//feng: get dep by 2-level index
extern Dep* getDep(DepExt *depext, UInt id);
//feng:init dep extend
extern void initDepExt(void);


//feng:print dep info
extern void printDepTmp();
extern void printDepAddr();

//feng:print args info
extern void printArgs(UWord *args,UInt n,const char *name);

#endif // !FZ_H
