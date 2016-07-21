
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
#define MAX_DATA_TRUNK 	20
#define MAX_LINE		1024
#define EXIT_RECORD_FILE "./output/exit_record.txt" //Adam:exit_list_file directory
#define MAX_VUL_NUM    1000
extern Char*         FZ_(clo_file_filter);
extern Bool          FZ_(clo_taint_file);
extern Bool          FZ_(verbose);
extern Bool          FZ_(clo_taint_stdin);
extern Bool 		 FZ_(clo_taint_network);
extern Bool 		 FZ_(clo_is_mapping);
extern Bool			 FZ_(clo_first_round);
extern Char*         FZ_(clo_module_name);
extern Char*         FZ_(clo_obj_list);
extern Char*         FZ_(clo_test_target);
extern Char object_lists[MAX_OBJ_NUM][MAX_OBJ_SIZE];
extern Bool          FZ_(clo_is_symbolize);
extern Int          FZ_(clo_max_bound);
extern Int			FZ_(clo_packet_num);

extern Bool	FZ_(clo_is_symbol_process);
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
#define XXX_MAX_BUF       1024*8
#define XXX_MAX_COUNT	  1024*8

//Feng : extend dep, ��һ��С������ÿһ��dependency��չ���С��ֱ��Ӱ��Ч��
#define DEP_BLOCK_SIZE 4096

//��¼�Ĳ���ȫ������������
#define MAX_FUNC_NUM	100

#define MAX_FUNC_CYCLE 1000
#define Fdirty 0
#define Tdirty 101
#define FORMAT_FUNC_COUNT 	20
#define FORMAT_STR_COUNT	30
#define MAX_LIB_FUNC_NUM	100
typedef enum{
    symbol = 100,
    Iconst,    
    put,
    get,
    load,
    loadI,
    rdtmp,
    unop,
    binop,
    mux0x,
    store,
    cat,
    x86g,
    amd64g,
	modu,
	mods
}OP;


typedef enum solverop
{
     S_bvnot = 1000,
     S_not,
     S_cat,
     S_if, 
     S_and,
     S_equal,
     S_or,
     S_bvle,
     S_sbvle,
     S_bvlt,
     S_sbvlt,
     S_bvxor,
     S_bvsub,
     S_bvplus,
     S_bvmult,
     S_sbvmult,
     S_bvmod,
     S_sbvmod,
     S_bvdiv,
     S_sbvdiv,
     S_shr,
     S_shl,
     S_bvsx
}Sop;




typedef struct i_op_j
{
    int i;
    int j;
    int type; // LT or LE
    int sign;
}Opij;
typedef struct exit_branch{ //Adam:Coverage rate record node
	Addr addr;
	int true_taken;
	int false_taken;
	struct exit_branch* next_record; 
}Exit_record_node,*Exit_record_link;


typedef struct s_dependency {
    union {
        //Tmp tmp;
        //Reg reg;
        Addr addr;
    } value;
    unsigned int size;      /* dependency size, in bits */
   // char *cons;             /* pointing to buf while cons_size <= XXX_MAX_BUF */
   // char buf[XXX_MAX_BUF];
   // unsigned int cons_size;
/* luo:chang database*/
    OP op;
    UInt buop;
    //UInt op_size;
    UInt cond; // for x86g_calculate_condition and amd64g_calculate_condition
    UInt father;
	UInt dirty;
#if defined(VGA_x86)     
    int opval;
#elif defined(VGA_amd64)
    long opval;
#endif
    struct s_dependency *left;
    struct s_dependency *right;
} Dep;

typedef struct s_dependency_ext{
	UInt total;
	UInt count;
	Dep *dep[DEP_BLOCK_SIZE];
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


typedef struct FuncInfo
{
	char name[50];			//Σ�պ�����
	int danger_param;		//Σ�պ�����������
}FuncInfo;


typedef struct Func_info
{
	FuncInfo  func[MAX_FUNC_NUM];
	int count;
}Func_info;

//add 7.10
typedef struct FormatFuncInfo
{
	char name[50];			//��ʽ��Σ�պ�����
	int danger_param;		//������������		
}FormatFuncInfo;
typedef struct {
	FormatFuncInfo funcname[MAX_FUNC_NUM];
	unsigned int used;
}FormatFuncs;

typedef struct{
	char format_string[FORMAT_STR_COUNT][30];
	unsigned int used;
}FormatStrs;
typedef struct {
	int func_addr[MAX_LIB_FUNC_NUM] ;
	int para_index[MAX_LIB_FUNC_NUM] ;
	int func_count;
}LibFuncAddr; 

extern DepExt deptmp;
extern DepExt depreg;
extern DepExt depaddr8;
extern DepExt depaddr16;
extern DepExt depaddr32;
extern DepExt depaddr64;

//Feng Jin:��һ�������Ĵ�С�趨���������ܵ��³������صĴ���
#define MAX_DATA_BUF_LEN 15000

extern BinopData binopData[MAX_DATA_BUF_LEN];
extern CalcData calcData[MAX_DATA_BUF_LEN];
extern int binopDataSite;
extern int calcDataSite;

extern unsigned long coverage_total; // Adam:the denominator to be counted for coverage rate
extern unsigned long coverage_taken; // Adam:the numerator to be counted for coverage rate
extern Exit_record_link exit_record_list;//Adam:the head of exit_link_list

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
extern void Final_count(Exit_record_link exit_record_list);
extern void Store_record_list(Exit_record_link exit_record_list);
extern UInt add_dependency_addr(Addr, UInt);
extern void del_dependency_addr(Addr, UInt);
extern char * depend_on_addr(Addr, UInt);

extern void FZ_(setup_tainted_map)(void);

extern void FZ_(syscall_socket)(ThreadId tid, UWord *args, UInt nArgs, SysRes res);
extern void FZ_(syscall_socketcall)(ThreadId tid, UWord *args, UInt nArgs, SysRes res);
extern void FZ_(syscall_recv)(ThreadId tid, UWord *args, UInt nArgs, SysRes res);
extern void FZ_(syscall_send)(ThreadId tid, UWord *args, UInt nArgs, SysRes res);
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
extern Opij get_opij(IROp op);
extern IROp getIRop(int i , int j);
extern char * fz_treesearch(Dep* dep,char* buf);
extern Dep* x86g_parse(Dep* dep, UInt cc_op, UInt cond);
extern Dep* amd64g_parse(Dep* dep, UInt cc_op, UInt cond);
extern Bool simplify(Dep* dep);
extern char* fz_solver(Dep* dep,char* query);
extern void del_dep(Dep* dep);
extern void add_father(Dep* dep);


//feng: create new dep( auto extending)
extern int extendDep(DepExt *depext);
//feng: get dep by 2-level index
extern Dep* getDep(DepExt *depext, UInt id);
extern Dep* getDep_for_depend( DepExt *depext, UInt id );
extern Dep* getDep_for_malloc( DepExt *depext, UInt id );
//feng:init dep extend
extern void initDepExt(void);


//feng:print dep info
extern void printDepTmp();
extern void printDepAddr();

//feng:print args info
extern void printArgs(UWord *args,UInt n,const char *name);

typedef struct {
	Tmp varname;
	char type;
	//int bitnum; 
	//Addrty addr;
	Addr addr;
}varnode;

typedef struct {
	Addr addr;
	char type;
}addrtype;

typedef struct node {
	varnode* data;
	struct node* next;
}Node, *PList, * Pnode;

typedef struct rnode {
	addrtype* data;
	struct rnode* next;
}AddrNode, *AddrList, *Anode;

#endif // !FZ_H
