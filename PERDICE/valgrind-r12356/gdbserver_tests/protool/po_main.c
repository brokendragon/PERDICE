

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <string.h>
#include <ctype.h>


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
#include "pub_tool_threadstate.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_libcfile.h"


DepExt deptmp;
DepExt depreg;
DepExt depaddr8;
DepExt depaddr16;
DepExt depaddr32;
DepExt depaddr64;

char fn_buf[200];
char buf[100];
char run_times;
char func_config_name[50] = "./config/func_config.ini";		//用于读取危险函数信息
char *solv_buf[XXX_MAX_COUNT];
int cons_count = 0;
int varcount = -1;

//extern Node headnode;
Node headnode={0};
PList list=NULL;
AddrNode hnode={0};
AddrList addrlist=NULL;

// char* cons_file_name = "./output/constraints.txt";
// char* vars_file_name = "./output/vars.txt";

unsigned long coverage_total=0; // Adam:the denominator to be counted for coverage rate
unsigned long coverage_taken=0; // Adam:the numerator to be counted for coverage rate
Exit_record_link exit_record_list;//Adam:the head of exit_link_list
#define FZ_DEBUG
//#undef FZ_DEBUG

#define VER_0.9
BinopData binopData[MAX_DATA_BUF_LEN];
CalcData calcData[MAX_DATA_BUF_LEN];
int binopDataSite;
int calcDataSite;

Func_info function_info;
long int stoi(char *str) //string to long int
{
    char *temp = str;
    int i = 0;
    int flags = 0;
    long int sum = 0;
    while(*temp == ' ')
        ++temp;
    if(*temp != '-' && *temp != '+' && (*temp < '0' || *temp > '9'))
        {//第一个字符不是数字
        return 0;
        }
    if(*temp == '-')
        { //第一个是负号
        flags = 1;
        ++temp;
        }else if(*temp == '+')
        {
        ++temp;
        }
    while(*temp >= '0' && *temp <= '9')
        {
        sum = sum * 10 + (*temp - '0');
        ++temp;
        }
    if(flags==0)
        return sum;
    else
        return 0-sum;
}
void Restore_record_list(Exit_record_link exit_record_list)//Adam:Restore from a file
{   
    Exit_record_link p=exit_record_list;
    Exit_record_link q;
    char buffer[65];
    long int temp;
    int fd;
    SysRes record_file;
    record_file=VG_(open)(EXIT_RECORD_FILE,VKI_O_RDONLY,0);
    if(!sr_isError(record_file))
	{
		fd = sr_Res(record_file);
		VG_(lseek)(fd,0,SEEK_SET);
		while(VG_(read)(fd,buffer,65)>0)
		{
			q=(Exit_record_link)VG_(malloc)("0000",sizeof(Exit_record_node));
			q->next_record=NULL;
			p->next_record=q;
			q->addr=stoi(buffer);      
			VG_(read)(fd,buffer,VG_(strlen)("1")+1) ;
			if(VG_(strcmp)(buffer,"1")==0)
				q->true_taken=1;
			else
				q->true_taken=0;
			VG_(read)(fd,buffer,VG_(strlen)("1")+1) ;
			if(VG_(strcmp)(buffer,"1")==0)
				q->false_taken=1;
			else
				q->false_taken=0;
			p=q;
		} 
		VG_(close)(fd);
	}
}
static void fz_fini(Int exitcode)
{
/*
    int fd;
    int j;
    int i;
    SysRes res;
    char* tmpbuf = (char*)VG_(malloc)("\x00",20);
    if(varcount < 0) return;
    res=VG_(open)(vars_file_name,VKI_O_WRONLY|VKI_O_CREAT|VKI_O_TRUNC,VKI_S_IRWXU);
    if(!sr_isError(res))
    {
        fd = sr_Res(res);
		for(i=0; i<= varcount; i++)
		{
			j = VG_(snprintf)(tmpbuf,XXX_MAX_BUF,"x%d : BITVECTOR(8);\n",i);
        	VG_(lseek)(fd,0,SEEK_END);
        	VG_(write)(fd,tmpbuf,j);
		}
    }
    else{VG_(printf)("File open failed ! \n");}
	*/
	VG_(printf)("****Feng:Debug fini 20150511\n");
	VG_(printf)("fz_fini***********Coverage Rate Count************\n");
	Final_count(exit_record_list); //Adam:print coverage rate
	Store_record_list(exit_record_list);//Adam: store coverage data into a file
    return;
}
static void fz_post_clo_init(void) {
    FZ_(setup_tainted_map)();
}

/*------------------------------------------------------------*/
/*--- Syscall event handlers                                ---*/
/*------------------------------------------------------------*/



static void fz_pre_syscall(ThreadId tid, UInt syscallno, UWord* args, UInt nArgs) {

}


static void fz_post_syscall(ThreadId tid, UInt syscallno, UWord* args, UInt nArgs, SysRes res) {

    if(FZ_(clo_is_symbolize))
        return;
    switch (syscallno) {
#if defined(VGA_x86)		
	//feng:add for network api
	case __NR_socketcall:
	VG_(printf)("****x86: socketcall!\n");
	FZ_(syscall_socketcall)(tid, args, nArgs, res);
        break;
	// case __NR_recvmmsg:
	// VG_(printf)("****x86: recvmmsg!\n");
        // FZ_(syscall_read)(tid, args, nArgs, res);
        // break;
#elif defined(VGA_ppc32)		
	//feng:add for network api
	case __NR_socketcall:
		FZ_(syscall_socketcall)(tid, args, nArgs, res);
        break;
	case __NR_recvmmsg:
        FZ_(syscall_read)(tid, args, nArgs, res);
        break;
#elif defined(VGA_amd64)
	case __NR_socket:
		VG_(printf)("****amd64: socketcall!\n");
		FZ_(syscall_socket)(tid, args, nArgs, res);
        break;
	case __NR_recvfrom:
		VG_(printf)("****amd64: recvfrom!\n");
		FZ_(syscall_read)(tid, args, nArgs, res);
        break;
#elif defined(VGA_ppc64)
	case __NR_socketcall:
		FZ_(syscall_socketcall)(tid, args, nArgs, res);
        break;
	case __NR_recv:
		FZ_(syscall_read)(tid, args, nArgs, res);
        break;		
	case __NR_recvfrom:
		FZ_(syscall_read)(tid, args, nArgs, res);
        break;
#endif
	//originall functions for file api
    case __NR_read:
        FZ_(syscall_read)(tid, args, nArgs, res);
        break;
    case __NR_write:
        FZ_(syscall_write)(tid, args, nArgs, res);
        break;
    case __NR_open:
        FZ_(syscall_open)(tid, args, nArgs, res);
        break;
    case __NR_close:
        FZ_(syscall_close)(tid, args, nArgs, res);
        break;
    case __NR_lseek:
#ifdef __NR__llseek
    case __NR__llseek:
#endif
        FZ_(syscall_lseek)(tid, args, nArgs, res);
        break;
	//originall functions for memory api	
#ifdef __NR_mmap
    case __NR_mmap:
#endif
#ifdef __NR_mmap2
    case __NR_mmap2:
#endif
        FZ_(syscall_mmap2)(tid, args, nArgs, res);
        break;
    case __NR_munmap:
        FZ_(syscall_munmap)(tid, args, nArgs, res);
        break;
    default:
        break;
    }
}

/*------------------------------------------------------------*/
/*--- Command line args                                    ---*/
/*------------------------------------------------------------*/

static Char   FZ_(default_file_filter)[]      = "";

Char*       FZ_(clo_file_filter)            = FZ_(default_file_filter);	//测试数据文件
Char*       FZ_(clo_test_target)            = "";			//代码覆盖率计算的主模块
Bool        FZ_(clo_taint_file)             = False;
Bool        FZ_(clo_taint_stdin)            = False;
Bool		FZ_(clo_taint_network)		  	= False;		//符号化网络数据源标记
Bool		FZ_(clo_first_round)			= False;		//是否为状态的第一轮测试
Int         FZ_(clo_max_bound)              = -1;			//最大测试深度
Int			FZ_(clo_packet_num)				= 1;			//符号化输入数据包id
Char*       FZ_(clo_module_name)            = "";			//选择符号执行的函数名
Char*       FZ_(clo_obj_list)               = "";			//选择符号执行的动态链接库数列表
Bool        FZ_(clo_is_symbolize)           = False;		//符号化接口

Bool		FZ_(verbose)                    = False;		//为true会在valgrind output中打印IR
//选择符号执行使用
Char          object_lists[MAX_OBJ_NUM][MAX_OBJ_SIZE] = {0};//选择符号执行的动态链接库数列表
Bool          just_module_sym = False;
UInt          obj_num = 0;


#ifdef VER_0.9

static void get_func_info(void)				//从配置文件中读取危险函数信息
{
	SysRes func_file ;
	int fd,read_size ;
	char buffer[2048];
	char *tmp1 = NULL, *tmp2 = NULL,*buff=NULL;
	char *out = NULL;

    func_file = VG_(open)(func_config_name,VKI_O_RDONLY,0);
    if(sr_isError(func_file))
	{
		VG_(printf)("Open func_config file failed!\n");
		return ;
	}
	function_info.count = 0;

	fd = sr_Res(func_file);
	VG_(lseek)(fd,0,SEEK_SET);
	read_size = VG_(read)(fd,buffer,2048) ;
	buff = buffer;
	tmp1 = VG_(strtok_r)(buff,"#",&out);
	//VG_(printf)("tmp1 %s\n",tmp1);
	while( tmp1 != NULL )
	{
		//VG_(printf)("tmp1 %s\n",tmp1);
		tmp2 = VG_(strtok)(tmp1,",");
		VG_(strcpy)(function_info.func[function_info.count].name,tmp2);
		tmp2 = VG_(strtok)(NULL,",");

		function_info.func[function_info.count].danger_param = *tmp2 - '0';
		function_info.count ++;
		//VG_(printf)("%s : %d\n",function_info.func[function_info.count-1].name,function_info.func[function_info.count-1].danger_param);
		buff = NULL;
		tmp1 = VG_(strtok_r)(buff,"#",&out);
	}
	//VG_(printf)("total function is %d\n",function_info.count);
}

static void process_obj_para(void)			//处理obj list 不同obj以逗号隔开
{
    Char    *tmp = NULL;
    UInt    i=0;
    if(VG_(strcmp)(object_lists[0],"") != 0)
        return ;
    tmp = VG_(strtok)(FZ_(clo_obj_list),",");
    //VG_(printf)("tmp is %s\n\n",tmp);
    while(tmp != NULL)
    {
        VG_(strcpy)(object_lists[i],tmp);
        tmp = VG_(strtok)(NULL,",");
        i++;
    }
    obj_num = i;

}
#endif //VER_0.9

static Bool fz_process_cmd_line_options(Char* arg) {

    if VG_STR_CLO(arg, "--file-filter", FZ_(clo_file_filter)) {}

    if VG_STR_CLO(arg, "--module-filter", FZ_(clo_module_name)){}
    if VG_STR_CLO(arg, "--obj-list", FZ_(clo_obj_list)){}
    if VG_STR_CLO(arg, "--test-target", FZ_(clo_test_target)){}
    if VG_BOOL_CLO(arg, "--symbolize", FZ_(clo_is_symbolize)) {}
    else if VG_BOOL_CLO(arg, "--taint-stdin", FZ_(clo_taint_stdin)) {}
    else if VG_BOOL_CLO(arg, "--taint-file", FZ_(clo_taint_file)) {}
	else if VG_BOOL_CLO(arg, "--taint-netin", FZ_(clo_taint_network)) {}
    else if VG_BOOL_CLO(arg, "--show-ir", FZ_(verbose)) {}
    else if VG_BOOL_CLO(arg, "--symbolize", FZ_(clo_is_symbolize)) {}
	else if VG_BOOL_CLO(arg, "--first-round", FZ_(clo_first_round)) {}
	else if VG_INT_CLO(arg, "--max-bound", FZ_(clo_max_bound)) {}
	else if VG_INT_CLO(arg, "--packet-num", FZ_(clo_packet_num)) {}

    //VG_(printf)("is_symbolize %d\n",(int)(FZ_(clo_is_symbolize)));
    // VG_(printf)("netin %d\n",(int)(FZ_(clo_taint_network)));
    VG_(printf)("first_round %d\n",(int)(FZ_(clo_first_round)));
    if(VG_(strcmp)(FZ_(clo_module_name),"") != 0)
    {
        if(VG_(strcmp)(FZ_(clo_module_name),"None") != 0)
        {
            just_module_sym = True;

            VG_(printf)("func:%s\n\n",FZ_(clo_module_name));
            if(VG_(strcmp)(FZ_(clo_obj_list),"") != 0)
            {
                if(VG_(strcmp)(FZ_(clo_obj_list),"None") != 0)
                {
                    //VG_(printf)("%s\nobj list:%s\n\n",FZ_(clo_file_filter),FZ_(clo_obj_list));
                    process_obj_para();
                }
            }
        }
        else
        {
            //VG_(printf)("$$$$$$ %s\nfunc:%s\n\n",FZ_(clo_file_filter),FZ_(clo_module_name));
            //VG_(printf)("$$$$$$ %s\nobj list:%s\n\n",FZ_(clo_file_filter),FZ_(clo_obj_list));
            just_module_sym = False;

        }
    }

    return True;
}


static void fz_print_usage(void) {
    VG_(printf)(

        "    --taint-stdin=no|yes             enables stdin tainting [no]\n"
        "    --taint-file=no|yes              enables file tainting [no]\n"
        "    --file-filter=/path/prefix       enforces tainting on any files under\n"
        "                                     the given prefix. []\n"
        "    --show-ir=no|yes                 show intermediate representation statements [no]\n"

        "    --module-filter = module name    just symbolix execution in a specific function\n"
        "    --obj-list = obj name    symbolixc execution in specific objects,different object name split whih ","\n"

        );
}

static void fz_print_debug_usage(void) {
}


static void fz_pre_clo_init(void)
{
    UInt i;
    int j;
    int fd1;
    int fd2;
    int fd3;
	int func_file;

    int bufRead1;
    int bufRead2;
    int bufRead3;
    SysRes res1;
    SysRes res2;
    SysRes res3;
    char run_times_buf[2];

    //char current_dir[MAX_DIR_LENGTH];
    char *filename="./config/input_filename.txt";						//用于读写STP求解的结果

    char input_file[100];
	get_func_info();										//获取高危函数信息

    exit_record_list=(Exit_record_link)VG_(malloc)("0000",sizeof(Exit_record_node));//Adam:initialize the head of record list
    exit_record_list->addr=0;
    exit_record_list->true_taken=0;
    exit_record_list->false_taken=0;
    exit_record_list->next_record=NULL;
    Restore_record_list(exit_record_list);//Adam:restore from a file
    VG_(printf)("Protool with Debug info!\n");
    VG_(details_name)            ("Protool");
    VG_(details_version)         (NULL);
    VG_(details_description)     ("a super fuzzer");
    VG_(details_copyright_author)(
        "Copyright (C) 2002-2011, and GNU GPL'd.");
    VG_(details_bug_reports_to)  (VG_BUGS_TO);

    //VG_(clo_vex_control).iropt_unroll_thresh = 0;
    //VG_(clo_vex_control).guest_chase_thresh = 0;
    VG_(basic_tool_funcs)        (fz_post_clo_init,
        fz_instrument,
        fz_fini);

    VG_(needs_command_line_options)(fz_process_cmd_line_options,
        fz_print_usage,
        fz_print_debug_usage);

    VG_(needs_syscall_wrapper)   ( fz_pre_syscall,
        fz_post_syscall );

#ifdef VER_0.9
    //VG_(getcwd)(current_dir,sizeof(current_dir));
    //VG_(printf)("main current dir: %s \n",current_dir);

    // add by Luo ,symbolize_LLL
    res1=VG_(open)("./config/run_times.txt",VKI_O_RDONLY,0);
    if(!sr_isError(res1))
    {
        fd1 = sr_Res(res1);
        VG_(lseek)(fd1,0,SEEK_SET);
        bufRead1 = VG_(read)(fd1,run_times_buf,VG_(fsize)(fd1));
        run_times = run_times_buf[0];
        VG_(close)(fd1);

    }

    res2=VG_(open)(filename,VKI_O_RDONLY,0);
    if(!sr_isError(res2))
    {
        fd2 = sr_Res(res2);
        VG_(lseek)(fd2,0,SEEK_SET);
        bufRead2 = VG_(read)(fd2,fn_buf,VG_(fsize)(fd2));
        if(bufRead2 > 0)
        {
            res3=VG_(open)(fn_buf,VKI_O_RDONLY,0);
            if(!sr_isError(res3))
            {
                fd3 = sr_Res(res3);
                bufRead2=VG_(read)(fd3,buf,VG_(fsize)(fd3));
                VG_(close)(fd3);
            }
        }
        VG_(close)(fd2);
    }
#endif //VER_0.9

    // res1=VG_(open)(cons_file_name,VKI_O_TRUNC,0);
    // if(!sr_isError(res1))
    // {
        // fd1= sr_Res(res1);
		// VG_(close)(fd1);
	// }
    // res1=VG_(open)(vars_file_name,VKI_O_TRUNC,0);
    // if(!sr_isError(res1))
    // {
        // fd1= sr_Res(res1);
		// VG_(close)(fd1);
	// }    


    VG_(memset)(binopData, 0, sizeof(BinopData)*MAX_DATA_BUF_LEN);
    VG_(memset)(calcData, 0, sizeof(CalcData)*MAX_DATA_BUF_LEN);
    binopDataSite=0;
    calcDataSite=0;

    initDepExt();

	varnode *empty=(varnode*)VG_(malloc)("\x00", sizeof(varnode));
    headnode.data=empty;
    headnode.next=NULL;
    list = &headnode;
	
	addrtype *data=(addrtype*)VG_(malloc)("\x00", sizeof(addrtype));
	hnode.data=data;
	hnode.next=NULL;
	addrlist=&hnode;
}

VG_DETERMINE_INTERFACE_VERSION(fz_pre_clo_init)
