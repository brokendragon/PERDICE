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


#include "stdio.h"
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
#include "fz.h"
#include "valgrind.h"
#include "pub_tool_vki.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_libcfile.h"

//Dep deptmp[MAX_DEP];
//Dep depreg[MAX_DEP];
//Dep depaddr8[MAX_DEP];
//Dep depaddr16[MAX_DEP];
//Dep depaddr32[MAX_DEP];

DepExt deptmp;
DepExt depreg;
DepExt depaddr8;
DepExt depaddr16;
DepExt depaddr32;
DepExt depaddr64;
//UInt depaddr8.count = 0;
//UInt depaddr16.count = 0;
//UInt depaddr32.count = 0;
//UInt depaddr64.count = 0;

char fn_buf[200];
char buf[100];
char run_times;
#define FZ_DEBUG
//#undef FZ_DEBUG

#define VER_0.9
BinopData binopData[MAX_DATA_BUF_LEN];
CalcData calcData[MAX_DATA_BUF_LEN];
int binopDataSite;
int calcDataSite;

static void fz_fini(Int exitcode)
{
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

    if(FZ_(is_symbolize))
        return;
    switch (syscallno) {
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
Char*         FZ_(clo_file_filter)            = FZ_(default_file_filter);
Bool          FZ_(clo_taint_file)             = False;
Bool          FZ_(clo_taint_stdin)            = False;
Bool          FZ_(verbose)                    = False;//Feng:will do some VG printf while true//especially the instruments

#ifdef VER_0.9
Char*         FZ_(module_name)                = FZ_(default_file_filter);
Char*         FZ_(obj_list)                   = "";
Bool          FZ_(is_symbolize)               = False;

Char          object_lists[MAX_OBJ_NUM][MAX_OBJ_SIZE]                  = {0};

Bool          just_module_sym = False;
UInt          obj_num = 0;
#endif //VER_0.9

#ifdef VER_0.9
static void process_obj_para(void)
{
    Char    *tmp = NULL;
    UInt    i=0;
    if(VG_(strcmp)(object_lists[0],"") != 0)
        return ;
    tmp = VG_(strtok)(FZ_(obj_list),",");
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
#ifdef VER_0.9
    if VG_STR_CLO(arg, "--module-filter", FZ_(module_name)){}
    if VG_STR_CLO(arg, "--obj-list", FZ_(obj_list)){}
#endif //VER_0.9
    if VG_BOOL_CLO(arg, "--symbolize", FZ_(is_symbolize)) {}
    else if VG_BOOL_CLO(arg, "--taint-stdin", FZ_(clo_taint_stdin)) {}
    else if VG_BOOL_CLO(arg, "--taint-file", FZ_(clo_taint_file)) {}
    else if VG_BOOL_CLO(arg, "--show-ir", FZ_(verbose)) {}
    else if VG_BOOL_CLO(arg, "--symbolize", FZ_(is_symbolize)) {}

#ifdef VER_0.9

    //VG_(printf)("is_symbolize %d\n",(int)(FZ_(is_symbolize)));

    if(VG_(strcmp)(FZ_(module_name),"") != 0)
    {
        if(VG_(strcmp)(FZ_(module_name),"None") != 0)
        {
            just_module_sym = True;

            VG_(printf)("func:%s\n\n",FZ_(module_name));
            if(VG_(strcmp)(FZ_(obj_list),"") != 0)
            {
                if(VG_(strcmp)(FZ_(obj_list),"None") != 0)
                {
                    //VG_(printf)("%s\nobj list:%s\n\n",FZ_(clo_file_filter),FZ_(obj_list));
                    process_obj_para();
                }
            }
        }
        else
        {
            //VG_(printf)("$$$$$$ %s\nfunc:%s\n\n",FZ_(clo_file_filter),FZ_(module_name));
            //VG_(printf)("$$$$$$ %s\nobj list:%s\n\n",FZ_(clo_file_filter),FZ_(obj_list));
            just_module_sym = False;

        }
    }
#endif //VER_0.9

    return True;
}



static void fz_print_usage(void) {
    VG_(printf)(

        "    --taint-stdin=no|yes             enables stdin tainting [no]\n"
        "    --taint-file=no|yes              enables file tainting [no]\n"
        "    --file-filter=/path/prefix       enforces tainting on any files under\n"
        "                                     the given prefix. []\n"
        "    --show-ir=no|yes                 show intermediate representation statements [no]\n"
#ifdef VER_0.9
        "    --module-filter = module name    just symbolix execution in a specific function\n"
        "    --obj-list = obj name    symbolixc execution in specific objects,different object name split whih ","\n"
#endif //VER_0.9
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

    int bufRead1;
    int bufRead2;
    int bufRead3;
    SysRes res1;
    SysRes res2;
    SysRes res3;
    char run_times_buf[2];
    //char current_dir[MAX_DIR_LENGTH];
    char *filename="./filename.txt";
    char input_file[100];

    VG_(printf)("Feng:Fuzzgrind with Debug info!\n");
    VG_(details_name)            ("Fuzzgrind");
    VG_(details_version)         (NULL);
    VG_(details_description)     ("a super fuzzer");
    VG_(details_copyright_author)(
        "Copyright (C) 2008-2009, ("__DATE__", "__TIME__") by Gabriel Campana.");
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
    res1=VG_(open)("./run_times.txt",VKI_O_RDONLY,0);
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


    VG_(memset)(binopData, 0, sizeof(BinopData)*MAX_DATA_BUF_LEN);
    VG_(memset)(calcData, 0, sizeof(CalcData)*MAX_DATA_BUF_LEN);
    binopDataSite=0;
    calcDataSite=0;

    initDepExt();

}

VG_DETERMINE_INTERFACE_VERSION(fz_pre_clo_init)
