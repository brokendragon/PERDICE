
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
#include "pub_tool_vki.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_threadstate.h"
#include "pub_tool_stacktrace.h"
#include "pub_tool_libcfile.h"

#include "pub_tool_libcsetjmp.h"

//#include "../coregrind/pub_core_xarray.h"
//#include"../coregrind/m_debuginfo/priv_tytypes.h"
//#include"../coregrind/m_debuginfo/priv_storage.h"

#include "po.h"

#include "../coregrind/pub_core_basics.h"
#include "../coregrind/pub_core_vki.h"
#include "../coregrind/pub_core_vkiscnums.h"
#include "../coregrind/pub_core_threadstate.h"

#define FZ_DEBUG
#undef FZ_DEBUG

//版本控制
#define VER_0.9

//调试控制
#define Debug_jin 0
#define Debug_Luo

//数据常量
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

//
typedef struct RetAddr
{
	Addr ret_addr_list[MAX_FUNC_CYCLE];
	int count;
};

typedef struct {
    UWord args[GP_COUNT];
    UInt used;
} GuestArgs;

// for debug output
char cons[XXX_MAX_BUF];

//control the max bound of the constraints or say the number of dependency 
//用于限定约束获取的深度，即数目
int depending_counter=0;

//in catch : global
int *addrp;
static int flag=0;
static int stpcpy_flag=0;
static int func_index = -1;			//检测危险函数时,发现的危险函数在数据库中的索引
static int count=0;
extern char fn_buf[200];
extern char buf[100];
extern char run_times;
extern Func_info function_info;		//危险函数检测函数信息结构体
extern char* solv_buf[XXX_MAX_COUNT];
extern int cons_count;
extern int varcount;

extern char* cons_file_name;

Bool firstcmp = True;
// for selective synbolic execution

//parameters in registers
static  unsigned long func_ebp = 0,main_ebp = 0;

//parameters to enable the extra function
//启用额外功能的控制变量
static Bool    is_in_func = False;
static Bool    is_in_obj = False;

//用于检查危险函数
static Addr    ret_addr = 0;
static Char		FZ_(func_name)[100];

//HWY: for integer checking
extern Node headnode;
extern PList list;

extern AddrNode hnode;
extern AddrList addrlist;

//return address
struct RetAddr ret_list;

//disable flag
Bool depDisable=False;
Bool helper2Disable=False;
//enable flag
printDetailEnable=False;
//Debug flag
//Print info flag
Bool fengflag=False;
Bool debugflag=False;

//site
Bool fengSwitch=False;			//for switch in fz_instrument
Bool fengEnterHelper=False;		//for helper_xx enter
Bool feng8664Flag=False;		//for x86_xx and amd64_xx

//parameters
Bool fengHelperPara=False;		//for helper parameters

//behavior
Bool fengAddDirty=False;		//for add dirty
Bool fengBinopFlag=False;		//for binop parameters

Bool fengRetFlag=False;			//for return
Bool fengConsFlag=False;		//for constraint print

//dependency
Bool fengDepFlag=False;			//for xx_dependency_xx
Bool fengAddTmp=False;			//flag before add dep tmp
Bool fengAddAddr=False;			//flag before add dep

//info of dependency
Bool fengDepTmp=False;			//for temp debug
Bool fengDepAddr=False;			//for addr print

//size
Bool fengSizeHelpercFlag=False;	//for size in helperc
Bool fengSizeFlag=False;		//for size
Bool fengSizeDepFlag=False;		//for size in dep

//assert
Bool fengAssert=False;

//selective debug!
Bool jinAssertObjFlag = False;
Bool jinAssertFlag = False;

static varnode* lookupVar(PList list, Tmp tmp) {
	Pnode p, temp;
	p = list;
	
	while(p!=NULL) {
		temp = p;
		if(temp->data->varname == tmp) {
			//VG_(printf)("varname:%d, type:%c\n", temp->data->varname,temp->data->type);
			return temp->data;
		}
		p = temp->next;
	}
	return NULL;			
}

static varnode* getVarType(UInt op,Tmp tmp) {
	varnode *item=NULL;
	varnode *item1=NULL;
	item =(varnode*)VG_(malloc)("\x00", sizeof(varnode));
    if(item==NULL){
        VG_(printf)("****FF HWY:gettype return NULL\n");
        return NULL;
    }
	item1=lookupVar(list,tmp);
	if(item1!=NULL){
		item->addr=item1->addr;
	}
	switch(op) {
		case Iop_CmpLT32S: 
            //VG_(printf)("HWY:get the type of variable 1"); 
		case Iop_CmpLE32S: 
			//VG_(printf)("HWY:get the type of variable 2");
			item->varname = tmp;
			item->type = 'S';
			//item->bitnum = 32;
			//item->addr = addr;
			break;
		case Iop_CmpLT32U: 
            //VG_(printf)("HWY:get the type of variable 3");
		case Iop_CmpLE32U:
			//VG_(printf)("HWY:get the type of variable 4");
			item->varname = tmp;
			item->type = 'U';
			//item->bitnum = 32;
			//item->addr = addr;
			break;
		case Iop_CmpLT64S: 
            //VG_(printf)("HWY:get the type of variable 5");
		case Iop_CmpLE64S:
			//VG_(printf)("HWY:get the type of variable 6");
			item->varname = tmp;
			item->type = 'S';
			//item->bitnum = 64;
			//item->addr = addr;
			break;
		case Iop_CmpLT64U: 
            //VG_(printf)("HWY:get the type of variable 7");
		case Iop_CmpLE64U:
			//VG_(printf)("HWY:get the type of variable 8");
			item->varname = tmp;
			item->type = 'U';
			//item->bitnum = 64;
			//item->addr = addr;
			break;
	/*	case Iop_8Uto16:
		case Iop_8Uto32:
		case Iop_16Uto32:
		case Iop_32Uto64:
		case Iop_16Uto64:
		case Iop_8Uto64:
		case Iop_1Uto8:
		case Iop_1Uto32:
		case Iop_1Uto64:
			item->varname = tmp;
			item->type = 'U';*/
			//item->addr = addr;
			//VG_(printf)("FF:iop to:t%d is U\n",tmp);
			//break;
	/*	case Iop_8Sto16:
		case Iop_8Sto32:
		case Iop_16Sto32:
		case Iop_32Sto64:
		case Iop_16Sto64:
		case Iop_8Sto64:
		case Iop_1Sto8:
		case Iop_1Sto16:
		case Iop_1Sto32:
		case Iop_1Sto64:
			item->varname = tmp;
			item->type = 'S';*/
			//item->addr = addr;
			//VG_(printf)("FF:iop to:t%d is S\n",tmp);
			//break;
		/*case Iop_32to8:
		case Iop_64to16:
		case Iop_64to8:
		case Iop_Not1:
		case Iop_32to1:
		case Iop_64to1:
			item->varname = tmp;
		*/
		default:
        	//VG_(printf)("HWY:default? Fatal!");
            //VG_(free)(item);
            return NULL;
			//break;
			// item->varname = tmp;
			// item->type = 'X';
			// item->addr = addr;
			// break;
	}
	//VG_(printf)("varname:%d, type:%c\n", item->varname,item->type);
	return item;
}

static lookupVarType(PList list, varnode* item ) {
	Pnode p, temp;
	p = list;
	while(p!=NULL) {
		temp = p;
		if(temp->data->varname == item->varname) {
			if( temp->data->type != item->type) {
				
				if(temp->data->type=='X'){//origin is unknown,update by new
					temp->data->type = item->type;
					
				}else if(item->type=='X'){//new is unknown, update by origin
					item->type= temp->data->type;
					
				}else{//conversion confilict
					 VG_(printf)("HWY:may conversion error in t%d origin(%c) new(%c)\n",item->varname,temp->data->type,item->type);
				}
			}else if(temp->data->addr!=item->addr){
				VG_(printf)("HWY FF:address is different, origin=%08X, new=%08X\n",temp->data->addr,item->addr);
				temp->data->addr=item->addr;		
			}
			temp->data = item;
			return True;
		}
				// }else if ( 'S' == temp->data->type && 'U'==item->type) {
					// temp->data = item;
					// VG_(printf)("HWY:may conversion error in t%d origin(%c) new(%c)\n",item->varname,temp->data->type,item->type);
				// }
		p = temp->next;	
	}
	return False;		
}
			
static void insertVar(PList list, varnode* item){
	Pnode p,q,temp;
	p = list;//get pointer of list head
    if(p==NULL){
        VG_(printf)("****FF HWY:list pointer = NULL\n");
        //VG_(exit)(0);
    }
	
	if(item==NULL) {
		return;
	}
	
    //VG_(printf)("****FF HWY:before next\n");
	temp = p->next;//temp the next node
    //VG_(printf)("****FF HWY:ready to lookup\n");
	if(!lookupVarType(list, item)) {
            //VG_(printf)("****FF HWY:ready to insert\n");
		q = (Node*)VG_(malloc)("\x00", sizeof(Node));
		if(q == NULL) {
    		VG_(printf)("malloc error!");
			
        }else{
            //VG_(printf)("****FF HWY:insert before \n");            
			q->data = item;
			
			p->next = q;
			q->next = temp;
            //VG_(printf)("****FF HWY:insert after\n");      
		}
		
		VG_(printf)("Inserted:varname:%d, type:%c, addr:%x\n", item->varname,item->type,item->addr);
		
	}else{
		//VG_(printf)("Found:varname:%d, type:%c, addr:%x\n", item->varname,item->type,item->addr);
	}
}

static varnode* getAddr(Tmp tmp,Tmp tmp_to,Addr addr){
	
	varnode* item=NULL;
	
	item =(varnode*)VG_(malloc)("\x00", sizeof(varnode));
	if(item==NULL){
        return NULL;
    }
	
	if(tmp==0){
		item->varname=tmp_to;
		item->type='X';
		item->addr=addr;
	}
	else{
		item->varname=tmp;
		item->type='X';
		item->addr=addr;
	}
	
	return item;
}

static varnode* addr_change(Addr addr,Tmp tmp){
	varnode* item=NULL;
	
	item=lookupVar(list,tmp);
	if(item==NULL){
		return NULL;
	}
	item->addr=addr;
	return item;
}

static addrtype* getAddrType(varnode* item){
	addrtype* node=NULL;
	node=(addrtype*)VG_(malloc)("\x00",sizeof(addrtype));
	
	if(node==NULL){
		return NULL;
	}
	
	if(item==NULL){
		return NULL;
	}
	
	node->addr=item->addr;
	node->type=item->type;
	
	return node;
}

static lookupAddrType(AddrList addrlist , addrtype* item) {
	Anode p,temp;
	p=addrlist;
	// if(item->addr==0){
		// return;
	// }
	while(p!=NULL) {
		temp=p;
		if(temp->data->addr==item->addr){
			if(temp->data->type!=item->type){
				
				if(temp->data->type=='X'){
					temp->data->type=item->type;
				}
				else if(item->type=='X'){
					item->type=temp->data->type;
				}
				else{
					VG_(printf)("HWY:may conversion error at address 0x%08X with type=%c\n",temp->data->addr,temp->data->type);
					temp->data->type=item->type;
				}
			}
			return True;
		}
		p=temp->next;
	}
	return False;
}

static void insertAddr(AddrList addrlist , addrtype* item) {

	Anode p,q,temp;
	p=addrlist;
	
	if(p==NULL){
        VG_(printf)("**** HWY:list pointer = NULL\n");
    }
	
	if(item==NULL) {
		return;
	}
	
	if(item->addr==0){
		return;
	}
	
	temp=p->next;
	
	//VG_(printf)("**** HWY:addr lookup\n");
	if(!lookupAddrType(addrlist,item)){
		q = (AddrNode*)VG_(malloc)("\x00",sizeof(AddrNode));
		if(q==NULL){
			VG_(printf)("malloc error!");
		}
		else{
			//VG_(printf)("**** HWY:addr insert\n");
			q->data=item;
			p->next = q;
			q->next = temp;
			VG_(printf)("**** HWY:addr:%x, type:%c\n", item->addr,item->type);
		}
	}	
}

static isCmp(UInt op){
	
	if(op==0){
		return False;
	}
	switch(op){
		case Iop_CmpLT32S:
		case Iop_CmpLE32S:
		case Iop_CmpLT32U:
		case Iop_CmpLE32U:
		case Iop_CmpLT64S:
		case Iop_CmpLE64S:
		case Iop_CmpLT64U:
		case Iop_CmpLE64U:
		
			return True;
	}
	return False;
}

static addrtype* lookupAddr(AddrList addrlist, Addr addr){
	Anode p,temp;
	p=addrlist;
	
	while(p!=NULL){
		temp=p;
		if(temp->data->addr==addr){
			return temp->data;
		}
		p = temp->next;
	}
	return NULL;
}

static varnode* getTypefromAddr(varnode* item){
	Addr addr=0;
	addrtype* item1=NULL;
	varnode* item2=NULL;
	
	if(item!=NULL){
		addr=item->addr;
	}
	item1=lookupAddr(addrlist,addr);
	if(item1!=NULL){
		if(item1->type!='X'){
			item->type=item1->type;
		}
	}
	item2=item;
	return item2;
}

/*get the type of the result of the operation*/
static varnode* getType(Tmp tmp_to, Tmp tmp1, Tmp tmp2, UInt op) {
	varnode* item=NULL;
	varnode* item1=NULL;
	varnode* item2=NULL;
	varnode* item3=NULL;
	Addr addr1,addr2;
	char type1,type2;
	char defaultType= 'X';
	extern PList list;
	Bool is_Compare=False;
	
	is_Compare=isCmp(op);
	item =(varnode*)VG_(malloc)("\x00", sizeof(varnode));
	
    if(item==NULL){
        VG_(printf)("****FF HWY:gettype return NULL\n");
        return NULL;
    }
	
	item->varname = tmp_to;
	item->addr = 0;
	item->type='X';//default as X(unknown) if without info of type

	if(tmp1==0){
		item1=NULL;
	}else{
		item1=lookupVar(list,tmp1);
	}
    
    if(item1!=NULL){
        addr1=item1->addr;
		type1=item1->type;
		//VG_(printf)("HWY:varname:%d, type:%c\n", item1->varname,item1->type);
    }

	if(tmp2==0){
		item2=NULL;
	} else {
		item2=lookupVar(list,tmp2);
	}

    if(item2!=NULL){
        addr2=item2->addr;
		type2=item2->type;
    }
	
	if(item1 || item2) {
		//type1=item1->type;
		//type2=item2->type;
		if(item1 && item2) {
			if(type2=='X'){//type2 is unknown
				item->type = type1;
				//item2->type = type1;
				//insertVar(list,item2);
				
				if(type1=='U') { 
					item->type = 'U';
					//item2->type = 'U';
					
				}else if(type1=='S'){
					item->type = 'S';
					//item2->type = 'S';
					
				}else{
					item->type = defaultType;
					//item2->type = defaultType;
				}
				
			}else if(type1=='X'){//type1 is unknown
				item->type = type2;
				//item1->type = type2;
				//insertVar(list,item1);
				
				if(type2=='S') { 
					item->type = 'S';
					//item1->type = 'S';
					
				}else if(type2=='U'){
					item->type = 'U';
					//item1->type = 'U';
					
				}else{
					item->type = defaultType;
					//item1->type = defaultType;
				}
				
			}else if(type1==type2) {//same type
				item->type = type1;
			
			}else if(type1!=type2){//different type
				
				VG_(printf)("HWY:may cause convertion error here\n" );
				
				item->type= 'X';	
		}else if(item1){
			//VG_(printf)("varname:%d, type:%c\n", item1->varname,item1->type);
			item->type = type1;
			if(!is_Compare){
				item->addr = addr1;
			}
			//return item;
			
		}else if(item2) {
			item->type = type2;
			if(!is_Compare){
				item->addr = addr2;
			}
			//return item;
		}
		
	}else{
        VG_(printf)("HWY FF:item1=item2=NULL \n");
		item3=lookupVar(list,tmp_to);
		
		if(item3){
			// item->type=item3->type;
			// item->addr=item3->addr;
			item=item3;
		}else{
			item->type= defaultType;//default set type as signed if and only if its dependencies without info of type
			item->addr=0;
			VG_(printf)("HWY FF:default set as %c\n",defaultType);
		}
	}
	//VG_(printf)("varname:%d, type:%c\n", item->varname,item->type);
	return item;
}

void itoa (long int n,char s[])  //long int to string
{
    long int sign;
    int i=0,j,h;
    char temp;
    if((sign=n)<0)//记录符号
        n=-n;//使n成为正数
    do{
       s[i++]=n%10+'0';//取下一个数字
    }while ((n/=10)>0);//删除该数字
    s[64]='\0';
    for(j=0;j<i;j++)
	{
	s[63-j]=s[j];
	}
    for(i=0;i<=63-j;i++)
	s[i]='0';
    if(sign<0)
        s[0]='-';
}
void Final_count(Exit_record_link exit_record_list)//Adam:calculate the coverage rate and print it out
{
	coverage_taken=0;
	Exit_record_link p=exit_record_list;
	while(p->next_record!=NULL)
	{
		p=p->next_record;
		if(p->true_taken==1)
      		 {
			coverage_taken++;          
       		 }
		if(p->false_taken==1)
		{
			coverage_taken++;
		}
	}	
	VG_(printf)("Taken Branch:%d\n",coverage_taken);
}
void Only_Store(Exit_record_link exit_record_list)     //Adam:store into a file
{
    char addr_record[65];
    Exit_record_link p=exit_record_list;
    Exit_record_link q=exit_record_list;
    SysRes record_file;
    int fd;
    record_file=VG_(open)(EXIT_RECORD_FILE,VKI_O_WRONLY,0);
	if(!sr_isError(record_file))
    {
		fd = sr_Res(record_file);
		VG_(lseek)(fd,0,SEEK_SET);
		while(p!=NULL)
		{
			p=p->next_record;
				if(p!=NULL)
				{	
					itoa(p->addr,addr_record);	
					VG_(write)(fd,addr_record,VG_(strlen)(addr_record)+1);
					if(p->true_taken==1)
							VG_(write)(fd,"1",VG_(strlen)("1")+1);
					else 
							VG_(write)(fd,"0",VG_(strlen)("0")+1);
					if(p->false_taken==1)
							VG_(write)(fd,"1",VG_(strlen)("1")+1);
					else 
							VG_(write)(fd,"0",VG_(strlen)("0")+1);  
				}      
			q=p;
		} 
		VG_(close)(fd);
	}
}
void Store_record_list(Exit_record_link exit_record_list)//Adam:store into a file
{
    char addr_record[65];
    Exit_record_link p=exit_record_list;
    Exit_record_link q=exit_record_list;
    SysRes record_file;
    int fd;
    record_file=VG_(open)(EXIT_RECORD_FILE,VKI_O_WRONLY,0);
    if(sr_isError(record_file))
	return;
    fd = sr_Res(record_file);
    VG_(lseek)(fd,0,SEEK_SET);
	while(p!=NULL)
	{
		p=p->next_record;
      		if(p!=NULL)
        	{	
        	itoa(p->addr,addr_record);	
        	VG_(write)(fd,addr_record,VG_(strlen)(addr_record)+1);
        if(p->true_taken==1)
            VG_(write)(fd,"1",VG_(strlen)("1")+1);
        else 
            VG_(write)(fd,"0",VG_(strlen)("0")+1);
        if(p->false_taken==1)
            VG_(write)(fd,"1",VG_(strlen)("1")+1);
        else 
            VG_(write)(fd,"0",VG_(strlen)("0")+1);  
        }      
		VG_(free)(q);
		q=p;
	} 
    VG_(close)(fd);
}
Exit_record_link Set_node(Addr exit_addr)//Adam:add one node that hasn't run yet
{
	Exit_record_link q=(Exit_record_link)VG_(malloc)("0000",sizeof(Exit_record_node));
	q->addr=exit_addr;
	q->next_record=NULL;
	q->true_taken=0;
	q->false_taken=0;
	return q;
}
Exit_record_link Init_node(Addr exit_addr, UInt taken)//Adam:add one node that has run 
{
	Exit_record_link q=(Exit_record_link)VG_(malloc)("0000",sizeof(Exit_record_node));
	q->addr=exit_addr;
	q->next_record=NULL;
	if(taken == 1)
	{
		q->true_taken=1;
		q->false_taken=0;
	}else
	{
		q->true_taken=0;
		q->false_taken=1;
	}
	return q;
}
Bool Check_total_node(Exit_record_link exit_record_list,Addr exit_addr)//Adam:count all exit branch
{
	Exit_record_link p=exit_record_list;
	while(p->next_record!=NULL)
	{
		p=p->next_record;
		if(p->addr==exit_addr)
		{
			return True;
		}
	}
	p->next_record=Set_node(exit_addr);
	return False;
}
Bool Check_taken_node(Exit_record_link exit_record_list,Addr exit_addr, UInt taken)//Adam:check the node that have run just now
{
    static char objname[MAX_FILE_SIZE];  
    Bool named;
    named = VG_(get_objname)(exit_addr, objname, MAX_FILE_SIZE);
    if(VG_(strcmp)(objname,FZ_(clo_test_target))!=0)
        return False;
    Exit_record_link p=exit_record_list;
    while(p->next_record!=NULL)
	{
        p=p->next_record;
		if(p->addr==exit_addr)
		    {	
			if(taken==0 && p->false_taken==0)
				{				
					p->false_taken=1;
					if(exit_addr== 0x0804d020)
						VG_(printf)("false check:%d\n",taken);
					Final_count(exit_record_list); //Adam:print coverage rate
					Only_Store(exit_record_list);
				}
			if(taken==1 && p->true_taken==0)
				{				
					p->true_taken=1;
				    	if(exit_addr== 0x0804d020)
						VG_(printf)("true check:%d\n",taken);
					Final_count(exit_record_list); //Adam:print coverage rate
					Only_Store(exit_record_list);
				}
			return True;
		    }
	}
	p->next_record=Init_node(exit_addr,taken);
	Final_count(exit_record_list); //Adam:print coverage rate
	Only_Store(exit_record_list);
	return False;
}
Bool Check_objname(Exit_record_link exit_record_list) //check whether this obj is current program obj
{
    char objname[MAX_FILE_SIZE];  
	Bool named;
	Exit_record_link p=exit_record_list;
    Exit_record_link q=exit_record_list;
    while(p->next_record!=NULL)
	{
        q=p;
        p=p->next_record;
        VG_(strcpy)(objname, "");
        named = VG_(get_objname)(p->addr, objname, MAX_FILE_SIZE);
        if(VG_(strcmp)(objname,FZ_(clo_test_target))!=0)
            {
            q->next_record=p->next_record;
            VG_(free)(p);
            p=q;
            }
    }
    return True;
}
Bool Print_objname(Exit_record_link exit_record_list,Addr exit_addr) //print all nodes
{
    static char objname[MAX_FILE_SIZE];
    static char this_objname[MAX_FILE_SIZE];
    Exit_record_link p=exit_record_list;
    Bool named;
    int count=0;
    named = VG_(get_objname)(exit_addr, this_objname, MAX_FILE_SIZE);
    if(VG_(strcmp)(this_objname,FZ_(clo_test_target))==0)
        while(p->next_record!=NULL)
	    {
        p=p->next_record;
        named = VG_(get_objname)(p->addr, objname, MAX_FILE_SIZE);
        VG_(printf)("objname:%s\t%d\n",objname,++count);
        }
}
static VG_REGPARM(0) Bool is_max_bound()
{
	int max_bound=FZ_(clo_max_bound);//get max bound
	if(depending_counter>=max_bound){
		return True;
	}else{
		return False;
	}
}
//count depending depth
static VG_REGPARM(0) Bool count_bound(int num)
{
	int max_depend=FZ_(clo_max_bound);
	//VG_(printf)("feng:max depend=%ud\n",max_depend);
	
	if(max_depend<0){
		return False;		
	}
	if(num>1){
		VG_(tool_panic)("count_bound error");
	}
	
	//update counter
	depending_counter++;
	//VG_(printf)("feng:now depending number=%ud\n",depending_counter);
	
	//no depending depth limit
	
	//check depending number
	if(depending_counter>=max_depend){
		return True;
	}else{
		return False;
	}
}


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
    guest_args[tid].args[5] = ts->arch.vex.guest_RDX;				//参数3
    guest_args[tid].args[6] = ts->arch.vex.guest_RCX;				//参数4
    guest_args[tid].args[7] = ts->arch.vex.guest_R8; 				//参数5
    guest_args[tid].args[8] = ts->arch.vex.guest_R9; 				//参数6 超过6个参数在栈上传递
    guest_args[tid].used = 8;
}
#else
static void populate_guest_args(ThreadId tid) {
	//unknown platform, please add the con details here
	//待定平台，加入对应的内容
}
#endif

//#define VGA_amd64
#if defined(VGA_amd64)
#define FENG_AMD64
#endif // defined(VGA_amd64)

/*
Feng:here, we should change all type into 64bit? do it by #define
Feng:I add all types here to support 64bit which can be seen in switch case
Feng:but now we still use 32 env type
*/
#ifdef FENG_AMD64
static IRExpr *assignNew(IRSB *bb, IRExpr *e) {
	IRTemp t = newIRTemp(bb->tyenv, Ity_I64);

	if(fengSwitch){VG_(printf)("feng:type of ir expr:%d\n",typeOfIRExpr(bb->tyenv, e));}
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
		//if(fengSwitch){VG_(printf)("feng:switch f128\n");}
		return NULL;
		//addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F128toI64S, e)));
		break;
	case Ity_V128:
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_V128to64, e)));
		break;
	default:
		if(fengSwitch){VG_(printf)("feng:switch default\n");}
		VG_(tool_panic)("assignNew");
	}
	return IRExpr_RdTmp(t);
}
#else
//now only tested in x86
static IRExpr *assignNew(IRSB *bb, IRExpr *e) {
	IRTemp t = newIRTemp(bb->tyenv, Ity_I32);

	if(fengSwitch){VG_(printf)("feng:type of ir expr:%d\n",typeOfIRExpr(bb->tyenv, e));}
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
	case Ity_I128:
		//	if(fengSwitch){VG_(printf)("feng:switch i128\n");}
		//	return NULL;
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_128to64, e)));
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_64to32, e)));
		break;
		//case Ity_F32:
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F32toI32S, e)));
		//	break;
		//case Ity_F64:
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F64toI32S, e)));
		//	break;
		//case Ity_F128:
		//	if(fengSwitch){VG_(printf)("feng:switch f128\n");}
		//	return NULL;
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F128toF32, e)));
		//	addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_F32toI32S, e)));
		//	break;
	case Ity_V128:
		//	if(fengSwitch){VG_(printf)("feng:switch v128\n");}
		//	return NULL;
		addStmtToIRSB(bb, IRStmt_WrTmp(t, IRExpr_Unop(Iop_V128to32, e)));
		break;
	default:
		if(fengSwitch){VG_(printf)("feng:switch default\n");}
		VG_(tool_panic)("assignNew");
	}
	return IRExpr_RdTmp(t);
}
#endif // FENG_AMD64



/*
* Check that the size of the constraint buffer is large enough to contain the
* new string. If not, reallocate the buffer.
*/
/*
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
	do {                                                                               \											\
	res_snprintf = VG_(snprintf)((d).cons, (d).cons_size, (fmt), __VA_ARGS__);     \
	if (res_snprintf >= (d).cons_size - 1) {  // valgrind's buggy snprintf...    \
	realloc_cons_buf(&(d), res_snprintf);                                      \
	res_snprintf = VG_(snprintf)((d).cons, (d).cons_size, (fmt), __VA_ARGS__); \
	ok = (res_snprintf < (d).cons_size - 1);                                   \
	}                                                                              \
	} while (!ok);                                                                     \
} while (0)
*/

static UInt add_dependency_reg(Reg reg, UInt size) {
    Dep* preg =NULL;
	if(depDisable){
		return INVALID_TMP;
	}
	if(fengDepFlag || fengSizeDepFlag){VG_(printf)("feng:entered add_dependency_reg with reg=%d size=%d\n",reg,size);}


	// 	tl_assert(reg >= 0 && reg < MAX_DEP);
	// 	tl_assert(size != 0);
	if (reg < 0)
	{
		VG_(printf)("Feng:depend of reg=%d\n",reg);
		VG_(tool_panic)("feng:depend of reg: invalid reg !");
	}

	//feng:why
	// 	if (reg > depreg.count){
	// 		return INVALID_TMP;
	// 	}

	if (size==1 || size==8 || size==16 || size==32 ||size==64 || size==128)
	{
		//only these size valid
	}else{
		VG_(printf)("Feng:dep reg size=%d\n", size);
		VG_(tool_panic)("Feng: no handled size\n");
	}

	preg=getDep(&depreg,reg);
	if (preg==NULL){
		return INVALID_TMP;
	}
    if(preg->dirty == Fdirty)
	{
	preg->size=size;
		preg->dirty = Tdirty;
    }
    else
    {
		preg->father -= 1;
        preg = getDep_for_malloc(&depreg,reg);
		if(preg != NULL)
		{
        preg->size = size;
		preg->dirty = Tdirty;
		}
    }

	//feng:why
	// 	//feng:update count
	// 	if (depreg.count<reg){
	// 		depreg.count=reg;
	// 	}

#ifdef FZ_DEBUG
	VG_(printf)("[+] dependency_reg[%d]\n", reg);
#endif

	if(fengRetFlag)VG_(printf)("feng:return\n");
	return reg;
}


static UInt add_dependency_tmp(Tmp tmp, UInt size) {
	if(depDisable){
		return INVALID_TMP;
	}
	if(fengDepFlag){VG_(printf)("feng:entered add_dependency_tmp with size:%d tmp:%d\n",size,tmp);}

	//tl_assert(tmp >= 0 && tmp < MAX_DEP);
    //防止DEP无约束扩展
	if (tmp < 0)
	{
		VG_(printf)("Feng:depend of tmp=%d\n",tmp);
		VG_(tool_panic)("feng:depend of reg: invalid reg !");
	}

	if (tmp > deptmp.total){
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
	if(ptmp->dirty == Fdirty)
    {
        ptmp->size = size;
		ptmp->dirty = Tdirty;
    }
    else 
    {
		ptmp->father -= 1;	
		ptmp = getDep_for_malloc(&deptmp,tmp);
		if(ptmp != NULL)
		{
		ptmp->size=size;
		ptmp->dirty = Tdirty;
		}
    }

	// 	//feng:update count
	// 	if (deptmp.count<tmp){
	// 		deptmp.count=tmp;
	// 	}


#ifdef FZ_DEBUG
	VG_(printf)("[+] dependency_tmp[%d]\n", tmp);
#endif

	if(fengRetFlag)VG_(printf)("feng:return\n");
	return tmp;
}

//Feng:ok
UInt add_dependency_addr(Addr addr, UInt size) {
	if(depDisable){
		return INVALID_TMP;
	}
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
		if(paddr == NULL) return INVALID_ADDR;
		paddr->value.addr=addr;
		*depaddr_count += 1;
	    paddr->size=size;
		paddr->dirty = Tdirty;
	}
    else
    {
		paddr=getDep(depaddr,i);
		if(paddr == NULL) return INVALID_ADDR;
		paddr->father -= 1;
        paddr = getDep_for_malloc(depaddr,i);
		if(paddr != NULL)
		{
	        paddr->value.addr = addr;
			paddr->size=size;
			paddr->dirty = Tdirty;
		}
    }
#ifdef FZ_DEBUG
	VG_(printf)("[+] dependency_addr[%d]\n", i);
#endif

	if(fengRetFlag)VG_(printf)("feng:return\n");

	return i;
}

//Feng:ok
static void del_dependency_tmp(Tmp tmp) {
	if(depDisable){
		return ;
	}
	if(fengDepFlag){VG_(printf)("feng:entered del_dependency_tmp with tmp=%d\n",tmp);}

	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;

	tl_assert(tmp >= 0 && tmp < deptmp.total);
	ptmp=getDep(&deptmp,tmp);
    if(ptmp->dirty == Tdirty)
	{
		ptmp->father -= 1;
		del_dep(ptmp);
        ptmp = getDep_for_malloc(&deptmp,tmp); 
		if(ptmp != NULL)
			ptmp->dirty = Fdirty;
		return;
	}
}

static void del_dependency_reg(Reg reg) {
	if(depDisable){
		return ;
	}
	if(fengDepFlag){VG_(printf)("feng:entered del_dependency_reg\n");}
	if(fengDepFlag){VG_(printf)("Feng:del dep reg=%d\n",reg);}

	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;

	tl_assert(reg >= 0 && reg < deptmp.total);
	preg=getDep(&depreg,reg);
    if(preg->dirty == Tdirty)
	{
		preg->father -= 1;
		del_dep(preg);
        preg = getDep_for_malloc(&depreg,reg); 
		if(preg != NULL)
        	preg->dirty = Fdirty;
		return;
	}
}

//Feng:may ok
void del_dependency_addr(Addr addr, UInt size) {
	if(depDisable){
		return ;
	}
	if(fengDepFlag){VG_(printf)("feng:entered del_dependency_addr\n");}
	if(fengDepFlag){VG_(printf)("Feng:del dep addr=%d\n",addr);}

	DepExt *depaddr = SELECT_DEPADDR(size);
	UInt *depaddr_count = SELECT_DEPADDR_COUNT(size);
	UInt i, j = *depaddr_count - 1;
	Dep* preg=NULL;
	Dep* paddr=NULL;
	Dep* ptmp=NULL;
	UInt m;
	Dep* pi=NULL;
	Dep* pj=NULL;

	for (i = 0; i < *depaddr_count; i++) {
		pi=getDep(depaddr,i);
		if (pi->value.addr == addr) {
#ifdef FZ_DEBUG
			VG_(printf)("[+] removing dependency_addr[%d]\n", i);
			//ppDepAddr(pi);
#endif
			//free_cons_buf(pi);
			//VG_(printf)("Feng:i=%d ? j=%d ? depaddr count=%d\n",i,j,*depaddr_count);
			if (i < j) {
				pj=getDep(depaddr,j);
				pi->father -= 1;
				//del_dep(pi);
                pi = getDep_for_malloc(depaddr,i); 
				if(pi == NULL) VG_(tool_panic)("malloc failed in del_dependency failed!");
				pi->value.addr = pj->value.addr;
				pi->size = pj->size;
                pi->left = pj->left;
                pi->right = pj->right;
                pi->op = pj->op;
                pi->buop = pj->buop;
                pi->opval = pj->opval;
                pi->cond = pj->cond;
				pi->dirty = Tdirty;
				add_father(pi);
				pj->father -= 1;

                pj = getDep_for_malloc(depaddr,j); 
				if(pj != NULL)
                	pj->dirty = Fdirty;         
				if(fengflag){VG_(printf)("feng:delete dep addr=%llu\n",addr);}//temp debug
			}
            else if(i == j)
            {
				pj=getDep(depaddr,j);
				pj->father -= 1;

				pj=getDep_for_malloc(depaddr,j);
				if(pj != NULL)
					pj->dirty = Fdirty;
            }
			*depaddr_count -= 1;
			VG_(printf)("Feng:depaddr count=%d\n",*depaddr_count);
			break;
		}

	}

}

static UInt depend_of_reg(Reg reg) {
	if(depDisable){
		return NULL;
	}
	if(fengDepFlag){VG_(printf)("Feng:enter depend of reg=%d\n",reg);}
	Dep* preg;
	//tl_assert(reg >= 0 && reg < MAX_DEP);
	if (reg < 0)
	{
		VG_(printf)("Feng:depend of reg=%d\n",reg);
		VG_(tool_panic)("feng:depend of reg: invalid reg !");
	}

	if (reg > depreg.total){
		return False;
	}

	preg = getDep_for_depend(&depreg,reg);
	if(preg == NULL) return False;
	if(preg->dirty == Tdirty) return True;
	else return False;
}

static UInt depend_of_tmp(Tmp tmp) {
	if(depDisable){
		return NULL;
	}
	if(fengDepFlag){VG_(printf)("Feng:depend of tmp=%d\n",tmp);}
	Dep* ptmp;
	//tl_assert(tmp >= 0 && tmp < MAX_DEP);
	if (tmp < 0)
	{
		{VG_(printf)("Feng:depend of tmp=%d\n",tmp);}
		VG_(tool_panic)("feng:depend of tmp: invalid tmp !");
	}

	if (tmp > deptmp.total){
		return False;
	}

	ptmp = getDep_for_depend(&deptmp,tmp);
	if(ptmp == NULL) return False;
	if (ptmp->dirty == Tdirty) return True;
	else return False;
}
/*
* Write a value to a register
* tmp is invalid if it's a constant
*/
//Feng:ok
static VG_REGPARM(0) void helperc_put(Tmp tmp, Reg offset) {
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_put\n");}
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
			j = add_dependency_reg(offset, ptmp->size);
			if (j==INVALID_TMP){
				del_dependency_reg(offset);
				return;
			}

			pj=getDep(&depreg,j);
            pj->left = ptmp;
            pj->right = NULL;
            pj->op = put;
			add_father(pj);
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
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_get with size:%d\n",size);}
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
		if (j==INVALID_TMP){
			del_dependency_tmp(tmp);
			return;
		}

		pj=getDep(&deptmp,j);

        pj->left = preg;
        pj->right = NULL;
        pj->op = get;
		add_father(pj);
		if(Debug_jin){
			fz_treesearch(pj, cons);
			VG_(printf)("===Cons: %s\n", cons);
		}
		return;
	}
	
	del_dependency_tmp(tmp);
}

void assign(Dep* dep,Dep* left,Dep* right,OP op,UInt buop,UInt size)
{
    if(dep == NULL) return;
    dep->left = left;
    dep->right = right;
    dep->op = op;
    dep->buop = buop;
    dep->size = size;
    dep->father = 0;
	dep->dirty = Tdirty;
	if(dep->left != NULL) dep->left->father += 1;
	if(dep->right != NULL) dep->right->father += 1;
}
static VG_REGPARM(0) void helperc_load(Addr addr, Tmp tmp, Tmp tmp_to, UInt size) {
	if(is_max_bound()){return;}
	if(fengDepTmp){VG_(printf)("feng:entered helperc_load with addr:%llu\n",addr);}
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
    Dep* ltmp16;
    Dep* ltmp24;
    Dep* ltmp32;
    Dep* htmp16;
    Dep* htmp24;
    Dep* htmp32;
    Dep* andtmp;
    Dep* shrtmp;
    Dep* unoptmp1;
    Dep* unoptmp2;
    Dep* constmp1;
    Dep* constmp2;
    Dep* loadtmp;
    Dep* loadtmp1;
    Dep* loadtmp2;
    Dep* loadtmp3;
    Dep* loadtmp4;
    Dep* loadtmp5;
    Dep* loadtmp6;
    Dep* loadtmp7;
	varnode* item1=NULL;
	varnode* item2=NULL;
	varnode* item=NULL;
	addrtype* item3=NULL;
	Addr ptmp_addr=0;
	
#if defined(Debug_Luo)
    char buffer1[XXX_MAX_BUF];
    char *buf = buffer1;
#endif
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
		if(fengSizeHelpercFlag){VG_(printf)("feng:do helperc_load with size:%d\n",size);}
		if (size == 8) {
			for (i = 0; i < depaddr8.count; i++) {
				paddr8=getDep(&depaddr8,i);

				if (paddr8->value.addr != addr){
					continue;
				}

				if (paddr8->op != symbol && paddr8->op != store) break;



				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);
                pj->left = paddr8;
                pj->right = NULL;
                pj->op = load;
                add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
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

				if (paddr16->op != symbol && paddr16->op != store) break;

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);
				
				if(Debug_jin){
					fz_treesearch(pj, cons);
					VG_(printf)("===Cons: %s\n", cons);
				}

#ifdef FENG_AMD64
				//VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);
				//SPRINTF_CONS(*pj,
				//	"64to8(And64(Shr64(8Uto64(LDle:I8(%s)),0x%x:I64),0xff:I64))",
                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr16,NULL,load,0,8);
                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_8Uto64,64);
                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,64);
                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr64,64); 
                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xff;
                assign(constmp2,NULL,NULL,Iconst,0,64);
                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And64,64);
                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_64to8,8);
                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
#else
				//SPRINTF_CONS(*pj,
				//	"32to8(And32(Shr32(8Uto32(LDle:I8(%s)),0x%x:I32),0xff:I32))",
                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr16,NULL,load,0,8);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_8Uto32,32);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,32);

                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr32,32);


                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xff;
                assign(constmp2,NULL,NULL,Iconst,0,32);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And32,32);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_32to8,8);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
#endif // FENG_AMD64

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
				if (paddr32->op != symbol && paddr32->op != store) break;

				if(fengAddAddr){VG_(printf)("feng:in helper_load add dep 8\n");}

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);


#ifdef FENG_AMD64
                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr32,NULL,load,0,8);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_8Uto64,64);
                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,64);
                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr64,64);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xff;
                assign(constmp2,NULL,NULL,Iconst,0,64);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And64,64);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_64to8,8);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);

				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
#else
				//SPRINTF_CONS(*pj,
				//	"32to8(And32(Shr32(8Uto32(LDle:I8(%s)),0x%x:I32),0xff:I32))",
                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr32,NULL,load,0,8);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_8Uto32,32);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,32);

                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr32,32);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xff;
                assign(constmp2,NULL,NULL,Iconst,0,32);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And32,32);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_32to8,8);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
#endif // FENG_AMD64

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

				if (paddr64->op != symbol && paddr64->op != store) break;

				j = add_dependency_tmp(tmp_to, 8);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);


				VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);

				//SPRINTF_CONS(*pj,
				//	"64to8(And64(Shr64(8Uto64(LDle:I8(%s)),0x%x:I64),0xff:I64))",
                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr64,NULL,load,0,8);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_8Uto64,64);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,64);

                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr64,64);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xff;
                assign(constmp2,NULL,NULL,Iconst,0,64);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And64,64);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_64to8,8);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);

				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
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

				if (paddr16->op != symbol && paddr16->op != store) break;



				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);

				//SPRINTF_CONS(*pj, "LDle:I%d(%s)", size, paddr16->cons);
                pj->left = paddr16;
                pj->right = NULL;
                pj->op = load;
                add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);

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

				if (paddr32->op != symbol && paddr32->op != store) break;

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);


#ifdef FENG_AMD64
                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));            
                assign(loadtmp,paddr32,NULL,load,0,16);


                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_16Uto64,64);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->op = Iconst;
                assign(constmp1,NULL,NULL,Iconst,0,64);
				//VG_(printf)("Feng:helperc_load 64 shr64 with %d\n",8*pos);
				//SPRINTF_CONS(*pj,
				//	"64to16(And64(Shr64(16Uto64(LDle:I16(%s)),0x%x:I64),0xffff:I64))",
                
				shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr64,64);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xffff;
                assign(constmp2,NULL,NULL,Iconst,0,64);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And64,64);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_64to16,16);

                pj->left = unoptmp2;
                pj->right = NULL;

                pj->op = loadI;
				add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
#else
				//SPRINTF_CONS(*pj,
				//	"32to16(And32(Shr32(16Uto32(LDle:I16(%s)),0x%x:I32),0xffff:I32))",
                
				loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr32,NULL,load,0,16);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_16Uto32,32);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,32);

                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr32,32);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xffff;
                assign(constmp2,NULL,NULL,Iconst,0,32);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And32,32);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_32to16,16);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
#endif // FENG_AMD64

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
				if (paddr64->op != symbol && paddr64->op != store) break;

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);

                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr64,NULL,load,0,16);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_16Uto64,64);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,64);

                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr64,64);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xffff;
                assign(constmp2,NULL,NULL,Iconst,0,64);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And64,64);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_64to16,16);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj); 

				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
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

				if(fengAddAddr){VG_(printf)("feng:in helper_load add dep 16\n");}

				j = add_dependency_tmp(tmp_to, 16);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);

                loadtmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp1,getDep(&depaddr8,i),NULL,load,0,8);

                loadtmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp1,getDep(&depaddr8,a),NULL,load,0,8);

                pj->left = loadtmp1;
                pj->right = loadtmp2; 
                pj->op = cat;
				add_father(pj);

				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
				return;
			}
		}
		else if (size == 32) {


			for (i = 0; i < depaddr32.count; i++) {
				paddr32=getDep(&depaddr32,i);
				if (paddr32->value.addr != addr) {
					continue;
				}

				if (paddr32->op != symbol && paddr32->op != store) break;

				j = add_dependency_tmp(tmp_to, 32);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);

                pj->left = paddr32;
                pj->right = NULL;
                pj->op = load;
                add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);

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
				if (paddr64->op != symbol && paddr64->op != store) break;

				j = add_dependency_tmp(tmp_to, 32);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);

                loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(loadtmp,paddr64,NULL,load,0,32);

                unoptmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp1,loadtmp,NULL,unop,Iop_32Uto64,64);

                constmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp1->opval = 8*pos;
                assign(constmp1,NULL,NULL,Iconst,0,64);

                shrtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(shrtmp,unoptmp1,constmp1,binop,Iop_Shr64,64);

                constmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                constmp2->opval = 0xffffffff;
                assign(constmp2,NULL,NULL,Iconst,0,64);

                andtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(andtmp,shrtmp,constmp2,binop,Iop_And64,64);

                unoptmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                assign(unoptmp2,andtmp,NULL,unop,Iop_64to32,32);

                pj->left = unoptmp2;
                pj->right = NULL;
                pj->op = loadI;
				add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
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

					if(fengAddAddr){VG_(printf)("feng:in helper_load add dep 32\n");}
					j = add_dependency_tmp(tmp_to, 32);
					if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

					pj=getDep(&deptmp,j);

					//"Cat32(LDle:I8(%s),Cat24(LDle:I8(%s),Cat16(LDle:I8(%s),LDle:I8(%s))))"

                    loadtmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp1,getDep(&depaddr8,i),NULL,load,0,8);

                    loadtmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp2,getDep(&depaddr8,a),NULL,load,0,8);

                    ltmp16 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(ltmp16,loadtmp1,loadtmp2,cat,0,16);

                    loadtmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp3,getDep(&depaddr8,b),NULL,load,0,8);

                    ltmp24 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(ltmp24,ltmp16,loadtmp3,cat,0,24);

                    loadtmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp4,getDep(&depaddr8,c),NULL,load,0,8);

                    pj->left = ltmp24;
                    pj->right = loadtmp4;
                    pj->op = cat;
					add_father(pj);
					
					item1=getAddr(0,tmp_to,addr);
					//insertVar(list,item1);
					item3=getAddrType(item1);
					insertAddr(addrlist,item3);
					item2=getTypefromAddr(item1);
					insertVar(list,item2);
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

				if (paddr64->op != symbol && paddr64->op != store) break;

				j = add_dependency_tmp(tmp_to, 64);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

				pj=getDep(&deptmp,j);

                pj->left = paddr64;
                pj->right = NULL;
                pj->op = load;
                add_father(pj);
				
				item1=getAddr(0,tmp_to,addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
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

					if(fengAddAddr){VG_(printf)("feng:in helper_load add dep 64\n");}

					j = add_dependency_tmp(tmp_to, 64);
					if (j==INVALID_TMP){del_dependency_tmp(tmp_to);break;}

					pj=getDep(&deptmp,j);

                    loadtmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp,getDep(&depaddr8,i),NULL,load,0,8);

                    loadtmp1 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp1,getDep(&depaddr8,a),NULL,load,0,8);

                    ltmp16 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(ltmp16,loadtmp,loadtmp1,cat,0,16);

                    loadtmp2 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp2,getDep(&depaddr8,b),NULL,load,0,8);

                    ltmp24 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(ltmp24,ltmp16,loadtmp2,cat,0,24);

                    loadtmp3 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp3,getDep(&depaddr8,c),NULL,load,0,8);

                    ltmp32 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(ltmp32,ltmp24,loadtmp3,cat,0,32);

                    loadtmp4 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp4,getDep(&depaddr8,d),NULL,load,0,8);

                    loadtmp5 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp5,getDep(&depaddr8,e),NULL,load,0,8);

                    htmp16 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(htmp16,loadtmp4,loadtmp5,cat,0,16);

                    loadtmp6 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp6,getDep(&depaddr8,f),NULL,load,0,8);

                    htmp24 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(htmp24,htmp16,loadtmp6,cat,0,24);

                    loadtmp7 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));              
                    assign(loadtmp7,getDep(&depaddr8,g),NULL,load,0,8);

                    htmp32 = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                    assign(htmp32,htmp24,loadtmp7,cat,0,32);

                    pj->left = ltmp32;
                    pj->right = htmp32;
                    pj->op = cat;
					add_father(pj);
					
					item1=getAddr(0,tmp_to,addr);
					//insertVar(list,item1);
					item3=getAddrType(item1);
					insertAddr(addrlist,item3);
					item2=getTypefromAddr(item1);
					insertVar(list,item2);
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
				if (ptmp->op != symbol && ptmp->op != store){
					VG_(printf)("[-] Losing dependency\n");
                    if(tmp_to != INVALID_TMP)
                    {
                        pj = getDep(&deptmp,tmp_to);
                        if(pj->dirty == Tdirty)
                        {
							pj->father -= 1;
                            pj = getDep_for_malloc(&deptmp,tmp_to); 
							if(pj != NULL)
								pj->dirty = Fdirty;
                        }
                    }
			}
			else {
				if (fengAddTmp){VG_(printf)("Feng:helperc_load add tmp size=%d",ptmp->size);}

				ptmp=getDep(&deptmp,tmp);
				ptmp_addr=ptmp->value.addr;

				j = add_dependency_tmp(tmp_to, ptmp->size);
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to); return;} 

				pj=getDep(&deptmp,j);

                pj->left = ptmp;
                pj->right = NULL;
                pj->op = load;
                add_father(pj);
				
				item1=getAddr(tmp,tmp_to,ptmp_addr);
				//insertVar(list,item1);
				item3=getAddrType(item1);
				insertAddr(addrlist,item3);
				item2=getTypefromAddr(item1);
				insertVar(list,item2);
				item=getType(tmp_to,tmp,0,0);
				insertVar(list,item);

				return;
			}
		}
	}

	del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_rdtmp(Tmp tmp, Tmp tmp_to) {
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_rdtmp\n");}
	UInt j;

	Dep* ptmp=NULL;
	Dep* pj=NULL;
	varnode* item=NULL;
	addrtype* item1=NULL;

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		VG_(printf)("for S2E, returned\n");
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
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}

			pj=getDep(&deptmp,j);
			if(Debug_jin){
				fz_treesearch(pj, cons);
				// VG_(printf)("===Cons: %s\n", cons);
			}
            pj->left =  ptmp;
            pj->right = NULL;
            pj->op = rdtmp;
			add_father(pj); 
			
			item=getType(tmp_to,tmp,0,0);
			insertVar(list,item);
			item1=getAddrType(item);
			insertAddr(addrlist,item1);
			
			if(Debug_jin){
				fz_treesearch(pj, cons);
				VG_(printf)("===Cons: %s\n", cons);
			}
			return;
		}
	}

	del_dependency_tmp(tmp_to);
}


static VG_REGPARM(0) void helperc_unop(Tmp tmp, Tmp tmp_to, UInt size, UInt op) {
	//if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_unop with size:%d\n",size);}
	UInt j;
	char buffer[XXX_MAX_BUF];

	Dep* ptmp=NULL;
	Dep* pj=NULL;
	varnode* item=NULL;
	addrtype* item1=NULL;

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
			if(fengDepTmp){VG_(printf)("feng:in helperc_unop after if tmp:%d\n",tmp);}
			if (fengAddTmp){VG_(printf)("Feng:in helperc_unop add dep tmp size=%d",size);}
			ptmp=getDep(&deptmp,tmp);
			// We must use size, because some expressions change the dependency
			// size. For example: 8Uto32(a).

			j = add_dependency_tmp(tmp_to, size);
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
			pj=getDep(&deptmp,j);
			if(Debug_jin){
				fz_treesearch(pj, cons);
				VG_(printf)("===Cons: %s\n", cons);
			}
            pj->left = ptmp;
            pj->right = NULL;
            pj->buop = op;
            pj->op = unop;
			add_father(pj);
			
			item=getType(tmp_to,tmp,0,op);
			insertVar(list,item);
			item1=getAddrType(item);
			insertAddr(addrlist,item1);
			return;
		}
	}

	del_dependency_tmp(tmp_to);
}

#ifdef FENG_AMD64
static VG_REGPARM(0) void helperc_binop(Tmp tmp1, Tmp tmp2, BinopData *data, UInt tmp1_value, UInt tmp2_value) {
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_binop\n");}

	UInt tmp_to=data->tmp_to;
	UInt op=data->op;
	UInt end_size=data->end_size;
#else
static VG_REGPARM(0) void helperc_binop(Tmp tmp1, Tmp tmp2, Tmp tmp_to, UInt op, UInt tmp1_value, UInt tmp2_value, UInt end_size) {
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_binop\n");}
#endif // FENG_AMD64
	UInt j = 0;
	Bool b1 = False, b2 = False;
	char *p=NULL;
	char buffer[XXX_MAX_BUF]={0};
	char type;
	int size=0;

	Dep* ptmp1=NULL;
	Dep* ptmp2=NULL;
	Dep* pj=NULL;
    Dep* constmp = NULL;
	varnode* item1=NULL; 
	varnode* item2=NULL;
    varnode* item3=NULL;
	addrtype* item=NULL;

	if(fengSizeHelpercFlag){VG_(printf)("feng:binop size=%lld\n",end_size);}
	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj)
	{
		if(jinAssertFlag) VG_(printf)("for S2E returned!\n ");
		return;
	}
	if(just_module_sym && !is_in_func)
	{
		if(jinAssertFlag) VG_(printf)("binop returned!\n ");
		return;
	}
	if (tmp1 != INVALID_TMP || tmp2 != INVALID_TMP) {

		if (tmp1 != INVALID_TMP) {
			if (depend_of_tmp(tmp1)) {
				b1 = True;
			}
		}

		if (tmp2 != INVALID_TMP) {
			if (depend_of_tmp(tmp2)) {
				b2 = True;
			}
		}

		if (b1 || b2) {
			IROp_to_str(op, buffer);//CT,Feng:may return error - ok,pass
			//Feng:impossible op, pass it???
			/*if(buffer[0]<=11){
				return;
			}*/
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
				j = add_dependency_tmp(tmp_to, end_size);
				if(j == INVALID_TMP){del_dependency_tmp(tmp_to); return;}
				pj=getDep(&deptmp,j);

				ptmp1 = getDep(&deptmp,tmp1);
				ptmp2 = getDep(&deptmp,tmp2);

                pj->left = ptmp1;
                pj->right = ptmp2;
                pj->buop = op;
                pj->op = binop;
				add_father(pj);
				
				item1=getVarType(op,tmp1);
				insertVar(list, item1);
				item=getAddrType(item1);
				insertAddr(addrlist,item);
				item2=getVarType(op,tmp2);
				insertVar(list, item2);
				item=getAddrType(item2);
				insertAddr(addrlist,item);

				item3=getType(tmp_to,tmp1,tmp2,op);
				insertVar(list, item3);
				item=getAddrType(item3);
				insertAddr(addrlist,item);
			}
			else if (b1) {

				j = add_dependency_tmp(tmp_to, end_size);
				if(j == INVALID_TMP){del_dependency_tmp(tmp_to); return;}
				pj=getDep(&deptmp,j);
				ptmp1 = getDep(&deptmp,tmp1);

				#ifdef FENG_AMD64
								tmp2_value &= (0xffffffffffffffff >> (64 - size));
				#else
								tmp2_value &= (0xffffffff >> (32 - size));
				#endif // FENG_AMD64

                constmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep)); 
                constmp->op = Iconst; 
                constmp->left = NULL;
                constmp->right = NULL;
                constmp->opval = tmp2_value;
                constmp->size = size;  
				constmp->father = 0; 

                pj->left = ptmp1;
                pj->right = constmp;
                pj->buop = op;
                pj->op = binop;
				add_father(pj);
				
				item1=getVarType(op,tmp1);
				insertVar(list, item1);
				item=getAddrType(item1);
				insertAddr(addrlist,item);

				item3=getType(tmp_to,tmp1,0,op);
				insertVar(list, item3);
				item=getAddrType(item3);
				insertAddr(addrlist,item);
			}
			else if (b2) {
				j = add_dependency_tmp(tmp_to, end_size);
				if(j == INVALID_TMP){del_dependency_tmp(tmp_to); return;}
				pj=getDep(&deptmp,j);
				ptmp2 = getDep(&deptmp,tmp2);

				#ifdef FENG_AMD64
								tmp1_value &= (0xffffffffffffffff >> (64 - size));
				#else
								tmp1_value &= (0xffffffff >> (32 - size));
				#endif // FENG_AMD64

                constmp = (Dep*)VG_(malloc)("\x00",sizeof(Dep));  
                constmp->op = Iconst;
                constmp->left = NULL;
                constmp->right = NULL;
                constmp->opval = tmp1_value;
                constmp->size = size;               
				constmp->father = 0; 

                pj->right = ptmp2;
                pj->left = constmp;
                pj->buop = op;
                pj->op = binop;
				add_father(pj);
				
				item2=getVarType(op,tmp2);
				insertVar(list, item2);
				item=getAddrType(item2);
				insertAddr(addrlist,item);

				item3=getType(tmp_to,0,tmp2,op);
				insertVar(list, item3);
				item=getAddrType(item3);
				insertAddr(addrlist,item);
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
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_mux0x\n");}
	UInt j;
	Tmp t = (cond_value) ? exprX : expr0;

	Dep* ptmp=NULL;
	Dep* pj=NULL;
	varnode* item=NULL;
	addrtype* item1=NULL;

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
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}

			pj=getDep(&deptmp,j);

            pj->left = ptmp;
            pj->right = NULL;
            pj->op = mux0x;
			add_father(pj);
			
			item=getType(tmp_to,t,0,0);
			insertVar(list,item);
			item1=getAddrType(item);
			insertAddr(addrlist,item1);
			return;
		}
	}

	del_dependency_tmp(tmp_to);
}

static VG_REGPARM(0) void helperc_store(Addr addr, Tmp tmp) {
	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_store\n");}
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

			if(fengEnterHelper){VG_(printf)("feng:in helper_store with ptmp->%d\n",ptmp->size);}

			// XXX - we're asserting that values don't overlap
#ifdef FENG_AMD64
			//Feng:add for 64bit
			if (ptmp->size==64){
				j = add_dependency_addr(addr, 64);
				pj=getDep(&depaddr64,j);

                pj->left = ptmp;
                pj->right = NULL;
                pj->op = store;
				add_father(pj);

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

                pj->left = ptmp;
                pj->right = NULL;
                pj->op = store;
				add_father(pj);

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

                pj->left = ptmp;
                pj->right = NULL;
                pj->op = store;
				add_father(pj);

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
                pj->left = ptmp;
                pj->right = NULL;
                pj->op = store;
				add_father(pj);

				// if it overwrite a longer bits value like 32 or 16 bits value, just fragment them
			}
			else {
				VG_(printf)("deptmp[%d].size = %d\n", tmp, ptmp->size);
				//VG_(printf)("deptmp[%d].cons = %s", tmp, ptmp->cons);
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
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_exit\n");}


	unsigned long rbp;
	UInt linenum = 0,tid;
	Bool dirname_available;
	char filename[MAX_FILE_SIZE], dirname[MAX_FILE_SIZE];
	static char objname[MAX_FILE_SIZE];
    Check_objname(exit_record_list);  //delete repeat node
	Check_taken_node(exit_record_list,addr,taken);//Adam:check the exit node that has run

	if(is_max_bound()){return;}
	if(fengEnterHelper){VG_(printf)("feng:entered helperc_exit\n");}
	Bool named;
    Bool changed = False;
	Bool has_line_info;
    int i=0;
    char *query;
	//char *buf ;
	char *ret;
    char* constraint;
    int wrbit = 0;

	char* buf ;//= (char*)VG_(malloc)("\x00",XXX_MAX_BUF);

    int fd;
    SysRes res;

	named = VG_(get_objname)(addr, objname, MAX_FILE_SIZE);
	has_line_info = VG_(get_filename_linenum)(addr, filename, MAX_FILE_SIZE, dirname, MAX_FILE_SIZE, &dirname_available, &linenum); 
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
		i = 0;
        do{
            changed = simplify(getDep(&deptmp,guard));
            i++;
        }
		while(changed == True && i<100);
		query = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
		if(query == NULL) return ;
		firstcmp = True;
        ret = fz_solver(getDep(&deptmp,guard),query);
        if(ret != NULL )
        {
            constraint = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);  
			if(constraint == NULL) {VG_(free)(query); return;}    
			if(has_line_info){
				if(taken == 1){
					wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"(%s = 0b1)$0$%s$%d\n",query,filename, linenum);
				}
				else{
					wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"(~(%s) = 0b1)$0$%s$%d\n",query,filename, linenum);
            }
			}
			else{
				if(taken == 1){
					wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"(%s = 0b1)$0$None$0\n",query);
				}
				else{
					wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"(~(%s) = 0b1)$0$None$0\n",query);
            }
			}
			if(wrbit >= XXX_MAX_BUF - 1)
				VG_(printf)("This constraint has been give up\n");
			else{
		        // res=VG_(open)(cons_file_name,VKI_O_WRONLY|VKI_O_CREAT,VKI_S_IRWXU);
		        // if(!sr_isError(res)){
		            // fd = sr_Res(res);
		            // VG_(lseek)(fd,0,SEEK_END);
		            // VG_(write)(fd,constraint,wrbit);
		            // VG_(close)(fd);
		        // }
				// else{
					// VG_(printf)("------Open constraints.txt failed\n");
				// }
				VG_(printf)("Cons:%s\n",constraint);
			}

			VG_(free)(constraint);
        }
		VG_(free)(query);
		query = NULL;

		if(named){
			VG_(printf)("branch is in obj %s\n",objname);
		}
		if(count_bound(1)){
			//VG_(exit)(1);
		}
		return;
	}

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
	if(is_max_bound()){return;}

	UInt cond=data->cond;
	Tmp tmp_to=data->tmp_to;
	Tmp cc_dep1=data->cc_dep1;
	Tmp cc_dep2=data->cc_dep2;

	if(feng8664Flag){VG_(printf)("feng:entered helperc_amd64\n");}
	UInt j = 0;
	Bool b1 = False, b2 = False;
	char type = 'I';
	int size = 64;

	Dep* pcc1=NULL,*pcc2=NULL,*pj=NULL;
    Dep* tmpconst;
	varnode* item1=NULL;
	varnode* item2=NULL;
	varnode* item3=NULL;
	addrtype* item=NULL;

    int tmpsize;
    switch(cc_op%4){
        case 1: tmpsize = 8; break;
        case 2: tmpsize = 16; break;
        case 3: tmpsize = 32; break;
        case 0: tmpsize = 64; break;
    }

	// Jin add for S2E
	if(obj_num != 0 && !is_in_obj){
		return;
	}

	if(just_module_sym && !is_in_func){
		if(jinAssertFlag) VG_(printf)("amd64 calculate returned!\n ");
		return;
	}

	if (cc_dep1 != INVALID_TMP && depend_of_tmp(cc_dep1)) {
		b1 = True;
	}
	if (cc_dep2 != INVALID_TMP && depend_of_tmp(cc_dep2)) {
		b2 = True;
	}

		if (b1 || b2) {
			if (b1 && b2) {
				//pj1=getDep(&deptmp,j1);
				pcc1=getDep(&deptmp,cc_dep1);
				pcc2=getDep(&deptmp,cc_dep2);
				j = add_dependency_tmp(tmp_to, pcc2->size);	
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
				pj=getDep(&deptmp,j);
				
/*              SPRINTF_CONS(*pj2,
					"amd64g_calculate_condition(0x%x:I64,0x%x:I64,%s,%s)",
					cond, cc_op, pcc1->cons, pcc2->cons);
*/
                pj->left = pcc1;
                pj->right = pcc2;
                pj->op = amd64g;
                pj->opval = cc_op;
                pj->cond = cond;
				add_father(pj);
				
				item1=getVarType(cc_op,cc_dep1);
				insertVar(list, item1);
				item=getAddrType(item1);
				insertAddr(addrlist,item);
				item2=getVarType(cc_op,cc_dep2);
				insertVar(list, item2);
				item=getAddrType(item2);
				insertAddr(addrlist,item);
				
				item3=getType(tmp_to,cc_dep1,cc_dep2,cc_op);
				insertVar(list,item3);
				item=getAddrType(item3);
				insertAddr(addrlist,item);

			}
			else if (b1) {
				pcc1=getDep(&deptmp,cc_dep1);
				j = add_dependency_tmp(tmp_to, pcc1->size);	
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
				pj=getDep(&deptmp,j);



/*
				SPRINTF_CONS(*pj1,
					"amd64g_calculate_condition(0x%x:I64,0x%x:I64,%s,0x%x:%c%d)",
					cond, cc_op, pcc1->cons, cc_dep2_value, type, size);
				ppDepTmp(pj1);
*/

                tmpconst = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                tmpconst->left = NULL;
                tmpconst->right = NULL;
                tmpconst->op = Iconst;
                tmpconst->opval = cc_dep2_value;
				tmpconst->father = 0;
                switch(tmpsize){
                    case 8:  
                        if(cond == 4)tmpconst->size = 64;
                        else tmpconst->size = 8 ;
                        break;
                    case 16: tmpconst->size = 16;break;
                    case 32: tmpconst->size = 32;break;
                    case 64: tmpconst->size = 64;break;                    
                }

                pj->left = pcc1;
                pj->right = tmpconst;
                pj->op = amd64g;
                pj->opval = cc_op;
                pj->cond = cond;
				add_father(pj);
				
				item1=getVarType(cc_op,cc_dep1);
				insertVar(list, item1);
				item=getAddrType(item1);
				insertAddr(addrlist,item);
				
				item3=getType(tmp_to,cc_dep1,0,cc_op);
				insertVar(list,item3);
				item=getAddrType(item3);
				insertAddr(addrlist,item);
			}
			else if (b2) {

				pcc2=getDep(&deptmp,cc_dep2);		
				j = add_dependency_tmp(tmp_to, pcc2->size);	
				if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
				pj=getDep(&deptmp,j);

/*
				SPRINTF_CONS(*pj2,
					"amd64g_calculate_condition(0x%x:I64,0x%x:I64,0x%x:%c%d,%s)",
					cond, cc_op, cc_dep1_value, type, size, pcc2->cons);
*/
			//	ppDepTmp(pj2);

                tmpconst = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
                tmpconst->left = NULL;
                tmpconst->right = NULL;
                tmpconst->op = Iconst;
                tmpconst->opval = cc_dep1_value;
				tmpconst->father = 0;
                switch(tmpsize){
                    case 8:  
                        if(cond == 4)tmpconst->size = 64;
                        else tmpconst->size = 8 ;
                        break;
                    case 16: tmpconst->size = 16;break;
                    case 32: tmpconst->size = 32;break;
                    case 64: tmpconst->size = 64;break;                    
                }
                pj->left = tmpconst;
                pj->right = pcc2;
                pj->op = amd64g;
                pj->opval = cc_op;
                pj->cond = cond;
				add_father(pj);
				
				item2=getVarType(cc_op,cc_dep2);
				insertVar(list, item2);
				item=getAddrType(item2);
				insertAddr(addrlist,item);
				
				item3=getType(tmp_to,0,cc_dep2,cc_op);
				insertVar(list,item3);
				item=getAddrType(item3);
				insertAddr(addrlist,item);
			}
			data->used=False;
			return;
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
	if(is_max_bound()){return;}
	if(feng8664Flag){VG_(printf)("feng:entered helperc_x86\n");}
	UInt j = 0;
	Bool b1 = False, b2 = False;
	char type = 'I';
	int size = 32;
	Dep* pcc1=NULL,*pcc2=NULL,*pj=NULL;

    Dep* tmpconst;
	char buffer[1024]={0};
	varnode* item1=NULL;
	varnode* item2=NULL;
	varnode* item3=NULL;
	addrtype* item=NULL;

    int tmpsize;
    switch(cc_op%3)
    {
        case 1: tmpsize = 8; break;
        case 2: tmpsize = 16; break;
        case 0: tmpsize = 32; break;
    }

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

	if (cc_dep1 != INVALID_TMP && depend_of_tmp(cc_dep1)) {
		b1 = True;
	}
	if (cc_dep2 != INVALID_TMP && depend_of_tmp(cc_dep2)) {
		b2 = True;
	}

	if (b1 || b2) {
		if (b1 && b2) {

			pcc1=getDep(&deptmp,cc_dep1);
			pcc2=getDep(&deptmp,cc_dep2);	
			j = add_dependency_tmp(tmp_to, pcc2->size);	
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
			pj=getDep(&deptmp,j);
/*
			SPRINTF_CONS(*pj2,
				"x86g_calculate_condition(0x%x:I32,0x%x:I32,%s,%s)",
				cond, cc_op, pcc1->cons, pcc2->cons);
			ppDepTmp(pj2);
*/
            pj->left = pcc1;
            pj->right = pcc2;
            pj->op = x86g;
            pj->opval = cc_op;
            pj->cond = cond;
			add_father(pj);  

			item1=getVarType(cc_op,cc_dep1);
			insertVar(list, item1);
			item=getAddrType(item1);
			insertAddr(addrlist,item);
			item2=getVarType(cc_op,cc_dep2);
			insertVar(list, item2);
			item=getAddrType(item2);
			insertAddr(addrlist,item);
				
			item3=getType(tmp_to,cc_dep1,cc_dep2,cc_op);
			insertVar(list,item3);
			item=getAddrType(item3);
			insertAddr(addrlist,item);
		}
		else if (b1) {
			pcc1=getDep(&deptmp,cc_dep1);	
			j = add_dependency_tmp(tmp_to, pcc1->size);	
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
			pj=getDep(&deptmp,j);
/*
			SPRINTF_CONS(*pj1,
				"x86g_calculate_condition(0x%x:I32,0x%x:I32,%s,0x%x:%c%d)",
				cond, cc_op, pcc1->cons, cc_dep2_value, type, size);
			ppDepTmp(pj1);
*/                   
            tmpconst = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
            tmpconst->left = NULL;
            tmpconst->right = NULL;
            tmpconst->op = Iconst;
            tmpconst->opval = cc_dep2_value;
			tmpconst->father = 0;
            switch(tmpsize){
                case 8:  
                    if(cond == 4)tmpconst->size = 32;
                    else tmpconst->size = 8 ;
                    break;
                case 16: tmpconst->size = 16;break;
                case 32: tmpconst->size = 32;break;                   
            }

            pj->left = pcc1;
            pj->right = tmpconst;
            pj->op = x86g;
            pj->opval = cc_op;
            pj->cond = cond;
			add_father(pj);
			
			item1=getVarType(cc_op,cc_dep1);
			insertVar(list, item1);
			item=getAddrType(item1);
			insertAddr(addrlist,item);
		
			item3=getType(tmp_to,cc_dep1,0,cc_op);
			insertVar(list,item3);
			item=getAddrType(item3);
			insertAddr(addrlist,item);
		}
		else if (b2) {
				//pcc1=getDep(&deptmp,cc_dep1);
			pcc2=getDep(&deptmp,cc_dep2);
			j = add_dependency_tmp(tmp_to, pcc2->size);	
			if (j==INVALID_TMP){del_dependency_tmp(tmp_to);return;}
			pj=getDep(&deptmp,j);

/*
			SPRINTF_CONS(*pj2,
				"x86g_calculate_condition(0x%x:I32,0x%x:I32,0x%x:%c%d,%s)",
				cond, cc_op, cc_dep1_value, type, size, pcc2->cons);
			ppDepTmp(pj2);
*/                    
            tmpconst = (Dep*)VG_(malloc)("\x00",sizeof(Dep));
            tmpconst->left = NULL;
            tmpconst->right = NULL;
            tmpconst->op = Iconst;
            tmpconst->opval = cc_dep1_value;
			tmpconst->father = 0;
            switch(tmpsize){
                case 8:  
                    if(cond == 4)tmpconst->size = 32;
                    else tmpconst->size = 8 ;
                    break;
                case 16: tmpconst->size = 16;break;
                case 32: tmpconst->size = 32;break;                    
            }


            pj->left = tmpconst;
            pj->right = pcc2;
            pj->op = x86g;
            pj->opval = cc_op;
            pj->cond = cond;
            //pj2->size = 32; 
			add_father(pj);
			
			item2=getVarType(cc_op,cc_dep2);
			insertVar(list, item2);
			item=getAddrType(item2);
			insertAddr(addrlist,item);
				
			item3=getType(tmp_to,0,cc_dep2,cc_op);
			insertVar(list,item3);
			item=getAddrType(item3);
			insertAddr(addrlist,item);
		}

		return;
	}
	//add_dirty2(helperc_rdtmp,mkIRExpr_HWord(INVALID_TMP),mkIRExpr_HWord(tmp_to));
	del_dependency_tmp(tmp_to);
}












//Luo add divide by zero check

static VG_REGPARM(0) void helperc_div(Tmp tmp, UInt op,Addr addr) {
	if(helper2Disable){
		return;
	}

    char *p;
    char buffer[XXX_MAX_BUF];
    char type;
    UInt size;
    UInt linenum = 0;
    Bool dirname_available;
    char filename[1024], dirname[1024];
	int zero = 0;
	
	Bool changed = False;
	int i;
	Dep*ptmp;
	char* query;
	char* ret;
	int fd;
	SysRes res;
	int wrbit;
	char* constraint;
	if(depend_of_tmp(tmp)){
		ptmp = getDep(&deptmp,tmp);
		size = ptmp->size;
		switch(op){
			case Iop_DivU32:
			case Iop_DivU64:
			case Iop_DivModU64to32:
			case Iop_DivModU128to64:
			case Iop_DivS32:
			case Iop_DivS64:
			case Iop_DivModS64to32:
			case Iop_DivModS128to64:
				VG_(get_filename_linenum)(addr, filename, 1024, dirname, 1024, &dirname_available, &linenum);
				if( linenum != 0){
					do{
						changed = simplify(ptmp);
						i++;
					}while(changed == True && i<100);
					simplify(ptmp);				
					query = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
					if(query == NULL) return;
					firstcmp = True;			
					ret = fz_solver(ptmp,query);
					if(ret != NULL){
						// res=VG_(open)(cons_file_name,VKI_O_WRONLY|VKI_O_CREAT,VKI_S_IRWXU);
						// if(!sr_isError(res)){
							// fd = sr_Res(res);	
							switch(size){
								case 32:
									constraint = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
									wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"((IF (%s = 0h%08x) THEN (0b1) ELSE (0b0) ENDIF) = 0b1)$1$%s$%d\n",query,zero,filename,linenum);
									if(wrbit >= XXX_MAX_BUF -1) break;
									VG_(printf)("Cons:%s\n", constraint);
									VG_(printf)("detect fault in %s, fault type is 0, line num is %d\n",filename,linenum);
									// VG_(lseek)(fd,0,SEEK_END);
									// VG_(write)(fd,constraint,wrbit);
									VG_(free)(constraint);
									break;
								case 64:
									constraint = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
									wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"((IF (%s = 0h%016x) THEN (0b1) ELSE (0b0) ENDIF) = 0b1)$1$%s$%d\n",query,zero,filename,linenum);
									if(wrbit >= XXX_MAX_BUF -1) break;
									VG_(printf)("Cons:%s\n", constraint);
									VG_(printf)("detect fault in %s, fault type is 0, line num is %d\n",filename,linenum);	
									// VG_(lseek)(fd,0,SEEK_END);
									// VG_(write)(fd,constraint,wrbit);
									VG_(free)(constraint);
									break;
								default:
									VG_(free)(query);
									// VG_(close)(fd);
									query = NULL;
									return;
							}
							// VG_(close)(fd);
						// }
					}
					VG_(free)(query);
					query = NULL;
					 //VG_(printf)("[+] 0x%08x depending of input: if (CmpEQ%d(%s,0x0:I%d)) => 3\n",(UInt)addr,size,size,getDep(&deptmp,tmp)->cons,size);
					 //VG_(printf)("detect fault in %s, fault type is 0, line num is %d\n",filename,linenum);
				}

				break;
			default:
				break;
		}
    return;
	}
}


// add by Luo index out of range check and Null pointer access 
static VG_REGPARM(0) void helperc_pointer_arry(Tmp tmp, Addr current_addr) {

	if(helper2Disable){
		return;
	}
    //UInt a, b, c, i, j, pos;
    UInt linenum = 0;
    Bool dirname_available;
    char filename[1024], dirname[1024];
    UInt nips;

    //Addr ips[VG_(clo_backtrace_size)];
    //Addr sps[VG_(clo_backtrace_size)];
    //Addr fps[VG_(clo_backtrace_size)];
    //nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);
	
	Bool changed = False;
	int i;
	char* ret;
	Dep* ptmp;
	UInt cons_size;
	
	int fd;
	SysRes res;
	int wrbit;
	char* query;
	char* constraint;
    int zero = 0;

	UInt tid= VG_(get_running_tid)();
	populate_guest_args(tid);
    VG_(get_filename_linenum)(current_addr, filename, 1024, dirname, 1024, &dirname_available, &linenum);
	//if(linenum !=0 )VG_(printf)("entered helperc_pointer_arry: in line %d\n",linenum);
	if(linenum != 0)
	{
		if(depend_of_tmp(tmp))
		{
			ptmp = getDep(&deptmp,tmp);
			//if(ptmp->op != store && ptmp->op != symbol) return;
			cons_size = ptmp->size;
			query = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
			do{
				changed = simplify(ptmp);
				i++;
			}while(changed == True && i<100);
			ret = fz_solver(ptmp,query);
			if(ret != NULL)
			{
				// res=VG_(open)(cons_file_name,VKI_O_WRONLY|VKI_O_CREAT,VKI_S_IRWXU);
				// if(!sr_isError(res))
				// {
					// fd = sr_Res(res);	
					switch(cons_size)
					{
						case 32:
							constraint = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
							wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"((IF (%s = 0h%08x) THEN (0b1) ELSE (0b0) ENDIF) = 0b1)$1$%s$%d\n",query,zero,filename,linenum);
							if(wrbit >= XXX_MAX_BUF -1) break;
							// VG_(lseek)(fd,0,SEEK_END);
							// VG_(write)(fd,constraint,wrbit);
							VG_(printf)("Cons:%s\n", constraint);
							VG_(printf)("detect fault in %s, fault type is 1, line num is %d\n",filename,linenum);
							wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"((IF SBVLE(%s,0h%08x) THEN (0b1) ELSE (0b0) ENDIF) = 0b1)$1$%s$%d\n",query,guest_args[tid].args[3],filename,linenum);
							if(wrbit >= XXX_MAX_BUF -1) break;
							VG_(printf)("Cons:%s\n", constraint);
							VG_(printf)("detect fault in %s, fault type is 2, line num is %d\n",filename,linenum);
							// VG_(lseek)(fd,0,SEEK_END);
							// VG_(write)(fd,constraint,wrbit);
							VG_(free)(constraint);
							break;
						case 64:
							constraint = (char*)VG_(malloc)("\x00",XXX_MAX_BUF);
							wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"((IF (%s = 0h%016x) THEN (0b1) ELSE (0b0) ENDIF) = 0b1)$1$%s$%d\n",query,zero,filename,linenum);
							if(wrbit >= XXX_MAX_BUF -1) break;
							VG_(printf)("Cons:%s\n", constraint);
							VG_(printf)("detect fault in %s, fault type is 1, line num is %d\n",filename,linenum);
							// VG_(lseek)(fd,0,SEEK_END);
							// VG_(write)(fd,constraint,wrbit);
							wrbit = VG_(snprintf)(constraint,XXX_MAX_BUF,"((IF SBVLE(%s,0h%016x) THEN (0b1) ELSE (0b0) ENDIF) = 0b1)$1$%s$%d\n",query,guest_args[tid].args[3],filename,linenum);
							VG_(printf)("Cons:%s\n", constraint);
							VG_(printf)("detect fault in %s, fault type is 2, line num is %d\n",filename,linenum);
							// VG_(lseek)(fd,0,SEEK_END);
							// VG_(write)(fd,constraint,wrbit);
							VG_(free)(constraint);
							break;
						default:
							VG_(free)(query);
							// VG_(close)(fd);
							query = NULL;
							return;
					}
					// VG_(close)(fd);
				// }								
			}
			VG_(free)(query);
			query = NULL;
		}
	}

}


int is_in_function_list(const char *name,int *index)
{
	int i=0;
	for(i=0; i<function_info.count; i++)
	{
		if(VG_(strcmp)(function_info.func[i].name,name) == 0)
		{
			*index = function_info.func[i].danger_param;
			return 1;
		}
	}
	
	return 0;
}


static VG_REGPARM(0) void helperc_func(UInt addr,const char *func_name)
{
	int i,j,k, para_index;
	Dep* pdepaddr = NULL;
	UInt tid,linenum;
    UInt nips;
    Addr ips[VG_(clo_backtrace_size)];
    Addr sps[VG_(clo_backtrace_size)];
    Addr fps[VG_(clo_backtrace_size)];
    unsigned long *re;
	ULong ebp,addr_param1,tmp;
	Addr check_param;
    Bool dirname_available;
    char filename[MAX_FILE_SIZE], dirname[MAX_FILE_SIZE], fnname[100];
	static Bool  in_func = False;
	static unsigned long func_addr;
	Bool Symbol_ready = False, in_list = False;
	tid= VG_(get_running_tid)();
    populate_guest_args(tid);
    ebp = guest_args[tid].args[3] ;
    if (VG_(get_fnname_if_entry)(addr, fnname, sizeof(fnname)))
	{
		if( is_in_function_list(fnname,&para_index) )
		{
			stpcpy_flag = 0;
			nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);
			re = (void*)(sps[0]);
			func_addr = *re - 5;
			check_param = (Addr)(ebp);		//获取检测参数的地址
		}
	} 	
	else if( is_in_function_list(func_name,&para_index) )
	{
			stpcpy_flag ++;	
			nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);
			check_param = (Addr)(ebp);		//获取检测参数的地址
	}
	else	
			stpcpy_flag = -1;
	if( stpcpy_flag != 3 )					//仅在第二条指令处检测
	{
		return ;
	}
	nips = VG_(get_StackTrace)(VG_(get_running_tid)(), ips, VG_(clo_backtrace_size), sps, fps, 0);
	VG_(printf)("cheking~~~para is %d\n",para_index);
	if(para_index>6)
	{
		VG_(printf)("unhandled param index ,big than 6\n");
		return;
	}
#if defined(VGA_x86)
    populate_guest_args(tid);
    ebp = guest_args[tid].args[3] ;
	check_param = (Addr)(ebp + (para_index*4 + 4));		//获取检测参数的地址
	void **pvoid=(unsigned long long)check_param;
	for(k=0;k<depaddr8.count;k++)
	{
		pdepaddr=getDep(&depaddr8,k);
		if(*pvoid==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready==False) for(k=0;k<depaddr16.count;k++)	
	{
		pdepaddr=getDep(&depaddr16,k);
		if(*pvoid==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready==False) for(k=0;k<depaddr32.count;k++)
	{
		pdepaddr=getDep(&depaddr32,k);
		if(*pvoid==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready)
	{
		if (VG_(get_filename_linenum)(func_addr, filename, MAX_FILE_SIZE, dirname, MAX_FILE_SIZE, &dirname_available, &linenum) == True)
			VG_(printf)("dirty source found in %s, function name is:%s, line_num is:%d\n",filename,func_name,linenum);
		else
			VG_(printf)("dirty source found in none, line_num is:0 function name is:%s\n",func_name);
	}
#elif defined(VGA_amd64)
    populate_guest_args(tid);
	ebp =  guest_args[tid].args[3];
	if(para_index < 3)				//根据guest_args中各个寄存器的设定,这里参数的获取要分类
	{
		check_param = guest_args[tid].args[para_index];
	}
	else
	{
		check_param = guest_args[tid].args[para_index+2];
	}
	VG_(printf)(" check_param is %x ebp is %x\n",check_param,ebp);
	for(k=0;k<depaddr8.count;k++)
	{
		pdepaddr=getDep(&depaddr8,k);
		if(check_param==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready==False) for(k=0;k<depaddr16.count;k++)
	{
		pdepaddr=getDep(&depaddr16,k);
		if(check_param==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready==False) for(k=0;k<depaddr32.count;k++)
	{
		pdepaddr=getDep(&depaddr32,k);
		if(check_param==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready==False) for(k=0;k<depaddr64.count;k++)
	{
		pdepaddr=getDep(&depaddr64,k);
		if(check_param==pdepaddr->value.addr) Symbol_ready=True;
	}
	if(Symbol_ready)
	{
		VG_(printf)("func addr is %x\n",func_addr);
		if (VG_(get_filename_linenum)(func_addr, filename, MAX_FILE_SIZE, dirname, MAX_FILE_SIZE, &dirname_available, &linenum) == True)
			VG_(printf)("dirty source found in %s, function name is:%s, line_num is:%d\n",filename,func_name,linenum);
		else
			VG_(printf)("dirty source found in none, line_num is:0 function name is:%s\n",func_name);
	}
#endif 
    return;
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
    Dep *pj;

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
					//VG_(snprintf)(getDep(&depaddr8,j)->cons, XXX_MAX_BUF, "input(%d)",j);
                    if(j == INVALID_ADDR) return;
		            pj = getDep(&depaddr8,j);
                    pj->op = symbol;
                    pj->opval = j;
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
			//VG_(snprintf)(getDep(&depaddr8,j)->cons, XXX_MAX_BUF, "input(%d)",j);
            if(j == INVALID_ADDR) return;
            pj = getDep(&depaddr8,j);
            pj->op = symbol;
            pj->opval = j;
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













//Feng:change site
//Feng:warning, fuzz will crash here because of the differ between 32 and 64
//Feng:crashed here now we know
IRSB* fz_instrument ( VgCallbackClosure* closure,
					 IRSB* bb_in,
					 VexGuestLayout* layout,
					 VexGuestExtents* vge,
					 IRType gWordTy, IRType hWordTy )
{
	if(fengEnterHelper){
		VG_(printf)("feng:entered fz_instrument\n");
	}

	Addr current_addr = 0,inst_addr = 0;
	IRSB*   bb=NULL;
	Int     i=0, j=0;
	static Addr last_addr = 0;
    Bool named = False;
	Bool is_first_Imark = True;

	char fnname[MAX_FILE_SIZE];

	UInt linenum=0,tid;
	Bool dirname_available;
	char filename[MAX_FILE_SIZE],dirname[MAX_FILE_SIZE];	

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

		if(st->tag == Ist_IMark && just_module_sym){
			inst_addr = st->Ist.IMark.addr;
			//VG_(printf)("first Imark, addr is %08x\n",inst_addr);
			add_dirty2(helperc_get_ret,mkIRExpr_HWord(inst_addr),mkIRExpr_HWord(FZ_(clo_module_name)));
			add_dirty1(helperc_in_objs,mkIRExpr_HWord(inst_addr));
			//is_in_obj = is_in_obj_lists(inst_addr);
		}

		if (FZ_(verbose)) {
			VG_(printf)("-> ");
			ppIRStmt(st);
			VG_(printf)("\n");
		}

		if(True){
			//VG_(printf)("feng:trigger the debug\n");
			//VG_(exit)(1);//feng:debug
			
			//VG_(printf)("instrumented\n");
			switch (st->tag) {
				//Feng:crashed here now we know
				//Feng:imark标记
			case Ist_IMark:
				if(fengSwitch){VG_(printf)("feng:switch imark\n");}
				//判断是否退出函数
				current_addr = st->Ist.IMark.addr;
				/*
					if (VG_(get_fnname_if_entry)(st->Ist.IMark.addr, 
												fnname, sizeof(fnname))
					   && 0 == VG_(strcmp)(fnname, "strcpy"))
						VG_(printf)("first ins in strcpy addr is %x~\n",current_addr);
						*/
				add_dirty1(helperc_imark,mkIRExpr_HWord(current_addr));

				named = VG_(get_fnname)(current_addr, fnname, MAX_FILE_SIZE);
				if((VG_(strcmp)(fnname,"Symbolize_LLL")==0 ) && (named == True))
				{
					add_dirty1(helperc_catch,mkIRExpr_HWord(current_addr));
					VG_(printf)("\n++++++++++++++Symbolize has found~\n");
				}
				if(named == True)
				{
					VG_(strcpy)(FZ_(func_name),fnname);
					add_dirty2( helperc_func,mkIRExpr_HWord(current_addr),mkIRExpr_HWord(FZ_(func_name)) );
				}
				last_addr = current_addr;
				//VG_(printf)("instrumented\n");
				break;

				//Feng:put传递参数
			case Ist_Put:
				if(fengSwitch){VG_(printf)("feng:switch put\n");}
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
				if(fengSwitch){VG_(printf)("feng:switch wrtmp\n");}
				switch (st->Ist.WrTmp.data->tag) {
					//Feng:常量
				case Iex_Const:
					if(fengSwitch){VG_(printf)("feng:switch switch const\n");}
					to = st->Ist.WrTmp.tmp;
					add_dirty2(helperc_rdtmp,
						mkIRExpr_HWord(INVALID_TMP),
						mkIRExpr_HWord(to));
					break;

					//Feng:读临时
				case Iex_RdTmp:
					//if(fengSwitch){VG_(printf)("feng:switch switch rdtmp\n");}
					to = st->Ist.WrTmp.tmp;
					add_dirty2(helperc_rdtmp,
						mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.RdTmp.tmp),
						mkIRExpr_HWord(to));
					break;

					//Feng:扩展加载
				case Iex_Load:
					//Feng:error happened here
					//if(fengSwitch){VG_(printf)("feng:switch switch load\n");}
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
			            if(addr!=INVALID_ADDR){
						add_dirty2(helperc_pointer_arry,
                                       mkIRExpr_HWord(addr->Iex.RdTmp.tmp),
									   mkIRExpr_HWord(current_addr));
							}
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
	                    if(addr!=INVALID_ADDR){
						add_dirty2(helperc_pointer_arry,
							mkIRExpr_HWord(addr->Iex.RdTmp.tmp),
							mkIRExpr_HWord(current_addr));
						}						
                    }
#endif // FENG_AMD64
                    break;

                    //Feng:获取
                case Iex_Get:
                    if(fengSwitch){VG_(printf)("feng:switch switch get\n");}
                    j = st->Ist.WrTmp.data->Iex.Get.ty;
                    size = (j != Ity_I1) ? sizeofIRType(j) * 8 : 1;
                    add_dirty3(helperc_get,
                        mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Get.offset),
                        mkIRExpr_HWord(st->Ist.WrTmp.tmp),
                        mkIRExpr_HWord(size));
                    break;

                    //Feng:单元素操作
                case Iex_Unop:
                    if(fengSwitch){VG_(printf)("feng:switch switch unop\n");}
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
						if(fengSwitch){
							VG_(printf)("feng:switch switch binop\n");
						}
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
						/* Feng Jin. for 64bit to be tested
						data=&binopData[binopDataSite];
						while (data->used)
						{
							binopDataSite=(binopDataSite+1)%MAX_DATA_BUF_LEN;
							data=&binopData[binopDataSite];
						}
						data->used=True;
						binopDataSite=(binopDataSite+1)%MAX_DATA_BUF_LEN;
						*/


                    // this is a floating point operation, we don't care about it
                    // remove the dependency to the destination register
                    if (j == 1) {
                        if(fengAddDirty){VG_(printf)("feng:64 binop if adddir5 with argv5=data=0x%x and size=%d\n",data,data->end_size);}
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
					if(fengSwitch){VG_(printf)("feng:binop adddir7\n");}
					if(fengAddDirty){VG_(printf)("feng:64 binop if adddir5 with argv5=data=0x%x and size=%d\n",data,data->end_size);}
					//VG_(printf)("feng:64 binop if adddir5 with argv5=data=0x%x and size=%d\n",data,data->end_size);
#ifdef FENG_AMD64
					data->tmp_to=st->Ist.WrTmp.tmp;
					data->op=st->Ist.WrTmp.data->Iex.Binop.op;
					data->end_size=size;
					data->used=True;

					if(fengAddDirty){VG_(printf)("feng:64 binop if adddir5 with argv5=size=%d\n",size);}
					add_dirty5(helperc_binop,
						mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
						mkIRExpr_HWord(data),
						(e1->tag == Iex_RdTmp) ? assignNew(bb, e1) : mkIRExpr_HWord(e1->Iex.Const.con->Ico.U64),
						(e2->tag == Iex_RdTmp) ? assignNew(bb, e2) : mkIRExpr_HWord(e2->Iex.Const.con->Ico.U64));
						switch(st->Ist.WrTmp.data->Iex.Binop.op){
	                        case Iop_DivU32:
	                        case Iop_DivU64:
	                        case Iop_DivModU64to32:
	                        case Iop_DivModU128to64:
	                        case Iop_DivS32:
	                        case Iop_DivS64:
	                        case Iop_DivModS64to32:
	                        case Iop_DivModS128to64:
	                        if(e2->Iex.RdTmp.tmp != INVALID_TMP)
	                                    add_dirty3(helperc_div,
	                                               mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
	                                               mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Binop.op),
	                                               mkIRExpr_HWord(current_addr));
	                        break;
							default: 
								break;
                    }				
#else
                    if(fengAddDirty){VG_(printf)("feng:32 binop if adddir7 with argv7=size=%d\n",size);}
                    add_dirty7(helperc_binop,
                        mkIRExpr_HWord((e1->tag == Iex_RdTmp) ? e1->Iex.RdTmp.tmp : INVALID_TMP),
                        mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
                        mkIRExpr_HWord(st->Ist.WrTmp.tmp),
                        mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Binop.op),
                        (e1->tag == Iex_RdTmp) ? assignNew(bb, e1) : mkIRExpr_HWord(e1->Iex.Const.con->Ico.U32),
                        (e2->tag == Iex_RdTmp) ? assignNew(bb, e2) : mkIRExpr_HWord(e2->Iex.Const.con->Ico.U32),
                        mkIRExpr_HWord(size));
	                    switch(st->Ist.WrTmp.data->Iex.Binop.op)
						{
                        case Iop_DivU32:
                        case Iop_DivU64:
                        case Iop_DivModU64to32:
                        case Iop_DivModU128to64:
                        case Iop_DivS32:
                        case Iop_DivS64:
                        case Iop_DivModS64to32:
                        case Iop_DivModS128to64:
                        if(e2->Iex.RdTmp.tmp != INVALID_TMP)
                                    add_dirty3(helperc_div,
                                               mkIRExpr_HWord((e2->tag == Iex_RdTmp) ? e2->Iex.RdTmp.tmp : INVALID_TMP),
                                               mkIRExpr_HWord(st->Ist.WrTmp.data->Iex.Binop.op),
                                               mkIRExpr_HWord(current_addr));
                        break;
                        default: break;
                    }					
#endif // FENG_AMD64
                    break;

                    //Feng:多元操作
                case Iex_Mux0X:
                    if(fengSwitch){VG_(printf)("feng:switch switch muxox\n");}
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
					if(fengSwitch){VG_(printf)("feng:switch switch triop\n");}
					break;

					//Feng:
				case Iex_GetI:  // only used by floating point operations
					if(fengSwitch){VG_(printf)("feng:switch switch geti\n");}
					break;

					//Feng:call函数
					//Feng:why we need helper amd64 and helper x86 calculate condition
				case Iex_CCall:
					// XXX - x86g_calculate_condition
					// look at guest_x86_spechelper
					// encounterd when IR optimization failed
					//Feng:优化失败时会触发这一部分代码
					if(fengSwitch){VG_(printf)("feng:switch switch ccall\n");}
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
					if(fengSwitch){VG_(printf)("feng:switch switch others\n");}
					ppIRStmt(st);
					VG_(tool_panic)("Ist_WrTmp: data->tag not handled");
					break;
				}
				break;

				//Feng:数据存储
			case Ist_Store:
				if(fengSwitch){VG_(printf)("feng:switch store\n");}
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
				if(st->Ist.Store.addr->tag == Iex_RdTmp)
				{
					add_dirty2(helperc_pointer_arry,
						mkIRExpr_HWord(st->Ist.Store.addr->Iex.RdTmp.tmp),
						mkIRExpr_HWord(current_addr));
				}				
                break;
#else
                add_dirty2(helperc_store,
                    (st->Ist.Store.addr->tag == Iex_Const) ? mkIRExpr_HWord(st->Ist.Store.addr->Iex.Const.con->Ico.U32) : st->Ist.Store.addr,
                    mkIRExpr_HWord((data->tag == Iex_RdTmp) ? data->Iex.RdTmp.tmp : INVALID_TMP));
				if(st->Ist.Store.addr->tag == Iex_RdTmp)
				{
					add_dirty2(helperc_pointer_arry,
						mkIRExpr_HWord(st->Ist.Store.addr->Iex.RdTmp.tmp),
						mkIRExpr_HWord(current_addr));
				}                
				break;
#endif // FENG_AMD64

                //Feng:退出
            case Ist_Exit:
                if(fengSwitch){VG_(printf)("feng:switch exit\n");}
                tl_assert(st->Ist.Exit.guard->tag == Iex_RdTmp);
                add_dirty3(helperc_exit,
                    mkIRExpr_HWord(st->Ist.Exit.guard->Iex.RdTmp.tmp),
					mkIRExpr_HWord(current_addr),
					assignNew(bb, st->Ist.Exit.guard));
				break;

			case Ist_PutI:
				if(fengSwitch){VG_(printf)("feng:switch puti\n");}
				//VG_(printf)("oops, tag Ist_PutI not handled at 0x%08x\n", current_addr);
				break;
			case Ist_NoOp:
			case Ist_AbiHint:
			case Ist_MBE:
			case Ist_Dirty:
			default:
				if(fengSwitch){VG_(printf)("feng:switch others\n");}
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
