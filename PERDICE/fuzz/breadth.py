#!/usr/bin/env python
# -*- coding: UTF-8 -*-
import getopt
import os
import re
import shutil
import subprocess
import sys
import time
import thread
import datetime
import hashlib
import cPickle as pickle


from config import *
from valgrind import *
from stp import *
from fault_checker import *

report = None #record output report
file_t = None #record the time used for every input

MAX_DEPTH = 5000
MIN_DEPTH = -1
test_round = 0

depth_stack = [] # 深度搜索栈
'''
深度栈格式
[0,1,2,3]
'''

pop_depth = MIN_DEPTH
path = []
fault_info = [] 
'''
路径上的漏洞约束信息，{'file': fault_file, 'type': fault_type, 'line_num': line_num}
'''
#index = 0

EXPR = 1

is_first_expandExecution = True #indicates that it is the first expand_execution
base_comparison = {} #as the basic standard to compute the cache missing increment of every path
                     #its format:{(file, linenum): [score, x.txt]}
                     
g_filename = {}  #存储每条路径对应的文件名，将其转化为数字存储
g_num = 0

  
def normal_handlePC(pc,c_index,c_vul_index,stp,constraints):
    '''
    @jin
    功能：
    参数： 
        pc          :   路径约束，compute_path_constraint 的返回值
        c_index     :   路径索引
        c_vul_index :   约束索引
        stp         :   stp实例
        constraints :   路径约束
    '''
    global depth_stack,vul_stack,pop_depth
    jin = 0
    j = 1
    
    for (c, taken) in pc:           #将二元约束改为一元约束，同时根据二元约束中约束的真假建立路径真值表
        
        if (taken==0 or taken==2):
            c = 'Not1(%s)' % c
            
        #start_v =  time.time()
        #print "before parse %s\n" % c
        expr = parse_expr(c)
        #print "after parse %s\n" % expr.pp()
        #print "parse_expr cost :",str(time.time()-start_v)
        jin = jin + 1
        #feng add
        if(expr==None):             #返回为空表明这个约束是无法处理的，我们将其从PC中移除
            #print "\na usefulness or unhandled constraints\nconstraints: %s\n" %(c)
            if (taken ==0 or taken==2 ):
                c = c[5:-1]
            xx = (c,taken)
            pc.remove(xx)
            continue

        constraints = contraint_subsumption(constraints, expr, stp)  #在STP中加入该约束
        #print "len(constraints): %d\n" % len(constraints)
        stp.first_cmp = True # XXX - dirty
        os.write(sys.stdout.fileno(), '%s%d' % ('\b' * len(str(j - 1)),j))
        j += 1
  
def depth_handlePC(pc,c_index,c_vul_index,stp,constraints):
    '''
    @jin
    功能：处理路径约束，将二元路径约束(c，taken)转为一元约束，同时对原始的约束表达式进行解析
    如果解析后的约束暂时无法处理，将其从PC中移除；否则，依据约束类型的不同，形成路径约束栈和
    漏洞约束栈，并将约束加入到STP实例中
    参数： 
        pc          :   路径约束，compute_path_constraint 的返回值
        c_index     :   路径索引
        c_vul_index :   约束索引
        stp         :   stp实例
        constraints :   路径约束
    '''
    global depth_stack,vul_stack,pop_depth
    jin = 0
    j = 1
    
    for (c, taken) in pc:           #将二元约束改为一元约束，同时根据二元约束中约束的真假建立路径真值表
        #print "index: %d\n" % jin
        if (taken==0 or taken==2):
            c = 'Not1(%s)' % c
            
        #start_v =  time.time()
        #print "before parse %s\n" % c
        expr = parse_expr(c)
        #print "after parse %s\n" % expr.pp()
        #print "parse_expr cost :",str(time.time()-start_v)
        jin = jin + 1
        #feng add
        if(expr==None):             #返回为空表明这个约束是无法处理的，我们将其从PC中移除
            #print "\na usefulness or unhandled constraints\nconstraints: %s\n" %(c)
            if (taken ==0 or taken==2 ):
                c = c[5:-1]
            xx = (c,taken)
            pc.remove(xx)
            continue

        if taken < 2:
            if pop_depth >= c_index:
                c_index = c_index + 1
            else:
                depth_stack.append(c_index)     #深度栈每次只将大于上次弹出深度的约束加入其中
                c_index = c_index + 1
        else :
            vul_stack.append((c_vul_index,c_index-1))
            c_vul_index = c_vul_index + 1

        if(EXPR):
            print("expr:",expr.pp())
        constraints = contraint_subsumption(constraints, expr, stp, taken)  #在STP中加入该约束
        #print "len(constraints): %d\n" % len(constraints)
        stp.first_cmp = True # XXX - dirty
        os.write(sys.stdout.fileno(), '%s%d' % ('\b' * len(str(j - 1)),j))
        j += 1


def runSymbolizeCheck(prog,prog_arg,input_file_name):
    '''
    使用Symbolize测试工具检测符号化功能产生的输入
    '''
    check_filename = run_valgrind_check(prog,prog_arg,input_file_name)

    fileObj = open(check_filename,'r')
    for eachLine in fileObj:
        if re.search("Process terminating", eachLine):
            return True
    return False

         
def get_input(filename):
    '''
    Load a file, and return it's content

    @param filename: name of the file to load
    @type  filename: str
    '''

    fp = open(filename)
    buf = fp.read()
    fp.close()

    return buf


class Input:
    def __init__(self, number, filename, bound, bytes=None):
        self.number = number
        self.filename = filename
        self.bound = bound
        if not bytes:
            self.bytes = get_input(filename)
        else:
            fp = open(filename, 'w')
            fp.write(bytes)
            fp.close()
            self.bytes = bytes


def constraint_implies(c1, c2):
    if c1.pp() == c2.pp():
        return True

    if c1.name == c2.name == 'unop' and c1.op.op == 'Not1':
        c1 = c1.arg
        c2 = c2.arg
        if c1.name == c2.name == 'binop' and (c1.op, c1.size) == (c2.op, c2.size):
            if c1.op.op == 'CmpLE32S':
                c1 = c1.arg1
                c2 = c2.arg1

                if c1.name == c2.name == 'binop' and \
                   (c1.op, c1.arg1.pp(), c1.size) == (c2.op, c2.arg1.pp(), c2.size):
                    binop = c1.op.op
                    if binop == 'Sub32' and c1.arg2.name == 'const' and c2.arg2.const == 'const' and \
                      c1.arg2.const.value < c2.arg2.const.value:
                        return True

    return False


def contraint_subsumption(constraints, new_c, stp):
    '''
    Check whether new_c definitely implies or is definitely implied by another
    constraint.

    @param constraints: constraint list
    @type  constraints: Iex list
    @param new_c:       new constraint
    @type  new_c:       Iex
    @param stp:
    @type  stp:         STP
    @param taken:
    @type  taken:       boolean
    '''
    # for  depth_first search ,constraint implies is necessary
    '''
    for c in constraints:
        # c => new_c
        if constraint_implies(c['expr'], new_c):
            return constraints

    result = []
    for c in constraints:
        # new_c => c
        if not constraint_implies(new_c, c['expr']):
            result.append(c)
        else:
            print 'new_c => c'
    '''
    result = constraints
    # don't store stp formula, only query number !
    # stp.query can be modified if two queries depend of same variables with
    # different size (eg. LDle:I8(input(0)) AND LDle:I32(input(0)))
    #print new_c.pp()
    try:
        stp_formula = stp.from_expr_(new_c)
    except STPShiftError, error:
        #if DEBUG_LAST:
        #print '    ! %s. Skipping constraint!' % error,
        return result
    stp.query.append(stp_formula)
    #add by jin
    # taken < 2 indicates that the constraints is branch constraints, otherwise is the vul constraints
    # added taken flag to distinguish the constraints kind
    result.append({ 'expr': new_c, 'n': len(stp.query) - 1 })

    return result


def score_cache(progname, progarg, input_file, taint_stdin=False):
    
    #global g_filename, g_num
    
    FUZZGRIND = './valgrind-r12356/build/bin/valgrind'
    arg_valgrind = [ FUZZGRIND, '--tool=cachegrind', '--branch-sim=yes', '--cachegrind-out-file=cachegrind-out' ]
    arg_prog = [ progname, input_file ]
    
    if not progarg:
        arg_prog = [ progname ]
        if not taint_stdin:
            arg_prog.append(input_file)
    else:
        progarg = re.sub('\$input', input_file, progarg)
        progarg = progarg.split()
        arg_prog = [ progname ] + progarg

    if not taint_stdin:
        stdin = None
    else:
        stdin = open(input_file, 'r')
    
    p = subprocess.Popen(arg_valgrind + arg_prog, stdin=stdin, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    stdout, stderr = p.communicate()

    line_score = {}

    for lines in stderr.split('*****'):
        
        for line in lines.split('\n'):
            m1 = re.match('file:\s+(.*)', line)
            m2 = re.match('==\d+==\s+line:\s+([\d,]+)', line)
            m3 = re.match('==\d+==\s+I1\s+misses:\s+([\d,]+)', line)
            m4 = re.match('==\d+==\s+D1\s+misses:\s+([\d,]+)', line)
            m5 = re.match('==\d+==\s+LL misses:\s+([\d,]+)', line)
            m6 = re.match('==\d+==\s+Mispredicts:\s+([\d,]+)', line)
            if m1:
                file = m1.group(1)
            if m2:
                linenum = int(re.sub(',', '', m2.group(1)))
            if m3:
                value1 = int(re.sub(',', '', m3.group(1)))
            if m4:
                value2 = int(re.sub(',', '', m4.group(1)))
            if m5:
                value3 = int(re.sub(',', '', m5.group(1)))
            if m6:
                value4 = int(re.sub(',', '', m6.group(1)))
                break
        '''    
        if file not in g_filename.keys():
            g_filename[file] = g_num
            g_num += 1
        '''    
        score = (value1+value2)*1+value3*20+value4*3
        #line_score[(g_filename[file],linenum)] = score
        line_score[file,linenum] = score
    
    info_file="./info/"+input_file.split('/')[-1]
    
    info_fp = open(info_file, 'w')
    pickle.dump(line_score,info_fp)
    info_fp.close()

  
def get_base(input):

    #get the first base_comparison
    global base_comparison
    
    fp=open("./info/"+input.filename.split('/')[-1],'r')
    line_score = pickle.load(fp)
    fp.close()
    
    for key in line_score.keys():
        base_comparison[key] = [line_score[key], input.filename.split('/')[-1]]
 
    return base_comparison
    
    
def base_update(input):

    #update the base_comparison after the input selected
    global base_comparison

    base = {}
    fp=open("./info/"+input.filename.split('/')[-1],'r')
    line_score = pickle.load(fp)
    fp.close()
    
    for key in line_score.keys():
        if key not in base_comparison.keys():
            base[key] = [line_score[key], input.filename.split('/')[-1]]
         
        if key in base_comparison.keys() and line_score[key] > base_comparison[key][0]:
            base_comparison[key] = [line_score[key], input.filename.split('/')[-1]]
    
    base_comparison.update(base)
    
    return base_comparison
  
def compute_score(base_comparison):

    score = 0
    for key in base_comparison.keys():
        score += base_comparison[key][0]**2

    return score
    
  
def write_report(score, input):
    
    report_filename = '%s%s-report.txt' % (PARAM['REPORT_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    report_score = open(report_filename, 'a')
    
    report_str= "score:%d, input: %s\n" %(score, input.filename.split('/')[-1])
    report_score.write(report_str)
    report_score.close()
    
    
def write_lineinfo():
    global base_comparison
    
    report_name='%s%s-lineinfo.txt' % (PARAM['LINE_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    line_info = open(report_name, 'w')
    l = sorted(base_comparison.iteritems(),key=lambda d: d[1][0], reverse=True)
    for i in range(len(l)):
        report_str= "file:%s, linenum:%d, score:%d, input:%s\n" %(l[i][0][0], l[i][0][1], l[i][1][0], l[i][1][1])
        line_info.write(report_str)
    line_info.close()  
    
  
def compute_path_constraint(input_file):
    '''
    Get the path constraints for a given input

    @param input_file: input filename
    @type  input_file: str
    @return str list
    '''
    # global test_index
    # global fault_info

    #pos = 0
    #'%s%d%s' % (PARAM['OUTPUT_FOLDER'], ninput, PARAM['EXTENSION'])
    # str_file_name = '%s%d%s.txt'%(PARAM['OUTPUT_FOLDER'],test_index,'_path')
    # test_path_file = open(str_file_name,'wa')

    output_filename = run_valgrind(PARAM['PROGNAME'],
                                       PARAM['PROGARG'],
                                       input_file,
                                       sym_module,
                                       object_list,
                                       is_symbolize,
                                       taint_stdin=PARAM['TAINT_STDIN'],
                                       max_constraint=PARAM['MAX_BOUND'])
    '''
    print 'sym_module',sym_module
    print 'object-list',object_list
    print 'output_file',output_filename
    print 'is_symbolize',is_symbolize
    '''

    pc = []
    fp = open(output_filename, 'r')
    # line_count = 1;
    # path_constraint = []
    # fault_info = []

    for line in fp:
        m = re.match('\[\+\] 0x[0-9]+.* depending of input: if \((.*)\) => (\d)', line)
        if m:
            #print "pc: ",line
            constraint = m.group(1)
            taken = int(m.group(2))
            pc.append((constraint, taken))
            #print '    + constraint\t%s' % (constraint[:100])
        elif line == "If that doesn't help, please report this bug to: www.valgrind.org\n" or \
          ('oops, we depend of x86g_calculate_condition' in line and False):
            print '[-] Oops, a bug occured in Valgrind. See /tmp/valgrind_output.txt'
            sys.exit(-1)
      
        if len(pc) == PARAM['MAX_BOUND']:
            break
            
    fp.close()
        
    # for cons in pc:
        # print "cons:",cons
    return pc


def expand_execution(input, callbacks):
    '''
    Symbolically execute the program under test with that input, and generate
    new input computed from the expanded path constraints

    @param input: input to expand
    @type  input: Input instance
    @return new inputs
    '''

    global ninput, pop_depth, path, vul_input_num
    global query_t,stp_t,report
    global start
    global total_t
    global test_index
    #global vul_stp_cache,expected_path_cons,current_path_cons
    global file_t

    stp = STP()
    threshold = 0
    constraints = []
    child_inputs = []

    # compute path constraint
    #add by Luo

    print '[+] expanding execution with file %s ' % input.filename.split('/')[-1]
    #start_v =  time.time()
    pc = compute_path_constraint(input.filename)
    #query_t = query_t + (time.time() - start_v)
    #print "compute_path_constraint time is ",str(time.time()-start_v)

    # parse valgrind's output and do constraint subsumption

    os.write(sys.stdout.fileno(), '       ')

    j = 1
    path_temp = [] #print the path of the current test input

    c_index = 0;
    c_vul_index = 0;
    
    #处理解析约束，建立路径约束栈和漏洞约束栈
    #depth_handlePC(pc,c_index,c_vul_index,stp,constraints)
    normal_handlePC(pc,c_index,c_vul_index,stp,constraints)

    #index += 1
    #print '    * %d path constraints' % (c_index)
    #print '    * %d vul constraints' % (c_vul_index)
    os.write(sys.stdout.fileno(), '%s' % '\b' * (len(str(j - 1)) + 6))

    # all queries are computed, there will not be change anymore, so we can
    # safely create the constraints
    for c in constraints:
        c['stp'] = stp.query[c.pop('n')]
        
    if depth > len(constraints):
        return child_inputs
    #stp.query = []
    #print 'len(depth_stack)',len(depth_stack),"\n"
    
    for index in range(depth, len(constraints)):
        
        stp.query = []              #置空STP query 根据栈深度加入本次求解约束
        for k in range(0, index+1):
            # try:
                # stp.query += [ constraints[k]['stp'] ]
            # except IndexError:
                # print "k %d\n" %k
                # raise
            stp.query += [ constraints[k]['stp'] ]
        if len(stp.query) == 0:
            continue
            
        stp.negate(len(stp.query) - 1)
        #print "stp query negate:",stp.pp()

        start_stp = time.time()     #记录stp执行时间
        stp.execute()
        solution = stp.interpret()
        stp_t = stp_t + (time.time() - start_stp)

        if solution:

            #add by Luo 用于Symbolize保存符号变量的值
            fp1=open(input.filename)
            #print "name : %s"  %(input.filename)

            bytes=fp1.read()
            bytes=list(bytes)
            #print "solution: ",solution.iteritems()
            for (byte, (value, size)) in solution.iteritems():
                #print byte,value,size
                for i in range(0, size / 8):
                    bytes[byte + i] = chr((value >> (i * 8)) & 0xff)
                    #bytes.append(chr((value >> (i * 8)) & 0xff))
            bytes = ''.join(bytes)

            ninput += 1
            filename = '%s%d%s' % (PARAM['OUTPUT_FOLDER'], ninput, PARAM['EXTENSION'])
            new_input = Input(ninput, filename, j + 1, bytes)
            child_inputs.append([index,new_input])

            printable_bytes = re.sub('[^\w,;\.!\*&~"#\'\{\}\(\)\[\]]', '.', bytes[:])

    return child_inputs


def search(target, worklist, callbacks):
    global ninput,test_index,vul_input_num, depth, test_round
    global run_times_flag
    global start
    global total_t
    global stp_t
    global query_t
    global file_t,report
    global is_first_expandExecution, base_comparison
    test_index = 0


    run_times_flag = 1
    fp3=open('run_times.txt','w')
    fp3.seek(0)
    fp3.write(str(run_times_flag))

    # report = open('./analysis/%s-report'%(PARAM['PROGNAME'][9:]),"w")

    # if report == None :
        # print "report file create failed\n"

    while len(worklist) > 0:
        keys = worklist.keys()
        keys.sort()
        input = None
        for k in keys:
            if worklist[k] != []:
                input = worklist[k].pop(0) 
                depth = k + 1
                break
            else:
                del worklist[k]    

        if input == None:
            break

        score_cache(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['TAINT_STDIN'])
        
        if is_first_expandExecution:
            
            base_comparison = get_base(input)
            is_first_expandExecution = False 
            
        else:
            base_comparison = base_update(input) 
        
        input_score = compute_score(base_comparison)
        write_report(input_score, input)
        write_lineinfo()
        
        child_inputs = expand_execution(input, callbacks)

        #feng add
        if(child_inputs==None):
            continue

        print '[+] checking each new input\n'
        inputs = []
        for k in range(0,len(child_inputs)):
            inputs.append(child_inputs[k][1])
        for input in inputs:
            os.write(sys.stdout.fileno(), '    %s' % input.filename.split('/')[-1])
            #print "isSymb:::: ",is_symbolize
            if not is_symbolize:
                fault = check(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['FAULT_CHECKER'], PARAM['TAINT_STDIN'])
            else:
                fault = runSymbolizeCheck(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename)
            os.write(sys.stdout.fileno(), '\b' * (len(input.filename.split('/')[-1]) + 4))
            if fault:
                print '[+] ' + ('@' * 75)
                print '    Fault detected on test input %s' % input.filename.split('/')[-1]
                print '    ' + ('@' * 75)
            if fault:
                filecopy = os.path.join(PARAM['CRASH_FOLDER'], os.path.basename(input.filename))
                shutil.copy(input.filename, filecopy)
                
        for k in range(0, len(child_inputs)):
            j = child_inputs[k][0]
            keys = worklist.keys()
            if not j in keys:
                worklist[j] = [ child_inputs[k][1] ]
            else:
                worklist[j].append(child_inputs[k].pop())
        
        test_round += 1
        if test_round >= 1000 :
            sys.exit(0)
            
        run_times_flag += 1
        if run_times_flag > 1:
            run_times_flag = 1
        #print 'run_times : %d ' % run_times_flag
        fp3.seek(0)
        fp3.write(str(run_times_flag))

    fp3.close()
    #file_t.close()
    #report.close()
    os.remove('run_times.txt')

    total_t = (time.time() - start)

    print "\nTotal running time is %s S\nSTP execute time is %s S\nValgrind query time is %s S\n"%(round(total_t,2),round(stp_t,2),round(query_t,2))

    print "Total test input is %d \n" % ninput
    print "Total vul input is %d \n" % vul_input_num
def usage():
    print 'Usage: %s <parameter name> prog_name \n ' % sys.argv[0]

    print '  -h --help\t\tshow summary of options'
    print '  -f --func=\t\tselect a specific function to symbolic execute'
    print '  -o --obj=\t\tconstraint the symbolic execution in some choosen objects, this must be used simultaneously with the -f option'
    print '---Note:different objects split with "," like 1.so,2.so\n'
    print '  -t --time=\t\tspecify the running time,if this parameter is set, the execution will stop after the given time.'

    sys.exit(0)


def timer(t,flag):
    if (not flag):
        thread.exit()
    start = time.time()
    while(True):
        time.sleep(2)
        #print "#######\ntime.time() - start %f : t is %d" %(time.time() - start,(int)(t))
        if(time.time() - start > float(t)):
            thread.interrupt_main()
            thread.exit()

if __name__ == '__main__':

    sym_module = ""
    object_list = ""
    is_symbolize = False;
    run_time = 0

    time_flag = False

    try:
        opts, args = getopt.getopt(sys.argv[1:], 'hsf:o:t:', ['help','symbolize','func=','obj=','time='])
    except getopt.GetoptError, err:
        print str(err)
        usage()
        sys.exit(-1)

    if(len(args) != 1):
        usage()
        sys.exit(-1)

    target = args[0]

    for name,value in opts:
        if name in ('-f',"--func"):
            sym_module = value
            print "func ",sym_module
            continue
        if name in ('-o','--obj'):
            object_list = value
            print "obj_lists",object_list
            continue
        if name in ('-h','--help'):
            usage()
            sys.exit(-1)
            continue
        if name in ('-s','--symbolize'):
            is_symbolize = True
            continue
        if name in ('-t','--time'):
            time_flag = True
            run_time = value
            print "time ",run_time
            print "flag ",time_flag
            continue
        else:
            assert False,'unhandled options!'
    if sym_module == "" and object_list != "":
        print "you need to use -f to specify the function if you want to use -o/--obj option!"
        sys.exit(-1)

    configfile = 'fuzz/settings.cfg'
    worklist               = None


    total_t = 0
    query_t = 0
    stp_t = 0
    vul_input_num = 0
    start = time.time()

    if not worklist:
        PARAM = get_config(configfile, target)
        ninput = PARAM.get('N', 0)
        input_seed = Input(0, PARAM['INPUT_FILE'], PARAM.get('MIN_BOUND', 0))
        worklist ={-1:[ input_seed ] }
        
    thread.start_new_thread(timer,(run_time ,time_flag))
    try:
        search(target, worklist, [ None ] * 10)
    except KeyboardInterrupt:
        total_t = (time.time() - start)
        print "\nTotal running time is %s S\nSTP execute time is %s S\nValgrind query time is %s S\n"%(round(total_t,2),round(stp_t,2),round(query_t,2))

        print "Total test input is %d \n"%ninput
        print "Total vul input is %d \n" % vul_input_num
        thread.exit()


    # if(report!=None):
        # report.close();
