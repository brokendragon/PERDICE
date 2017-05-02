#!/usr/bin/env python
# -*- coding: UTF-8 -*-
#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import getopt
import os
import re
import shutil
import subprocess
import sys
import cPickle as pickle

from config import *
from valgrind import *
from stp import *
from fault_checker import *
#from copy import deepcopy
#import session

is_first_expandExecution = True #indicates that it is the first expand_execution
base_comparison = {} #as the basic standard to compute the cache missing increment of every path
                     #its format:{(file, linenum): [score, x.txt]}

g_filename = {}  #存储每条路径对应的文件名，将其转化为数字存储
g_num = 0

test_round = 0

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
    def __init__(self, number, filename, bound, note, bytes=None):
        self.number = number
        self.filename = filename
        self.bound = bound
        self.note = note
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
    
    if CONSTRAINT_SUBSUMPTION:
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
    else:
        result = constraints
            
    # don't store stp formula, only query number !
    # stp.query can be modified if two queries depend of same variables with
    # different size (eg. LDle:I8(input(0)) AND LDle:I32(input(0)))
    #print new_c.pp()
    try:
        stp_formula = stp.from_expr_(new_c)
    except STPShiftError, error:
        if DEBUG_LAST:
            print '    ! %s. Skipping constraint!' % error,
        return result
    stp.query.append(stp_formula)
    result.append({ 'expr': new_c, 'n': len(stp.query) - 1 })
    
    return result


def compute_path_constraint(input_file):
    '''
    Get the path constraints for a given input
    
    @param input_file: input filename
    @type  input_file: str
    @return str list
    '''
    
    if not DEBUG_LAST:
        output_filename = run_valgrind(PARAM['PROGNAME'],
                                       PARAM['PROGARG'],
                                       input_file,
                                       sym_module,
                                       object_list,
                                       is_symbolize,
                                       taint_stdin=PARAM['TAINT_STDIN'],
                                       max_constraint=PARAM['MAX_BOUND'])
    else:
        output_filename = DEBUG_LAST

    pc = []
    fp = open(output_filename, 'r')
    for line in fp:
        m = re.match('\[\+\] 0x[0-9]+.* depending of input: if \((.*)\) => (\d)', line)
        if m:
            constraint = m.group(1)
            taken = bool(int(m.group(2)))
            pc.append((constraint, taken))
            #print '    + constraint\t%s' % (constraint[:100])    
        elif line == "If that doesn't help, please report this bug to: www.valgrind.org\n" or \
          ('oops, we depend of x86g_calculate_condition' in line and False):
            print '[-] Oops, a bug occured in Valgrind. See /tmp/valgrind_output.txt'
            sys.exit(-1)
        if len(pc) == PARAM['MAX_BOUND']:
            break
    fp.close()
   
    return pc
    
    
def score_cache(progname, progarg, input_file, taint_stdin=False):
    '''
    get the cache miss and branch mispredict counts of every source code line by cachegrind 
    and compute the score
    '''
    #global g_filename, g_num

    CACHEGRIND = './valgrind-r12356/build/bin/valgrind'
    arg_valgrind = [ CACHEGRIND, '--tool=cachegrind', '--branch-sim=yes', '--cachegrind-out-file=cachegrind-out']
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
  
        score = (value1+value2)*1+value3*20+value4*3
        #line_score[(g_filename[file],linenum)] = score
        line_score[(file,linenum)] = score
    
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
    
    #compare the score of every corresponding source line of input with the base_comparison, update the base_comparison with the lager score
    
    for key in line_score.keys():
        if key not in base_comparison.keys():
            base[key] = [line_score[key], input.filename.split('/')[-1]]
         
        elif line_score[key] > base_comparison[key][0]:
            base_comparison[key] = [line_score[key], input.filename.split('/')[-1]]
    
    base_comparison.update(base)
    
    return base_comparison
  
def get_increment(input):
    '''
    get the missing score increment of every path in line level compared 
    with the base_comparison
    '''
    
    path_cache_increment = []
    
    fp=open("./info/"+input.filename.split('/')[-1],'r')
    line_score = pickle.load(fp)
    fp.close()
    
    for key in line_score.keys():
        if key not in base_comparison.keys():
            increment = line_score[key]**2
            path_cache_increment.append(increment)
            
        elif line_score[key] > base_comparison[key][0]:
            increment = line_score[key]**2 - base_comparison[key][0]**2
            path_cache_increment.append(increment)
                
    return  path_cache_increment  
  
  
def compute_score(dict):

    # compute the total score of base_comparison after updating
    
    score = 0
    for key in dict.keys():
        score += dict[key][0]**2

    return score


def score_input(input):

    fp=open("./info/"+input.filename.split('/')[-1],'r')
    line_score = pickle.load(fp)
    fp.close()

    score = 0
    for key in line_score.keys():
        score += line_score[key]
    
    return score
    
    
def write_report(score, input):

    #report the base_comparison score of every symbolic execution
    
    report_filename = '%s%s-report.txt' % (PARAM['REPORT_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    report_score = open(report_filename, 'a')
    
    report_str= "score:%d, input:%s，increment:%d\n" %(score, input.filename.split('/')[-1], input.note)
    report_score.write(report_str)
    report_score.close()    


def write_input(score, input):

    report_name = '%s%s-input_report.txt' % (PARAM['REPORT_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    report_score = open(report_name, 'a')   
    
    report_str = "input:%s, score:%d\n" %(input.filename.split('/')[-1], score)
    report_score.write(report_str)
    report_score.close()
    

def write_lineinfo():

    #report the detail score of every source line

    global base_comparison
    
    report_name='%s%s-lineinfo.txt' % (PARAM['LINE_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    line_info = open(report_name, 'w')
    l = sorted(base_comparison.iteritems(),key=lambda d: d[1][0], reverse=True)
    for i in range(len(l)):
        report_str= "file:%s, linenum:%d, score:%d, input:%s\n" %(l[i][0][0], l[i][0][1], l[i][1][0], l[i][1][1])
        line_info.write(report_str)
    line_info.close()
    
    
def expand_execution(input, callbacks):
    '''
    Symbolically execute the program under test with that input, and generate
    new input computed from the expanded path constraints
    
    @param input: input to expand
    @type  input: Input instance
    @return new inputs
    '''
    
    global ninput
    global query_t,stp_t
    global start
    global total_t,cache_t
    
    callback_start_constraint_solver = callbacks[0]
    callback_constraint_solved = callbacks[1]
    callback_start_constraint_analyser = callbacks[2]
    callback_constraint_analysed = callbacks[3]
    callback_start_expander = callbacks[4]
    callback_expanded = callbacks[5]
    
    stp = STP()
    threshold = 0
    constraints = []
    child_inputs = []
    
    # compute path constraint
    if not callback_start_expander:
        print '[+] expanding execution with file %s, increment %d' % (input.filename.split('/')[-1], input.note)
    else:
        callback_start_expander(input)
    #compute pc time
    start_pc = time.time()
    pc = compute_path_constraint(input.filename)
    query_t = query_t + (time.time()-start_pc)
    
    if callback_expanded:
        callback_expanded()
    
    # parse valgrind's output and do constraint subsumption
    if not callback_start_constraint_analyser:
        #print '    * %d path constraints (bound: %d)' % (len(pc), input.bound)
        os.write(sys.stdout.fileno(), '       ')
    else:
        callback_start_constraint_analyser(len(pc))
    j = 1
    for (c, taken) in pc:
        if not taken:
            c = 'Not1(%s)' % c
        expr = parse_expr(c)
        if(expr==None):
            #print "in fuzz expr==None"
            continue
        constraints = contraint_subsumption(constraints, expr, stp) # is input.bound still consistent ?
        stp.first_cmp = True # XXX - dirty
        if not callback_constraint_analysed:
            os.write(sys.stdout.fileno(), '%s%d' % ('\b' * len(str(j - 1)), j))
        else:
            callback_constraint_analysed()
        j += 1
    if not callback_constraint_analysed:
        os.write(sys.stdout.fileno(), '%s' % '\b' * (len(str(j - 1)) + 6))
    
    #if len(constraints) != len(pc):
    #    print '    * %d path constraints (thanks to constraint subsumption)' % len(constraints)
    
    # all queries are computed, there will not be change anymore, so we can
    # safely create the constraints
    for c in constraints:
        c['stp'] = stp.query[c.pop('n')]
    stp.query = []
    
    if input.bound > len(constraints):
        return child_inputs
    elif input.bound > 0:
        # XXX - we should reuse previous stp.query
        stp.query = [ constraints[j]['stp'] for j in range(0, input.bound) ]
        stp.negate(len(stp.query) - 1)
    
    if callback_start_constraint_solver:
        callback_start_constraint_solver(len(constraints) - input.bound)
            
    # solve constraints
    for j in range(input.bound, len(constraints)):
        # if not callback_constraint_solved:
            # print '    * solving constraints [0:%d]' % j
        
        if stp.query:
            stp.negate(len(stp.query) - 1)
        
            if DEBUG_LAST:
                print '     ', constraints[j-1]['expr'].pp()
                print '     ', constraints[j-1]['stp'].pp()
            if DEBUG_LAST or VERIF_SOLVABLE:
                stp.execute()
                if not stp.interpret():
                    stp.query.pop()
                    print '    ! unsolvable constraint, skipping it !'
                    sys.exit(0)
                    if callback_constraint_solved:
                        callback_constraint_solved(None)
                    break
        
        #print '***', constraints[j]['expr'].pp()
        stp.query += [ constraints[j]['stp'] ]
        stp.negate(len(stp.query) - 1)
        
        start_stp = time.time()     #记录stp执行时间
        stp.execute()
        solution = stp.interpret()
        stp_t = stp_t + (time.time() - start_stp)
        
        if solution:
            bytes = list(input.bytes)
            for (byte, (value, size)) in solution.iteritems():
                for i in range(0, size / 8):
                    bytes[byte + i] = chr((value >> (i * 8)) & 0xff)
            bytes = ''.join(bytes)
            
            ninput += 1
            filename = '%s%d%s' % (PARAM['OUTPUT_FOLDER'], ninput, PARAM['EXTENSION'])
            new_input = Input(ninput, filename, j + 1, 0, bytes)
            child_inputs.append(new_input)
            #adb_push(new_input.filename)

            if not callback_constraint_solved:
                printable_bytes = re.sub('[^\w,;\.!\*&~"#\'\{\}\(\)\[\]]', '.', bytes[:10])
                # print '    * new_input (%d%s): %s' % (ninput, PARAM['EXTENSION'], printable_bytes)
            else:
                callback_constraint_solved(new_input)
        else:
            if callback_constraint_solved:
                callback_constraint_solved(None)
    
    if DEBUG_LAST:
        sys.exit(0)
    
    return child_inputs


def search(target, worklist, callbacks):    
    global ninput,test_round
    global is_first_expandExecution, base_comparison
    global start
    global total_t
    global stp_t
    global query_t, cache_t 
    
    callback_start_scoring = callbacks[6]
    callback_scored = callbacks[7]
    
    callback_start_check = callbacks[8]
    callback_checked = callbacks[9]
    
    while worklist:
        input = worklist.pop()
        #print '[+] input %s' % input.filename
        
        if is_first_expandExecution:
            #compute cachegrind time
            start_cache = time.time()
            score_cache(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['TAINT_STDIN'])
            cache_t = cache_t + (time.time()-start_cache)
            score = score_input(input)
            write_input(score, input)
            '''
            fp = open("./info/"+input.filename.split('/')[-1], 'r')
            base_comparison = pickle.load(fp)
            fp.close()
            '''
            base_comparison = get_base(input)
            is_first_expandExecution = False 
            
        else:
            base_comparison = base_update(input) 
        
        input_score = compute_score(base_comparison)
        write_report(input_score, input)
        write_lineinfo()
        
        child_inputs = expand_execution(input, callbacks)
        
        if not callback_start_check:
            print '[+] checking each new input'
        else:
            callback_start_check(len(child_inputs))
        for input in child_inputs:
            if not callback_checked:
                os.write(sys.stdout.fileno(), '    %s' % input.filename.split('/')[-1])
            fault = check(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['FAULT_CHECKER'], PARAM['TAINT_STDIN'])
            if not callback_checked:
                os.write(sys.stdout.fileno(), '\b' * (len(input.filename.split('/')[-1]) + 4))
                if fault:
                    print '[+] ' + ('@' * 75)
                    print '    Fault detected on file %s' % input.filename.split('/')[-1]
                    print '    ' + ('@' * 75)
            else:
                callback_checked(input.number, fault)
            if fault:
                filecopy = os.path.join(PARAM['CRASH_FOLDER'], os.path.basename(input.filename))
                shutil.copy(input.filename, filecopy)
        '''
        if not callback_start_scoring:
            print '[+] scoring each new input'
        else:
            callback_start_scoring(len(child_inputs))
        for input in child_inputs:
            if not callback_scored:
                os.write(sys.stdout.fileno(), '    %s' % input.filename.split('/')[-1])
            input.note = score(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['TAINT_STDIN'])
            #input.note = random_score()
            if not callback_scored:
                os.write(sys.stdout.fileno(), '\b' * (len(input.filename.split('/')[-1]) + 4))
            else:
                callback_scored(input)
        '''
        for input in child_inputs:
            start_cache = time.time()
            score_cache(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['TAINT_STDIN'])
            cache_t = cache_t + (time.time()-start_cache)
            score = score_input(input)
            write_input(score, input)
            
        worklist += child_inputs
        
        for input in worklist:
            source_increment = get_increment(input)
            input.note = 0                
            for k in range(0, len(source_increment)):
                input.note += source_increment[k]
            
        worklist.sort(key=lambda x: x.note)
        
        # this is couner-intuitive, but a lot of blocks are executed on
        # completely wrong images
        if PARAM['PROGNAME'] == '/usr/bin/convert':
            worklist.reverse()
        
        #symbolic execution 1000 rounds
        test_round += 1
        if test_round >= 1000 :
            sys.exit(0)
        
        #session.save(target, PARAM, ninput, worklist)

        
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

        if(time.time() - start > float(t*3600)):
            thread.interrupt_main()
            thread.exit()
         
            
if __name__ == '__main__':

    sym_module = ""
    object_list = ""
    is_symbolize = False;

    time_flag = False

    try:
        opts, args = getopt.getopt(sys.argv[1:], 'hsf:o:t:', ['help','symbolize','func=','obj=','time='])
    except getopt.GetoptError, err:
        print str(err)
        usage()
        sys.exit(-1)
        
    if len(args) != 1:
        usage()
        sys.exit(-1)
    
    configfile = 'fuzz/settings.cfg'
    worklist               = None
    DEBUG_LAST             = False
    VERIF_SOLVABLE         = False
    CONSTRAINT_SUBSUMPTION = False
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
            
    target = args[0]
    
    total_t = 0
    query_t = 0
    stp_t = 0
    cache_t = 0
    start = time.time()
    
    if not worklist:
        PARAM = get_config(configfile, target)
        ninput = PARAM.get('N', 0)
        input_seed = Input(0, PARAM['INPUT_FILE'], PARAM.get('MIN_BOUND', 0), 0)
        worklist = [ input_seed ]
    
    #thread.start_new_thread(timer,(5, True))
    try:
        search(target, worklist, [ None ] * 10)
    except KeyboardInterrupt:
        total_t = (time.time() - start)
        print "\nTotal running time is %s S\nSTP execute time is %s S\nValgrind query time is %s S\n"%(round(total_t,2),round(stp_t,2),round(query_t,2))

        print "Total test input is %d \n"%ninput
        thread.exit()
