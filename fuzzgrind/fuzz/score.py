import os
import random
import re
import subprocess
import sys


FUZZGRIND = './valgrind-r12356/build/bin/valgrind'


def random_score():
    return random.randint(0,1000000)
    
    
def score(progname, progarg, input_file, taint_stdin=False):
    
    arg_valgrind = [ FUZZGRIND, '--tool=cachegrind', '--branch-sim=yes' ]
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
        line_score[(file,linenum)] = score
    
    return line_score

  