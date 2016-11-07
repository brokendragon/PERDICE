# -*- coding: UTF-8 -*-
#   This file is part of Fuzzgrind.
#   Copyright (C) 2009 Gabriel Campana
#
#   This work is licensed under the terms of the GNU GPL, version 3.
#   See the LICENSE file in the top-level directory.


import os
import random
import re
import subprocess
import sys
import time
import cPickle as pickle

FUZZGRIND = './valgrind-r12356/build/bin/valgrind'



def score(progname, progarg, input_file, taint_stdin=False):
    arg_valgrind = [ FUZZGRIND, '--tool=lackey', '--basic-counts=yes']
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
    total = 0
    for line in stderr.split('\n'):
        m = re.match('==\d+==\s+total:\s+([\d,]+)', line)
        if m:
            total = int(  re.sub(',', '', m.group(1) ) )
            break
    #print total
    
    return total
	
	
def scoreMs(progname, progarg, input_file, taint_stdin=False):
    
    arg_valgrind = [ FUZZGRIND, '--tool=massif', '--massif-out-file=massif-output']
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
    p.wait()
    #print "run over, wait for data process"

    fp = open('massif-output', 'r')

    heap1 = 0
    heap2 = 0
    total = 0
    for line in fp:
        line = line.strip()
        
        m1 = re.match('total=([\d]+)', line)
        if m1:
            total = int(m1.group(1))
            break
 
    #total = heap1 + heap2
    fp.close()
    print "total:",total
    return total


if __name__ == "__main__":
    total = score('/usr/bin/convert', '/tmp/bla.jpg')
    print total
