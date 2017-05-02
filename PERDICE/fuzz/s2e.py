#!/usr/bin/env python
# -*- coding: UTF-8 -*-
import sys
import os
import re
import cPickle as pickle
import subprocess
from config import *

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
    def __init__(self, number, filename, bytes=None):
        self.number = number
        self.filename = filename
        if not bytes:
            self.bytes = get_input(filename)
        else:
            fp = open(filename, 'w')
            fp.write(bytes)
            fp.close()
            self.bytes = bytes


def get_inputs(ninput):
            
    filename = '%s%d%s' % (PARAM['OUTPUT_FOLDER'], ninput, PARAM['EXTENSION'])
    new_input = Input(ninput, filename)
        
    return new_input

    
def score_cache(progname, progarg, input_file, taint_stdin=False):
    '''
    get the cache miss and branch mispredict of every source code line by cachegrind 
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

    
def score_input(input):

    fp=open("./info/"+input.filename.split('/')[-1],'r')
    line_score = pickle.load(fp)
    fp.close()

    score = 0
    for key in line_score.keys():
        score += line_score[key]
    
    return score    
    
    
def write_report(score, input):
    
    report_filename = '%s%s-report.txt' % (PARAM['REPORT_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    report_score = open(report_filename, 'a')
    
    report_str= "score:%d, input:%s\n" %(score, input.filename.split('/')[-1])
    report_score.write(report_str)
    report_score.close()    
    
    
def write_input(score, input):

    report_name = '%s%s-input_report.txt' % (PARAM['REPORT_FOLDER'], PARAM['PROGNAME'].split('/')[-1])
    report_score = open(report_name, 'a')   
    
    report_str = "score:%d, input:%s\n" %(score, input.filename.split('/')[-1])
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

def cache(target, worklist):

    firstExec = True
    
    while worklist:
        input = worklist.pop(0)
        score_cache(PARAM['PROGNAME'], PARAM['PROGARG'], input.filename, PARAM['TAINT_STDIN'])
        score = score_input(input)
        write_input(score,input)

        if firstExec:
            base_comparison = get_base(input)
            firstExec = False 
        else:
            base_comparison = base_update(input) 
        
        input_score = compute_score(base_comparison)
        write_report(input_score, input)
        write_lineinfo()
        
            
if __name__=='__main__':

    configfile = 'fuzz/settings.cfg' 
    worklist = []
    target = sys.argv[1]
    base_comparison = {}
    
    if not worklist:
        PARAM = get_config(configfile, target)
        input_seed = Input(0, PARAM['INPUT_FILE'], PARAM.get('MIN_BOUND', 0))
        worklist = [ input_seed ]
        
    for i in range(1,1001):
        input = get_inputs(i)
        worklist.append(input)

    cache(target, worklist) 
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                             
    
    
    
    
    
    
