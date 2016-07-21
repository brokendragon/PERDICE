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




from config import *
from valgrind import *
from stp import *
from fault_checker import *

report = None #record output report
file_t = None #record the time used for every input

MAX_DEPTH = 5000
MIN_DEPTH = -1

depth_stack = [] # 深度搜索栈
'''
深度栈格式
[0,1,2,3]
'''
vul_stack = []   # 漏洞约束栈
'''
格式:包括两个域，第一个代表了漏洞约束的索引，第二个代表了该索引位于哪一个分支约束之后，如果为-1表明这个漏洞约束之前
没有分支约束
eg：
[[0,-1],[1,1][2,3]]
'''

vul_stp_cache = {}
'''
漏洞约束求解缓存，记录了某个路径下对应的解文件名
'''
#期望的执行路径、当前执行路径 stp 表达式列表
expected_path_cons = []
current_path_cons = []

pop_depth = MAX_DEPTH#
path = []
fault_info = []	
'''
路径上的漏洞约束信息，{'file': fault_file, 'type': fault_type, 'line_num': line_num}
'''
index = 0

EXPR = 0


def solve_path_vul(constraints,stp,input,vinput,ninput):
	'''
	@jin
	函数功能：对漏洞约束进行求解
	参数：
		constraints	:	路径约束和漏洞约束
		stp			:	STP类实例，在解析约束过程中将约束对应的stp表达式也加入到了stp query
		input		：	输入用例文件
		vinput		:	漏洞用例个数
		ninput		:	全局用例个数
	'''
	global fault_info,vul_stack,is_symbolize,vul_input_num
	
	
	m = 0
	k = len(vul_stack)
	while m < k:		#单个漏洞约束逐一求解
		stp.query = []  #empty the stp query after a stp execution
		j = vul_stack[m][0] + vul_stack[m][1] + 1
		for c in range(0,j):
			if constraints[c]['taken'] == 0:        # 0 indicates that this constraint is a branch constraint ,not vul constraint
				stp.query += [constraints[c]['stp']]
			else:
				stp.query += [constraints[c]['stp']]# all the other vul constraint should be negate here!
				stp.negate(len(stp.query) - 1)
		stp.query += [constraints[j]['stp']]
		query_md5 = hashlib.md5(stp.pp()).hexdigest()
	   # print "stp: %s md5 %s\n"%(stp.pp(),query_md5)
		if is_in_cache(query_md5):
			print "vul had already solved~~~~\n"
		else:
			# execute
			stp.execute()
			solution = stp.interpret()

			if solution:
				fp1=open(input.filename)			#
				print "name : %s"  %(input.filename)

				bytes=fp1.read()
				bytes=list(bytes)

				for (byte, (value, size)) in solution.iteritems():
					for i in range(0, size / 8):
						#print "i: %d    size : %d\n" %(i,size)
						bytes[byte + i] = chr((value >> (i * 8)) & 0xff)
				bytes = ''.join(bytes)
				printable_bytes = re.sub('[^\w,;\.!\*&~"#\'\{\}\(\)\[\]]', '.', bytes[:])
				#print "bytes: ",printable_bytes
				vinput += 1
				filename = '%s%s_vul_%d-%d%s' % (PARAM['OUTPUT_FOLDER'],PARAM['PROGNAME'][9:],ninput,vinput, PARAM['EXTENSION'])
				new_input = Input(ninput, filename, j + 1, bytes)

				printable_bytes = re.sub('[^\w,;\.!\*&~"#\'\{\}\(\)\[\]]', '.', bytes[:10])
				print '\n   # new_vul_input (%s%svul_%d-%d%s)' % (PARAM['OUTPUT_FOLDER'],PARAM['PROGNAME'][9:],ninput,vinput, PARAM['EXTENSION'])
				if not is_symbolize: #依据是否使用Symbolize，使用不同函数进行漏洞用例确认
					fault = check(PARAM['PROGNAME'], PARAM['PROGARG'], new_input.filename, PARAM['FAULT_CHECKER'], PARAM['TAINT_STDIN'])
				else :
					fault = runSymbolizeCheck(PARAM['PROGNAME'], PARAM['PROGARG'], new_input.filename)
				#print PARAM['PROGNAME'], PARAM['PROGARG'], new_input.filename, PARAM['FAULT_CHECKER'], PARAM['TAINT_STDIN'] #debug
				if fault:
					print 'fault location info :',fault_info[m]
					fault_info_name = '%s%s_vul_info_%d-%d%s' % (PARAM['OUTPUT_FOLDER'],PARAM['PROGNAME'][9:],ninput,vinput, PARAM['EXTENSION'])
					fault_file = open(fault_info_name,'wa')
					fault_file.write('fault found in file :'+fault_info[m]['file']+'\n')
					fault_file.write('fault type is :'+fault_info[m]['type']+'\n')
					fault_file.write('fault line number is :'+fault_info[m]['line_num']+'\n')
					fault_file.write('\n\n\n=============================================\n')
					fault_file.write('Note:\nfault types:\n0 -> devide by zero;\n1 -> null pointer refference;\n2 -> array index out of range\n\n')
					detect_time = datetime.datetime.now()
					fault_file.write(str(detect_time))
					fault_file.close()
					filecopy = os.path.join(PARAM['CRASH_FOLDER'], os.path.basename(new_input.filename))
					fault_info_file = os.path.join(PARAM['CRASH_FOLDER'], os.path.basename(fault_info_name))
					shutil.move(new_input.filename, filecopy)
					shutil.move(fault_info_name,fault_info_file)
					vul_input_num = vul_input_num + 1

					insert_stp_cache(query_md5,os.path.basename(new_input.filename)) #保存这个漏洞约束解文件名
				else:
					print "not real fault input!\n"
					insert_stp_cache(query_md5,"not_real_vul")
					#os.remove(new_input.filename)
			else:
				print 'vul constraints no solution\n'
				insert_stp_cache(query_md5,"")
		m = m + 1
	
def depth_handlePC(pc,c_index,c_vul_index,stp,constraints):
	'''
	@jin
	功能：处理路径约束，将二元路径约束(c，taken)转为一元约束，同时对原始的约束表达式进行解析
	如果解析后的约束暂时无法处理，将其从PC中移除；否则，依据约束类型的不同，形成路径约束栈和
	漏洞约束栈，并将约束加入到STP实例中
	参数：	
		pc			:	路径约束，compute_path_constraint 的返回值
		c_index		:	路径索引
		c_vul_index	:	约束索引
		stp			:	stp实例
		constraints	:	路径约束
	'''
	global depth_stack,vul_stack,pop_depth
	jin = 0
	j = 1
	
	for (c, taken) in pc:			#将二元约束改为一元约束，同时根据二元约束中约束的真假建立路径真值表
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
		if(expr==None):				#返回为空表明这个约束是无法处理的，我们将其从PC中移除
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
				depth_stack.append(c_index)		#深度栈每次只将大于上次弹出深度的约束加入其中
				c_index = c_index + 1
		else :
			vul_stack.append((c_vul_index,c_index-1))
			c_vul_index = c_vul_index + 1

		if(EXPR):
			print("expr:",expr.pp())
		constraints = contraint_subsumption(constraints, expr, stp, taken) 	#在STP中加入该约束
		#print "len(constraints): %d\n" % len(constraints)
		stp.first_cmp = True # XXX - dirty
		os.write(sys.stdout.fileno(), '%s%d' % ('\b' * len(str(j - 1)),j))
		j += 1

def breadth_handlePC(pc,c_index,c_vul_index,stp,constraints):
	'''
	@jin
	功能：处理路径约束，将二元路径约束(c，taken)转为一元约束，同时对原始的约束表达式进行解析
	如果解析后的约束暂时无法处理，将其从PC中移除；否则，依据约束类型的不同，形成路径约束队列和
	漏洞约束队列，并将约束加入到STP实例中
	参数：	
		pc			:	路径约束，compute_path_constraint 的返回值
		c_index		:	路径索引
		c_vul_index	:	约束索引
		stp			:	stp实例
		constraints	:	路径约束
	'''
	global depth_stack,vul_stack,pop_depth
	jin = 0
	j = 1
	tmp_stack = []
	for (c, taken) in pc:			#将二元约束改为一元约束，同时根据二元约束中约束的真假建立路径真值表
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
		if(expr==None):				#返回为空表明这个约束是无法处理的，我们将其从PC中移除
			#print "\na usefulness or unhandled constraints\nconstraints: %s\n" %(c)
			if (taken ==0 or taken==2 ):
				c = c[5:-1]
			xx = (c,taken)
			pc.remove(xx)
			continue

		if taken < 2:
			if c_index < pop_depth:
				tmp_stack.append(c_index)		#深度栈每次只将小于上次弹出深度的约束加入其中
				c_index = c_index + 1
			else:
				c_index = c_index + 1
		else :
			vul_stack.append((c_vul_index,c_index-1))
			c_vul_index = c_vul_index + 1

		if(EXPR):
			print("expr:",expr.pp())
		constraints = contraint_subsumption(constraints, expr, stp, taken) 	#在STP中加入该约束
		#print "len(constraints): %d\n" % len(constraints)
		stp.first_cmp = True # XXX - dirty
		os.write(sys.stdout.fileno(), '%s%d' % ('\b' * len(str(j - 1)),j))
		j += 1	
	if depth_stack != []:
		depth_stack = tmp_stack + depth_stack
	else:
		depth_stack = tmp_stack
	print "\npop_depth %d" % pop_depth
	#print "\nbefore pop,depth_stack",depth_stack
	
def get_bran_cons_id(pop_depth):
	'''
	@jin
	功能：获取某一个路径深度在constraints[]中的索引ID
	'''
	index = pop_depth
	global vul_stack
	for c in vul_stack:
		if c[1] < pop_depth:
			index = index + 1
	return index

def get_branch_constraints_num(constraints):
	'''
	@jin
	计算总共的约束数目
	'''
	num = 0
	for c in constraints:
		if c['taken'] == 0:
			num += 1
	return num

def get_vul_depth(pop_depth):
	'''
	计算漏洞栈深度
	'''
	index = 0

	while index < len(vul_stack):
		if vul_stack[index][1] < pop_depth:
			index = index + 1
		else:
			return index
	return index

def get_cons_md5(stp_query):
	return md5.new(stp_query).hexdigest()

def is_in_cache(md5):
	if md5 in vul_stp_cache:
		print "this vul constariants has already solved! result file is %s\n" % vul_stp_cache[md5]
		return True
	else:
		return False

def insert_stp_cache(md5,filename):
	if (md5!=""):
		vul_stp_cache[md5] = filename

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

def negateStpQuery(query):
	'''
	将STP格式的约束取反
	'''
	if query[:2] == "(~":
		query = query[2:]
		tmp = query
		query = query[:-8]
		query += tmp[-7:]
		return query
	elif query[:2] == "((" :
		query = "(~" + query
		tmp = query
		query = query[:-7]
		query = query + ")" + tmp[-7:]
		return query
	else :
		return query

def getCompareLen(current ,expected):
	if (len(current) >= len(expected)):
		return len(expected)
	else:
		return len(current)
		 
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


def contraint_subsumption(constraints, new_c, stp,taken):
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
		print '    ! %s. Skipping constraint!' % error,
		return result
	stp.query.append(stp_formula)
	#add by jin
	# taken < 2 indicates that the constraints is branch constraints, otherwise is the vul constraints
	# added taken flag to distinguish the constraints kind
	if taken < 2:
		result.append({ 'expr': new_c, 'n': len(stp.query)-1, 'taken':0 })
	else:
		result.append({ 'expr': new_c, 'n': len(stp.query)-1, 'taken':1 })


	return result


def compute_path_constraint(input_file):
	'''
	Get the path constraints for a given input

	@param input_file: input filename
	@type  input_file: str
	@return str list
	'''
	global test_index
	global fault_info

	pos = 0
	#'%s%d%s' % (PARAM['OUTPUT_FOLDER'], ninput, PARAM['EXTENSION'])
	str_file_name = '%s%d%s.txt'%(PARAM['OUTPUT_FOLDER'],test_index,'_path')
	test_path_file = open(str_file_name,'wa')

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
	line_count = 1;
	path_constraint = []
	fault_info = []

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
		m_path = re.match('depending path (\d)\n',line)

		#  @add by jin,write path(0,1,2,3) to the output path file
		if m_path:
			path_to = int(m_path.group(1))
			#print("##############################",path_to)
			test_path_file.write(str(path_to))
			pos = pos + 1
			if(pos>1023):
				pos = 0
				test_path_file.write("\n")
		#add by jin ,get the branch information of the current path

		m_path_line = re.match('\[\-\]path:(\d) depending file linenum =>(.*\n)',line)

		if m_path_line:
			#print "line:",line
			taken = int(m_path_line.group(1))
			line_num = m_path_line.group(2)
			#print("####line number info:"+line_num+'\n')
			line_info = '%d%s%spath:    %d\n'%(line_count,' path constraint: ',line_num,taken)
			path_constraint.append(line_info)

			line_count = line_count+1

		m_fault = re.match('detect fault in (.*), fault type is (\d), line num is (.*)\n',line)
		if m_fault:
			fault_file = m_fault.group(1)
			fault_type = m_fault.group(2)
			line_num   = m_fault.group(3)
			fault_info.append({'file': fault_file, 'type': fault_type, 'line_num': line_num})
			#print '\n fault type:'+fault_type+'    line num:'+line_num+'\n'
		if len(pc) == PARAM['MAX_BOUND']:
			break
	test_path_file.write('\n\n')
	for info in path_constraint:
		test_path_file.write(info+'\n')
	fp.close()
	test_path_file.close()
	test_index = test_index+1

	return pc


def expand_execution(input, callbacks):
	'''
	Symbolically execute the program under test with that input, and generate
	new input computed from the expanded path constraints

	@param input: input to expand
	@type  input: Input instance
	@return new inputs
	'''

	global ninput, pop_depth, path, index,vul_input_num
	global query_t,stp_t,report
	global start
	global total_t
	global test_index
	global vul_stp_cache,expected_path_cons,current_path_cons
	global file_t

	stp = STP()
	threshold = 0
	constraints = []
	child_inputs = []

	# compute path constraint
	#add by Luo
	fp2=open('filename.txt','w')
	fp2.seek(0)
	fp2.writelines(list(input.filename))
	fp2.close()

	print '@@@@@@@@@\n\n[+] expanding execution with file %s ' % input.filename.split('/')[-1]
	start_v =  time.time()
	pc = compute_path_constraint(input.filename)
	query_t = query_t + (time.time() - start_v)
	print "compute_path_constraint time is ",str(time.time()-start_v)

	# parse valgrind's output and do constraint subsumption

	os.write(sys.stdout.fileno(), '       ')

	j = 1
	path_temp = [] #print the path of the current test input

	c_index = 0;
	c_vul_index = 0;
	
	#处理解析约束，建立路径约束栈和漏洞约束栈
	breadth_handlePC(pc,c_index,c_vul_index,stp,constraints)

	index += 1
	print '    * %d path constraints' % (c_index)
	print '    * %d vul constraints' % (c_vul_index)
	os.write(sys.stdout.fileno(), '%s' % '\b' * (len(str(j - 1)) + 6))

	# all queries are computed, there will not be change anymore, so we can
	# safely create the constraints
	for c in constraints:
		c['stp'] = stp.query[c.pop('n')]
	#stp.query = []
	print 'len(depth_stack)',len(depth_stack),"\n"

	#print 'fault info:  ',fault_info
	vinput = 0
	bool_vul_stp = False		
	#用于标志一条路径上的漏洞约束是否求解过，如果求解过，当路径约束求解无结果，弹出下一深度继续求解时，也不再
	#求解该漏洞约束了
	bool_is_check = False
	div_depth = 0		#出现分歧的深度
	
	while len(depth_stack) > 0:
		
		#print "vul_stack:",vul_stack
		#print "len(constraints):",constraints
		if not bool_is_check:	#每一轮求解只检测一次分歧
			current_path_cons = []		#清空当前路径stp约束
			for k in range(0, get_branch_constraints_num(constraints)):
				i = get_bran_cons_id(k)
				current_path_cons.append(constraints[i]['stp'].pp())     #获得当前路径stp约束
				
			'''
			print "expected_path_cons is:\n%s\n" % "#".join(expected_path_cons)
			print "compare expected_path_cons is:\n%s\n" % "#".join(expected_path_cons[:pop_depth+1])
			print "current path cons is:\n%s\n " % "#".join(current_path_cons)
			print "compare current path cons is:\n%s\n " % "#".join(current_path_cons[:pop_depth+1])
			'''
			print "last pop_depth: %d\n" % pop_depth
			compareLen = getCompareLen(current_path_cons,expected_path_cons)
			if test_index != 1:
				#当前路径长度小于期望路径长度，肯定有分歧
				bool_is_check = True
				if len(current_path_cons)<len(expected_path_cons) :
					print " ~~~~~~~~~~~~~\ndiv happend!\n~~~~~~~~~~~~~~~~~~~~\n"
					for i in range(0,len(current_path_cons)):
						if current_path_cons[i] != expected_path_cons[i]:
							div_depth = i
							print "div depth: %d\n" % div_depth
							break					
				elif(expected_path_cons[:compareLen] != current_path_cons[:compareLen]):
					print " ~~~~~~~~~~~~~\ndiv happend!\n~~~~~~~~~~~~~~~~~~~~\n"
					for i in range(0,compareLen):
						if current_path_cons[i] != expected_path_cons[i]:
							div_depth = i
							print "div depth: %d\n" % div_depth
							break		
		pop_depth = -1
		print "depth_stack:",depth_stack
		while True:

			pop_depth = depth_stack.pop(0) #弹出上次求解深度，如果比当前约束总数大，继续弹深度栈，否则确定该深度进行求解
			if pop_depth < get_branch_constraints_num(constraints):
				if div_depth ==0:
					break
				elif pop_depth < div_depth:
					break
			if len(depth_stack) == 0:	#深度栈弹空后不进行求解
				pop_depth = - 1
				break
		print"pop_depth is %d ,depth stack length %d constraints num is %d"% (pop_depth,len(depth_stack),get_branch_constraints_num(constraints))
		#如果一次 expand_execution 没有求解过漏洞约束，进行求解
		if not bool_vul_stp:
			bool_vul_stp = True
			solve_path_vul(constraints,stp,input,vinput,ninput)

		print "\nstp pop_depth:%d "% pop_depth
		stp.query = []				#置空STP query 根据栈深度加入本次求解约束
		for k in range(0, pop_depth+1):
			i = get_bran_cons_id(k)
			stp.query += [ constraints[i]['stp'] ]
		if len(stp.query) == 0:
			continue
			
		#获得预期执行路径约束，之所以放在stp negate之前是为了方便处理最后一个约束取反
		expected_path_cons = []	
		for k in range(0,len(stp.query)):
			expected_path_cons.append(stp.query[k].pp())			
		expected_path_cons[len(stp.query) - 1] = negateStpQuery(stp.query[len(stp.query) - 1].pp())
		

		stp.negate(len(stp.query) - 1)
		#print "stp query negate:",stp.pp()

		start_stp = time.time()		#记录stp执行时间
		stp.execute()
		solution = stp.interpret()
		stp_t = stp_t + (time.time() - start_stp)

		if solution:

			#add by Luo 用于Symbolize保存符号变量的值
			fp1=open(input.filename)
			print "name : %s"  %(input.filename)

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
			child_inputs.append(new_input)

			printable_bytes = re.sub('[^\w,;\.!\*&~"#\'\{\}\(\)\[\]]', '.', bytes[:])
			print '\n#########################\n'
			print '\n    * new_input (%d%s): ' % (ninput, PARAM['EXTENSION']), list(new_input.bytes)
			print '\n#########################\n'

			total_t = (time.time() - start)

			time_str = "%5d input used time:%10s min\n" %(test_index,round(total_t/60,4))
			print time_str
			file_t.write(time_str)

			if(report==None):
				report=open("report.txt",'w')
			report.write('    * new_input (')
			report.write(str(ninput))
			report.write(str(PARAM['EXTENSION']))
			report.write('):')
			report.write(str(list(new_input.bytes)))
			report.write("\n");

			while len(vul_stack) > 0:
				#print "vul_stack",vul_stack
				vul_stack.pop()
			break
		else:
			print 'no solution\n'


	if len(depth_stack) == 0:		#处理只有漏洞约束，没有路径约束的情况，算是异常处理吧
		if len(vul_stack) != 0:
			solve_path_vul(constraints,stp,input,vinput,ninput)

			while len(vul_stack) > 0:
				vul_stack.pop()


	#print vul_stp_cache
	return child_inputs


def search(target, worklist, callbacks):
	global ninput,test_index,vul_input_num
	global run_times_flag
	global start
	global total_t
	global stp_t
	global query_t
	global file_t,report
	test_index = 0


	run_times_flag = 1
	fp3=open('run_times.txt','w')
	fp3.seek(0)
	fp3.write(str(run_times_flag))


	time_tt = datetime.datetime.now()
	file_str = '%s%s-time.txt' % (PARAM['OUTPUT_FOLDER'],time_tt)
	print "file_str:",file_str
	file_t = open(file_str,'w')



	if file_t == None :
		print "create time file failed\n"

	report = open('./analysis/%s-report'%(PARAM['PROGNAME'][9:]),"w")

	if report == None :
		print "report file create failed\n"

	while worklist:
		input = worklist.pop()
		print '[+] input %s' % input.filename


		child_inputs = expand_execution(input, callbacks)

		#feng add
		if(child_inputs==None):
			continue

		print '[+] checking each new input\n'
		for input in child_inputs:
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

		worklist += child_inputs

		run_times_flag += 1
		if run_times_flag > 1:
			run_times_flag = 1
		#print 'run_times : %d ' % run_times_flag
		fp3.seek(0)
		fp3.write(str(run_times_flag))


	fp3.close()
	file_t.close()
	report.close()
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
		worklist = [ input_seed ]
	thread.start_new_thread(timer,(run_time ,time_flag))
	try:
		search(target, worklist, [ None ] * 10)
	except KeyboardInterrupt:
		total_t = (time.time() - start)
		print "\nTotal running time is %s S\nSTP execute time is %s S\nValgrind query time is %s S\n"%(round(total_t,2),round(stp_t,2),round(query_t,2))

		print "Total test input is %d \n"%ninput
		print "Total vul input is %d \n" % vul_input_num
		thread.exit()


	if(report!=None):
		report.close();
