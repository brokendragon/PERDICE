Requirements:
(1)	bzip2
(2)	autoconf
(3)	make
(4)	gcc
(5)	python

Installation:
Execute the following commands under the directory fuzzgrind/valgrind-r12356
mkdir -p build/
./autogen.sh
./configure CFLAGS=-fno-stack-protector --prefix=`pwd`/build/
make
sudo make install

Configuration:
Configuration file: fuzz/settings.cfg
The program under test must be compiled with –g, and the compiled binary file are usually put in the test-input directory. 
The programs tested are in the test directory.

Execution:
$ ./fuzz/cache.py program

Example:
$ ./fuzz/cache.py test1
New inputs are created in test-input/input/ 
Crash files are be saved in test-input/crash/
The report that represents the total score after every symbolic execution is put in test-input/report/
The detail score of every source code line is put in test-input/line-info/
Our main code in the file fuzz/cache.py and valgrind-r12356/cachegrind/cg_main.c

/fuzz/cache.py: PERDICE
/fuzz/fuzz-g.py：generational search
/fuzz/depth.py: depth-first search
/fuzz/breadth.py: breadth-first search
/fuzz/rand.py: random search
/s2e.py: s2e test