SRCPATH = ../src/
CC = gcc
CFLAGS = -Wall -O2 -DHAVE_CONFIG_H -I.. -I$(SRCPATH) #-g
RM = /bin/rm -f
SRC1 = genccitt.c
SRC2 = test.c
SRC3 = bench.c
PROG1 = genccitt
PROG2 = test
PROG3 = bench
PROG2_OBJS = ccitt.o checksum.o
PROG3_OBJS = $(PROG2_OBJS) gettime.o

all: $(PROG1) $(PROG2) $(PROG3)

$(PROG1): $(SRC1)
	$(CC) $(CFLAGS) $(SRC1) -o $(PROG1)

$(PROG2): $(SRC2) $(PROG2_OBJS)
	$(CC) $(CFLAGS) $(SRC2) $(PROG2_OBJS) -o $(PROG2)

$(PROG3): $(SRC3) $(PROG3_OBJS)
	$(CC) $(CFLAGS) $(SRC3) $(PROG3_OBJS) -o $(PROG3)

ccitt.o: $(SRCPATH)ccitt.c $(SRCPATH)ccitt.h $(SRCPATH)tipos.h ../config.h
	$(CC) $(CFLAGS) -c $(SRCPATH)ccitt.c

checksum.o: $(SRCPATH)checksum.c $(SRCPATH)checksum.h $(SRCPATH)tipos.h ../config.h
	$(CC) $(CFLAGS) -c $(SRCPATH)checksum.c

gettime.o: $(SRCPATH)gettime.h $(SRCPATH)gettime.c
	$(CC) $(CFLAGS) -c $(SRCPATH)gettime.c


strip:
	strip $(PROG1) $(PROG2) $(PROG3)

cleanobjs:
	$(RM) $(PROG3_OBJS)

cleanall:
	$(RM) $(PROG1) $(PROG2) $(PROG3) $(PROG3_OBJS)
