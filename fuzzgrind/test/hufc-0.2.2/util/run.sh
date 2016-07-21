#!/bin/bash
rm -f $1

for i in `seq 1 5`; do
	#./bench >> $1
	/usr/bin/time -p hufc $2 $3 -b >> $1 2>&1
done
