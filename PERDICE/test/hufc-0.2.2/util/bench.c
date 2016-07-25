#include <stdio.h>
#include <string.h>
#include "gettime.h"
#include "ccitt.h"
#include "checksum.h"
#include "tipos.h"

#define DATA_SIZE	512
#define INIT_VAL	37
#define ITERATIONS	5e7


int main(void)
{
	BYTE data[DATA_SIZE];
	double tiempo;
	u32 i;


	/* Data initialization */
	memset(data, INIT_VAL, DATA_SIZE);

	/* CRC-16 */
	tiempo=gettime();
	for (i=0; i < ITERATIONS; i++)
		ccitt(0xFFFF, DATA_SIZE, data);
	tiempo=gettime()-tiempo;
	printf("CRC-16 time:\t%g s\n", tiempo);

	/* Checksum */
	tiempo=gettime();
	for (i=0; i < ITERATIONS; i++)
		checksum(0, DATA_SIZE, data);
	tiempo=gettime()-tiempo;
	printf("Checksum time:\t%g s\n", tiempo);
	return 0;
}
