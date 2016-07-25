#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <netinet/in.h>
#include "ccitt.h"
#include "checksum.h"
#include "tipos.h"

#define MAX_DATA_SIZE	1024


int main(int argc, char *argv[])
{
	u16 crc=0xFFFF;
	u16 sum=0;
	BYTE data[MAX_DATA_SIZE];
	size_t data_len=1;
	const char *delim=",";
	char *next;


	if (argc != 2)
	{
		printf("Use: %s <data>\nExample: %s 34,67,8\n", argv[0], argv[0]);
		return 0;
	}

	next=strtok(argv[1], delim);
	data[0]=atoi(next);
	printf("Data = %d", data[0]);
	while ( (next=strtok(NULL, delim)) && data_len < MAX_DATA_SIZE )
	{
		data[data_len]=atoi(next);
		printf(" %d", data[data_len]);
		data_len++;
	}
	printf("\nData length = %zu\n", data_len);

	crc=ccitt(crc, data_len, data);
	sum=checksum(sum, data_len, data);
	printf("CRC-16   = 0x%04X\n", crc);
	printf("Checksum = 0x%04X\n", htons(sum));
	return 0;
}
