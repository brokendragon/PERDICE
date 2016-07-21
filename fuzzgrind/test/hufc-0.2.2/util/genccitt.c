#include <stdio.h>
#include <stdlib.h>

#define POLY	0x1021	/* CRC-16 CCITT */


int main(void)
{
	FILE *fp;
	unsigned short i, j, v;


	if ((fp=fopen("lookup.crc16.ccitt", "w")) == NULL)
	{
		perror("fopen");
		exit(1);
	}

	fprintf(fp, "/*\n * CRC-16 CCITT lookup table\n */\n\n");
	fprintf(fp, "typedef unsigned short u16;\n\n");
	fprintf(fp, "static const u16 crctable[256] =\n{\n");

	for (i=1; i <= 256; i++)
	{
		v=(i-1) << 8;

		for (j=0; j < 8; j++)
			v=v & 0x8000 ? (v << 1) ^ POLY : v << 1;

		fprintf(fp, " 0x%04X", v);
		if (i != 256)
			fprintf(fp, ",");

		if (i%8 == 0)
			fprintf(fp, "\n");
	}

	fprintf(fp, "};\n");
	fclose(fp);
	return 0;
}
