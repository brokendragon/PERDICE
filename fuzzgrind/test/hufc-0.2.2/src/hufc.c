/*
 * 'hufc' is a utility to compress or expand files based on Huffman coding
 * Copyright (C) 2006-2014 Jose Ignacio Agulleiro Baldo
 * Email: jiagulleiro@users.sourceforge.net
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version. See file COPYING.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301 USA.
 */

/*
 * hufc v. 0.2.2
 */

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include <stdio.h>
#include <netinet/in.h>
#include <sys/stat.h>
#include "tipos.h"
#include "bitsop.h"
#include "header.h"
#include "huffman.h"
#include "tablacod.h"
#include "argshand.h"
#include "ccitt.h"
#include "checksum.h"
#include "gettime.h"

#define FILE_OK		1
#define FILE_CORRUPTED	-1

#define COMPRIMIR	0
#define DESCOMPRIMIR	1


BYTE comprimir(FILE *fpin, FILE *fpout, struct tablaCod *tabla, int verbose);
void descomprimir(FILE *fpin, FILE *fpout, struct nodo *raiz, struct header *h, int verbose);
u16 calculacrc(FILE *fp);
u16 calculasum(FILE *fp, int op);
u16 readcrcsum(FILE *fp);
void writecrcsum(FILE *fp, u16 v);
int testfile(FILE *fp, BYTE deterr);
void sintaxis(char *progname);


int main(int argc, char *argv[])
{
	FILE *fpin, *fpout;
	struct nodo *raiz;
	struct tablaCod *tabla;
	struct header h;
	u16 v;
	int verbose=0, benchmark=0;
	double tiempo;


	printf("hufc v. 0.2.2 Compress/Expand files using Huffman coding\n");

	if (argc < 2)
	{
		printf("To see help, write: %s -h\n", argv[0]);
		exit(0);
	}

	// Mostrar la ayuda?
	if (ExistArg("-h", argc, argv))
	{
		sintaxis(argv[0]);
		exit(0);
	}

	// Modo verbose?
	if (ExistArg("-v", argc, argv))
		verbose=1;

	// Medir el tiempo de crc o de checksum?
	if (ExistArg("-b", argc, argv))
		benchmark=1;

	if ((fpin=fopen(argv[1], "rb")) == NULL)
	{
		perror("fopen: input file");
		exit(1);
	}

	// Leer crc o checksum?
	if (ExistArg("-r", argc, argv))
	{
		if (!isHuf(fpin))
			printf("%s: not in huf format!\n", argv[1]);
		else
		{
			switch (leerDetErr(fpin))
			{
				case USE_CCITT:
					printf("%s: crc = 0x%04X\n", argv[1], readcrcsum(fpin));
					break;

				case USE_CHECKSUM:
					printf("%s: checksum = 0x%04X\n", argv[1], readcrcsum(fpin));
					break;

				default:
					printf("%s: error detection not used\n", argv[1]);
			}
		}

		fclose(fpin);
		exit(0);
	}

	// Testear el fichero?
	if (ExistArg("-t", argc, argv))
	{
		if (!isHuf(fpin))
			printf("%s: not in huf format!\n", argv[1]);
		else
		{
			switch (testfile(fpin, leerDetErr(fpin)))
			{
				case FILE_OK:
					printf("%s: seems to be ok\n", argv[1]);
					break;

				case FILE_CORRUPTED:
					printf("%s: file corrupted!\n", argv[1]);
					break;

				default:
					printf("%s: error detection not used\n", argv[1]);
			}
		}

		fclose(fpin);
		exit(0);
	}

	// Descomprimir
	if (ExistArg("-x", argc, argv))
	{
		if (!isHuf(fpin))
		{
			printf("%s: not in huf format!\n", argv[1]);
			fclose(fpin);
			exit(0);
		}

		// Testeamos el fichero
		h.deterr=leerDetErr(fpin);
		if (testfile(fpin, h.deterr) == FILE_CORRUPTED)
		{
			printf("%s: file corrupted!\n", argv[1]);
			fclose(fpin);
			exit(0);
		}

		raiz=leerCabecera(fpin, &h);
		fpout=fopen(h.filename, "wb");
		if (fpout == NULL)
		{
			perror("fopen: output file");
			exit(1);
		}

		// Le damos al fichero sus permisos originales
		chmod(h.filename, h.permisos);
		descomprimir(fpin, fpout, raiz, &h, verbose);
	}

	// Comprimir
	else
	{
		if (verbose)
		{
			printf("Scanning file (this may take a while)... ");
			fflush(stdout);
		}
		calcularFreq(fpin, &raiz);
		if (verbose)
			printf("Done\n");
		raiz=crearArbolHuffman(raiz);
		tabla=crearTablaCod(raiz);

		if (ExistArg("-ccitt", argc, argv))
			h.deterr=USE_CCITT;
		else if (ExistArg("-sum", argc, argv))
			h.deterr=USE_CHECKSUM;
		else
			h.deterr=DONT_USE_ERR_DET;

		setHeaderPermisos(&h, argv[1]);
		setHeaderFileName(&h, argv[1]);
		fpout=fopen(getCompressedFileName(&h), "w+b");
		if (fpout == NULL)
		{
			perror("fopen: output file");
			exit(1);
		}

		escribirCabecera(fpout, &h, raiz);
		h.padding_bits=comprimir(fpin, fpout, tabla, verbose);
		escribirPadding(fpout, h.padding_bits);
		borrarTablaCod(tabla);
		fflush(fpout);

		switch (h.deterr)
		{
			case USE_CCITT:
				if (benchmark)
					tiempo=gettime();

				v=calculacrc(fpout);

				if (verbose)
					printf("   crc = 0x%04X\n", v);

				if (benchmark)
					printf("crc time: %g s\n", gettime()-tiempo);

				writecrcsum(fpout, v);
				break;

			case USE_CHECKSUM:
				if (benchmark)
					tiempo=gettime();

				v=calculasum(fpout, COMPRIMIR);

				if (verbose)
					printf("   checksum = 0x%04X\n", v);

				if (benchmark)
					printf("checksum time: %g s\n", gettime()-tiempo);

				writecrcsum(fpout, v);
				break;

			default:
				if (verbose)
					printf("\n");
		}
	}

	borrarArbolHuffman(raiz);
	fclose(fpin);
	fclose(fpout);

	return 0;
}


BYTE comprimir(FILE *fpin, FILE *fpout, struct tablaCod *tabla, int verbose)
/*
 * Codifica cada caracter del fichero usando la
 * tabla de codificacion creada a partir del
 * arbol de Huffman
 */
{
	BYTE buf_lec[BUF_SZ], buf_esc[BUF_SZ+1], padding;
	int pos_buf_esc=0, pos_pos=0, i, j, nbytes;
	struct tablaCod *entry;
	float completado=0.0F, inc;
	struct stat statbuf;


	if (verbose)
	{
		fstat(fileno(fpin), &statbuf);
		inc = (BUF_SZ*100.0F) / statbuf.st_size;
		if (inc > 100.0F)
			inc=100.0F;

		printf("Compressing... 0%%");
	}

	rewind(fpin);
	memset(buf_esc, 0, BUF_SZ+1);

	for (;;)
	{
		nbytes=fread(buf_lec, 1, BUF_SZ, fpin);
		if (ferror(fpin))
		{
			perror("fread: comprimir()");
			exit(1);
		}

		for (i=0; i < nbytes; i++)
		{
			entry=getEntry(tabla, buf_lec[i]);
			for (j=0; j < entry->len; j++)
			{
				writeBits(buf_esc, &pos_buf_esc, &pos_pos, entry->cod[j], 1);
				if (pos_buf_esc == BUF_SZ)
				{
					fwrite(buf_esc, 1, BUF_SZ, fpout);
					if (ferror(fpout))
					{
						perror("fwrite: comprimir()");
						exit(1);
					}

					buf_esc[0]=buf_esc[BUF_SZ];
					memset(buf_esc+1, 0, BUF_SZ);
					pos_buf_esc=0;
				}
			}
		}

		if (verbose)
		{
			if ((int)completado == 100)
				printf("\b\b");
			else if ((int)completado >= 10)
				printf("\b");

			completado+=inc;
			if ((int)completado > 100)
				completado=100.0F;
			printf("\b\b%d%%", (int)completado);
		}

		if (feof(fpin))
		{
			padding=(8-pos_pos) % 8;
			if (padding != 0 || pos_buf_esc != 0)
			{
				fwrite(buf_esc, 1, padding == 0 ? pos_buf_esc : pos_buf_esc+1, fpout);
				if (ferror(fpout))
				{
					perror("fwrite: comprimir()");
					exit(1);
				}
			}

			if (verbose && (int)completado < 100)
				printf("\b\b\b100%%");

			break;	// Salimos del for(;;)
		}
	}

	return padding;
}


void descomprimir(FILE *fpin, FILE *fpout, struct nodo *raiz, struct header *h, int verbose)
{
	BYTE buf_lec[BUF_SZ], buf_esc[BUF_SZ], b;
	int pos_buf_lec, pos_pos=0, nbits, cont=0;
	struct nodo *tmp=raiz;
	float completado=0.0F, inc;
	struct stat statbuf;


	if (verbose)
	{
		fstat(fileno(fpin), &statbuf);
		inc = (BUF_SZ*100.0F) / statbuf.st_size;
		if (inc > 100.0F)
			inc=100.0F;

		printf("Expanding... 0%%");
	}

	fseek(fpin, getHeaderSize(h), SEEK_SET);

	for (;;)
	{
		pos_buf_lec=0;
		nbits=fread(buf_lec, 1, BUF_SZ, fpin);
		if (ferror(fpin))
		{
			perror("fread: descomprimir()");
			exit(1);
		}

		nbits<<=3;	// nbits*=8;
		if (feof(fpin))
		{
			nbits-=h->padding_bits;
			if (h->deterr != DONT_USE_ERR_DET)
				nbits-=16;
		}

		while (nbits != 0)
		{
			/*
			 * Esta comprobacion es necesaria por si se
			 * comprimio un fichero en el que todos los
			 * caracteres son el mismo, ya que el arbol
			 * solo tendra un nodo, la raiz
			 */
			if (tmp->hizq != NULL)
			{
				readBits(buf_lec, &pos_buf_lec, &pos_pos, &b, 1);
				if (b == 0)
					tmp=tmp->hizq;
				else
					tmp=tmp->hdch;
			}

			if (tmp->hizq == NULL)	// Hoja
			{
				buf_esc[cont]=tmp->c;
				cont++;
				if (cont == BUF_SZ)
				{
					cont=0;
					fwrite(buf_esc, 1, BUF_SZ, fpout);
					if (ferror(fpout))
					{
						perror("fwrite: descomprimir()");
						exit(1);
					}
				}

				tmp=raiz;
			}

			nbits--;
		}

		if (verbose)
		{
			if ((int)completado == 100)
				printf("\b\b");
			else if ((int)completado >= 10)
				printf("\b");

			completado+=inc;
			if ((int)completado > 100)
				completado=100.0F;
			printf("\b\b%d%%", (int)completado);
		}

		if (feof(fpin))
		{
			fwrite(buf_esc, 1, cont, fpout);
			if (ferror(fpout))
			{
				perror("fwrite: descomprimir()");
				exit(1);
			}

			if (verbose)
			{
				if ((int)completado < 100)
					printf("\b\b\b100%%");
				printf("\n");
			}

			break;	// Salimos del for(;;)
		}
	}
}


u16 calculacrc(FILE *fp)
{
	BYTE buf[BUF_SZ];
	size_t nbytes;
	u16 crc=0xFFFF;


	rewind(fp);
	while (!feof(fp))
	{
		nbytes=fread(buf, 1, BUF_SZ, fp);
		if (ferror(fp))
		{
			perror("fread: calculacrc()");
			exit(1);
		}

		crc=ccitt(crc, nbytes, buf);
	}

	return crc;
}


u16 calculasum(FILE *fp, int op)
{
	BYTE buf[BUF_SZ];
	size_t nbytes;
	u16 sum=0;


	rewind(fp);
	while (!feof(fp))
	{
		nbytes=fread(buf, 1, BUF_SZ, fp);
		if (ferror(fp))
		{
			perror("fread: calculasum()");
			exit(1);
		}

		if (feof(fp) && op == DESCOMPRIMIR)
			nbytes-=2;

		sum=~checksum(sum, nbytes, buf);
	}
#ifndef __HUFC_BIG_ENDIAN__
	sum=htons(sum);
#endif

	if (op == DESCOMPRIMIR)
		return sum+readcrcsum(fp);

	return ~sum;
}


u16 readcrcsum(FILE *fp)
{
	u16 stored;


	fseek(fp, -2, SEEK_END);
	fread(&stored, 2, 1, fp);
	return ntohs(stored);
}


void writecrcsum(FILE *fp, u16 v)
{
	fseek(fp, 0, SEEK_END);
	v=htons(v);
	fwrite(&v, 2, 1, fp);
}


int testfile(FILE *fp, BYTE deterr)
{
	switch (deterr)
	{
		case USE_CCITT:
			return calculacrc(fp) == 0 ? FILE_OK : FILE_CORRUPTED;

		case USE_CHECKSUM:
			return calculasum(fp, DESCOMPRIMIR) == 0xFFFF ? FILE_OK : FILE_CORRUPTED;

		case DONT_USE_ERR_DET:
			return DONT_USE_ERR_DET;

		default:
			return FILE_CORRUPTED;
	}
}


void sintaxis(char *progname)
{
	printf("Use: %s file [options]\n", progname);
	printf(" file\t\tfile to compress/expand\n");
	printf(" -h\t\tshow this help\n");
	printf(" -v\t\tverbose mode\n");
	printf(" -b\t\tshow crc or checksum time when compressing\n");
	printf(" -r\t\tread crc or checksum from a file\n");
	printf(" -x\t\texpand\n");
	printf(" -t\t\ttest a compressed file\n");
	printf(" -ccitt\t\tput a 16 bits crc when compressing\n");
	printf(" -sum\t\tput a checksum when compressing\n");
}
