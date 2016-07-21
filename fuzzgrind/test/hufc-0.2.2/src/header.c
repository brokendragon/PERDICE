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

#include "header.h"


int isHuf(FILE *fp)
// Comprueba si se trata de un fichero comprimido
{
	u32 magic=0;


	rewind(fp);
	fread(&magic, 4, 1, fp);
	return ntohl(magic) == MAGIC_NUMBER ? 1 : 0;
}


void escribirPadding(FILE *fp, BYTE padding)
/*
 * Los padding bits no los podemos saber hasta que no
 * comprimimos el fichero; de ahi la necesidad de esta
 * funcion
 */
{
	fseek(fp, 5, SEEK_SET);
	fwrite(&padding, 1, 1, fp);
}


BYTE leerDetErr(FILE *fp)
{
	BYTE deterr;


	fseek(fp, 6, SEEK_SET);
	fread(&deterr, 1, 1, fp);
	return deterr;
}


void setHeaderPermisos(struct header *h, char *filename)
{
	struct stat buf;


	stat(filename, &buf);
	h->permisos=htonl(buf.st_mode);
}


void setHeaderFileName(struct header *h, char *filename)
{
	char *nombre=strrchr(filename, '/');


	strcpy(h->filename, nombre == NULL ? filename : nombre+1);
}


int getHeaderSize(struct header *h)
{
	return 8+sizeof(mode_t)+strlen(h->filename)+h->tree_sz;
}


char *getCompressedFileName(struct header *h)
{
	static char filename[MAX_FILENAME_LEN];


	if (strlen(h->filename) > MAX_FILENAME_LEN-5)
		strncpy(filename, h->filename, MAX_FILENAME_LEN-5);
	else
		strcpy(filename, h->filename);

	strcat(filename, ".huf");
	return filename;
}


struct nodo *leerCabecera(FILE *fp, struct header *h)
{
	struct nodo *raiz;


	// Leemos el numero de version
	fseek(fp, 4, SEEK_SET);
	fread(&h->version, 1, 1, fp);

	// Leemos los padding bits
	fread(&h->padding_bits, 1, 1, fp);

	// Leemos los permisos
	fseek(fp, 1, SEEK_CUR);
	fread(&h->permisos, 1, sizeof(mode_t), fp);
	h->permisos=ntohl(h->permisos);

	// Leemos el nombre del fichero que fue comprimido
	fgets(h->filename, MAX_FILENAME_LEN+1, fp);
	h->filename[strlen(h->filename)-1]='\0';

	// Leemos el arbol de Huffman y lo reconstruimos
	/*
	 * Si fread() nos devuelve 0, quiere decir que
	 * se comprimio un fichero vacio
	 */
	h->tree_sz=fread(h->tree, 1, MAX_TREE_SZ, fp);

	if (h->deterr == DONT_USE_ERR_DET && h->tree_sz == 0)
		return NULL;

	if (h->deterr != DONT_USE_ERR_DET && h->tree_sz == 2)
	{
		h->tree_sz=0;
		return NULL;
	}

	h->tree_sz=cargarArbolHuffman(&raiz, h->tree);
	return raiz;
}


void escribirCabecera(FILE *fp, struct header *h, struct nodo *raiz)
{
	rewind(fp);

	// Escribimos el magic number
	h->magic_number=htonl(MAGIC_NUMBER);
	fwrite(&h->magic_number, 4, 1, fp);

	// Escribimos el numero de version
	h->version=HEADER_VERSION;
	fwrite(&h->version, 1, 1, fp);

	// Escribimos los padding bits (incorrectos)
	fwrite(&h->padding_bits, 1, 1, fp);

	// Escribimos la deteccion de errores usada
	fwrite(&h->deterr, 1, 1, fp);

	// Escribimos los permisos
	fwrite(&h->permisos, sizeof(mode_t), 1, fp);

	// Escribimos el nombre del fichero a comprimir
	fprintf(fp, "%s\n", h->filename);

	// Leemos y escribimos el arbol de Huffman
	memset(h->tree, 0, MAX_TREE_SZ);
	h->tree_sz=salvarArbolHuffman(raiz, h->tree);
	if (h->tree_sz != 0)
		fwrite(h->tree, 1, h->tree_sz+1, fp);
}
