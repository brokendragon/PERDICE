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

#ifndef __HEADER_H__
#define __HEADER_H__

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <netinet/in.h>
#include "tipos.h"
#include "huffman.h"

#define MAGIC_NUMBER		0x9A485546	/* 0x9A 'H' 'U' 'F' */
#define HEADER_VERSION		0x11		/* Version 1.1 */
#define MAX_FILENAME_LEN	256
#define MAX_TREE_SZ		320

#define DONT_USE_ERR_DET	0
#define USE_CCITT		0xFF
#define USE_CHECKSUM		0xAA


struct header
{
	u32 magic_number;
	mode_t permisos;
	char filename[MAX_FILENAME_LEN];
	BYTE tree[MAX_TREE_SZ];
	u16 tree_sz;
	BYTE version;
	BYTE padding_bits;
	BYTE deterr;
};


int isHuf(FILE *fp);
void escribirPadding(FILE *fp, BYTE padding);
BYTE leerDetErr(FILE *fp);
void setHeaderPermisos(struct header *h, char *filename);
void setHeaderFileName(struct header *h, char *filename);
int getHeaderSize(struct header *h);
char *getCompressedFileName(struct header *h);
struct nodo *leerCabecera(FILE *fp, struct header *h);
void escribirCabecera(FILE *fp, struct header *h, struct nodo *raiz);


#endif
