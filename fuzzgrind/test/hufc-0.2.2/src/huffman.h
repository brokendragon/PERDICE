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

#ifndef __HUFFMAN_H__
#define __HUFFMAN_H__

#include <stdio.h>
#include <stdlib.h>
#include "tipos.h"
#include "bitsop.h"

#define BUF_SZ	512
#define UNO	0x80


struct nodo
{
	BYTE c;
	long long freq;
	struct nodo *padre;
	struct nodo *hizq;
	struct nodo *hdch;
	struct nodo *sig;
};


void calcularFreq(FILE *fp, struct nodo **raiz);
struct nodo *crearArbolHuffman(struct nodo *raiz);
void borrarArbolHuffman(struct nodo *raiz);
int salvarArbolHuffman(struct nodo *raiz, BYTE *mem);
int cargarArbolHuffman(struct nodo **raiz, BYTE *mem);


#endif
