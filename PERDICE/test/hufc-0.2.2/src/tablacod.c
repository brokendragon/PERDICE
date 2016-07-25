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

#include "tablacod.h"


void rellenarTablaCod(struct nodo *raiz, struct tablaCod *tabla)
{
	static BYTE cod[MAX_LEN_COD];
	static short int len;


	if (raiz != NULL)
	{
		if (raiz->hizq == NULL)   // Hoja
		{
			if (len == 0)
				len=1;

			tabla[raiz->c].len=len;
			tabla[raiz->c].cod=malloc(len);
			if (tabla[raiz->c].cod == NULL)
			{
				perror("malloc: rellenarTablaCod()");
				exit(1);
			}
			memcpy(tabla[raiz->c].cod, cod, len);
		}
		else	// NO hoja
		{
			cod[len]=0;
			len++;
			rellenarTablaCod(raiz->hizq, tabla);
			cod[len-1]=UNO;
			rellenarTablaCod(raiz->hdch, tabla);
			len--;
		}
	}
}


struct tablaCod *crearTablaCod(struct nodo *raiz)
{
	struct tablaCod *tabla;


	tabla=calloc(TABLA_SZ, sizeof(struct tablaCod));
	if (tabla == NULL)
	{
		perror("calloc: crearTablaCod()");
		exit(1);
	}

	rellenarTablaCod(raiz, tabla);
	return tabla;
}


struct tablaCod *getEntry(struct tablaCod *tabla, BYTE c)
{
	return &tabla[c];
}


void borrarTablaCod(struct tablaCod *tabla)
{
	int cont;


	for (cont=0; cont < TABLA_SZ; cont++)
	{
		if (tabla[cont].len != 0)
			free(tabla[cont].cod);
	}

	free(tabla);
}
