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

#ifndef __TABLACOD_H__
#define __TABLACOD_H__

#if HAVE_CONFIG_H
# include <config.h>
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "tipos.h"
#include "huffman.h"

#define MAX_LEN_COD	256
#define TABLA_SZ	256


// Estructura para cada entrada de la tabla
// Indexamos segun el valor numerico del caracter
struct tablaCod
{
	short int len;	// Longitud de la codificacion
	BYTE *cod;	// Codificacion
};


struct tablaCod *crearTablaCod(struct nodo *raiz);
inline struct tablaCod *getEntry(struct tablaCod *tabla, BYTE c);
void borrarTablaCod(struct tablaCod *tabla);


#endif
