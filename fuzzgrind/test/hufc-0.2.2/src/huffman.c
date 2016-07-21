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

#include "huffman.h"


struct nodo *crearNodo(void)
// Reserva memoria para un nodo
{
	struct nodo *nuevo;


	if ((nuevo=calloc(1, sizeof(struct nodo))) == NULL)
	{
		perror("calloc: crearNodo()");
		exit(1);
	}

	return nuevo;
}


struct nodo *insertar(struct nodo *raiz, BYTE c)
/*
 * Inserta al principio de la lista enlazada un nuevo
 * nodo con el caracter `c'
 */
{
	struct nodo *tmp=raiz;


	raiz=crearNodo();
	raiz->c=c;
	raiz->freq=1;
	raiz->sig=tmp;

	return raiz;
}


struct nodo *yaInsertado(struct nodo *raiz, BYTE c)
/*
 * Devuelve el nodo con el caracter `c' o NULL si
 * ese nodo no existe
 */
{
	while (raiz != NULL)
	{
		if (raiz->c == c)
			return raiz;

		raiz=raiz->sig;
	}

	return NULL;
}


struct nodo *ordenar(struct nodo *raiz)
// Ordena la lista enlazada de menor a mayor frecuencia
{
	struct nodo *inicio=raiz, *mayor, *ant, *aux;


	raiz=NULL;

	while (inicio != NULL)
	{
		aux=mayor=inicio;

		while (aux->sig != NULL)
		{
			if (aux->sig->freq > mayor->freq)
			{
				ant=aux;
				mayor=aux->sig;
			}

			aux=aux->sig;
		}

		if (inicio == mayor)
			inicio=inicio->sig;
		else
			ant->sig=mayor->sig;

		mayor->sig=raiz;
		raiz=mayor;
	}

	return raiz;
}


void calcularFreq(FILE *fp, struct nodo **raiz)
{
	BYTE buf[BUF_SZ];
	int nbytes, cont;
	struct nodo *n;


	rewind(fp);
	*raiz=NULL;

	do
	{
		nbytes=fread(buf, 1, BUF_SZ, fp);
		if (ferror(fp))
		{
			perror("fread: calcularFreq()");
			exit(1);
		}

		for (cont=0; cont < nbytes; cont++)
		{
			if ((n=yaInsertado(*raiz, buf[cont])))
				n->freq++;
			else
				*raiz=insertar(*raiz, buf[cont]);
		}
	} while (!feof(fp));

	*raiz=ordenar(*raiz);
}


struct nodo *insertarOrden(struct nodo *raiz, struct nodo *nuevo)
{
	struct nodo *aux=raiz, *ant;


	while (aux != NULL && nuevo->freq > aux->freq)
	{
		ant=aux;
		aux=aux->sig;
	}

	nuevo->sig=aux;
	if (aux == raiz)
		raiz=nuevo;
	else
		ant->sig=nuevo;

	return raiz;
}


struct nodo *crearArbolHuffman(struct nodo *raiz)
{
	struct nodo *nuevo;


	if (raiz == NULL)
		return NULL;

	while (raiz->sig != NULL)
	{
		nuevo=crearNodo();
		nuevo->freq=raiz->freq + raiz->sig->freq;
		nuevo->hizq=raiz;
		nuevo->hdch=raiz->sig;
		raiz=insertarOrden(raiz->sig->sig, nuevo);
	}

	return raiz;
}


void borrarArbolHuffman(struct nodo *raiz)
// Libera la memoria ocupada por el arbol de Huffman
{
	if (raiz != NULL)
	{
		borrarArbolHuffman(raiz->hizq);
		borrarArbolHuffman(raiz->hdch);
		free(raiz);
	}
}


int salvarArbolHuffman(struct nodo *raiz, BYTE *mem)
{
	static int pos_mem, pos_pos;


	if (raiz != NULL)
	{
		if (raiz->hizq == NULL)   // Hoja
		{
			writeBits(mem, &pos_mem, &pos_pos, UNO, 1);
			writeBits(mem, &pos_mem, &pos_pos, raiz->c, 8);
		}
		else	// NO hoja
		{
			writeBits(mem, &pos_mem, &pos_pos, 0, 1);
			salvarArbolHuffman(raiz->hizq, mem);
			salvarArbolHuffman(raiz->hdch, mem);
		}
	}

	return pos_mem;
}


struct nodo *buscarNodoSinHdch(struct nodo *n)
{
	while (n != NULL && n->hdch != NULL)
		n=n->padre;

	return n;
}


int cargarArbolHuffman(struct nodo **raiz, BYTE *mem)
{
	struct nodo *aux, *nuevo;
	int pos_mem=0, pos_pos=0, dch=0;
	BYTE b;


	*raiz=crearNodo();
	readBits(mem, &pos_mem, &pos_pos, &b, 1);
	if (b == UNO)
	{
		readBits(mem, &pos_mem, &pos_pos, &b, 8);
		(*raiz)->c=b;
		return 2;
	}

	aux=*raiz;
	while (aux != NULL)
	{
		nuevo=crearNodo();
		nuevo->padre=aux;

		readBits(mem, &pos_mem, &pos_pos, &b, 1);
		if (b == 0)
		{
			if (dch)
			{
				aux->hdch=nuevo;
				dch=0;
			}
			else
				aux->hizq=nuevo;

			aux=nuevo;
		}
		else
		{
			readBits(mem, &pos_mem, &pos_pos, &b, 8);
			nuevo->c=b;

			if (dch)
			{
				aux->hdch=nuevo;
				aux=buscarNodoSinHdch(aux);
			}
			else
			{
				aux->hizq=nuevo;
				dch=1;
			}
		}
	}

	return pos_mem+1;
}
