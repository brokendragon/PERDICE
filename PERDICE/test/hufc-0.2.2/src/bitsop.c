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

#include "bitsop.h"


void writeBits(BYTE *mem, int *pos_mem, int *pos_pos, BYTE b, int bit_count)
{
	b = (b >> (8-bit_count)) << (8-bit_count);
	mem[*pos_mem] |= b >> *pos_pos;

	if (bit_count >= 8-(*pos_pos))
	{
		(*pos_mem)++;

		if (bit_count > 8-(*pos_pos))
			mem[*pos_mem] |= b << (8-(*pos_pos));
	}

	*pos_pos=(*pos_pos + bit_count) % 8;
}


void readBits(BYTE *mem, int *pos_mem, int *pos_pos, BYTE *b, int bit_count)
{
	*b=mem[*pos_mem] << *pos_pos;

	if (bit_count >= 8-(*pos_pos))
	{
		(*pos_mem)++;

		if (bit_count > 8-(*pos_pos))
			*b |= mem[*pos_mem] >> (8-(*pos_pos));
	}

	*b=(*b >> (8-bit_count)) << (8-bit_count);
	*pos_pos=(*pos_pos + bit_count) % 8;
}
