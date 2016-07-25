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

#include "checksum.h"

/*
 * On a little endian machine, the checksum is returned with
 * swapped bytes. There is nothing wrong with this as it will
 * be the same when stored in a file, independently of the
 * endian. Example:
 *
 * Big endian checksum    = 0x03E8 (stored as 03E8 in memory)
 * Little endian checksum = 0xE803 (stored as 03E8 in memory)
 *
 * The problem raises if the checksum is printed on the
 * screen because it is going to be interpreted differently.
 * The solution is to explicitly swap the bytes before the
 * printing using the function htons() or a similar one.
 */


#ifdef __HUFC_USE_X86_ASM__

u16 checksum(u16 sum, size_t len, BYTE *data)
{
	u32 dummy;


	asm ("add%z3	%2,%3\n\t"
	     "neg%z2	%2\n\t"
	     "jnc	2f\n\t"		// Jump if there are no data
	     "bt%z2	$0,%2\n\t"
	     "jnc	0f\n\t"		// Jump if data length is even

	     "movzbl	-1(%3),%1\n\t"	// Read the last byte in data
	     "sub%z3	$1,%3\n\t"
	     "addl	%1,%k0\n\t"
	     "add%z2	$1,%2\n\t"
	     "jz	1f\n\t"		// Jump if we had just one byte of data

	     "0:movzwl	(%3,%2),%1\n\t"
	     "addl	%1,%k0\n\t"
	     "add%z2	$2,%2\n\t"
	     "jnz	0b\n\t"

	     "1:movl	%k0,%1\n\t"
	     "shrl	$16,%1\n\t"
	     "addw	%w1,%0\n\t"
	     "adcl	$0,%k0\n\t"
	     "2:notl	%k0"
	    : "+r"(sum), "=&r"(dummy)
	    : "r"(len), "r"(data)
	    : "cc"
	    );

	return sum;
}

#else

u16 checksum(u16 sum, size_t len, BYTE *data)
{
	u32 tmp=sum;


	while (len > 1)
	{
		tmp += *(u16 *)data;
		data += sizeof(u16);
		len -= 2;
	}

	if (len > 0)
#ifdef __HUFC_BIG_ENDIAN__
		tmp += ((u16)*data) << 8;
#else
		tmp += *data;
#endif

	while (tmp >> 16)
		tmp = (tmp & 0xFFFF) + (tmp >> 16);

	return ~tmp;
}

#endif
