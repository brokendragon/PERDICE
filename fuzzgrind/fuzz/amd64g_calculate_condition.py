

def inverse(d):
    new_d = {}
    for (k, v) in d.items():
        new_d[v] = k
    return new_d
    

# valgrind/VEX/priv/guest-amd64/gdefs.h
AMD64CCop = inverse({
    'AMD64G_CC_OP_COPY':0,

    'AMD64G_CC_OP_ADDB':1,
    'AMD64G_CC_OP_ADDW':2 ,
    'AMD64G_CC_OP_ADDL':3,
    'AMD64G_CC_OP_ADDQ':4,

    'AMD64G_CC_OP_SUBB':5,
    'AMD64G_CC_OP_SUBW':6 ,
    'AMD64G_CC_OP_SUBL':7,
    'AMD64G_CC_OP_SUBQ':8,

    'AMD64G_CC_OP_ADCB':9,
    'AMD64G_CC_OP_ADCW':10,
    'AMD64G_CC_OP_ADCL':11,
    'AMD64G_CC_OP_ADCQ':12,

    'AMD64G_CC_OP_SBBB':13,
    'AMD64G_CC_OP_SBBW':14 ,
    'AMD64G_CC_OP_SBBL':15,
    'AMD64G_CC_OP_SBBQ':16,

    'AMD64G_CC_OP_LOGICB':17,
    'AMD64G_CC_OP_LOGICW':18 ,
    'AMD64G_CC_OP_LOGICL':19,
    'AMD64G_CC_OP_LOGICQ':20,

    'AMD64G_CC_OP_INCB':21,
    'AMD64G_CC_OP_INCW':22 ,
    'AMD64G_CC_OP_INCL':23,
    'AMD64G_CC_OP_INCQ':24,

    'AMD64G_CC_OP_DECB':25,
    'AMD64G_CC_OP_DECW':26 ,
    'AMD64G_CC_OP_DECL':27,
    'AMD64G_CC_OP_DECQ':28,

    'AMD64G_CC_OP_SHLB':29 ,
    'AMD64G_CC_OP_SHLW':30 ,
    'AMD64G_CC_OP_SHLL':31,
    'AMD64G_CC_OP_SHLQ':32,

    'AMD64G_CC_OP_SHRB':33 ,
    'AMD64G_CC_OP_SHRW':34 ,
    'AMD64G_CC_OP_SHRL':35,
    'AMD64G_CC_OP_SHRQ':36,

    'AMD64G_CC_OP_ROLB':37,
    'AMD64G_CC_OP_ROLW':38 ,
    'AMD64G_CC_OP_ROLL':39,
    'AMD64G_CC_OP_ROLQ':40,

    'AMD64G_CC_OP_RORB':41,
    'AMD64G_CC_OP_RORW':42 ,
    'AMD64G_CC_OP_RORL':43,
    'AMD64G_CC_OP_RORQ':44,

    'AMD64G_CC_OP_UMULB':45,
    'AMD64G_CC_OP_UMULW':46 ,
    'AMD64G_CC_OP_UMULL':47,
    'AMD64G_CC_OP_UMULQ':48,

    'AMD64G_CC_OP_SMULB':49,
    'AMD64G_CC_OP_SMULW':50 ,
    'AMD64G_CC_OP_SMULL':51,
    'AMD64G_CC_OP_SMULQ':52
})
    
AMD64Condcode = inverse({ 
      'AMD64CondO'      : 0,  #/* overflow           */
      'AMD64CondNO'     : 1,  #/* no overflow        */
      'AMD64CondB'      : 2,  #/* below              */
      'AMD64CondNB'     : 3,  #/* not below          */
      'AMD64CondZ'      : 4,  #/* zero               */
      'AMD64CondNZ'     : 5,  #/* not zero           */
      'AMD64CondBE'     : 6,  #/* below or equal     */
      'AMD64CondNBE'    : 7,  #/* not below or equal */
      'AMD64CondS'      : 8,  #/* negative           */
      'AMD64CondNS'     : 9,  #/* not negative       */
      'AMD64CondP'      : 10, #/* parity even        */
      'AMD64CondNP'     : 11, #/* not parity even    */
      'AMD64CondL'      : 12, #/* jump less          */
      'AMD64CondNL'     : 13, #/* not less           */
      'AMD64CondLE'     : 14, #/* less or equal      */
      'AMD64CondNLE'    : 15, #/* not less or equal  */
      'AMD64CondAlways' : 16  #/* HACK */
})


SIZE = {
    'Q':64,
    'L': 32,
    'W': 16,
    'B': 8
}


def sub(size, cond, cc_dep1, cc_dep2):
    if cond == 'AMD64CondZ':
        if   size == 8:  return '1Uto64(CmpEQ8(64to8(%s),64to8(%s)))' % (cc_dep1, cc_dep2)
        elif size == 64: return '1Uto64(CmpEQ64(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'AMD64CondLE':
        if  size == 8: return '1Uto64(CmpLE64S(8Sto64(%s),8Sto64(%s)))' % (cc_dep1, cc_dep2)
        elif   size == 32: return '1Uto64(CmpLE64S(32Sto64(%s),32Sto64(%s)))' % (cc_dep1, cc_dep2)
        elif   size == 64: return '1Uto64(CmpLE64S(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'AMD64CondL':
        if  size == 8: return '1Uto64(CmpLT64S(8Sto64(%s),8Sto64(%s)))' % (cc_dep1, cc_dep2)
        elif   size == 32: return '1Uto64(CmpLT64S(32Sto64(%s),32Sto64(%s)))' % (cc_dep1, cc_dep2)
        elif   size == 64: return '1Uto64(CmpLT64S(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'AMD64CondB':
        if   size == 8:  return '1Uto64(CmpLT64U(8Uto64(%s),8Uto64(%s)))' % (cc_dep1, cc_dep2)
        elif size == 16: return '1Uto64(CmpLT64U(16Uto64(%s),16Uto64(%s)))' % (cc_dep1, cc_dep2)
        elif size == 32: return '1Uto64(CmpLT64U(32Uto64(%s),32Uto64(%s)))' % (cc_dep1, cc_dep2)
        elif size == 64: return '1Uto64(CmpLT64U(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'AMD64CondBE':
        if   size == 8:  return '1Uto64(CmpLE64U(8Uto64(%s),8Uto64(%s)))' % (cc_dep1, cc_dep2)
        elif size == 16: return '1Uto64(CmpLE64U(16Uto64(%s),16Uto64(%s)))' % (cc_dep1, cc_dep2)
        elif size == 32: return '1Uto64(CmpLE64U(32Uto64(%s),32Uto64(%s)))' % (cc_dep1, cc_dep2)
        elif size == 64: return '1Uto64(CmpLE64U(%s,%s))' % (cc_dep1, cc_dep2)
    elif cond == 'AMD64CondNBE':
        if   size == 8:  return '1Uto64(CmpLT64U(8Uto64(%s),8Uto64(%s)))' % (cc_dep1, cc_dep2)
        
    assert False, "Can't generate constraint for cond=%s, size=%d" % (cond, size)


def amd64g_calculate_condition(cond, cc_op, cc_dep1, cc_dep2,cc_dep3=0):
    cond = AMD64Condcode[cond.const.value]
    cc_op = AMD64CCop[cc_op.const.value]
    size = SIZE[cc_op[-1]]
    
    if 'SUB' in cc_op:
        e = sub(size, cond, cc_dep1, cc_dep2)
    else:
        print "in amd64g return None"
        return None
        #assert False, cc_op
        
    return e
