/*----------------------------------------------------------------------------*/
/* argshand.c -- Manipulation of the input arguments. gse. 1997.              */
/*----------------------------------------------------------------------------*/
#include "argshand.h"

/*----------------------------------------------------------------------------*/
/* Look for the string 'str_to_find' in 'arg'.                                */
/* If it is found, return the next string in arg.                             */
/* In other case return NULL.                                                 */
/*----------------------------------------------------------------------------*/
char *GetArg(char *str_to_find, int narg, char **arg) {
    int i;
    for(i=0;i<narg;i++)
        if(strstr(arg[i],str_to_find))
            return arg[i+1];
    return NULL;
}


/*----------------------------------------------------------------------------*/
/* Return 1 if the string 'str_to_find' is in the command line 'arg'          */
/*----------------------------------------------------------------------------*/
int ExistArg(char *str_to_find, int narg, char **arg) {
    int i;
    for(i=0;i<narg;i++)
        if(strstr(arg[i],str_to_find)) return 1;
    return 0;
}
