//
//  parser.c
//  Parser & Code Generator
//
//  UCF - COP 3402: Systems Software
//  Summer 2015
//
//  Team Members:
//  Justin Mackenzie
//  Alan Yepez
//

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

//  I/O file names.
#define INPUT_FILE "lexemelist.txt"
#define VM_OUTPUT_FILE "mcode.txt"

#define MAX_SIZE 12
#define MAX_SYMBOL_TABLE_SIZE 100
#define MAX_CODE_LENGTH 500         //  From module 1.

//  Internal representation of PL\0 Tokens.
typedef enum Tokens{
    nulsym = 1, identsym = 2, numbersym = 3, plussym = 4,
    minussym = 5, multsym = 6,  slashsym = 7, oddsym = 8,
    eqlsym = 9, neqsym = 10, lessym = 11, leqsym = 12,
    gtrsym = 13, geqsym = 14, lparentsym = 15, rparentsym = 16,
    commasym = 17, semicolonsym = 18, periodsym = 19, becomessym = 20,
    beginsym = 21, endsym = 22, ifsym = 23, thensym = 24,
    whilesym = 25, dosym = 26, callsym = 27, constsym = 28,
    varsym = 29, procsym = 30, writesym = 31, readsym = 32,
    elsesym = 33
}token_type;

typedef struct {
    int kind;       // const = 1, var = 2, proc = 3
    char name[MAX_SIZE];  // name up to 11 chars
    int val;        // number (ASCII value)
    int level;      // L level
    int addr;       // M address
} symbol;

typedef struct {
    int op;
    int l;
    int m;
} instruction;

//  Global variable declaration.
FILE *ifp, *ofp = NULL;
symbol symbol_table[MAX_SYMBOL_TABLE_SIZE];
instruction vm_code[MAX_CODE_LENGTH];
int c = 0,      //  Index for the vm code.
symi = 0,   //  Index for symbol table.
token = -1, //  Token class.
valid = 1;  //  Boolean. 1 = no errors, 0 = errors.

//  Function declarations.
void parser();
void program(int lex);
void procedure(int lex);
void block(int lex);
void statement(int lex);
void condition(int lex);
void expression(int lex);
void term(int lex);
void factor(int lex);
void error();

void record(int kind, char name[], int val, int level, int addr);  //  Write a new symbol to symbol table.
int find(char name[]);    //  Searches for an existing symbol in symbol table.
void translate(int op, int l, int m);   //  Conversion to VM language.

int main(int argc, const char * argv[]) {
    
    ifp = fopen(INPUT_FILE, "r");
    ofp = fopen(VM_OUTPUT_FILE, "w");
    
    parser();
    
    if (valid == 1)
        
        fprintf(ofp, "No errors, program is syntactically correct.\n");
    
    int i;
    
    for ( i = 0; i <= c; i ++ )
        
        fprintf(ofp, "%d %d %d\n", vm_code[i].op, vm_code[i].l, vm_code[i].m);
    
    fclose(ifp);
    fclose(ofp);
    
    return 0;
    
}

// Wrapper function for the parsing logic.
void parser()
{
    
    int lex = 0;
    //  Initiate parsing by calling procedure parser function.
    program(lex);
    
}

void program(int lex)
{
    
    fscanf(ifp, "%d", &token);
    
    translate(6, lex, 5);
    
    block(lex);
    
    if (token != periodsym && valid)
        
        error(9);
    
    if (valid)
        
        translate(2, 0, 0);
    
}

void block(int lex)    //  Alan
{
    
    int kind, val;
    char name[MAX_SIZE];
    
    if (token == constsym)
    {
        
        kind = constsym;
        
        do
        {
            
            fscanf(ifp, "%d", &token);
            
            if (token != identsym )
            {
                error(4);
                
                return;
                
            }
            else
            {
                
                fscanf(ifp, "%s", name);
                
            }
            
            if (token != eqlsym)
            {
                
                if (token == becomessym)
                    
                    error(1);
                
                else
                    
                    error(3);
                
                return;
                
            }
            
            fscanf(ifp, "%d", &token);
            
            if (token != numbersym)
            {
                
                error(2);
                
                return;
                
            }
            else
            {
                
                fscanf(ifp, "%d", &val);
                
            }
            
            record(kind, name, val, 0, 0);
            
            fscanf(ifp, "%d", &token);
            
        }
        while (token == commasym);
        
        if (token != semicolonsym)
        {
            
            error(5);
            
            return;
            
        }
        
        fscanf(ifp, "%d", &token);
        
    }
    
    if (token == varsym)
    {
        
        int j = 3;
        
        kind = varsym;
        
        do
        {
            fscanf(ifp, "%d", &token);
            
            if (token != identsym && valid)
            {
                error(4);
                
                return;
                
            }
            else
            {
                
                fscanf(ifp, "%s", name);
                
            }
            
            record(kind, name, 0,  lex, j);
            
            fscanf(ifp,"%d", &token);
            
            j++;
            
            
        }
        while ( token == commasym );
        
        if (token != semicolonsym && valid)
        {
            
            error(5);
            
            return;
            
        }
        
        fscanf(ifp,"%d", &token);
        
    }
    
    while (token == procsym)
    {
        
        kind = procsym;
        
        fscanf(ifp,"%d", &token);
        
        if (token != identsym && valid)
        {
            error(4);
            
            return;
            
        }
        else
        {
            
            fscanf(ifp, "%s", name);
            
        }
        
        record(kind, name, 0,  lex, c);
        
        fscanf(ifp, "%d", &token);
        
        if (token != semicolonsym && valid)
        {
            
            error(6);
            
            return;
            
        }
        
        fscanf(ifp, "%d", &token);
        
        block(lex + 1);
        
        if (token != semicolonsym && valid)
        {
            
            error(5);
            
            return;
            
        }
        
        fscanf(ifp, "%d", &token);
        
        translate(2, 0, 0);
        
    }
    
    statement(lex);
    
}

void statement(int lex)    //  Justin
{
    
    if (token == identsym)
    {
        
        char name[MAX_SIZE];
        
        fscanf(ifp, "%s", name);
        
        int index = find(name);
        
        if (index == -1 && valid)
        {
            
            error(11);
            
            return;
            
        }
        
        if (symbol_table[index].kind != varsym  && valid)
        {
            
            error(12);
            
            return;
            
        }
        
        fscanf(ifp, "%d", &token);
        
        if (token != becomessym && valid)
        {
            
            error(13);
            
        }
        
        fscanf(ifp, "%d", &token);
        
        expression(lex);
        
        translate(4, symbol_table[index].level, symbol_table[index].addr);
        
    }
    else if (token == callsym)
    {
        
        fscanf(ifp,"%d", &token);
        
        if (token != identsym && valid)
        {
            
            error(14);
            
            return;
            
        }
        
        char name[MAX_SIZE];
        
        fscanf(ifp,"%s", name);
        
        int index = find(name);
        
        if (index == -1  && valid)
        {
            
            error(11);
            
            return;
            
        }
        
        translate(5, symbol_table[index].level, symbol_table[index].addr);
        
        translate(6, lex, 4);
        
        fscanf(ifp,"%d", &token);
        
    }
    else if (token == beginsym)
    {
        
        fscanf(ifp,"%d", &token);
        
        statement(lex);
        
        while (token == semicolonsym)
        {
            
            fscanf(ifp,"%d", &token);
            
            statement(lex);
            
        }
        
        if (token != endsym && valid)
        {
            
            error(9);
            
            return;
            
        }
        
        fscanf(ifp,"%d", &token);
        
    }
    else if (token == ifsym)
    {
        
        fscanf(ifp,"%d", &token);
        
        condition(lex);
        
        if (token != thensym && valid)
        {
            
            error(16);
            
            return;
        }
        
        else
        {
            
            fscanf(ifp,"%d", &token);
            
        }
        
        int c1 = c;
        
        translate(8, 0, 0);
        
        statement( lex);
        
        if (token == elsesym)
        {
            
            fscanf(ifp,"%d", &token);
            
            int c2 = c;
            
            translate(7, 0, 0);
            
            vm_code[c1].m = c;
            
            statement(lex);
            
            vm_code[c2].m = c;
            
        }
        
        else
        {
            
            vm_code[c1].m = c;
            
        }
        
    }
    else if (token == whilesym)
    {
        
        int c1 = c;
        
        fscanf(ifp,"%d", &token);
        
        condition(lex);
        
        int c2 = c;
        
        translate(8, 0, 0);
        
        if (token != dosym && valid)
        {
            
            error(18);
            
            return;
            
        }
        
        else
        {
            
            fscanf(ifp,"%d", &token);
            
        }
        
        statement(lex);
        
        translate(7, 0, c1);
        
        vm_code[c2].m = c;
        
    }
    
}

void condition(int lex)    //  Alan
{
    
    if (token == oddsym)
    {
        
        fscanf(ifp, "%d", &token);
        
        expression(lex);
        
        translate(2, 0, 6);
        
    }
    else
    {
        
        expression(lex);
        
        int rational = token;
        
        if ((token < eqlsym || token > geqsym) && valid)
        {
            
            error(20);
            
            return;
            
        }
        
        fscanf(ifp, "%d", &token);
        
        expression(lex);
        
        translate(2, 0, rational - 1);
        
    }
    
}

void expression(int lex) //    Justin
{
    
    int operation;
    
    if (token == plussym || token == minussym)
    {
    
        operation = token;
        
        fscanf(ifp, "%d", &token);
        
        term(lex);
        
        if (operation == minussym)
        {
            translate(2, 0, 1);
        }
        
    }
    else
        
        term(lex);
    
    
    while (token == plussym || token == minussym)
    {
        
        operation = token;
        
        fscanf(ifp, "%d", &token);
        
        term(lex);
        
        if (operation == plussym)
        {
            
            translate(2, 0, 2);
            
        }
        else
        {
            
            translate(2, 0, 4);
            
        }
        
        
    }
    
}

void term(int lex)   // Alan
{
    
    int operation = 0;
    
    factor(lex);
    
    while (token == multsym || token == slashsym)
    {
        
        operation = token;
        
        fscanf(ifp, "%d", &token);
        
        factor(lex);
        
        if (operation == multsym)
        {
            
            translate(2, 0, 4);
            
        }
        else
        {
            
            translate(2, 0, 5);
            
        }
        
    }
    
}

void factor(int lex) //    Justin
{
    
    char name[12];
    
    int index, val;
    
    if (token == identsym)
    {
        
        fscanf(ifp, "%s", name);
        
        index = find(name);
        
        if (symbol_table[index].kind == constsym)
        {
            
            translate(1, 0, symbol_table[index].val);
            
        }
        else if (symbol_table[index].kind == varsym)
        {
            
            translate(3, symbol_table[index].level, symbol_table[index].addr);
            
        }
        else
        {
            
            error(21);
            
            return;
            
        }
        
        fscanf(ifp,"%d", &token);
        
    }
    
    else if (token == numbersym)
    {
        
        fscanf(ifp, "%d", &val);
        
        translate(1, 0, val);
        
        fscanf(ifp,"%d", &token);
        
    }
    
    else if (token == lparentsym)
    {
        
        fscanf(ifp,"%d", &token);
        
        expression(lex);
        
        if (token != rparentsym && valid)
        {
            
            error(22);
            
            return;
            
        }
        
        fscanf(ifp,"%d", &token);
        
    }
    
    else
    {
        
        error(19);
        
        return;
        
    }
    
}

void driver(int argc, const char * argv[])      //  TODO: Move logical to another .c.
{
    
    int i;
    
    for ( i = 0; argc > 0; i++, argc-- )
    {
        
        const char* directive = argv[i];
        
        if ( strcmp(directive, "-l") )
            
            printf("Print the list of lexemes/tokens.\n");
        
        else if ( strcmp(directive, "-a") )
            
            printf("Print the generated assembly code.\n");
        
        else if ( strcmp(directive, "-v") )
            
            printf("Print virtual machine execution trace.\n");
        
    }
    
}

void record(int kind, char name[], int val, int level, int addr)
{
    
    if ( find(name) == -1 )
    {
        
        if (kind == constsym)
        {
            
            symbol_table[symi].kind = constsym;
            strcpy(symbol_table[symi].name, name);
            symbol_table[symi].val = val;
            
        }
        
        else
        {
            
            symbol_table[symi].kind = kind;
            strcpy(symbol_table[symi].name, name);
            symbol_table[symi].level = level;
            symbol_table[symi].addr = addr;
            
        }
        
        symi++;
        
    }
    
}

int find(char name[])
{
    
    int i = 0;
    
    if( c != 0 )
    {
        
        while ( i != c )
        {
            
            if ( strcmp(symbol_table[i].name, name) == 0 )
                
                return i;
            
            else
                
                i++;
            
        }
        
    }
    
    return -1;
    
}

void translate(int op, int l, int m)
{
    
    if ( c <= MAX_CODE_LENGTH )
    {
        
        vm_code[c].op = op;
        vm_code[c].l = l;
        vm_code[c].m = m;
        
        c++;
        
    }
    else
        
        error(26);
    
}

//  Prints error message corresponding to an error code.
void error(int err)
{
    
    //  Mark code as not valid.
    valid = 0;
    
    switch (err)
    {
            
        case 1:
        {
            
            printf("Error 1: Use = instead of :=.\n");
            
            break;
            
        }
        case 2:
        {
            
            printf("Error 2: = must be followed by a number.\n");
            
            break;
            
        }
        case 3:
        {
            
            printf("Error 3: Identifier must be followed by =.\n");
            
            break;
            
        }
        case 4:
        {
            
            printf("Error 4: const, int, procedure must be followed by identifier.\n");
            
            break;
            
        }
        case 5:
        {
            
            printf("Error 5: Semicolon or comma missing.\n");
            
            break;
            
        }
        case 6:
        {
            
            printf("Error 6: Incorrect symbol after procedure declaration.\n");
            
            break;
            
        }
        case 7:
        {
            
            printf("Error 7: Statement expected.\n");
            
            break;
            
        }
        case 8:
        {
            
            printf("Error 8: Incorrect symbol after statement part in block.\n");
            
            break;
            
        }
        case 9:
        {
            
            printf("Error 9: Period expected.\n");
            
            break;
            
        }
        case 10:
        {
            
            printf("Error 10: Semicolon between statements missing.\n");
            
            break;
            
        }
        case 11:
        {
            
            printf("Error 11: Undeclared identifier.\n");
            
            break;
            
        }
        case 12:
        {
            
            printf("Error 12: Assignment to constant or procedure is not allowed.\n");
            
            break;
            
        }
        case 13:
        {
            
            printf("Error 13: Assignment operator expected.\n");
            
            break;
            
        }
        case 14:
        {
            
            printf("Error 14: call must be followed by an identifier.\n");
            
            break;
            
        }
        case 15:
        {
            
            printf("Error 15: Call of a constant or variable is meaningless.\n");
            
            break;
            
        }
        case 16:
        {
            
            printf("Error 16: then expected.\n");
            
            break;
            
        }
        case 17:
        {
            
            printf("Error 17: Semicolon or } expected.\n");
            
            break;
            
        }
        case 18:
        {
            
            printf("Error 18: do expected.\n");
            
            break;
            
        }
        case 19:
        {
            
            printf("Error 19: Incorrect symbol following statement.\n");
            
            break;
            
        }
        case 20:
        {
            
            printf("Error 20: Relational operator expected.\n");
            
            break;
            
        }
        case 21:
        {
            
            printf("Error 21: Expression must not contain a procedure identifier.\n");
            
            break;
            
        }
        case 22:
        {
            
            printf("Error 22: Right parenthesis missing.\n");
            
            break;
            
        }
        case 23:
        {
            
            printf("Error 23: The preceding factor cannot begin with this symbol.\n");
            
            break;
            
        }
        case 24:
        {
            
            printf("Error 24: An expression cannot begin with this symbol.\n");
            
            break;
            
        }
        case 25:
        {
            
            printf("Error 25: This number is too large.\n");
            
            break;
            
        }
        case 26:
        {
            
            printf("Error: Code size has been exceed.\n");
            
            break;
            
        }
        default:
            
            printf("Error: Error not vald=id.\n");    //bug
            
    }
    
}