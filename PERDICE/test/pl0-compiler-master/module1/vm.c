//
//  Alan Yepez
//  UCF - COP 3402: Systems Software
//  Summer 2015
//  Last revision: 5-29-15.
//  Due 05-31-15.
//

#include <stdio.h>

//  Declaration of constants.

#define MAX_CODE_LENGTH 500
#define MAX_LEXI_LEVELS 3
#define MAX_STACK_HEIGHT 2000

//  Declaration of instruction struct.

typedef struct intructionStructure
{
    
    int op;
    int l;
    int m;
    
}instruction;

//  Declaration of global variables.

static int bp = 1;
static instruction ir;
static int pc;
static int sp;;

static int instrCount;
static int lexiLevel;
static char *opName[] = {"null", "lit", "opr", "lod", "sto", "cal", "inc", "jmp", "jpc", "sio"};
static FILE *ofp = NULL;

//  Declaration of staticly-sized data structures.

instruction code[MAX_CODE_LENGTH];
int stack[MAX_STACK_HEIGHT];
int basePointers[MAX_STACK_HEIGHT];

//  Function declarations.

int base (int b, int level);
void execution();
void op2execution();
void printInterpretedAssemblyLanguage();
void printStack();
int readInputFile();

int main ( int argc, const char * argv[] )
{
    
    //  Function call to read input file.
    
    instrCount = readInputFile();
    
    //  Print the input to output file, formatted.
    
    printInterpretedAssemblyLanguage();
    
    //  Function call to begin execution of instructions.
    
    execution();
    
    //  Function end.

    return 0;
    
}

//
//  Reads input file into code struct array.
//
//  @return
//      int, number of instructions read.
// 
int readInputFile ()
{
    
    //  Create a file pointer.
    
     FILE *ifp = fopen("mcode.txt", "r");
    
    //  Reference for number of instruction in input file.
    
    int instrCount = 0;
    
    //  Verify file exists.
    
    if ( ifp )
    {
        
        //  Read inputs until end of file is reached.
        
        while ( !feof(ifp) )
        {
            
            fscanf(ifp, "%d %d %d", &code[instrCount].op, &code[instrCount].l, &code[instrCount].m);
            
            instrCount++;
            
        }
        
    }
    
    //  Case for missing input file.
    
    else
        
        printf("ERROR: File was not found.\n");
    
    //  Return number of instructions read.
    
    return instrCount;
    
}

//
//  Prints input intructions from code struct array to output file.
//
void printInterpretedAssemblyLanguage ()
{
    
    //  Create, then verify output file exists.
    
    ofp = fopen("stacktrace.txt", "w");
    
    if ( ofp )
    {
        
        //  Print formatted header for output file.
        
        fprintf(ofp, "%-6s %-5s %-5s %-5s\n", "Line", "OP", "L", "M");
        
        //  Formatting for scenario with no instructions.
        
        if ( instrCount < 1 )
            
            fprintf(ofp, "N/A\n");
        
        //  Iteratively print instructions to output file.
        
        int i;
        
        for ( i = 0; i < instrCount; i++ )
            
            if ( code[i].op > 0 &&  code[i].op <= 9)
            
                fprintf(ofp, "%-6d %-5s %-5d %-5d\n", i, opName[code[i].op], code[i].l, code[i].m);
            
        
    }
    
    //  Display error message if output file could not be generated.
    
    else
        
        printf("ERROR: Output file does not exist.\n");
    
}

//
//  Begins execution of instructions. Prints results to output file.
//
void execution ()
{
    
    //  Initialize the execution output.
    
    fprintf(ofp, "\n%27s %5s %5s %8s\n", "pc", "bp", "sp", "stack");
    fprintf(ofp, "%-24s %-5d %-5d %-5d\n", "Initial values", pc, bp, sp);
    
    //  Continue execution util instruction exists.

    while ( pc < instrCount )
    {
        
        //  Retrieve instruction from memory.
        
        ir = code[pc];
        
        //  Print instruction to output file. Update PC after printing.
        
        fprintf(ofp, "%-6d %-5s %-5d %-5d ", pc++, opName[ir.op], ir.l, ir.m);
        
        //  Enter switch statement to appropriate perform instruction.
        
        switch ( ir.op )
        {

            case 1: //   LIT
                
                stack[++sp] = ir.m;

                break;
                
            case 2: //   OPR
                
                //  Method call to perform arithmetic and logical operations.
                    
                op2execution();
                
                break;
                
            case 3: //   LOD
                
                stack[++sp] = stack[base(bp, ir.l) + ir.m];

                break;
                
            case 4: //   STO
                
                stack[base(bp, ir.l) + ir.m] = stack[sp--];
                
                break;
                
            case 5: //   CAL
                
                stack[sp + 1] = 0;
                stack[sp + 2] = base(bp, ir.l);
                stack[sp + 3] = bp;
                stack[sp + 4] = pc;
                
                bp = sp + 1;
                pc = ir.m;
                
                if ( ++lexiLevel > MAX_LEXI_LEVELS )
                    
                    printf("ERROR: Lexicographical level exceeded maximum.");
                
                basePointers[lexiLevel] = bp;
                
                break;
                
            case 6: //   INC
                
                sp += ir.m;
                
                break;
                
            case 7: //   JMP
                
                pc = ir.m;
                
                break;
                
            case 8: //   JPC
                
                if ( stack[sp--] == 0 )
                    
                    pc = ir.m;
                
                break;
                
            case 9: //   SIO
                
                if ( ir.m == 0 )
                    
                    printf("%d\n", stack[sp--]);
                
                else if ( ir.m == 1 )
                {
                    
                    printf("Specify input for SIO instruction on line %d.\n", pc);
                    
                    scanf("%d", &stack[++sp]);
                    
                }
                
                else if ( ir.m != 2 )
                    
                    printf("ERROR: Invalid M value encountered.\n");
                
                break;
                
            default:
                
                printf("ERROR: Invalid OP encountered.\n");
                
        }

        //  Print status of registers and stack to output file.
        
        fprintf(ofp, "%-5d %-5d %-6d", pc, bp, sp);
        printStack();
        
        //  Exit loop instruction called for hault.
        
        if ( ir.op == 9 && ir.m == 2 )
            
            return;

    }
    
}

// 
//  Prints the contents of the stack. Elements separated by a space.
//
void printStack ()
{
    
    //  Create variables for local use.
    
    int i;
    int ll = lexiLevel;
    int currentLevel = 1;
    
    //  Iterate through all items on stack and print.
    
    for ( i = 1; i <= sp; i++ )
    {
        
        //  Conditionally watch for brackets.
        
        if ( ll > 0 && currentLevel <= ll && basePointers[currentLevel] == i )
        {
            
            fprintf( ofp, "| " );
            
            currentLevel++;
        
        }
        
        fprintf( ofp, "%d ", stack[i] );
        
    }
    
    //  Newline formatting.
    
    fprintf( ofp, "\n" );
        
}

//
//  Recursively finds the base when an L offset exists.
//
//  @param  b
//      int representing the base pointer.
//  @param  level
//      int representing the number of offset levels.
//  @return
//      int representing adjusted base.
//
int base (int b, int level)
{
    
    //  Recursive call until base case is met.
    
    return level < 1 ? b : base( stack[b + 2], --level );
    
}

//
//  Differentiates and executes op = 2 arithmetic and logical operations.
//
void op2execution ()
{
    
    //  Conditionally decrement stack pointer.
    
    if ( ir.m != 0 && ir.m != 1 && ir.m != 6 )
        
        sp--;
    
    //  Enter switch statement to decipher instruction.
    
    switch ( ir.m ) {
            
        case 0: //  RET
            
            sp = bp - 1;
            pc = stack[sp + 4];
            bp = stack[sp + 3];
            
            lexiLevel--;
            
            break;
            
        case 1: //  NEG
            
            stack[sp] *= -1;
            
            break;
            
        case 2: //  ADD
            
            stack[sp] += stack[sp + 1];
            
            break;
            
        case 3: //  SUB
            
            stack[sp] -= stack[sp + 1];
            
            break;
            
        case 4: //  MUL
            
            stack[sp] *= stack[sp + 1];
            
            break;
            
        case 5: //  DIV
            
            stack[sp] /= stack[sp + 1];
            
            break;
            
        case 6: //  ODD
            
            stack[sp] %= 2;
            
            break;
            
        case 7: //  MOD
            
            stack[sp] %= stack[sp + 1];
            
            break;
            
        case 8: //  EQL
            
            stack[sp] = (stack[sp] == stack[sp + 1]);
            
            break;
            
        case 9: //  NEQ
            
            stack[sp] = (stack[sp] != stack[sp + 1]);
            
            break;
            
        case 10: // LSS
            
            stack[sp] = (stack[sp] < stack[sp + 1]);
            
            break;
            
        case 11: // LEQ
            
            stack[sp] = (stack[sp] <= stack[sp + 1]);
            
            break;
            
        case 12: // GTR
            
            stack[sp] = (stack[sp] > stack[sp + 1]);
            
            break;
            
        case 13: // GEQ
            
            stack[sp] = (stack[sp] >= stack[sp + 1]);
            
            break;
        
        default:
        
            printf("ERROR: Invalid M value encountered.\n");
       
    }
    
}

