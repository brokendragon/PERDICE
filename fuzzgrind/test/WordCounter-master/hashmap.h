
#include <stdlib.h>
#include <stdio.h>
#include <stdlib.h>

//Defining the struct needed for the node 
typedef struct node_t {
  char* word; 
  int count;
  struct node_t* next;
} node;

node** table;

//Function to increase the count for a word that exists in the hash table
void increaseCount(char* word);

//Printing the output to a file, given as a parameter 
void printAllToFile(char * output);

//Function to read in a text file
char * readText(char* input);

//Hash function
node** hashFunction(int count);

//Creating a new node
node* create(int count, char* word);

//Insertion function 
void insert(char * word);

//Getting the node for each word, returns 0 if not found and 1 if found
int exists(char* word); 

//Function to get the maximum string size in order to reserve memory
long getStringSize(char* word); 
