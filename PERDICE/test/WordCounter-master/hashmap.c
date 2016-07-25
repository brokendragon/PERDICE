#include <stdlib.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "hashmap.h"
int tableSize = 99991; //The size of the hash table is declared, prime to make it more efficent
int maximumCount;  //Storing the maximum word count
void printAllToFile(char * output){ //Output string is the file name to write too
  printf("Writing to %s\n", output);
  FILE *file = fopen(output,"w"); 
  if(file == NULL)
  {
    perror("Cannot open file"); 
    exit(EXIT_FAILURE);
  }
  int e; 
  int i; 
  for (e = maximumCount+1; e --> 0; ) //Looping through the word count in reverse, takes into account maximum word count (Will give an order)
  {
    for(i = 0; i < tableSize; i++) //Looping through the hash table
    {
      if (table[i] != NULL) 
      { 
        node* temp = table[i];
        int count = temp->count; 
        if(count == e) //If the count is the one we need and is in the right order then print out
        {
          char * word = temp->word; 
          printf("%s ", word);
          printf("%d\n", count);
          fprintf(file, "%s,%d \n", word, count); //Printing word and count to the file 
        }

        temp = temp->next; //temp is pointed to the next node in the chain
        while(temp != NULL) //While the iterator is not null (Looping through the chain)
        {
          int count = temp->count; 
          if(count == e) //If it is in the riht place to be written
          {
            char * word = temp->word; 
            printf("%s ", word);
            printf("%d\n", count); 
            fprintf(file, "%s,%d \n", word, count); //Writing to the file
          }
          temp = temp->next; //Going to the next chanined node
        }
      }
    }
  }
  fclose(file);  
  if (file == NULL) //Check the file has been correctly written
  {
    printf("Check file name and extension provided\n");
  }
  else
  {
    printf("File has been created and is available within the directory\n");
  }
} 

node** hashFunction(int count) { 
  int newCount = count % tableSize; 
  return (node**) (table + newCount * sizeof(node*)); //Hash function on combined ASCII value and remainder of size
}

node* create(int value, char* word) 
{
  node* newNode = malloc(sizeof(node)); //Reserving memory for the new node
  newNode->word = word; 
  newNode->count = value;
  newNode->next = NULL; //Next value will be null for a newly created node 
  return newNode; 
}

void insert(char* word){ 
  char * tempWord = word; 
  if (exists(tempWord) == 0) //Uses a function which will return 0 if word does not exist
  {
    int length = strlen(word); 
    int changedWord = 0; 
    int count = 1; //The count is set to 1 because it is a new node 

    /*The for loop below calculates the total ASCII Values for a word,
    which my hash function is based on */
    int i; 
    for (i = 0; i < length; i++) 
    {
      changedWord+= word[i];
    }
    node** n = (node**)hashFunction(changedWord); //Creating the node from the hash function
    node* chainedNodes = (node*) *n; //Iterator to loop through the chained nodes

    if(*n == NULL) 
    {
      *n = create(count, word); //If it is NULL then add a new node at given location
    }
    else 
    {
      while(chainedNodes->next != NULL)
      { 
        chainedNodes = chainedNodes->next; //Moves through chain until the end
      } 
      chainedNodes->next = create(count, word); //Adding the node to the end of the chain
    }
  }
  else 
  {
    increaseCount(tempWord); //Increase node count for a word
  }
}

void increaseCount(char* givenWord) 
{
  char* word = givenWord; 
  int length = strlen(word);  
  int changedWord = 0; 
  //Calculating the combined ASCII total for the hash function
  int i; 
  for (i = 0; i < length; i++)
  {
    changedWord+= word[i];
  }
    
  node* thisNode = (node*) *hashFunction(changedWord); //Finding memory location 

  while(thisNode != NULL && strcmp(thisNode->word,givenWord) != 0) 
  { 
    thisNode = thisNode->next; //Moving through chain if not the one wanted to be increased
  }

  thisNode->count++;  //Increasing the count value

  if(thisNode->count > maximumCount) //Increasing the maximum count global variable if it is bigger
  {
    maximumCount = thisNode->count;
  }
}

int exists(char* word) { 
  char* givenWord = word; 
  int length = strlen(word); 
  int changedWord = 0; 
  //Calculating the combined ASCII total for the hash function
  int r; 
  for (r = 0; r < length; r++)
  {
    changedWord+= word[r];
  }
    
  node* nodeLocation = (node*) *hashFunction(changedWord); //Finding memory location 
  node* wantedNode; 

  while(nodeLocation != NULL && strcmp(nodeLocation->word,givenWord) != 0) 
  { 
    nodeLocation = nodeLocation->next;  //Moving through chain 
  }

  if(nodeLocation == NULL)
  {
    return 0; //Returning 0 as word not found
  } 
  else 
  { 
    return 1; //Returns 1 if word found
  }
}
char* readText(char* input) 
{
  FILE* fileInput = fopen(input,"r"); 
  if(fileInput == NULL)
  {    
    printf ("File can not be found\n"); //Error for when file cannot be found
    return NULL;
  }
  
  fseek(fileInput, 0, SEEK_END); 
  long int size = ftell(fileInput);
  rewind(fileInput);
  
  char* content = calloc(size + 1, 1); //Reading the file into this variable

  fread(content,1,size,fileInput); 

  int fclose(FILE* fileInput);
  int fflush(FILE* fileInput); 

  return content;
}
long getStringSize(char* input) //Function to get the maximum string size in order to reserve memory
{
  FILE* fileInput = fopen(input,"r"); 
  if(fileInput == NULL)
  {    
    printf ("File can not be found\n"); //Error for when file cannot be found
  }
  
  fseek(fileInput, 0, SEEK_END); 
  long int size = ftell(fileInput);

  return size; //Returning the sizes
}