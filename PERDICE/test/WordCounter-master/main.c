
#include <stdio.h>
#include <malloc.h>
#include <stdlib.h>
#include <string.h>
#include "hashmap.c"

int main (int argc, char *argv[]) {

  char* tempfullstring;
  char* input = argv[1]; 
  char* output = argv[2]; 

  long stringSize = getStringSize(input); //Function to get the string size
  tempfullstring = malloc(sizeof(char)*stringSize+1); //Reserves memory based on the string size
  tempfullstring = readText(input); //Reads text file into string
  int len = strlen(tempfullstring); 

  int q;
  for(q = 0; q < len; q++)
  {
    //Difference between ASCII code of an upper case character and a lower case one is 32
    
    if (tempfullstring[q] >= 65 && tempfullstring[q] <= 90) //Range of upper case characters is between 65 and 90 ASCII code
    {
      tempfullstring[q]+=32; //Converts them to lower case by adding 32 to the ascii value 
    }
  }

  char* nospecstring = malloc(sizeof(char)*len+1); //String without special characters
  int counter = 0; //Counter for the amount of characters that are added to the new string
  int i; 
  for(i = 0; i < len; i++) //Looping through every character
  {
    if (tempfullstring[i]>=97 && tempfullstring[i] <=122) //Adding lower case characters to the string
    {
      char value = tempfullstring[i];
      nospecstring[counter]= value;
      counter++;
    }
    if (tempfullstring[i] == 32) //Adding spaces as commas to the string
    {
      nospecstring[counter] = 44;
      counter++;
    }
    if(tempfullstring[i] == 12 || tempfullstring[i] == 10) // Adding new lines as commas to the string
    {
      if (nospecstring[counter-1] != 44 && i != len-1) //Checks multiple commas aren't added
      {
        nospecstring[counter] = 44; //Adding commas to the string
        counter++; 
      }
    }
  }
  nospecstring[counter] = '\0'; 
  int noSpecLen = strlen(nospecstring); //New length of the no special characters string
  int tableSize = 99991; //The size of the hash table is declared, prime to make it more efficent
 
  table = malloc(sizeof(node*) * tableSize); //Reserving the correct amount of memory for the hash table
  memset(table, 0, sizeof(node*) * tableSize); 

  char* token = malloc(sizeof(char)*30);
  char* string = malloc(sizeof(char)*noSpecLen+1); 
  string = strdup(nospecstring); 
  printf("The new string is '%s'\n", string); 
  if (string != NULL) {
    while ((token = strsep(&string, ",")) != NULL) //Splitting up the string based on spaces
    {
        if (strcmp(token, "") != 0){
          insert(token);}//Inserting string into hash map
    }
  }
  printAllToFile(output);
}

