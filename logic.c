#include "logic.h"
#include <string.h>
#include <stdlib.h>
#include <ctype.h>

#define BUFF_SIZE 2048

typedef struct {
    char* name;
    int  arity;
} PREDICATE;

typedef struct formula {
    int  arity;
    char* word;
    struct formula* sub_f1;
    struct formula* sub_f2;
} formula;

typedef struct interpretation {
    int    num_atoms;
    char** atoms;
} interpretation;

typedef struct assumption {
    char** atoms;
    int    num_atoms;
    int    truth;
} assumption;

/* A list of names read from the file. */
char** names;

/* Total number of names read from the file. */
int num_names;

/* A list of predicates read from the file. */
PREDICATE* predicates;

/* Total number of predicates read from the file. */
int num_predicates;


/* A list of formulas read from the file. */
Formula* formulas;

/* Total number of formulas read from the file. */
int num_formulas;

/*
 * A buffer for reading in tokens from stdin or files.
 */
char buff[BUFF_SIZE];

/*
 * A buffer for reading user input.
 */
char input_buffer[BUFF_SIZE * 10];

/* ==================== Helper Functions =====================*/
/* 
 * Count the number of valid tokens in a file.
 * This function can be called before reading the names.txt file 
 * and the predicates.txt file for preparing a large enough array
 * to hold the names and predicates.
 */
int count_tokens(char* filename) {
    FILE* file = fopen(filename, "r");
    char c;
    int  i = 0;            /* Current index in the buffer. */
    int  token_count = 0;  /* Number of tokens read. */ 
    
    while ((c = fgetc(file)) != EOF) {
        if (c != '\n' && c != '\t' && c != ' ' && c != '\r') {
            if (i != 0) {
                token_count++;
                i = 0;
            }
        }
        else {
            i++;
        }
    }
    
    if (i != 0) {
        token_count++;
        i = 0;
    }
    fclose(file);
    return token_count;
}

/*
 * Convert a string to a predicate structure and save it.
 */
void setPredicate(char str[], PREDICATE* predicate) {
    char deli[10] = "/\n";
    /* 1. Get predicate name. */
    char* token = strtok(str, deli);
    predicate->name = calloc(sizeof(char), strlen(token) + 1);
    strcpy(predicate->name, token);
    
    /* 2. Get predicate arity. */
    token = strtok(NULL, deli);
    predicate->arity = atoi(token);
}

/*
 * Search for a constant in the names array.
 * Return its index if the name exists, otherwise return -1.
 */
int getConstantIndex(char* constant_name) {
    int i;
    for (i=0; i<num_names; i++) {
        if (strcmp(names[i], constant_name) == 0) {
            return i;
        }
    }
    return -1;
}

/*
 * Search for a predicate in the predicate array.
 * Return its index if the predicate exists, otherwise return -1.
 */
int getPredicateIndex(char* predicate_name) {
    int i;
    for (i=0; i<num_predicates; i++) {
        if (strcmp(predicates[i].name, predicate_name) == 0) {
            return i;
        }
    }
    return -1;
}


bool special_symbol(char c) {
    return (c == ' ' || c == '\r' || c == '\n' ||
            c == '\t' || c == '[' || c == ']' || c == EOF);
}

bool special_non_space_symbol(char c) {
    return (c == '[' || c == ']');
}

/**
 * Read user input from console and save into the input buffer.
 */
void read_user_input() {
    char c;
    int i = 0;
    while ((c = fgetc(stdin)) != EOF) {
        input_buffer[i++] = c;
    }
    input_buffer[i] = '\0';
}

/*
 * Get the next token from stdin.
 * i is the current position that we have read.
 */
void nextToken(int* i) {
    /* get rid of all the spaces and new line symbols */
    char c = input_buffer[*i];
    while (c == ' ' || c == '\r' || c == '\n' || c == '\t') {
        (*i)++;
        c = input_buffer[*i];
    }
    
    // 1. If c is an empty character, return an empty string.
    if (c == '\0') {
        buff[0] = '\0';
        return;
    }
    
    // 2. for special symbols, return as a token
    int j = 0;
    if (special_non_space_symbol(c)) {
        buff[0] = c;
        buff[1] = '\0';
        (*i)++;
        return;
    }
    else {
        buff[j] = c;
        while (!special_symbol(c)) {
            buff[j++] = c;
            (*i)++;
            c = input_buffer[*i];
        }
        buff[j] = '\0';
    }
}

/*
 * Recursively read formula components from the input buffer, and
 * form a complete formula.
 */
Formula recursive_make_formula(int* i) {
    nextToken(i);
    
    if (strlen(buff) == 0) {
        return NULL;
    }
    Formula f = malloc(sizeof(formula));
    
    /* 1. If next token is '[', it then has 2 components. */
    if (strcmp(buff, "[") == 0) {
        f->arity = 2;
        f->sub_f1 = recursive_make_formula(i);
        if (f->sub_f1 == NULL) {
            free(f);
            return NULL;
        }
        
        nextToken(i);
        
        if (strlen(buff) == 0) {
            return NULL;
        }
        else if (strcmp(buff, "and") != 0 && strcmp(buff, "or") != 0 &&
            strcmp(buff, "implies") != 0 && strcmp(buff, "iff") != 0) {
            return NULL;
        }
        else {
            f->word = calloc(sizeof(char), strlen(buff) + 1);
            sprintf(f->word, "%s", buff);
        }
        
        f->sub_f2 = recursive_make_formula(i);
        if (f->sub_f2 == NULL) {
            free(f);
            return NULL;
        }
        
        nextToken(i);
        if (strlen(buff) == 0) {
            free(f);
            return NULL;
        }
        else if (strcmp(buff, "]") != 0) {
            return NULL;
        }
        else {
            return f;
        }
    }
    /* 2. If next token is 'not', the formula has only one formula. */
    else if (strcmp(buff, "not") == 0) {
        f->arity = 1;
        f->word = calloc(sizeof(char), 4);
        sprintf(f->word, "%s", "not");
        
        f->sub_f1 = recursive_make_formula(i);
        if (f->sub_f1 == NULL) {
            free(f);
            return NULL;
        }
        
        f->sub_f2 = NULL;
        return f;
    }
    
    /* These key words cannot exists by themselves. */
    else if (strcmp(buff, "]") == 0 || strcmp(buff, "and") == 0 || 
             strcmp(buff, "or") == 0 || strcmp(buff, "implies") == 0 || 
             strcmp(buff, "iff") == 0) {
        free(f);
        return NULL;
    }

    /* 3. If the next token is a normal string, simply attach it to the
     *    formula word.
     */
    else {
        f->arity = 0;
        f->sub_f1 = NULL;
        f->sub_f2 = NULL;
        f->word = calloc(sizeof(char), strlen(buff) + 1);
        sprintf(f->word, "%s", buff);
        return f;
    }
}

/**
 * Check whether a single function is syntactically correct.
 */
bool check_single_function(char* words) {
    int i = 0;
    int j = 0;
    int len = strlen(words);
    
    /* Stage 1: Capture predicate and check whether the predicate is valid. */
    int predicateIndex = -1;
    while (words[i] != '(') {
        if (words[i] == '\0') {
            break; 
        }
        buff[j] = words[i];
        i++;
        j++;
    }
    buff[j] = '\0';
    predicateIndex = getPredicateIndex(buff);
    if (predicateIndex == -1) {
        return false;
    }
    
    /* Stage 2: Counting and checking arguments. */
    int arity_count = predicates[predicateIndex].arity;
    int k;
    for (k = 0; k < arity_count; k++) {
        i++;
        j = 0;
        if (words[i] == ',') {
            return false;
        }
        else if (words[i] == '\0') {
            return false;
        }
        else {
            while (words[i] != ',' && words[i] != ')') {
                buff[j] = words[i];
                i++;
                j++;
            }
            buff[j] = '\0';
            if (getConstantIndex(buff) == -1) {
                return false;
            }
        }
    }
    
    /* 3. If there are still some tokens left, the formula is invalid. */
    if (arity_count > 0) {
        i++;
    }
    
    while (words[i] == ' ' || words[i] == '\t' ||
           words[i] == '\n' || words[i] == '\n') {
        i++;
    }
    if (words[i] != '\0') {
        return false;
    }
    return true;
}

/*
 * Convert the string in buffer to a fact atom, and save it into the
 * interpretation atom list.
 */
void save_atom(char buff[], Interpretation interp) {
    /* 1. Create a new atom. */
    char* atom = calloc(sizeof(char), strlen(buff) + 1);
    strcpy(atom, buff);
    
    /* 2. Save the ave to the interpretation. */
    if (interp->atoms == NULL) {
        interp->num_atoms = 1;
        interp->atoms = malloc(sizeof(char*));
        interp->atoms[0] = atom;
    }
    else {
        int i = interp->num_atoms;
        interp->atoms = realloc(interp->atoms, sizeof(char*) * (i + 1));
        interp->atoms[i] = atom;
        (interp->num_atoms)++;
    }
}

/**
 * Check whether a given atom is true by the given interpretation.
 */
bool fact_exist(char* atom, Interpretation interp) {
    int num_facts = interp->num_atoms;
    int i;
    for (i=0; i<num_facts; i++) {
        if (strcmp(interp->atoms[i], atom) == 0) {
            return true;
        }
    }
    return false;
}


bool assumption_exist(char* atom, assumption* ass) {
    if (ass->num_atoms == 0) {
        return false;
    }
    else {
        int i;
        int num_atoms = ass->num_atoms;
        for (i = 0; i < num_atoms; i++) {
            if (strcmp(ass->atoms[i], atom) == 0) {
                return true;
            }
        }
        return false;
    }
}

void add_to_assumption(char* atom, assumption* ass) {
    if (ass->num_atoms == 0) {
        ass->atoms = malloc(sizeof(char*));
        ass->atoms[0] = calloc(sizeof(char), strlen(atom) + 1);
        strcpy(ass->atoms[0], atom);
        ass->num_atoms = 1;
    }
    else {
        int num_atoms = ass->num_atoms;
        ass->atoms = realloc(ass->atoms, sizeof(char*) * (num_atoms + 1));
        ass->atoms[num_atoms] = calloc(sizeof(char), strlen(atom) + 1);
        strcpy(ass->atoms[num_atoms], atom);
        ass->num_atoms = num_atoms + 1;
    }
}

/*
 * Save all atoms that are not listed in the interpretation to 
 * the assumption list.
 */
void make_assumptions(Formula formula, assumption* ass) {
    if (formula != NULL) {
        if (strcmp(formula->word, "and") == 0 || strcmp(formula->word, "or") == 0 || 
            strcmp(formula->word, "iff") == 0 || strcmp(formula->word, "implies") == 0) {
            make_assumptions(formula->sub_f1, ass);
            make_assumptions(formula->sub_f2, ass);
        }
        else if (strcmp(formula->word, "not") == 0) {
            make_assumptions(formula->sub_f1, ass);
        }
        else {
            char* atom = formula->word;
            if (!assumption_exist(atom, ass)) {
                add_to_assumption(atom, ass);
            }
        }
    }
}

int get_assumption_index(char* atom, assumption* ass) {
    int num_atoms = ass->num_atoms;
    int i;
    for (i=0; i<num_atoms; i++) {
        if (strcmp(atom, ass->atoms[i]) == 0) {
            return i;
        }
    }
    return -1;
}

bool is_true_single_atom_assumption(char* atom, assumption* ass) {
    int i = get_assumption_index(atom, ass);
    int truth = ass->truth;
    
    if (((1<<i) & (truth)) == 0) {
        return false;
    }
    else {
        return true;
    }
}


bool is_true_with_assumption(Formula formula, assumption* ass) {
    if (strcmp(formula->word, "and") == 0) {
        bool state1 = is_true_with_assumption(formula->sub_f1, ass);
        bool state2 = is_true_with_assumption(formula->sub_f2, ass);
        return (state1 && state2);
    }
    else if (strcmp(formula->word, "or") == 0) {
        bool state1 = is_true_with_assumption(formula->sub_f1, ass);
        bool state2 = is_true_with_assumption(formula->sub_f2, ass);
        return (state1 || state2);
    }
    else if (strcmp(formula->word, "iff") == 0) {
        bool state1 = is_true_with_assumption(formula->sub_f1, ass);
        bool state2 = is_true_with_assumption(formula->sub_f2, ass);
        return ((state1 && state2) || (!state1 && !state2));
    }
    else if (strcmp(formula->word, "implies") == 0) {
        bool state1 = is_true_with_assumption(formula->sub_f1, ass);
        bool state2 = is_true_with_assumption(formula->sub_f2, ass);
        return !(state1 && !state2);
    }
    else if (strcmp(formula->word, "not") == 0) {
        return !is_true_with_assumption(formula->sub_f1, ass);
    }
    else {
        char* atom = formula->word;
        return is_true_single_atom_assumption(atom, ass);
    }
}

int count_trues(assumption* ass) {
    int truth = ass->truth;
    int count = 0;
    while (truth != 0) {
        if ((truth & 1) == 1) {
            count++;
        }
        truth = (truth >> 1);
    }
}

void make_witnesses_satisfiability(Formula formula, assumption* ass) {
    FILE* file = fopen("witnesses_satisfiability.txt", "w");
    
    int num_atoms = ass->num_atoms;
    int min_trues_count = -1;
    int min_truth = 0;
    
    ass->truth = 0;
    while ((ass->truth) < (1<<num_atoms)) {
        if (is_true_with_assumption(formula, ass)) {
            if (min_trues_count == -1) {
                min_trues_count = count_trues(ass);
                min_truth = ass->truth;
            }
            else if (count_trues(ass) < min_trues_count){
                min_trues_count = count_trues(ass);
                min_truth = ass->truth;
            }
        }
        (ass->truth)++;
    }
    
    int i = 0;
    while (min_truth != 0) {
        if ((min_truth & 1) == 1) {
            fprintf(file, "%s\n", ass->atoms[i]);
        }
        min_truth = (min_truth >> 1);
        i++;
    }
    
    fclose(file);
}

/* ==================== Functions Implemented =====================*/

void get_constants(FILE *file) {
    /* 1. Initialize the 'names' array. */
    num_names = count_tokens("names.txt");
    names = calloc(sizeof(char*), num_names);
    
    /* 2. Read the file and save the tokens to the names array. */
    int  i = 0;            /* Current index in the buffer. */
    int  token_count = 0;  /* Number of tokens read. */ 
    char c;
    while ((c = fgetc(file)) != EOF) {
        if (c == '\r' || c == '\n' || c == '\t' || c == ' ') {
            if (i != 0) {
                buff[i] = '\0';
                i = 0;
                names[token_count] = calloc(sizeof(char), strlen(buff) + 1);
                strcpy(names[token_count], buff);
                token_count++;
            }
        }
        else {
            buff[i++] = c;
        }
    }
}

void get_predicates(FILE *file) {
    /* 1. Initialize the 'predicates' array. */
    num_predicates = count_tokens("predicates.txt");
    predicates = calloc(sizeof(PREDICATE), num_predicates);
    
    /* 2. Read the file and save the tokens to the names array. */
    int  i = 0;            /* Current index in the buffer. */
    int  token_count = 0;  /* Number of tokens read. */ 
    char c;
    /* Something to be modified here!!!!! */
    while ((c = fgetc(file)) != EOF) {
        if (c == '\r' || c == '\n' || c == '\t' || c == ' ') {
            if (i != 0) {
                buff[i] = '\0';
                i = 0;
                setPredicate(buff, &predicates[token_count]);
                token_count++;
            }
        }
        else {
            buff[i++] = c;
        }
    }
}

Formula make_formula() {
    int i = 0;
    read_user_input();
    
    Formula form = recursive_make_formula(&i);
    
    /* If there are still extra tokens in the input buffer, return NULL. */
    nextToken(&i);
    if (strlen(buff) != 0) {
        return NULL;
    }
    else {
        return form;
    }
}

Interpretation make_interpretation(FILE *file) {
    Interpretation interp = malloc(sizeof(interpretation));
    interp->num_atoms = 0;
    interp->atoms = NULL;
    
    /* Read the file and unpack tokens to facts. */
    int  i = 0;            /* Current index in the buffer. */
    int  token_count = 0;  /* Number of tokens read. */ 
    char c;
    while ((c = fgetc(file)) != EOF) {
        if (c == '\r' || c == '\n' || c == '\t' || c == ' ') {
            if (i != 0) {
                buff[i] = '\0';
                i = 0;
                save_atom(buff, interp);
            }
        }
        else {
            buff[i++] = c;
        }
    }
    
    return interp;
}

bool is_syntactically_correct(Formula formula) {
    /* 1. Check arity */
    if (formula == NULL) {
        return false;
    }
    else if (formula->arity == 0) {
        if (formula->sub_f1 != NULL || formula->sub_f2 != NULL) {
            return false;
        }
        if (strcmp(formula->word, "and") == 0 || strcmp(formula->word, "or") == 0 ||
            strcmp(formula->word, "iff") == 0 || strcmp(formula->word, "implies") == 0) {
            return false;
        }
        if (strcmp(formula->word, "not") == 0) {
            return false;
        }
        
        /* For a single formula, check whether it contains correct components. */
        return check_single_function(formula->word);
    }
    else if (formula->arity == 1) {
        if (strcmp(formula->word, "and") == 0 || strcmp(formula->word, "or") == 0 ||
            strcmp(formula->word, "iff") == 0 || strcmp(formula->word, "implies") == 0) {
            return false;
        }
        if (strcmp(formula->word, "not") != 0) {
            return false;
        }
        if (formula->sub_f1 == NULL || formula->sub_f2 != NULL) {
            return false;
        }
        else {
            return is_syntactically_correct(formula->sub_f1);
        }
    }
    else if (formula->arity == 2) {
        if (strcmp(formula->word, "and") != 0 && strcmp(formula->word, "or") != 0 &&
            strcmp(formula->word, "iff") != 0 && strcmp(formula->word, "implies") != 0) {
            return false;
        }
        if (strcmp(formula->word, "not") == 0) {
            return false;
        }
        if (formula->sub_f1 == NULL || formula->sub_f2 == NULL) {
            return false;
        }
        else {
            bool result1 = is_syntactically_correct(formula->sub_f1);
            bool result2 = is_syntactically_correct(formula->sub_f2);
            return (result1 && result2);
        }
    }
}

bool is_true(Formula formula, Interpretation inter) {
    if (formula->arity == 0) {
        char* atom = formula->word;
        return fact_exist(atom, inter);
    }
    /* NOT */
    else if (formula->arity == 1) {
        return !is_true(formula->sub_f1, inter);
    }
    else {
        char* word = formula->word;
        /* AND */
        if (strcmp(word, "and") == 0) {
            bool state1 = is_true(formula->sub_f1, inter);
            bool state2 = is_true(formula->sub_f2, inter);
            return (state1 && state2);
        }
        /* OR */
        else if (strcmp(word, "or") == 0) {
            bool state1 = is_true(formula->sub_f1, inter);
            bool state2 = is_true(formula->sub_f2, inter);
            return (state1 || state2);
        }
        /* IMPLIES */
        else if (strcmp(word, "implies") == 0) {
            bool state1 = is_true(formula->sub_f1, inter);
            bool state2 = is_true(formula->sub_f2, inter);
            return !(state1 && !state2);
        }
        /* IFF */
        else {
            bool state1 = is_true(formula->sub_f1, inter);
            bool state2 = is_true(formula->sub_f2, inter);
            return ((state1 && state2) ||
                   (!state1 && !state2));
        }
    }
    return false;
}

bool is_satisfiable(Formula formula) {
    /* 1. Store all atoms that are not listed in the file true_atoms.txt */
    assumption* ass = malloc(sizeof(assumption));
    ass->num_atoms = 0;
    ass->atoms = NULL;
    ass->truth = 0;
    make_assumptions(formula, ass);
    
    /* 2. Check if the formula is satisfiable */
    int num_atoms = ass->num_atoms;
    ass->truth = 0;
    while ((ass->truth) < (1<<num_atoms)) {
        if (is_true_with_assumption(formula, ass)) {
            make_witnesses_satisfiability(formula, ass);
            return true;
        }
        (ass->truth)++;
    }
    return false;
}
