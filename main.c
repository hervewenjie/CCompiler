
#include <stdio.h>
#include <stdlib.h>
#include <memory.h>
#include <fcntl.h>
#include <unistd.h>

int debug;    // print the executed instructions
int assembly; // print out the assembly and source

int token; // current token
int token_val;   // value of current token (mainly for number)

int poolsize;
int line;    // line number of source code

int *pc, *bp, *sp, ax, cycle; // virtual machine registers

int *text;
int *old_text;
int *data;
int *stack;
char *src;char *old_src;

int *idmain;

int *symbols;
int *current_id;

int basetype;    // the type of a declaration, make it global for convenience
int expr_type;   // the type of an expression

// tokens and classes (operators last and in precedence order) copied from c4
enum {
    Num = 128, Fun, Sys, Glo, Loc, Id,
    Char, Else, Enum, If, Int, Return, Sizeof, While,
    Assign, Cond, Lor, Lan, Or, Xor, And, Eq, Ne, Lt, Gt, Le, Ge, Shl, Shr, Add, Sub, Mul, Div, Mod, Inc, Dec, Brak
};

// fields of identifier
enum {Token, Hash, Name, Type, Class, Value, BType, BClass, BValue, IdSize};

// instructions
enum { LEA ,IMM ,JMP ,CALL,JZ  ,JNZ ,ENT ,ADJ ,LEV ,LI  ,LC  ,SI  ,SC  ,PUSH,
    OR  ,XOR ,AND ,EQ  ,NE  ,LT  ,GT  ,LE  ,GE  ,SHL ,SHR ,ADD ,SUB ,MUL ,DIV ,MOD ,
    OPEN,READ,CLOS,PRTF,MALC,MSET,MCMP,EXIT };

// types of variable/function
enum { CHAR, INT, PTR };


void next() {
    char *last_pos;
    int hash;

    // enter while, only match then return
    while (token = *src) {
        ++src;

        if (token == '\n') {
            if (assembly) {
                // print compile info
            }
        }
        // skip macro
        else if (token == '#') {
            while (*src != 0 && *src != '\n') { src++; }
        }
        // identifier
        else if (token >= 'a' && token <= 'z' || (token >= 'A' && token <= 'Z') || (token == '_')) {
            last_pos = src - 1; // point to start of word
            hash = token;
            // compute hash, move src to end
            while ((*src >= 'a' && *src <= 'z') || (*src >= 'A' && *src <= 'Z') || (*src >= '0' && *src <= '9') || (*src == '_')) {
                hash = hash * 147 + *src;
                src++;
            }
            // look for existing identifier, linear search
            current_id = symbols; // start of symbol table
            while (current_id[Token]) {
                // not zero mean we have sth here
                if (current_id[Hash] == hash && !memcmp((char*)current_id[Name], last_pos, src - last_pos)) {
                    // found one, return
                    token = current_id[Token];
                    return;
                }
                // next identifier
                current_id = current_id + IdSize;
            }
            // store new ID in current pos
            current_id[Name] = (int) last_pos; // the word
            current_id[Hash] = hash;
            token = current_id[Token] = Id;
            return;
        }
        else if (token >= '0' && token <= '9') {
            // parse number, three kinds: dec(123) hex(0x123) oct(017)
            token_val = token - '0';
            if (token_val > 0) {
                // dec, starts with [1-9]
                while (*src >= '0' && *src <= '9') {
                    token_val = token_val*10 + *src++ - '0';
                }
            } else {
                // starts with number 0
                if (*src == 'x' || *src == 'X') {
                    //hex
                    token = *++src;
                    while ((token >= '0' && token <= '9') || (token >= 'a' && token <= 'f') || (token >= 'A' && token <= 'F')) {
                        token_val = token_val * 16 + (token & 15) + (token >= 'A' ? 9 : 0);
                        token = *++src;
                    }
                } else {
                    // oct
                    while (*src >= '0' && *src <= '7') {
                        token_val = token_val*8 + *src++ - '0';
                    }
                }
            }

            token = Num;
            return;
        }
        else if (token == '/') {
            if (*src == '/') {
                // skip comments
                while (*src != 0 && *src != '\n') {
                    ++src;
                }
            } else {
                // divide operator
                token = Div;
                return;
            }
        }
        else if (token == '"' || token == '\'') {
            // parse string literal, currently, the only supported escape
            // character is '\n', store the string literal into data.
            last_pos = data;
            while (*src != 0 && *src != token) {
                token_val = *src++;
                if (token_val == '\\') {
                    // escape character
                    token_val = *src++;
                    if (token_val == 'n') {
                        token_val = '\n';
                    }
                }

                if (token == '"') {
                    *data++ = token_val;
                }
            }

            src++;
            // if it is a single character, return Num token
            if (token == '"') {
                token_val = (int)last_pos;
            } else {
                token = Num;
            }

            return;
        }
        else if (token == '=') {
            // parse '==' and '='
            if (*src == '=') {
                src ++;
                token = Eq;
            } else {
                token = Assign;
            }
            return;
        }
        else if (token == '+') {
            // parse '+' and '++'
            if (*src == '+') {
                src ++;
                token = Inc;
            } else {
                token = Add;
            }
            return;
        }
        else if (token == '-') {
            // parse '-' and '--'
            if (*src == '-') {
                src ++;
                token = Dec;
            } else {
                token = Sub;
            }
            return;
        }
        else if (token == '!') {
            // parse '!='
            if (*src == '=') {
                src++;
                token = Ne;
            }
            return;
        }
        else if (token == '<') {
            // parse '<=', '<<' or '<'
            if (*src == '=') {
                src ++;
                token = Le;
            } else if (*src == '<') {
                src ++;
                token = Shl;
            } else {
                token = Lt;
            }
            return;
        }
        else if (token == '>') {
            // parse '>=', '>>' or '>'
            if (*src == '=') {
                src ++;
                token = Ge;
            } else if (*src == '>') {
                src ++;
                token = Shr;
            } else {
                token = Gt;
            }
            return;
        }
        else if (token == '|') {
            // parse '|' or '||'
            if (*src == '|') {
                src ++;
                token = Lor;
            } else {
                token = Or;
            }
            return;
        }
        else if (token == '&') {
            // parse '&' and '&&'
            if (*src == '&') {
                src ++;
                token = Lan;
            } else {
                token = And;
            }
            return;
        }
        else if (token == '^') {
            token = Xor;
            return;
        }
        else if (token == '%') {
            token = Mod;
            return;
        }
        else if (token == '*') {
            token = Mul;
            return;
        }
        else if (token == '[') {
            token = Brak;
            return;
        }
        else if (token == '?') {
            token = Cond;
            return;
        }
        else if (token == '~' || token == ';' || token == '{' || token == '}' || token == '(' || token == ')' || token == ']' || token == ',' || token == ':') {
            // directly return the character as token;
            return;
        }
    }
}

// if current token match, get next token, aka consume
void match(int tk) {
    if (token == tk) {
        next();
    } else {
        printf("%d: expected token: %d\n", line, tk);
        exit(-1);
    }
}

void enum_declaration() {

}

void global_declaration() {
    // int [*]id [; | (...) {...}]
    int type; // tmp, actual type for variable
    int i;    // tmp

    basetype = INT;

    // parse enum, this should be treated alone, return after this
    if (token == Enum) {
        // enum [id] {a = 10, b = 20, ...}
        match(Enum); // match means consume
        if (token != '{') {
            match(Id); // match id
        }
        if (token == '{') {
            // parse the assign part
            match('{');
            enum_declaration();
            match('}');
        }
        match(';');
        return;
    }

    // parse type information
    if (token == Int) {
        match(Int);
    }
}

void program() {
    // read util next token
    next();
    while (token > 0) {
        global_declaration();
    }
}

int eval() {

}

int main(int argc, char **argv) {
    int i, fd;
    int *tmp;

    argc--;
    argv++;

    // arg -s
    if (argc > 0 && **argv == '-' && (*argv)[1] == 's') {
        assembly = 1;
        --argc;++argv;
    }
    // arg -d
    if (argc > 0 && **argv == '-' && (*argv)[1] == 'd') {
        debug = 1;
        --argc;++argv;
    }

    if (argc < 1) { printf("usage: xc [-s] [-d] file ...\n"); return 0;}

    // open file
    if ( (fd = open(*argv, 0)) < 0 ) {printf("Cannot open %s\n", *argv); return -1;}

    poolsize = 256 * 1024; // arbitrary size
    line = 1;

    // alloc memory
    if ( !(text = malloc(poolsize)) ) {printf("Cannot malloc %d\n", poolsize); return -1;}
    if ( !(data = malloc(poolsize)) ) {printf("Cannot malloc %d\n", poolsize); return -1;}
    if ( !(stack = malloc(poolsize)) ) {printf("Cannot malloc %d\n", poolsize); return -1;}
    if ( !(symbols = malloc(poolsize)) ) {printf("Cannot malloc %d\n", poolsize); return -1;}

    // clear
    memset(text, 0, poolsize);
    memset(data, 0, poolsize);
    memset(stack, 0, poolsize);
    memset(symbols, 0, poolsize);

    old_text = text;

    src = "char else enum if int return sizeof while open read close printf malloc memset memcmp exit void main";

    // add keywords to symbol table
    i = Char;
    while (i <= While) { next(); current_id[Token] = i++; }
    i = OPEN;
    while (i <= EXIT) { next(); current_id[Class] = Sys; current_id[Type] = INT; current_id[Value] = i++;}
    next(); current_id[Token] = Char; // handle void
    next(); idmain = current_id;      // main
    // end add keywords to symbol table

    // malloc and read file
    if ( !(src = old_src = malloc(poolsize)) ) { printf("Cannot malloc %d\n", poolsize); return -1;}
    if ( (i = read(fd, src, poolsize - 1)) <= 0 ) { printf("Read returned %d\n", i); return -1;}
    src[i] = 0; // add EOF
    close(fd);

    for (int i = 0; i < 1024; ++i) {
        printf("c=%d ", *(symbols+i) );
    }

    // program to invoke next() parse source
    program();

    // from main
    if ( !(pc = (int*) idmain[Value])) { printf("Main not defined\n"); return -1; }

    // dump text
    if (assembly) { return 0;}

    // setup stack
    sp = (int*)( (int)stack + poolsize );
    *--sp = EXIT; // call exit if main returns
    *--sp = PUSH; tmp = sp;
    *--sp = argc;
    *--sp = (int) argv;
    *--sp = (int) tmp;

    return eval();
}