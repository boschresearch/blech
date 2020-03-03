/*
** This is generated code - do not touch!
*/

/*
** used C headers
*/

#include <stdio.h>

/*
** blech types
*/

#include "blech.h"

/*
** the generated blech program
*/

#include "blech/valid/bitwise.c"

/*
** external state for the blech program
*/



/*
** the test main loop
*/

 int main(void) {
    int running = 0; /* number of iterations */
    int bound = 60;
    printf("{\n\t\"trace\":[\n");

    blc_blech_valid_bitwise_init();

    while( running < bound )
    {
        /* call tick function */

        blc_blech_valid_bitwise_tick();
    
        /* display program state */
        printf ("\t\t{\n\t\t\t\"tick\": %i,\n", running);

        blc_blech_valid_bitwise_printState();

        ++running;       
        running < bound?printf("\t\t},\n"):printf("\t\t}\n");
    }
    printf("\t]\n}");
    return 0; /* OK */
}