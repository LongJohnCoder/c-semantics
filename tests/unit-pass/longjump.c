// code from http://stackoverflow.com/questions/1692814/exception-handling-in-c-what-is-the-use-of-setjmp-returning-0
// http://en.wikipedia.org/wiki/Setjmp.h
// http://aszt.inf.elte.hu/~gsd/halado_cpp/ch02s03.html

#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>


static jmp_buf x;
static jmp_buf buf;
 
void f() {
	printf("in f\n");
    longjmp(x,5);
	printf("secret code\n");
}

void second(void) {
    printf("second\n");         // prints
    longjmp(buf,1);             // jumps back to where setjmp was called - making setjmp now return 1
}

void first(void) {
    second();
    printf("first\n");          // does not print
}

void test1() {
	int i = 0;
    if ( ! setjmp(x) ) {
		printf("calling f\n");
        f();
		printf("zzz\n");
    } else {
        printf("error code = %d\n", i);
    }
	printf("xxx\n");
}

void test2(void){
	if ( ! setjmp(buf) ) {
        first();                // when executed, setjmp returns 0
    } else {                    // when longjmp jumps back, setjmp returns 1
        printf("test2\n");         // prints
    }
}


void foo ( char** data ) ;
void handle ( char* data ) ;
jmp_buf env;

int test3 () {
    char* data = 0;

    if ( setjmp( env ) == 0 )
        foo ( &data );
    else
        handle ( data );

    return 0;
}

void foo ( char** data ) {
    *data = (char*)malloc ( 32 );
    printf ( "in foo\n" );
    strcpy ( *data, "Hello World" );
    printf ( "data = %s\n", *data );
    longjmp ( env, 42 );
}

void handle ( char* data ) {
    printf ( "in handler\n" );

    if ( data ) {
        free ( data );
        printf ( "data freed\n" );
    }
}

int main() {
    test1();
	test2();
	test3();
	return 0;
}
