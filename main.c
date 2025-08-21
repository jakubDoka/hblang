#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>     // C99: Standard integer types
#include <stdbool.h>    // C99: Boolean type
#include <complex.h>    // C99: Complex arithmetic
#include <math.h>
#include <stdarg.h>
#include <inttypes.h>   // C99: Format macros for integer types

// C99: Inline functions
inline int square(int x) {
    return x * x;
}

// C99: Variable-length arrays function
//void process_matrix(int rows, int cols, int matrix[rows][cols]) {
//    printf("Processing %dx%d matrix:\n", rows, cols);
//    for (int i = 0; i < rows; i++) {        // C99: for-loop declarations
//        for (int j = 0; j < cols; j++) {
//            matrix[i][j] = i * cols + j + 1;
//            printf("%3d ", matrix[i][j]);
//        }
//        printf("\n");
//    }
//}

// C99: Flexible array member
struct dynamic_array {
    size_t length;
    int data[];     // C99: Flexible array member
};

// C99: Restrict keyword
void copy_array(int *restrict dest, const int *restrict src, size_t n) {
    for (size_t i = 0; i < n; i++) {    // C99: size_t in for loop
        dest[i] = src[i];
    }
}

// Variadic function (C89, but enhanced usage here)
//double average(int count, ...) {
//    va_list args;
//    va_start(args, count);
//    
//    double sum = 0.0;
//    for (int i = 0; i < count; i++) {
//        sum += va_arg(args, double);
//    }
//    
//    va_end(args);
//    return count > 0 ? sum / count : 0.0;
//}
//
// C99: Compound literals and designated initializers demo
void demonstrate_initializers(void) {
    printf("\n=== C99 Initializers Demo ===\n");
    
    // C99: Designated initializers for arrays
    int weekdays[7] = {
        [0] = 1,    // Monday
        [6] = 7,    // Sunday
        [1] = 2,    // Tuesday
        [5] = 6     // Saturday
        // [2], [3], [4] are zero-initialized
    };
    
    printf("Weekdays: ");
    for (int i = 0; i < 7; i++) {
        printf("%d ", weekdays[i]);
    }
    printf("\n");
    
    // C99: Designated initializers for structs
    struct point {
        double x, y, z;
        char label[16];
    };
    
    struct point origin = {
        .x = 0.0,
        .y = 0.0,
        .z = 0.0,
        .label = "Origin"
    };
    
    // C99: Compound literal
    struct point *p = &(struct point){
        .x = 3.14,
        .y = 2.71,
        .z = 1.41,
        .label = "Special"
    };
    
    printf("Origin: (%.2f, %.2f, %.2f) - %s\n", 
           origin.x, origin.y, origin.z, origin.label);
    printf("Point: (%.2f, %.2f, %.2f) - %s\n", 
           p->x, p->y, p->z, p->label);
}

int main(void) {
    printf("=== C99 and Earlier Features Demo ===\n");
    
    // C99: Mixed declarations and code
    printf("Square of 5: %d\n", square(5));
    
    //int rows = 3, cols = 4;
    //
    //// C99: Variable-length arrays
    //int matrix[rows][cols];     // VLA declaration
    //process_matrix(rows, cols, matrix);
    
    // C99: Standard integer types
    uint64_t big_number = UINT64_C(18446744073709551615);
    printf("\nBig number: %" PRIu64 "\n", big_number);
    
    // C99: Boolean type
    bool is_valid = true;
    printf("Is valid: %s\n", is_valid ? "true" : "false");
    
    // C99: Complex numbers
    double complex z1 = 3.0 + 4.0*I;
    double complex z2 = 1.0 + 2.0*I;
    double complex result = z1 * z2;
    
    printf("Complex multiplication: (%.1f + %.1fi) * (%.1f + %.1fi) = (%.1f + %.1fi)\n",
           creal(z1), cimag(z1), creal(z2), cimag(z2), 
           creal(result), cimag(result));
    
    // C99: Hexadecimal floating-point constants
    double hex_float = 0x1.23p4;    // 1.23 * 2^4 in hex
    printf("Hex float 0x1.23p4 = %.6f\n", hex_float);
    
    // Dynamic array with flexible array member
    struct dynamic_array *arr = malloc(sizeof(struct dynamic_array) + 5 * sizeof(int));
    if (arr != NULL) {
        arr->length = 5;
        for (size_t i = 0; i < arr->length; i++) {
            arr->data[i] = (int)(i * i);
        }
        
        printf("\nDynamic array: ");
        for (size_t i = 0; i < arr->length; i++) {
            printf("%d ", arr->data[i]);
        }
        printf("\n");
        
        free(arr);
    }
    
    // Array copying with restrict
    int source[] = {10, 20, 30, 40, 50};
    int destination[5];
    copy_array(destination, source, 5);
    
    printf("Copied array: ");
    for (int i = 0; i < 5; i++) {
        printf("%d ", destination[i]);
    }
    printf("\n");
    
    // Variadic function
    //double avg = average(4, 1.5, 2.5, 3.5, 4.5);
    //printf("Average of 1.5, 2.5, 3.5, 4.5: %.2f\n", avg);
    
    // C99 initializers demo
    demonstrate_initializers();
    
    // C99: // comments (as opposed to /* */ only in C89)
    // Single-line comments were added in C99
    
    /* Traditional C89 block comment
       still works fine */
    
    // C99: Variable declarations anywhere in block
    {
        printf("\n=== Block scope demo ===\n");
        int a = 10;
        printf("a = %d\n", a);
        
        // More code here...
        int b = 20;     // C99: declaration after statements
        printf("b = %d\n", b);
        
        // C99: for loop variable declaration
        for (int i = 0; i < 3; i++) {
            printf("Loop iteration %d\n", i);
        }
        // 'i' is no longer in scope here
    }
    
    return 0;
}
