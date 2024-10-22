
// --- global settings
// Note this brute forces entire magma space,
// but assuming first table index chosen for populating is index(0,0)
// then once this has tried values 0 and 1,
// all other results will just be related by some relabelling.

#define N 8

// use -1 to turn off completely
#define SHOW_DEPTH 5

//#define TRACE 1

// ---------------------------------------------------
#include <stdio.h>

#ifdef TRACE
#define trace_printf(...)  printf(__VA_ARGS__)
#else
#define trace_printf(...)
#endif

// let elements = {0, 1, 2, ..., N-1}
// implement op(x,y) as an N*N buffer
//   such that op(x,y) is at
//   index(x,y) = N*x - y
//   in the buffer
//
// now 'extend' this to allow UNKNOWN element
// such that for all x, op(x, UNKNOWN) = op(UNKNOWN, x) = UNKNOWN
//
// this can be done by letting UNKNOWN be a negative value
// and ensuring there is memory below the N*N op buffer
//
// UNKNOWN is value such that:
//   index(N-1, UKNOWN) = N*(N-1) + UNKNOWN < 0
//   UNKNOWN < -N*(N-1)
// let UNKNOWN = (-N*(N-1) - 1) = (-N*N + N - 1)
//
// max negative index is for op(UNKNOWN, UNKNOWN)
// index(UNKNOWN, UNKNOWN) = N*UNKNOWN + UKNOWN
//   = N*(-N*N + N - 1) + (-N*N + N - 1)
//   = -N*N*N + N*N - N  - N*N + N - 1
//   = -(N*N*N + 1)
#define UNKNOWN (-N*(N-1) - 1)
#define TABLE_OFFSET (N*N*N + 1)
#define TOTAL_BUF_SIZE (TABLE_OFFSET + N*N)

int buf[TOTAL_BUF_SIZE];

#define index(x, y) (TABLE_OFFSET + N*x + y)
#define op(x, y) buf[index(x,y)]


// allow unknown, only fail on contradiction
int fuzzy_check_eqn(int x, int y, int z)
{
    // eqn 1485: x = (y ◇ x) ◇ (x ◇ (z ◇ y))
    int a = op(op(y,x), op(x, op(z,y)));
    return ((a == UNKNOWN) || x == a);
}

//  -1 none found
// >=0 index in buf of first found unknown 
int first_unknown_in_eqn(int x, int y, int z)
{
    // eqn 1485: x = (y ◇ x) ◇ (x ◇ (z ◇ y))
    int a = op(y, x);
    if (a == UNKNOWN) {
        return index(y, x);
    }

    int b = op(z, y);
    if (b == UNKNOWN) {
        return index(z, y);
    }

    int c = op(x, b);
    if (c == UNKNOWN) {
        return index(x, b);
    }

    int d = op(a, c);
    if (d == UNKNOWN) {
        return index(a, c);
    }
    return -1;
}

//  -1 none found
// >=0 index in buf of first found unknown 
int one_unknown_in_eqn(int x, int y, int z)
{
    // eqn 1485: x = (y ◇ x) ◇ (x ◇ (z ◇ y))
    int a = op(y, x);
    if (a == UNKNOWN) {
        return index(y, x);
    }

    int b = op(z, y);
    if (b == UNKNOWN) {
        return index(z, y);
    }

    int c = op(x, b);
    if (c == UNKNOWN) {
        return index(x, b);
    }

    int d = op(a, c);
    if (d == UNKNOWN) {
        return index(a, c);
    }
    return -1;
}

int find_single_unknown_in_eqn(void)
{
    int a,b,c,d;
    int x,y,z;
    int idx;

    // find which elements have fully defined left or right multiplication
    int defR[N];
    int defL[N];
    for(x=0; x<N; ++x) {
        int rmul=0;
        int lmul=0;
        for(y=0; y<N; ++y) {
            if (op(x,y) >= 0) { ++lmul; }
            if (op(y,x) >= 0) { ++rmul; }
        }
        defL[x] = (lmul == N);
        defR[x] = (rmul == N);
    }

    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            for(z=0; z<N; ++z) {
                idx = -1;

                // eqn 1485: x = (y ◇ x) ◇ (x ◇ (z ◇ y))
                int a = op(y, x);
                if (a == UNKNOWN) {
                    idx = index(y,x);
                }

                int b = op(z, y);
                if (b == UNKNOWN) {
                    if (idx >= 0 || !defL[x] || !defL[a]) {
                        continue;
                    }
                    return index(z,y);
                }

                int c = op(x, b);
                if (c == UNKNOWN) {
                    if (idx >= 0 || !defL[a]) {
                        continue;
                    }
                    return index(x,b);
                }

                if (a == UNKNOWN) {
                    if (!defR[c]) {
                        continue;
                    }
                    return idx;
                }

                int d = op(a, c);
                if (d == UNKNOWN) {
                    return index(a, c);
                }
            }
        }
    }
    return -1;
}

void print_table(void)
{
    int a,x,y;
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            a = op(x,y);
            if (a == UNKNOWN) {
                printf(" ??");
            } else {
                printf(" %2d", a);
            }
        }
        printf("\n");
    }
}

void brute(int depth)
{
#ifdef TRACE
    if (1) {
#else
    if (depth <= SHOW_DEPTH) {
#endif
        printf(" -- depth=%d\n", depth);
        print_table();
    }

    int idx;
    int x,y,z;

    // return if contradiction
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            for(z=0; z<N; ++z) {
                if (!fuzzy_check_eqn(x,y,z)) {
                    trace_printf("contradiction #3 (%d, %d, %d)\n", x, y, z);
                    return;
                }
            }
        }
    }
/*
    // Note:
    // trying to check in same order that we are "filling in" actually hurts speed

    for(x=0; x<N; ++x) {
        if (!fuzzy_check_eqn(x,x,x)) {
            trace_printf("contradiction #1 (%d, %d, %d)\n", x, x, x);
            return;
        }
    }
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            if (x==y) {
                continue;
            }
            if (!fuzzy_check_eqn(x,x,y)) {
                trace_printf("contradiction #2 (%d, %d, %d)\n", x, x, y);
                return;
            }
            if (!fuzzy_check_eqn(x,y,x)) {
                trace_printf("contradiction #2 (%d, %d, %d)\n", x, y, x);
                return;
            }
            if (!fuzzy_check_eqn(y,x,x)) {
                trace_printf("contradiction #2 (%d, %d, %d)\n", y, x, x);
                return;
            }
        }
    }
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            if (x==y) {
                continue;
            }
            for(z=0; z<N; ++z) {
                if (x==z || y==z) {
                    continue;
                }
                if (!fuzzy_check_eqn(x,y,z)) {
                    trace_printf("contradiction #3 (%d, %d, %d)\n", x, y, z);
                    return;
                }
            }
        }
    }
*/

    // find idx of unknown
    // this is where choices appear to have the largest effects on speed
/*
    // As a test, try selecting in 'table order'
    // ... runs horribly slow
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            idx = index(x,y);
            if (buf[idx] == UNKNOWN) {
                goto found_idx;
            }
        }
    }
*/
    if ((idx = find_single_unknown_in_eqn()) >= 0) {
        goto found_idx;
    }

    for(x=0; x<N; ++x) {
        if ((idx = first_unknown_in_eqn(x,x,x)) >= 0) {
            goto found_idx;
        }
    }
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            if (x==y) {
                continue;
            }
            if ((idx = first_unknown_in_eqn(x,x,y)) >= 0) {
                goto found_idx;
            }
            if ((idx = first_unknown_in_eqn(x,y,x)) >= 0) {
                goto found_idx;
            }
            if ((idx = first_unknown_in_eqn(y,x,x)) >= 0) {
                goto found_idx;
            }
        }
    }
    for(x=0; x<N; ++x) {
        for(y=0; y<N; ++y) {
            if (x==y) {
                continue;
            }
            for(z=0; z<N; ++z) {
                if (x==z || y==z) {
                    continue;
                }
                if ((idx = first_unknown_in_eqn(x,y,z)) >= 0) {
                    goto found_idx;
                }
            }
        }
    }

    printf("---- Success ----\n");
    print_table();
    printf("----------\n");
    return;

found_idx:
    trace_printf("found idx=%d : x=%d y=%d\n", idx, (idx-TABLE_OFFSET)/N, (idx-TABLE_OFFSET)%N);
    for (x=0; x<N; ++x) {
        buf[idx] = x;
        brute(depth+1);
    }
    buf[idx] = UNKNOWN;
}


int main(void)
{
    // use line buffering even if output is piped
    setvbuf(stdout, NULL, _IOLBF, 0);

    // initialize buffer used for magma table
    for(int i=0; i<TOTAL_BUF_SIZE; ++i) {
        buf[i] = UNKNOWN;
    }

    // start recursion
    brute(0);
    return 0;
}
