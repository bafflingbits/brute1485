
// --- global settings
// Note this brute forces entire magma space,
// but assuming first table index chosen for populating is index(0,0)
// then once this has tried values 0 and 1,
// all other results will just be related by some relabelling.

#define N 9

// use -1 to turn off completely
#define SHOW_DEPTH 8

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

int contradiction_exists(void)
{
    for(int x=0; x<N; ++x) {
        for(int y=0; y<N; ++y) {
            for(int z=0; z<N; ++z) {
                if (!fuzzy_check_eqn(x,y,z)) {
                    return 1;
                }
            }
        }
    }
    return 0;
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

// -2 -> forced contradiction
// -1 -> no forced value (multiple are good)
// >=0 -> value it is forced to
int get_forced_val(int idx, int x, int y, int z)
{
    int found = -1;
    for (int v=0; v<N; ++v) {
        // temporarily define operation
        buf[idx] = v;
        // fast check for contradiction on instance this was found
        if (!fuzzy_check_eqn(x,y,z)) {
            continue;
        }
        // full check for contradiction
        if (!contradiction_exists()) {
            if (found >= 0) {
                // multiple, so not forced yet
                found = -2;
                break;
            }
            found = v;
        }
    }
    buf[idx] = UNKNOWN;
    return found;
}

// -2  -> forced contradiction
// -1  -> None
// >=0 -> idx
int find_forced_or_single_unknown_in_eqn(int *forced_val)
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

    int found = -1;
    int val;
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
                    idx = index(z,y);
                    goto found_one;
                }

                int c = op(x, b);
                if (c == UNKNOWN) {
                    if (idx >= 0 || !defL[a]) {
                        continue;
                    }
                    idx = index(x,b);
                    goto found_one;
                }

                if (a == UNKNOWN) {
                    if (!defR[c]) {
                        continue;
                    }
                    // idx from 'a' calculation
                    goto found_one;
                }

                int d = op(a, c);
                if (d == UNKNOWN) {
                    idx = index(a, c);
                    goto found_one;
                }

                continue;
found_one:
                val = get_forced_val(idx, x, y, z);
                if (val == -2) {
                    return -2;
                }
                if (val >= 0) {
                    *forced_val = val;
                    return idx;
                }
                if (found < 0) {
                    found = idx;
                }
            }
        }
    }
    return found;
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

void brute(int depth, long *call_count)
{
    *call_count += 1;
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
                    trace_printf("contradiction #0 (%d, %d, %d)\n", x, y, z);
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

    // choose an index to fill in next
    int forced_val = -1;

/*
    if (depth < N) {
        idx = index(depth, depth);
        goto found_idx;
    }
*/

/*
    if (depth > -1) {
        if ((idx = find_forced_or_single_unknown_in_eqn(&forced_val)) >= 0) {
            goto found_idx;
        }
        if (idx == -2) {
            trace_printf("found forced contradiction\n");
            return;
        }
    } else {
*/

        if ((idx = find_single_unknown_in_eqn()) >= 0) {
            goto found_idx;
        }

//    }

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
    if (forced_val >= 0) {
        trace_printf("forced idx=%d : x=%d y=%d val=%d\n",
                     idx, (idx-TABLE_OFFSET)/N, (idx-TABLE_OFFSET)%N, forced_val);
        buf[idx] = forced_val;
        brute(depth+1, call_count);
    } else {
        trace_printf("chose idx=%d : x=%d y=%d\n",
                     idx, (idx-TABLE_OFFSET)/N, (idx-TABLE_OFFSET)%N);
        for (x=0; x<N; ++x) {
            buf[idx] = x;
            brute(depth+1, call_count);
        }
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
    long call_count = 0;
    brute(0, &call_count);

    printf("Completed with %ld calls\n", call_count);
    return 0;
}
