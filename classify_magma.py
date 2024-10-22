
import itertools
import sys


def extract_found_magma(fname):
    out = []
    with open(fname, "r") as f:
        m = None
        for line in f:
            if m is None:
                if "Success" in line:
                    m = []
                continue
            if "--" in line:
                out.append(tuple(m))
                m = None
                continue
            line = line.strip()
            row = tuple(int(s) for s in line.split(' ') if s != "")
            m.append(row)
        if m is not None:
            print("Error: file ended in middle of magma data.")
            print("Rejecting partial data:", m)

    if len(out) == 0:
        print("Error: did not find any magma results.")
        return None

    # sanity check that all magma tables are square and the same size
    n = len(out[0])
    for m in out:
        if len(m) != n or any(len(row) != n for row in m):
            print("Error: found table of incorrect shape")
            print("data:", m)
            return None
    return out


def print_table(m):
    print("[" + ",\n ".join(str(list(row)) for row in m) + "]")


def categorize_magmas(mlist):
    """
    returns list of (magma canonical table, tuple permutations)
    """
    #seen = set()
    seen = {}
    count = []
    clist = []

    for m in mlist:
        if m in seen:
            count[seen[m]] += 1
            continue
        # find canonical table
        n = len(m)
        best = m
        for p in itertools.permutations(range(n)):
            d2 = {}
            for x,y in itertools.product(range(n), repeat=2):
                d2[(p[x],p[y])] = p[m[x][y]]
            m2 = tuple(tuple(d2[(x,y)] for y in range(n)) for x in range(n))
            seen[m2] = len(clist)
            if m2 < best:
                best = m2
        # there is probably a way to get this on first pass,
        # but this is easier
        # get permutations that leave 'canonical' table unchanged
        plist = []
        for p in itertools.permutations(range(n)):
            d2 = {}
            for x,y in itertools.product(range(n), repeat=2):
                d2[(p[x],p[y])] = p[best[x][y]]
            m2 = tuple(tuple(d2[(x,y)] for y in range(n)) for x in range(n))
            if m2 == best:
                plist.append(p)
        count.append(1)
        clist.append((best, tuple(plist)))

    for i,entry in enumerate(clist):
        best, plist = entry
        print(f"--- magma #{i}, count={count[i]}")
        print_table(best)
        for p in plist:
            print("perm:", p)
        print("")

    return clist


# -------------------------------------------------------------

if len(sys.argv) != 2:
    print("Usage: classify_magma.py brute_output.txt")
    sys.exit(1)
fname = sys.argv[1]

mlist = extract_found_magma(fname)
if mlist is None:
    sys.exit(1)

clist = categorize_magmas(mlist)

