
EXE := brute1485

all: $(EXE)

%: %.c
	gcc -O2 $^ -o $@

clean:
	rm -f $(EXE)

