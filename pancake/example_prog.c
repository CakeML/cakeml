
(*
  program for
   reading, preprocssing, writing,
   skipping until new characters are reached
 *)



#include <ctype.h>
#include <stdio.h>


int main (void) {
  int c;

  do {
    do {
      c = getchar();
    } while (isspace(c));

    while (!isspace(c) && c != EOF) {
      putchar(c);
      c = getchar();
    }

    while (c != '\n' && c != EOF) {
      c = getchar();
    }

    if (c == '\n') {
      putchar(c);
    }
  } while (c != EOF);

  return 0;
}


// The same task can be solved by thinking in terms of finite-state machines.
// Note that the parsing of a line has three stages:
// skipping the leading whitespace characters,
// printing the characters of the first word, and
// skipping the trailing characters.

// Let's call these automaton states BEFORE, INSIDE and AFTER.
// An automata-based version of the program could look like this:


// while, switch and break statements

// The body of the while loop is the automaton step and
// the loop itself is the cycle of the automaton step

#include <ctype.h>
#include <stdio.h>

enum State {BEFORE, INSIDE, AFTER};

int main(void) {
  int c;
  enum State s = BEFORE;

  while ((c = getchar()) != EOF) {
    switch (s) {
      case BEFORE:
        if (!isspace(c)) {
          putchar(c);
          s = INSIDE;
        }

        break;
      case INSIDE:
        if (c == '\n') {
          putchar(c);
          s = BEFORE;
        } else if (isspace(c)) {
          s = AFTER;
        } else {
          putchar(c);
        }

        break;
      case AFTER:
        if (c == '\n') {
          putchar(c);
          s = BEFORE;
        }

        break;
    }
  }

  return 0;
}


// With an explicit function step for the automation step,
// the program better demonstrates this property:

#include <ctype.h>
#include <stdio.h>

enum State {BEFORE, INSIDE, AFTER};


void step(enum State* const s, int const c) {
  switch (*s) {
    case BEFORE:
      if (!isspace(c)) {
        putchar(c);
        *s = INSIDE;
      }

      break;
    case INSIDE:
      if (c == '\n') {
        putchar(c);
        *s = BEFORE;
      } else if (isspace(c)) {
        *s = AFTER;
      } else {
        putchar(c);
      }

      break;
    case AFTER:
      if (c == '\n') {
        putchar(c);
        *s = BEFORE;
      }

      break;
  }
}


int main(void) {
  int c;
  enum State s = BEFORE;

  while ((c = getchar()) != EOF) {
    step(&s, c);
  }

  return 0;
}

// The program now clearly demonstrates the basic properties of automata-based code:

// 1. time periods of automaton step executions may not overlap;
// 2. the only information passed from the previous step to the next is
//    the explicitly specified automaton state.
