typedef union {
  struct { unsigned long num1, num2; } two_num;
  unsigned long num;
  long integer;
  char character;
  struct { int isLab; unsigned long num; } loc;
} struct_args;

typedef struct {
  unsigned int tag;
  struct_args args;
} inst;

struct inst_list {
  inst car;
  struct inst_list* cdr;
};

typedef struct inst_list inst_list;
