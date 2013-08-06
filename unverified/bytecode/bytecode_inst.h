typedef union {
  struct { long num1, num2; } two_num;
  long num;
  long integer;
  char character;
  struct { int isLab; long num; } loc;
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
