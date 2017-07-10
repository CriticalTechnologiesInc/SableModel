
int a;
int b;

void xxxx(void){
  int x = a;
  a = 42;
}
void swap(int* x, int* y){
  int t = *x;
  *x = *y;
  *y = t;
}
void f(void){
  a= 1;
  b = 2;
  swap(&a , &b);
}

