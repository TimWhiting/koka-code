#include <stdio.h>
#include <stdlib.h>
// To sort array a[] of size n: qsort(a,0,n-1)

void qsort2(int a[], int lo, int hi) 
{
  int h, l, p, t;

  if (lo < hi) {
    l = lo;
    h = hi;
    p = a[hi];

    do {
      while ((l < h) && (a[l] <= p)) 
          l = l+1;
      while ((h > l) && (a[h] >= p))
          h = h-1;
      if (l < h) {
          t = a[l];
          a[l] = a[h];
          a[h] = t;
      }
    } while (l < h);

    a[hi] = a[l];
    a[l] = p;

    qsort2( a, lo, l-1 );
    qsort2( a, l+1, hi );
  }
}

void main() {
  for (int t = 0; t < 100; t++){
    int a[10000];
    for (int i = 0; i < 10000; i++){
      a[i] = rand() % 10000;
    }
    qsort2(a, 0, 9999);
  }

  // for (int i = 0; i < 100; i++)
  //   printf("%d ", a[i]);
  // printf("\n");
}