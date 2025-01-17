#include <stdio.h>
#include <stdlib.h>

// a quicksort program.  set the "length" parameter in main() to the
// desired size of the sorted array.  if you want to sort an array
// bigger than 100 elements, you'll also need to adjust the declaration
// of the global array A.
int A[100];
int length;
int partition(int p, int r) {
  int x, i, j, t;
  int z;
  x = A[p];
  i = p - 1;
  j = r + 1;
  for (z = 0; z < length * length; z += 1) {
    int a;
    j = j - 1;
    for (a = 0; a < length; a += 1) {
      if (A[j] <= x) {
        break;
      }
      j = j - 1;
    }
    for (a = i + 1; a < length; a += 1) {
      if (A[a] >= x) {
        i = a;
        break;
      }
    }
    if (i < j) {
      t = A[i];
      A[i] = A[j];
      A[j] = t;
    } else {
      return j;
    }
  }
  return -1;
}
void quicksort(int p, int r) {
  int q;
  if (p < r) {
    q = partition(p, r);
    printf("q = %d %d %d\n", q, p, r);
    quicksort(p, q);
    quicksort(q + 1, r);
  }
}
void main() {
  int temp;
  int i;
  length = 10;
  // adjust for sort length
  printf("creating random array of %d elements\n", length);
  srandom(17);
  for (i = 0; i < length; i += 1) {
    temp = random();
    A[i] = temp;
  }
  printf("\nbefore sort:\n");
  for (i = 0; i < length; i += 1) {
    printf("%d\n", A[i]);
  }
  quicksort(0, length - 1);
  printf("\nafter sort\n");
  for (i = 0; i < length; i += 1) {
    printf("%d\n", A[i]);
  }
}
