//#include <stdlib.h>
//#include <stdio.h>
//#include <string.h>
//anaaktge mem safe version
void quicksort(int lo, int hi, int base[])
{ 
  int i,j;
  int pivot,temp;
    
  if (lo<hi) {
    for (i=lo,j=hi,pivot=base[hi];i<j;) {
      while (i<hi && base[i]<=pivot) i++;
      while (j>lo && base[j]>=pivot) j--;
      if (i<j) { temp=base[i]; base[i]=base[j]; base[j]=temp; }
    }
    temp=base[i]; base[i]=base[hi]; base[hi]=temp;
    quicksort(lo,i-1,base);  quicksort(i+1,hi,base);
  }
}

int cmpint(const void * i, const void * j)
{
  int vi = *((int *) i);
  int vj = *((int *) j);
  if (vi == vj) return 0;
  if (vi < vj) return -1;
  return 1;
}

int main()
{
  int n = 100;
  int i;
  int a[100];
  int b[100];

  for (i = 0; i < n; i++) b[i] = a[i] = i % 7;
    quicksort(0, n - 1, a);
  
  for (i = 0; i < (n-1); i++) {
    if (a[i] > a[i+1]) { return 2; }
  }
  return 0;
}
