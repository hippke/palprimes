// Exact count of base-b palindromic primes of a given digit length L.
// Usage: palcount b L [nthreads] [Xmax]  (with Xmax: only palindromes n <= Xmax)
// Prints: b L count_palindromes count_primes
// Method: enumerate the first ceil(L/2) digits (leading digit nonzero), build n,
// trial division by primes < 128, then deterministic Miller-Rabin for n < 2^64
// (bases 2, 325, 9375, 28178, 450775, 9780504, 1795265022; Sinclair set).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>

typedef unsigned __int128 u128;
static inline uint64_t mulmod(uint64_t a, uint64_t b, uint64_t m){ return (uint64_t)((u128)a*b % m); }
static uint64_t powmod(uint64_t a, uint64_t e, uint64_t m){
  uint64_t r=1; a%=m; while(e){ if(e&1) r=mulmod(r,a,m); a=mulmod(a,a,m); e>>=1;} return r; }
static int sprp(uint64_t n, uint64_t a){
  a%=n; if(a==0) return 1;
  uint64_t d=n-1; int s=0; while(!(d&1)){d>>=1;s++;}
  uint64_t x=powmod(a,d,n); if(x==1||x==n-1) return 1;
  for(int i=1;i<s;i++){ x=mulmod(x,x,n); if(x==n-1) return 1; if(x==1) return 0; }
  return 0; }
static const int SP[]={2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127};
static int isprime(uint64_t n){
  if(n<2) return 0;
  for(unsigned i=0;i<sizeof(SP)/sizeof(SP[0]);i++){ if(n==(uint64_t)SP[i]) return 1; if(n%SP[i]==0) return 0; }
  if(n<127ULL*127ULL) return 1;
  static const uint64_t B[]={2,325,9375,28178,450775,9780504,1795265022};
  for(int i=0;i<7;i++) if(!sprp(n,B[i])) return 0;
  return 1; }

int main(int argc,char**argv){
  if(argc<3){fprintf(stderr,"usage: palcount b L [threads]\n");return 1;}
  int b=atoi(argv[1]), L=atoi(argv[2]);
  if(argc>3) omp_set_num_threads(atoi(argv[3]));
  int h=(L+1)/2;               // number of free digits
  // check n < 2^64: b^L must fit
  long double bl=1; for(int i=0;i<L;i++) bl*=b; if(bl>1.8e19L){fprintf(stderr,"too large\n");return 2;}
  uint64_t pw[64]; pw[0]=1; for(int i=1;i<=L;i++) pw[i]=pw[i-1]*(uint64_t)b; // pw[L] may overflow only if L digits exceed, guarded above
  // coefficient of free digit j (j=0 is the leading digit position L-1 and the last digit position 0)
  uint64_t c[64];
  for(int j=0;j<h;j++){ int hi=L-1-j, lo=j; c[j]= (hi==lo)? pw[hi] : pw[hi]+pw[lo]; }
  uint64_t lo_start=pw[h-1], hi_end=pw[h]; // half values H in [b^(h-1), b^h)
  if(argc>4){ // palindrome value is increasing in the half H, so cut the H range by bisection
    uint64_t X=strtoull(argv[4],0,10), lo=lo_start, hi=hi_end; // find first H with pal(H) > X
    while(lo<hi){ uint64_t mid=lo+(hi-lo)/2, t=mid, n=0; for(int j=h-1;j>=0;j--){ n+=(t%(uint64_t)b)*c[j]; t/=(uint64_t)b; }
      if(n<=X) lo=mid+1; else hi=mid; }
    hi_end=lo; }
  uint64_t npal=hi_end-lo_start, nprime=0;
  #pragma omp parallel for schedule(dynamic,4096) reduction(+:nprime)
  for(uint64_t H=lo_start; H<hi_end; H++){
    // digits of H: most significant digit is free digit j=0
    uint64_t t=H, n=0;
    for(int j=h-1;j>=0;j--){ n+= (t% (uint64_t)b)*c[j]; t/= (uint64_t)b; }
    nprime+=isprime(n);
  }
  printf("%d %d %llu %llu\n",b,L,(unsigned long long)npal,(unsigned long long)nprime);
  return 0; }
