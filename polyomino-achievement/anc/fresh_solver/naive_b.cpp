// Naive bounded reference: P1 wins within r of its own moves? memo over (A,B), no pruning/symmetry.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <string>
#include <vector>
#include <algorithm>
#include <unordered_map>
using namespace std; typedef uint64_t u64;
int n,N,K; bool strongG; vector<u64> pl;
static bool has(u64 S){ for(u64 p:pl) if((p&S)==p) return true; return false; }
unordered_map<u64,char> memo; // key: A | B<<25 (N<=25) ; turn from popcounts
bool g(u64 A,u64 B){
  u64 key=A|(B<<25); auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int pa=__builtin_popcountll(A), pb=__builtin_popcountll(B);
  u64 fr=((1ULL<<N)-1)&~A&~B; bool res;
  if(pa==pb){ res=false;
    if(pa>=K) res=false; else
    for(int c=0;c<N&&!res;c++) if(fr>>c&1){ u64 A2=A|(1ULL<<c); if(has(A2)) res=true; else if(g(A2,B)) res=true; }
  } else { res=true; bool any=false;
    for(int c=0;c<N&&res;c++) if(fr>>c&1){ any=true; u64 B2=B|(1ULL<<c);
      if(strongG&&has(B2)) res=false; else if(!g(A,B2)) res=false; }
    if(!any) res=false;
  }
  return memo[key]=res;
}
int main(int argc,char**argv){
  n=atoi(argv[1]); N=n*n; strongG=string(argv[2])=="strong"; K=atoi(argv[3]);
  vector<pair<int,int>> S; for(int i=4;i+1<argc;i+=2) S.push_back({atoi(argv[i]),atoi(argv[i+1])});
  vector<u64> all;
  for(int t=0;t<8;t++){ vector<pair<int,int>> T; for(auto [x,y]:S){ int a=x,b=y; if(t&1) a=-a; if(t&2) b=-b; if(t&4) swap(a,b); T.push_back({a,b}); }
    for(int ox=-10;ox<n+10;ox++) for(int oy=-10;oy<n+10;oy++){ u64 m=0; bool ok=true;
      for(auto [a,b]:T){ int X=a+ox,Y=b+oy; if(X<0||Y<0||X>=n||Y>=n){ok=false;break;} m|=1ULL<<(Y*n+X);} if(ok) all.push_back(m);} }
  sort(all.begin(),all.end()); all.erase(unique(all.begin(),all.end()),all.end()); pl=all;
  printf("%d\n", (int)g(0,0));
}
