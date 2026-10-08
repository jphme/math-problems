// Naive reference: full minimax over (A,B) with memo, no pruning, no symmetry. Only for tiny boards.
// value f = minimum number of P1 moves (including completing move) in which P1 forces a win; INF otherwise.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <map>
#include <string>
#include <vector>
#include <unordered_map>
using namespace std; typedef uint64_t u64;
int n,N; bool strongG; vector<u64> pl; const int INF=1000;
static bool has(u64 S){ for(u64 p:pl) if((p&S)==p) return true; return false; }
unordered_map<u64,int> memo; // key: A | B<<25 ... N<=25 -> use two 25-bit fields in 64 bits (turn derived)
int f(u64 A,u64 B){
  u64 key=A|(B<<28); auto it=memo.find(key); if(it!=memo.end()) return it->second;
  int pa=__builtin_popcountll(A), pb=__builtin_popcountll(B);
  u64 free=((1ULL<<N)-1)&~A&~B; int res;
  if(pa==pb){ // P1 moves
    res=INF;
    for(int c=0;c<N;c++) if(free>>c&1){
      u64 A2=A|(1ULL<<c);
      int v;
      if(has(A2)) v=pa+1; else v=f(A2,B);
      if(v<res) res=v;
    }
  } else { // P2 moves; result = max over replies (P2 maximizes)
    res = free? -1 : INF;
    for(int c=0;c<N;c++) if(free>>c&1){
      u64 B2=B|(1ULL<<c); int v;
      if(strongG && has(B2)) v=INF; else v=f(A,B2);
      if(v>res) res=v;
    }
  }
  return memo[key]=res;
}
int main(int argc,char**argv){
  n=atoi(argv[1]); N=n*n; strongG=string(argv[2])=="strong";
  // shape cells from argv[3..] as x,y pairs
  vector<pair<int,int>> S; for(int i=3;i+1<argc;i+=2) S.push_back({atoi(argv[i]),atoi(argv[i+1])});
  vector<u64> all;
  for(int t=0;t<8;t++){
    vector<pair<int,int>> T; for(auto [x,y]:S){ int a=x,b=y; if(t&1) a=-a; if(t&2) b=-b; if(t&4) swap(a,b); T.push_back({a,b}); }
    for(int ox=-10;ox<n+10;ox++) for(int oy=-10;oy<n+10;oy++){ u64 m=0; bool ok=true;
      for(auto [a,b]:T){ int X=a+ox,Y=b+oy; if(X<0||Y<0||X>=n||Y>=n){ok=false;break;} m|=1ULL<<(Y*n+X);} if(ok) all.push_back(m);} }
  sort(all.begin(),all.end()); all.erase(unique(all.begin(),all.end()),all.end()); pl=all;
  int v=f(0,0); printf("naive %s n=%d: %s\n", argv[2], n, v>=INF?"no P1 win":("P1 wins in "+to_string(v)).c_str());
}
