#include <bits/stdc++.h>
using namespace std;

struct Term{ long long a; int b,c,d; };
struct Poly{
    vector<Term> t;
    void simplify(){
        vector<Term> v; v.reserve(t.size());
        for(auto &e: t) if(e.a!=0) v.push_back(e);
        if(v.empty()){ t.clear(); return; }
        sort(v.begin(), v.end(), [](const Term&A,const Term&B){
            if(A.b!=B.b) return A.b>B.b; if(A.c!=B.c) return A.c>B.c; if(A.d!=B.d) return A.d>B.d; return false; });
        vector<Term> r; r.reserve(v.size());
        Term cur=v[0];
        for(size_t i=1;i<v.size();++i){
            if(v[i].b==cur.b && v[i].c==cur.c && v[i].d==cur.d) cur.a+=v[i].a; else { if(cur.a!=0) r.push_back(cur); cur=v[i]; }
        }
        if(cur.a!=0) r.push_back(cur);
        t.swap(r);
    }
    static Poly fromInt(long long v){ Poly p; if(v!=0) p.t.push_back({v,0,0,0}); return p; }
    static Poly add(const Poly&x,const Poly&y){ Poly r; r.t=x.t; r.t.insert(r.t.end(), y.t.begin(), y.t.end()); r.simplify(); return r; }
    static Poly sub(const Poly&x,const Poly&y){ Poly r; r.t=x.t; for(auto &e: y.t) r.t.push_back({-e.a,e.b,e.c,e.d}); r.simplify(); return r; }
    static Poly mul(const Poly&x,const Poly&y){ Poly r; r.t.reserve((size_t)x.t.size()*y.t.size());
        for(auto &a: x.t){ if(a.a==0) continue; for(auto &b: y.t){ if(b.a==0) continue; r.t.push_back({a.a*b.a, a.b+b.b, a.c+b.c, a.d+b.d}); } }
        r.simplify(); return r; }
    static Poly deriv(const Poly&p){ Poly r; for(auto &e: p.t){ if(e.a==0) continue; if(e.b>=1) r.t.push_back({ e.a*e.b, e.b-1, e.c,   e.d   }); if(e.c>=1) r.t.push_back({ e.a*e.c, e.b,   e.c-1, e.d+1 }); if(e.d>=1) r.t.push_back({-e.a*e.d, e.b,   e.c+1, e.d-1 }); } r.simplify(); return r; }
};
struct Frac{ Poly p,q; };
static Poly Padd(const Poly&a,const Poly&b){ return Poly::add(a,b);} static Poly Psub(const Poly&a,const Poly&b){ return Poly::sub(a,b);} static Poly Pmul(const Poly&a,const Poly&b){ return Poly::mul(a,b);} 
static Frac Fadd(const Frac&x,const Frac&y){ Frac r; r.p=Padd(Pmul(x.p,y.q), Pmul(y.p,x.q)); r.q=Pmul(x.q,y.q); return r; }
static Frac Fsub(const Frac&x,const Frac&y){ Frac r; r.p=Psub(Pmul(x.p,y.q), Pmul(y.p,x.q)); r.q=Pmul(x.q,y.q); return r; }
static Frac Fmul(const Frac&x,const Frac&y){ Frac r; r.p=Pmul(x.p,y.p); r.q=Pmul(x.q,y.q); return r; }
static Frac Fdiv(const Frac&x,const Frac&y){ Frac r; r.p=Pmul(x.p,y.q); r.q=Pmul(x.q,y.p); return r; }
static Frac Fderiv(const Frac&f){ Frac r; Poly p1=Poly::deriv(f.p); Poly p2=Poly::deriv(f.q); r.p=Psub(Pmul(p1,f.q), Pmul(p2,f.p)); r.q=Pmul(f.q,f.q); return r; }

static bool isdig(char c){ return c>='0'&&c<='9'; }

static Term parse_term(const string &s, int l, int r){
    long long coef=1; int i=l; bool neg=false;
    if(i<r && (s[i]=='+'||s[i]=='-')){ neg=(s[i]=='-'); ++i; }
    long long val=0; bool has=false; while(i<r && isdig(s[i])){ has=true; val=val*10+(s[i]-'0'); ++i; }
    if(has) coef=val; if(neg) coef=-coef;
    int bx=0, bs=0, bc=0;
    auto parse_pow=[&](int &idx){ int pw=1; if(idx<r && s[idx]=='^'){ ++idx; int pv=0; bool hd=false; while(idx<r && isdig(s[idx])){ hd=true; pv=pv*10+(s[idx]-'0'); ++idx; } if(hd) pw=pv; } return pw; };
    while(i<r){
        if(s[i]=='x'){
            ++i; int pw=parse_pow(i); bx+=pw; continue;
        }
        if(i+3<=r && s[i]=='s'&&s[i+1]=='i'&&s[i+2]=='n'){
            i+=3; int pw=1; if(i<r && s[i]=='^'){ ++i; int pv=0; bool hd=false; while(i<r && isdig(s[i])){ hd=true; pv=pv*10+(s[i]-'0'); ++i; } if(hd) pw=pv; }
            if(i<r && s[i]=='x') ++i; bs+=pw; continue;
        }
        if(i+3<=r && s[i]=='c'&&s[i+1]=='o'&&s[i+2]=='s'){
            i+=3; int pw=1; if(i<r && s[i]=='^'){ ++i; int pv=0; bool hd=false; while(i<r && isdig(s[i])){ hd=true; pv=pv*10+(s[i]-'0'); ++i; } if(hd) pw=pv; }
            if(i<r && s[i]=='x') ++i; bc+=pw; continue;
        }
        if(s[i]=='*'){ ++i; continue; }
        break;
    }
    return Term{coef,bx,bs,bc};
}

static Poly parse_poly(const string &s, int l, int r){
    vector<Term> terms; int i=l; while(i<r){ int j=i; if(j<r && (s[j]=='+'||s[j]=='-')) ++j; while(j<r){ char ch=s[j]; if(ch=='+'||ch=='-') break; ++j; } terms.push_back(parse_term(s,i,j)); i=j; }
    Poly p; p.t=move(terms); p.simplify(); return p;
}

static int last_top_addsub(const string &s, int l, int r){ int depth=0; for(int i=r-1;i>=l;--i){ char ch=s[i]; if(ch==')') ++depth; else if(ch=='(') --depth; else if(depth==0 && (ch=='+'||ch=='-')){ if(i==l) return -1; return i; } } return -1; }
static int last_top_muldiv(const string &s, int l, int r){ int depth=0; for(int i=r-1;i>=l;--i){ char ch=s[i]; if(ch==')') ++depth; else if(ch=='(') --depth; else if(depth==0 && (ch=='*'||ch=='/')) return i; } return -1; }

static Frac parse_expr(const string &s, int l, int r){
    while(l<r && (unsigned char)s[l]<=32) ++l; while(r>l && (unsigned char)s[r-1]<=32) --r; if(l>=r){ Frac z; z.p=Poly::fromInt(0); z.q=Poly::fromInt(1); return z; }
    if(s[l]=='('){ int depth=0; bool encl=true; for(int i=l;i<r;i++){ if(s[i]=='(') ++depth; else if(s[i]==')'){ --depth; if(depth==0 && i!=r-1){ encl=false; break; } } } if(depth==0 && encl) return parse_expr(s,l+1,r-1); }
    int pos = last_top_addsub(s,l,r); if(pos!=-1){ char op=s[pos]; Frac L=parse_expr(s,l,pos); Frac R=parse_expr(s,pos+1,r); return (op=='+')? Fadd(L,R) : Fsub(L,R); }
    pos = last_top_muldiv(s,l,r); if(pos!=-1){ char op=s[pos]; Frac L=parse_expr(s,l,pos); Frac R=parse_expr(s,pos+1,r); return (op=='*')? Fmul(L,R) : Fdiv(L,R); }
    if(s[l]=='+'||s[l]=='-'){ bool neg=(s[l]=='-'); Frac sub = parse_expr(s,l+1,r); if(!neg) return sub; Frac m; m.p=Poly::fromInt(-1); m.q=Poly::fromInt(1); return Fmul(m, sub); }
    Poly p = parse_poly(s,l,r); Frac f; f.p=p; f.q=Poly::fromInt(1); return f;
}

static void print_poly(const Poly &p){
    if(p.t.empty()){ cout<<0; return; }
    for(size_t i=0;i<p.t.size();++i){ auto e=p.t[i]; long long a=e.a; if(i==0){ if(a<0){ cout.put('-'); a=-a; } }
        else { if(a<0) cout.put('-'); else cout.put('+'); if(a<0) a=-a; }
        bool isConst=(e.b==0&&e.c==0&&e.d==0);
        bool showCoef=!(a==1 && !isConst);
        if(showCoef) cout<<a;
        if(!isConst){
            if(e.b>0){ cout.put('x'); if(e.b!=1){ cout.put('^'); cout<<e.b; } }
            if(e.c>0){ cout.put('s'); cout.put('i'); cout.put('n'); if(e.c!=1){ cout.put('^'); cout<<e.c; } cout.put('x'); }
            if(e.d>0){ cout.put('c'); cout.put('o'); cout.put('s'); if(e.d!=1){ cout.put('^'); cout<<e.d; } cout.put('x'); }
        }
    }
}

static void print_frac(const Frac &f){
    if(f.p.t.empty()){ cout<<0; return; }
    bool denIsOne = (f.q.t.size()==1 && f.q.t[0].a==1 && f.q.t[0].b==0 && f.q.t[0].c==0 && f.q.t[0].d==0);
    if(denIsOne){ print_poly(f.p); return; }
    bool npar=(f.p.t.size()>1); bool dpar=(f.q.t.size()>1);
    if(npar) cout.put('('); print_poly(f.p); if(npar) cout.put(')'); cout.put('/'); if(dpar) cout.put('('); print_poly(f.q); if(dpar) cout.put(')');
}

int main(){
    ios::sync_with_stdio(false); cin.tie(nullptr);
    string expr; if(!getline(cin, expr)) return 0;
    Frac f = parse_expr(expr, 0, (int)expr.size());
    Frac df = Fderiv(f);
    print_frac(f); cout.put('\n'); print_frac(df); cout.put('\n');
    return 0;
}
