#!/usr/bin/env python3
"""Finite actual-xi scouts. All actual-xi results are numerical, NOT certified."""
import itertools, json, math, argparse
from pathlib import Path
from fractions import Fraction as Q
import mpmath as mp

def xi(s):
    return s*(s-1)/2 * mp.power(mp.pi,-s/2)*mp.gamma(s/2)*mp.zeta(s)

def moments(max_n, dps):
    mp.mp.dps = dps
    half = mp.mpf(1)/2
    A = [mp.diff(lambda w: xi(half+w), 0, 2*k)/mp.factorial(2*k)
         for k in range(max_n+2)]
    assert A[0]>0 and A[1]>0
    f = [mp.mpf(1)] + [A[k]*A[0]**(k-1)/A[1]**k for k in range(1,max_n+2)]
    u=[]
    for n in range(max_n+1):
        correction=sum((-1)**(j+1)*f[j]*u[n-j] for j in range(1,n+1))
        u.append((-1)**n*(n+1)*f[n+1]+correction)
    return u, A[1]/A[0]

def bernstein(u,N,j):
    return math.comb(N,j)*sum((-1)**r*math.comb(N-j,r)*u[j+r]
                              for r in range(N-j+1))

def quadratic(P,v):
    if not v: return mp.mpf(0)
    sol=mp.lu_solve(mp.matrix(P),mp.matrix(v))
    return sum(v[i]*sol[i] for i in range(len(v)))

def interval(u,N):
    if N==0: return mp.mpf(0),mp.mpf(1)
    if N%2==0:
        m=N//2
        P=[[u[i+j+1] for j in range(m)] for i in range(m)]
        a=[u[m+i+1] for i in range(m)]
        Q0=[[u[i+j]-u[i+j+1] for j in range(m)] for i in range(m)]
        b=[u[m+i]-u[m+i+1] for i in range(m)]
    else:
        m=(N-1)//2
        P=[[u[i+j] for j in range(m+1)] for i in range(m+1)]
        a=[u[m+i+1] for i in range(m+1)]
        Q0=[[u[i+j+1]-u[i+j+2] for j in range(m)] for i in range(m)]
        b=[u[m+i+1]-u[m+i+2] for i in range(m)]
    return quadratic(P,a),u[N]-quadratic(Q0,b)

def mul(a,b):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]+=x*y
    return out

def dual(u,q):
    sq=mul(q,q)
    return (sum(c*u[i] for i,c in enumerate([0]+sq)),
            sum(c*u[i] for i,c in enumerate(mul([1,-1],sq))))

def controls():
    q=[Q(-1),Q(2)]
    p=mul([Q(1),Q(-1)],mul(q,q))
    uniform=sum(c/Q(i+1) for i,c in enumerate(p))
    fake=[Q(1),Q(1,2),Q(0),Q(0)]
    exclusion=sum(c*fake[i] for i,c in enumerate(p))
    assert uniform==Q(1,6)
    assert exclusion==Q(-3,2)
    return {"positive":"1/6","negative":"-3/2",
            "test_polynomial":"(1-X)*(2*X-1)^2",
            "status":"EXACT_RATIONAL_PASS"}

def strnum(x): return mp.nstr(x,28)

def run():
    u_low,_=moments(8,65)
    u,kappa=moments(8,95)
    discrepancy=max(abs(a-b) for a,b in zip(u,u_low))
    rows=[]
    for n in range(9):
        row=[bernstein(u,n,j) for j in range(n+1)]
        rows.append({"N":n,"min_weight":strnum(min(row)),
                     "variation":strnum(sum(abs(x) for x in row)),
                     "numeric_nonnegative":bool(min(row)>=0)})
    successors=[]
    for n in (2,4,8):
        l,h=interval(u,n-1)
        successors.append({"N":n, "L":strnum(l),"xi_moment":strnum(u[n]),
                           "U":strnum(h), "left_margin":strnum(u[n]-l),
                           "right_margin":strnum(h-u[n]),
                           "numeric_pass":bool(l<=u[n]<=h)})
    candidates=0; bad=[]; minimum=None
    for degree in range(4):
        for q in itertools.product((-2,-1,0,1,2), repeat=degree+1):
            if q[-1]<=0: continue
            a,b=dual(u,q)
            candidates+=1
            minimum=min(a,b) if minimum is None else min(minimum,a,b)
            if a<0 or b<0:
                bad.append({"q":list(q),"x_q2":strnum(a),
                            "one_minus_x_q2":strnum(b)})
    good=(all(x["numeric_nonnegative"] for x in rows)
          and all(x["numeric_pass"] for x in successors) and not bad)
    return {
      "scope":"bounded finite moments of actual xi; numerical only",
      "status":"NUMERIC_PASS_NOT_RH_WITNESS" if good else
               "NUMERIC_NEGATIVE_CANDIDATE_REQUIRES_RIGOROUS_REPLAY",
      "precision_digits":[65,95],"maximum_repeat_difference":strnum(discrepancy),
      "kappa":strnum(kappa),"u0":strnum(u[0]),
      "bernstein_rows":rows,"successor_scouts":successors,
      "rational_quadratic":{"max_degree":3,"coefficient_range":[-2,2],
                            "tested":candidates,"minimum":strnum(minimum),
                            "negative_count":len(bad),"negative_samples":bad[:8]},
      "exact_synthetic_controls":controls(),
      "certified_actual_xi_enclosures":False,
      "all_N_propagation_proved":False,
      "accepted_positive_RH_witness":False}

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output",default="ci-results/sturmion-finite-scouts.json")
    args=p.parse_args()
    result=run()
    out=Path(args.output)
    out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(result,indent=2))
