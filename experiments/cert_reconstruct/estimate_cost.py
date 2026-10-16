import sys, math
def load(k, mfile):
    P=[];M={}
    for l in open(k+'.meas'):
        t=l.split()
        if t[0]=='PAIR': P.append(list(map(int,t[1:])))
    for l in open(mfile):
        t=l.split()
        if t[0]=='MAT': M[int(t[1])]=list(map(int,t[1:]))
    return P,M
for k in sys.argv[1:]:
    P,M=load(k, k+'.m2')
    ex=sum(m[4] for m in M.values()); lane=sum(m[6] for m in M.values())
    work_deg={}
    for p in P: work_deg[p[0]]=work_deg.get(p[0],0)+p[2]
    perdeg=0; adapt=0; garner=0; bydeg={}
    for d,steps,work,num,den,lcm,lq,g,s,w in P:
        bits=max(num+den+1, max(lcm+s, lq+g+math.ceil(math.log2(steps+3)))+1)
        bydeg[d]=max(bydeg.get(d,0),bits)
        np_=math.ceil(bits/31); rounds=math.ceil((np_+1)/8)   # +1 prime: confirm stability
        adapt += rounds*M[d][6]*work/work_deg[d]
        garner += steps*(8*rounds)**2/2*1.0   # ns, ~1ns per mulmod
    for d,m in M.items():
        perdeg += math.ceil((math.ceil(bydeg.get(d,0)/31)+1)/8)*m[6]
    print(f"{k:10s} exact={ex/1e6:7.0f}ms  8-lane pass={lane/1e6:6.1f}ms  est(per-degree rounds)={perdeg/1e6:7.0f}ms  est(per-pair rounds)={adapt/1e6:6.0f}ms + garner~{garner/1e6:5.0f}ms")
