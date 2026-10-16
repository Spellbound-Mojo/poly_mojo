import sys, math, statistics as st
for k in sys.argv[1:]:
    P=[];M=[]
    for l in open(k+'.meas'):
        t=l.split()
        if t[0]=='PAIR': P.append(list(map(int,t[1:])))
        if t[0]=='MAT': M.append(list(map(int,t[1:])))
    # deg steps work num den lcm lq g s width
    need=[]
    for d,steps,work,num,den,lcm,lq,g,s,w in P:
        rr=max(num+den+1, 0)             # individual rational reconstruction
        B=max(lcm+s, lq+g+math.ceil(math.log2(steps+3)))+1  # identity bound bits (2B)
        need.append((max(rr,B), work, rr, B))
    tw=sum(x[1] for x in need)
    mx=max(x[0] for x in need)
    wavg=sum(x[0]*x[1] for x in need)/tw
    col=lambda i: [p[i] for p in P]
    print(f"{k}: pairs={len(P)} steps={sum(col(1))} work/prime={tw}")
    for name,i in [('num',3),('den',4),('lcmD',5),('Dq',6),('g',7),('S',8)]:
        v=col(i); print(f"  {name:5s} max={max(v):6d} median={st.median(v):8.0f} mean={st.mean(v):8.0f}")
    print(f"  final row width limbs max={max(col(9))} median={st.median(col(9))}  (bits {64*max(col(9))})")
    print(f"  bits needed (max(rr,2B)) max={mx} work-weighted avg={wavg:.0f}; primes(31b): max={math.ceil(mx/31)} wavg={wavg/31:.1f}")
    print(f"  rr-only max={max(x[2] for x in need)}  B-only max={max(x[3] for x in need)}")
    ex=sum(m[4] for m in M); mo=sum(m[5] for m in M)
    # per-degree prime need if a whole matrix uses one prime count
    bydeg={}
    for (d,*_),x in zip(P,need): bydeg[d]=max(bydeg.get(d,0),x[0])
    est=sum(m[5]*math.ceil(bydeg.get(m[0],0)/31) for m in M)
    print(f"  exact={ex/1e6:.0f}ms  one-prime scalar={mo/1e6:.1f}ms  ratio={ex/mo:.1f}; est scalar modular total (per-degree primes)={est/1e6:.0f}ms")
    for m in M: print("    deg",m[0],"pairs",m[1],"rows",m[2],"cols",m[3],"exact ms %.1f"%(m[4]/1e6),"mod ms %.2f"%(m[5]/1e6),"bits",bydeg.get(m[0]))
