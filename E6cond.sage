#!/usr/bin/env sage

import argparse
from collections import defaultdict

parser = argparse.ArgumentParser(description="Conductors of hypergeometric motives")
parser.add_argument("infile")
parser.add_argument("--i", type=int, default=None)
parser.add_argument("--kmax", type=int, default=30)
parser.add_argument("--kmin", type=int, default=None)
def intlist(L):
    return [ZZ(c) for c in L.split(",")]
parser.add_argument("--ps", type=intlist, default=[2,3])

class PolyArray:
    def __init__(self, polys):
        if len(polys) == 5:
            # E6 case
            polys = polys[:2] + polys[3:]
        self.polys = polys

    @cached_method
    def specialize(self, t):
        """
        Return number fields with monic integral defining polynomials arising from specializing at t
        """
        S.<x> = QQ[]
        specialized = [S(f.subs(t=t)) for f in self.polys]
        integral = [f * f.denominator() for f in specialized]
        monics = [f.subs(x=x/f.leading_coefficient()).monic() for f in integral]
        nfs = [NumberField(f, 'a') for f in monics]
        discs = [K.discriminant() for K in nfs]
        return nfs, discs

    @cached_method
    def valuations(self, t, p):
        nfs, discs = self.specialize(t)
        val = QQ.valuation(p)
        return [val.extensions(K) for K in nfs]

    def conductor_exponent(self, p, k, v, vprec):
        def _exponent(D, ws, n):
            """
            INPUT:

            - D -- the discriminant of K
            - ws -- the p-adic valuations on K
            - n -- the degree of K
            """
            es = [w.value_group().gen().denominator() for w in ws]
            fs = [w.residue_field().cardinality().exact_log(p) for w in ws]
            assert sum(e*f for (e,f) in zip(es, fs)) == n
            c = D.valuation(p) - n + sum(fs)
            assert c >= 0
            return c
        ctr = 0
        while True:
            t = v * p^k
            try:
                nfs, discs = self.specialize(t)
                vals = self.valuations(t, p)
            except Exception:
                v += p^vprec
                ctr += 1
                if ctr > 3:
                    print(f"Warning: time {ctr} looping on v for p={p}, k={k}, v={v}")
            else:
                break
        try:
            cexps = [_exponent(D, ws, K.degree()) for (K, D, ws) in zip(nfs, discs, vals)]
        except AssertionError:
            return (p, k, v, None)
        else:
            if len(cexps) == 1:
                # Trinomial case
                return (k, v, cexps[0])
            elif len(cexps) == 4:
                c = 2*cexps[0] + cexps[2] - cexps[1] - cexps[3] # TODO
                assert c % 2 == 0
                return (p, k, v, c//2)

    def periodicity(self, L, p):
        """
        Return the smallest nonnegative integer r so that L[a] only depends on (a mod p^r).
        The largest possible value of r is the p-adic valuation of the length of L.
        If there is no periodicity, return -1.
        """
        n = ZZ(len(L))
        v = n.valuation(p)
        for m in range(v+1):
            if all(len(set(L[a::euler_phi(p^m)])) == 1 for a in range(p^m)):
                return m
        return -1


    def conductor_sweep(self, primes=[2,3], kbounds=(-30,31)):
        for p in primes:
            print(f"For p={p}:")
            for k in range(*kbounds):
                if k == 0: # skipping for now since not stable angularization
                    continue
                print(f" Starting k={k}")
                vprec = 3 if (p == 2) else 2
                start = 1
                array = []
                while True:
                    for v in range(start, p^vprec):
                        if v % p != 0:
                            array.append(self.conductor_exponent(p, k, v, vprec))
                    per = self.periodicity([c for (p, k, v, c) in array], p)
                    if per >= 0:
                        yield from array[:euler_phi(p^per)]
                        break
                    start = p^vprec + 1
                    vprec += 1
                    print(array)
                    print(f"  Increasing vprec to {vprec}")

args = parser.parse_args()
R.<t, x> = QQ[]
with open(args.infile) as F:
    s = F.read().replace("\n", "").replace(" ", "").replace("\\", "").replace("{", "[").replace("}", "]")
    polys = sage_eval(s, {'x': x, 't': t})
if args.i is None:
    outfile = f"{args.infile}.out"
    plotbase = f"{args.infile}.plot"
else:
    outfile = f"{args.infile}.{args.i}.out"
    plotbase = f"{args.infile}.{args.i}.plot"
    polys = [polys[args.i]]
if args.kmin is None:
    args.kmin = -args.kmax
kbounds = (args.kmin, args.kmax + 1)
plot_points = defaultdict(set)
with open(outfile, "w") as F:
    for f in polys:
        X = PolyArray(f)
        for p, k, v, c in X.conductor_sweep(args.ps, kbounds):
            plot_points[p].add((k, c))
            _ = F.write(f"{v}*{p}^{k} {c}\n")
            F.flush()
for p, pts in plot_points.items():
    points(pts).save(f"{plotbase}.{p}.png")
