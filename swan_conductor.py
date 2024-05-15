"""
Functions for computing the Swan conductor of a number field.
"""
import time
import re
from sage.all import ZZ, QQ, PolynomialRing, NumberField, pari, sage_eval, euler_phi, cached_method

class PolyArray:
    def __init__(self, polys, w, primes=[2,3], quiet=False):
        if len(polys) == 5:
            # E6 case
            polys = polys[:2] + polys[3:]
        self.polys = polys
        self.w = w
        self.primes = primes
        self.quiet = quiet

    @cached_method
    def specialize(self, t):
        """
        Return number fields with monic integral defining polynomials arising from specializing at t
        """
        S = PolynomialRing(QQ, "x")
        x = S.gen()
        specialized = [S(f.subs(t=t)) for f in self.polys]
        if not all(f.is_irreducible() for f in specialized):
            raise ValueError("Reducible specialization")
        integral = [f * f.denominator() for f in specialized]
        monics = [f.subs(x=x/f.leading_coefficient()).monic() for f in integral]
        discs = [ZZ(pari([f,self.primes]).nfdisc()) for f in monics]
        nfs = [NumberField(f, 'a') for f in monics]
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
            m0 = sum(e.val_unit(p)[1] * f for (e,f) in zip(es, fs))
            return c, m0
        ctr = 0
        while True:
            t = v * p**k
            try:
                nfs, discs = self.specialize(t)
                vals = self.valuations(t, p)
            except Exception:
                v += p**vprec
                ctr += 1
                if ctr > 3 and not self.quiet:
                    print(f"Warning: time {ctr} looping on v for p={p}, k={k}, v={v}")
            else:
                break
        try:
            cexps = [_exponent(D, ws, K.degree()) for (K, D, ws) in zip(nfs, discs, vals)]
        except AssertionError:
            return (p, k, v, p**vprec, None, None)
        else:
            if len(cexps) == 1:
                # Binomial or Trinomial case
                c, m0 = cexps[0]
                return (p, k, v, p**vprec, c, m0)
            elif len(cexps) == 4:
                c = 2*cexps[0][0] + cexps[2][0] - cexps[1][0] - cexps[3][0]
                assert c % 2 == 0
                m0 = 2*cexps[0][1] + cexps[2][1] - cexps[1][1] - cexps[3][1] - 1
                assert m0 % 2 == 0
                return (p, k, v, p**vprec, c//2, m0//2)
            else:
                raise NotImplementedError

    def periodicity(self, L, p):
        """
        Return the smallest nonnegative integer r so that L[a] only depends on (a mod p^r).
        The largest possible value of r is the p-adic valuation of the length of L.
        If there is no periodicity, return -1.
        """
        n = ZZ(len(L))
        v = n.valuation(p)
        for m in range(v+1):
            if all(len(set(L[a::euler_phi(p**m)])) == 1 for a in range(p**m)):
                return m
        return -1


    def conductor_sweep(self, ks):
        for p in self.primes:
            if not self.quiet:
                print(f"For p={p}:")
            t0 = time.time()
            for k in ks:
                if k == 0: # skipping for now since not stable angularization
                    continue
                if not self.quiet:
                    if len(ks) > 1:
                        print(f" Starting k={k} at time {time.time() - t0:.2f}")
                    else:
                        print(f" Starting k={k}")
                if k == 0:
                    vprec = self.w + 1 # k=0 won't stabilize, so we take the maximum expected precision
                else:
                    vprec = 3 if (p == 2) else 2
                start = 1
                array = []
                while True:
                    for v in range(start, p**vprec):
                        if v % p != 0:
                            array.append(self.conductor_exponent(p, k, v, vprec))
                    if k == 0:
                        per = self.w + 1
                    else:
                        per = self.periodicity([c for (p, k, v, vmod, c, m0) in array], p)
                    if per >= 0:
                        q = p**per
                        for (p, k, v, vmod, c, m0) in array[:euler_phi(q)]:
                            yield p, k, v, q, c, m0
                        break
                    start = p**vprec + 1
                    vprec += 1
                    # May need to update values to account for larger vprec
                    for j, (p, k, v, vmod, c, m0) in enumerate(array):
                        if v > vmod:
                            if v < p**vprec:
                                # Recompute
                                array[j] = self.conductor_exponent(p, k, (v % vmod) + p**vprec, vprec)
                            else:
                                # Just update vmod
                                array[j] = (p, k, v, p**vprec, c, m0)
                    if not self.quiet:
                        print(f"  Increasing vprec to {vprec}")

def data_to_list(infile, outfile):
    informat = re.compile(r"(\d+)\*(\d+)\^\(([0-9/\-]+)\) ([0-9/\-]+)")
    with open(infile) as F:
        with open(outfile, "w") as Fout:
            _ = Fout.write("{\n")
            for line in F:
                v, p, k, c = informat.match(line.strip()).groups()
                _ = Fout.write(f"{{{v},{k},{c}}},\n")
            _ = Fout.write("}\n")

def change_data_format():
    from pathlib import Path
    from collections import defaultdict
    R = PolynomialRing(QQ, "t,x")
    t,x = R.gens()
    DATA = Path("DATA")
    NEWDATA = Path("NEWDATA")
    fname_re = re.compile(r"(?P<p>\d+)\.(?P<w>\d+)\.(?P<r>\d+)\.(?P<m>\d+)\.(?P<k>[0-9\-]+)\.out")
    line_re = re.compile(r"\[(?P<m>\d+),(?P<v>\d+),(?P<vmod>\d+),(?P<x>[0-9/\-]+),(?P<y>[0-9/\-]+)\]")
    files = list(DATA.iterdir())
    maxw = defaultdict(int)
    for fname in files:
        match = fname_re.fullmatch(fname.name)
        if match:
            p, w, r, m, k = int(match.group("p")), int(match.group("w")), int(match.group("r")), int(match.group("m")), int(match.group("k"))
            if k == 0:
                maxw[p,r] = max(w, maxw[p,r])
    Y_lookup = defaultdict(dict)
    for j, fname in enumerate(files):
        if j and j % 100 == 0:
            print(f"Stage 1: {j}/{len(files)}")
        match = fname_re.fullmatch(fname.name)
        if match:
            p, w, r, m, k = int(match.group("p")), int(match.group("w")), int(match.group("r")), int(match.group("m")), int(match.group("k"))
            outfile = NEWDATA / f"{p}.{r}.{r}.{m}.{k}.out"
            if outfile.exists():
                continue
            b = m * p**r
            g = x**b - t
            Y = PolyArray([g], max(r, maxw[p,r]), [p], quiet=True)
            with open(outfile, "w") as F:
                for p, k, v, vmod, cond0 in Y.conductor_sweep([k]):
                    Y_lookup[p,r,m,k][v,vmod] = cond0
                    _ = F.write(f"{v},{vmod},{cond0}")

    for j, fname in enumerate(files):
        if j and j % 1000 == 0:
            print(f"Stage 2: {j}/{len(files)}")
        match = fname_re.fullmatch(fname.name)
        if match:
            p, w, r, m, k = int(match.group("p")), int(match.group("w")), int(match.group("r")), int(match.group("m")), int(match.group("k"))
            outfile = NEWDATA / f"{p}.{w}.{r}.{m}.{k}.out"
            with open(fname) as F:
                with open(outfile, "w") as Fout:
                    for line in F:
                        line = line.strip()[:-1] # strip ending comma or bracket
                        if line:
                            D = line_re.fullmatch(line)
                            d = m * (p**w - p**r)
                            v, vmod, x, y = int(D.group("v")), int(D.group("vmod")), QQ(D.group("x")), QQ(D.group("y"))
                            assert k == x*d
                            for (v0, v0mod), cond0 in Y_lookup[p,r,m,k].items():
                                if (v - v0) % min(vmod, vmod0) == 0:
                                    break
                            else:
                                raise RuntimeError(f"({v},{vmod}) not in Y_lookup[{p},{r},{m},{k}]")
                            cond = y * d + cond0
                            assert cond in ZZ
                            _ = Fout.write(f"{v},{vmod},{cond}")
