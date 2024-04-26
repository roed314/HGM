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
            return c
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
            return (p, k, v, p**vprec, None)
        else:
            if len(cexps) == 1:
                # Trinomial case
                return (p, k, v, p**vprec, cexps[0])
            elif len(cexps) == 4:
                c = 2*cexps[0] + cexps[2] - cexps[1] - cexps[3] # TODO
                assert c % 2 == 0
                return (p, k, v, p**vprec, c//2)
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
                        per = self.periodicity([c for (p, k, v, vmod, c) in array], p)
                    if per >= 0:
                        q = p**per
                        for (p, k, v, vmod, c) in array[:euler_phi(q)]:
                            yield p, k, v, q, c
                        break
                    start = p**vprec + 1
                    vprec += 1
                    # May need to update values to account for larger vprec
                    for j, (p, k, v, vmod, c) in enumerate(array):
                        if v > vmod:
                            if v < p**vprec:
                                # Recompute
                                array[j] = self.conductor_exponent(p, k, (v % vmod) + p**vprec, vprec)
                            else:
                                # Just update vmod
                                array[j] = (p, k, v, p**vprec, c)
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
