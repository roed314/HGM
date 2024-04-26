#!/usr/bin/env -S sage -python

import argparse
import time
from collections import defaultdict
from swan_conductor import PolyArray

parser = argparse.ArgumentParser(description="Computes Swan conductors hypergeometric motives with finite monodromy (from the Beukers-Heckman paper)")
parser.add_argument("infile", help="A file storing a list of lists of 5-polynomials in t and x (correponding to the degree 27, 36, 40a, 40b, 45 permutation representations of W(E6)).  Curly braces are replaced with square brackets and white space is stripped before loading into Sage.")
parser.add_argument("--i", type=int, default=None, help="If present, picks out the ith entry in the input file, used for parallelization with GNU parallel")
parser.add_argument("--kmax", type=int, default=30, help="maximum value of k so that specializations occur at t=p^k (defaults to 30)")
parser.add_argument("--kmin", type=int, default=None, help="minimum value of k so that specializations occur at t=p^k (defaults to -kmax)")
def intlist(L):
    return [ZZ(c) for c in L.split(",")]
parser.add_argument("--ps", type=intlist, default=[2,3], help="A list of primes p so that specialization occurs at t=p^k, given as a comma separated list of integers (defaults to 2,3)")

args = parser.parse_args()
R = PolynomialRing(QQ, "t,x")
t,x = R.gens()
with open(args.infile) as F:
    s = F.read().replace("\n", "").replace(" ", "").replace("\\", "").replace("{", "[").replace("}", "]")
    polys = sage_eval(s, {'x': x, 't': t})
if args.i is not None:
    polys = [polys[args.i]]
if args.kmin is None:
    args.kmin = -args.kmax
kbounds = (args.kmin, args.kmax + 1)
plot_points = defaultdict(set)
for i, f in enumerate(polys):
    if args.i is None:
        outfile = f"{args.infile}.{i}.out"
        plotbase = f"{args.infile}.{i}.plot"
    else:
        outfile = f"{args.infile}.{args.i}.out"
        plotbase = f"{args.infile}.{args.i}.plot"
    X = PolyArray(f, args.ps)
    with open(outfile, "w") as F:
        for p, k, v, vmod, c in X.conductor_sweep(kbounds):
            plot_points[p].add((k, c))
            _ = F.write(f"{v}*{p}^{k} {c}\n")
            F.flush()
    for p, pts in plot_points.items():
        points(pts).save(f"{plotbase}.{p}.png")
