#!/usr/bin/env -S sage -python

# EXAMPLE USAGE:
# ./trinomial_cond.py -p 2 -w='2-3' -r='0-2' -m='1-10' -j 80 --noramp
# ./trinomial_cond.py -p 2 --D -w='2-3' -r='0-2' -m='1-10' -j 80 --noramp

import argparse
import pathlib
import subprocess
import re
from collections import defaultdict
from sage.all import ZZ, QQ, PolynomialRing, points, Graphics, srange, floor, ceil
from swan_conductor import PolyArray

DATA = pathlib.Path("DATA")
DATA.mkdir(exist_ok=True)
PICS = pathlib.Path("pictures")
PICS.mkdir(exist_ok=True)

parser = argparse.ArgumentParser(description="Computes Swan conductors of trinomial hypergeometric motives\nThe trinomial motive is given by a^a x^b (1-x)^c - b^b c^c t, where m ranges from 1 to mmax (prime to p), b=mp^r, c=m(p^w-p^r), a=b+c, and t is specialized at up^k.")
ilist_re = re.compile(r"(-?\d+)(-\d+)?")
def intlist(keyname):
    def process_intlist(s):
        ans = []
        for piece in s.split(","):
            m = ilist_re.match(piece)
            if not m:
                raise ValueError(f"Invalid piece for {keyname}: {piece}")
            a, b = m.groups()
            if b:
                ans.extend(srange(ZZ(a), ZZ(b[1:])+1))
            else:
                ans.append(ZZ(a))
        if keyname == "p":
            ans = [p for p in ans if p.is_prime()]
        return sorted(set(ans))
    return process_intlist
def intminmax(keyname):
    def process_intminmax(s):
        m = ilist_re.match(s)
        if not m:
            raise ValueError(f"Invalid input for {keyname}: {s}")
        a, b = m.groups()
        if b:
            return ZZ(a), ZZ(b[1:])
        else:
            return ZZ(a), ZZ(a)
    return process_intminmax
parser.add_argument("-p", help="Prime", type=intlist("p"))
parser.add_argument("-w", help="Input for determining a,b,c from c=m(p^w-p^r), b=mp^r, a=b+c", type=intlist("w"))
parser.add_argument("-r", help="Input for determining a,b,c from c=m(p^w-p^r), b=mp^r, a=b+c", type=intlist("r"))
parser.add_argument("-k", help="Value of k so that specializations occur at t=p^k", type=intminmax("k"), default=None)
parser.add_argument("-m", help="Value of m, determining a,b,c from c=m(p^w-p^r), b=mp^r, a=b+c (m prime to p)", default=None, type=intlist("m"))
parser.add_argument("-j", "--jobs", help="Signals that jobs should be run in parallel, and specifies number of processes to use", type=int, default=None)
parser.add_argument("--type", default=None, help="Either trinomial, binomial or D")
parser.add_argument("--noramp", action="store_true", help="Omit k that are not prime to p")
parser.add_argument("--nograph", action="store_true", help="Only compute values, do not show graph")
parser.add_argument("--quiet", action="store_true", help="Do not print status output")
#parser.add_argument("--show", action="store_true", help="Only show stored values, do not compute")
args = parser.parse_args()
if args.m is None:
    args.m = list(range(1,10))
assert args.type in [None, "binomial", "trinomial", "D"]

def get_ks(p, w, r):
    if r > w:
        r -= w + 1
    if args.k is None:
        return (floor(-p**w / (p-1) * 1.5), ceil(p**w * (w-r) * 1.5))
    else:
        return args.k

def expand_ks(k0, k1, m, p):
    if args.noramp:
        return [k for k in range(m*k0, m*(k1+1)) if k%p == 0]
    else:
        return list(range(m*k0, m*(k1+1)))

def needed_pwr(p, w, r):
    if r == w:
        # binomial case
        if (r > 0) and (args.type is None or args.type == "binomial"):
            return [(p, r, r), (p, r-1, r-1)]
    elif r < w:
        # trinomial case
        if (r >= 0) and (args.type is None or args.type == "trinomial"):
            return [(p, w, r), (p, r, r)]
    else:
        # D case
        if p == 2 and (w > 0 and r < 2 * w + 1) and (args.type is None or args.type == "D"):
            return [(p, w, r), (p, w, r - w - 1)]
    return []

def outfile(p, w, r, m, k):
    return DATA / f"{p}.{w}.{r}.{m}.{k}.out"
def outfiles_exist(p, w, r, m, k0):
    # Used to determine whether a recursive call to this script needs to be made under parallel
    # The k0 here needs to be (roughly) multiplied by m to get valid inputs for outfile
    ks = expand_ks(k0, k0, m, p)
    if w == r: # binomial case
        return all(outfile(p, w, r, m, k).exists() for k in ks) and all(outfile(p, w-1, r-1, m, k).exists() for k in ks)
    elif r > w: # D case
        return all(outfile(p, w, r, m, k).exists() for k in ks) and all(outfile(p, w, r-w-1, m, k).exists() for k in ks)
    else:
        return all(outfile(p, w, r, m, k).exists() for k in ks) and all(outfile(p, r, r, m, k).exists() for k in ks)

R = PolynomialRing(QQ, "t,x")
t,x = R.gens()
def write_points(w, r, p, m, kminmax):
    rorig = r
    k0, k1 = kminmax
    ks = expand_ks(k0, k1, m, p)
    if r > w:
        D = True
        r -= (w + 1)
        assert r < w
    else:
        D = False
    b = m * p**r
    c = m * (p**w - p**r)
    a = b + c
    if D:
        f = a**a * x**b * (1 - x**2)**c - b**b * c**c * t
        g = a**a * x**b * (1 - x   )**c - b**b * c**c * t
    elif w == r:
        # binomial case
        assert r >= 1
        f = x**b - t
        g = x**(p**(r - 1)) - t
    elif w > r:
        # trinomial case
        f = a**a * x**b * (1-x)**c - b**b * c**c * t
        g = x**b - t
    d = f.degree(x) - g.degree(x)

    X = PolyArray([f], w, [p], quiet=args.quiet)
    for k in ks:
        fname = outfile(p, w, rorig, m, k)
        if fname.exists():
            continue
        with open(fname, "w") as F:
            for p, k, v, vmod, cond, m0 in X.conductor_sweep([k]):
                _ = F.write(f"{v},{vmod},{cond},{m0}")

    Y = PolyArray([g], w, [p], quiet=args.quiet)
    Y_lookup = defaultdict(dict)
    for k in ks:
        fname = outfile(p, w, r, m, k)
        if fname.exists():
            continue
        for p, k, v, vmod, cond in Y.conductor_sweep([k]):
            Y_lookup[k][v,vmod] = cond
        
        X = PolyArray([f], w, [p], quiet=args.quiet)
        with open(fname, "w") as F:
            _ = F.write("[\n")
            for p, k, v, vmod, cond in X.conductor_sweep([k]):
                for (v0, v0mod), cond0 in Y_lookup[k].items():
                    if (v - v0) % min(vmod, v0mod) == 0:
                        break
                else:
                    raise RuntimeError(f"({v}, {vmod}) not in {list(Y_lookup[k])}")
                _ = F.write(f"[{m},{v},{vmod},{k / d},{(cond - cond0) / d}],\n")
            _ = F.write("]\n")

if args.jobs is None:
    for w in args.w:
        for r in args.r:
            for p in args.p:
                for p, w, r in needed_pwr(p, w, r):
                    for m in args.m:
                        if m % p == 0:
                            continue
                        write_points(w, r, p, m, get_ks(p, w, r))
else:
    noramp = " --noramp" if args.noramp else ""
    jobfile = pathlib.Path("DATA", f"parallel{ZZ.random_element(65536).hex()}.jobs")
    ctr = 0
    with open(jobfile, "w") as F:
        for w in args.w:
            for r in args.r:
                for p in args.p:
                    if not needed_pwr(p, w, r):
                        continue
                    for m in args.m:
                        if m % p == 0:
                            continue
                        for k in range(*get_ks(p, w, r)):
                            if not outfiles_exist(p, w, r, m, k):
                                _ = F.write(f"{w} {r} {p} {m} {k}\n")
                                ctr += 1
    try:
        if ctr > 0:
            if not args.quiet:
                print(f"Starting parallel run with {ctr} jobs, tracked in {jobfile}.log")
            subprocess.run(f"parallel -j {args.jobs} -a {jobfile} --joblog {jobfile}.log --colsep ' ' ./trinomial_cond.py --quiet --nograph{noramp} -w='{{1}}' -r='{{2}}' -p='{{3}}' -m='{{4}}' -k='{{5}}'", shell=True, check=True)
    finally:
        jobfile.unlink()

if not args.nograph:
    if not args.quiet:
        print("Creating graphs and point files")
    fname_re = re.compile(r"(?P<p>\d+)\.(?P<w>\d+)\.(?P<r>\d+)\.(?P<m>\d+)\.(?P<k>[0-9\-]+)\.out")
    line_re = re.compile(r"(?P<v>\d+),(?P<vmod>\d+),(?P<c>\d+),(?P<m0>\d+)")
    data = defaultdict(list)
    for fname in DATA.iterdir():
        match = fname_re.fullmatch(fname.name)
        if match:
            p, w, r, m, k = int(match.group("p")), int(match.group("w")), int(match.group("r")), int(match.group("m")), int(match.group("k"))
            with open(fname) as F:
                for line in F:
                    D = line_re.fullmatch(line)
                    if D:
                        v, vmod, c, m0 = int(D.group("v")), int(D.group("vmod")), int(D.group("c")), int(D.group("m0"))
                        data[p,w,r,m,k].append((v, vmod, c, m0))

    plot_points = defaultdict(lambda: defaultdict(set))
    data_points = defaultdict(list)
    colors = ["blue", "salmon", "red", "maroon", "green", "navy", "purple", "brown", "orange", "gold", "turquoise", "black"]
    colors = colors[:len(args.m)]
    colors = colors + ["black" for _ in range(len(args.m)-len(colors))]
    for w in args.w:
        for r in args.r:
            for p in args.p:
                numden = needed_pwr(p, w, r)
                if numden:
                    num, den, d0 = numden
                    for m in args.m:
                        if m % p == 0:
                            continue
                        d = ZZ(m * d0)
                        for k in range(*get_ks(p, w, r)):
                            x = k / d
                            for v, vmod, c, m0 in data[num+(m,k)]:
                                for vv, vvmod, cc, mm0 in data[den+(m,k)]:
                                    if (v - vv) % (min(vmod, vvmod)) == 0:
                                        break
                                else:
                                    raise RuntimeError(f"{v},{vmod} not found for {p},{w},{r},{m},{k}")
                                y = (c - cc) / d
                                plot_points[p,w,r][m].add((x,y))
                                data_points[p,w,r].append((m, v % vmod, v, vmod, x, y, m0 - mm0))
    for fname in DATA.iterdir():
        match = fname_re.fullmatch(fname.name)
        if match:
            p, w, r, m, k = int(match.group("p")), int(match.group("w")), int(match.group("r")), int(match.group("m")), int(match.group("k"))
            ks = get_ks(p, w, r)
            if not (m in args.m and p in args.p and w in args.w and r in args.r and m*ks[0] <= k <= m*ks[1]):
                continue
            with open(fname) as F:
                for line in F:
                    line = line.strip()[:-1] # strip ending comma or bracket
                    if line:
                        D = line_re.fullmatch(line)
                        v, vmod, x, y = int(D.group("v")), int(D.group("vmod")), QQ(D.group("x")), QQ(D.group("y"))
                        plot_points[p,w,r][m].add((x, y))
                        data_points[p,w,r].append((m, v % vmod, v, vmod, x, y))
    for (p,w,r),D in plot_points.items():
        mmax = max([m for m in args.m if m % p != 0])
        plotfile = PICS / f"{p}.{w}.{r}.{mmax}.png"
        G = Graphics()
        for m, pts in D.items():
            color = colors[m-1]
            G += points(pts, color=color)
        G.save(str(plotfile))
    for (p,w,r),L in data_points.items():
        mmax = max([m for m in args.m if m % p != 0])
        L.sort()
        datafile = PICS / f"{p}.{w}.{r}.{mmax}.points"
        with open(datafile, "w") as F:
            _ = F.write("[\n")
            for m, vv, v, vmod, x, y, m0 in L:
                _ = F.write(f"[{m},{v},{vmod},{x},{y},{m0}],\n")
            _ = F.write("]\n")
