# Collect driver logs into a summary and a LaTeX table for Theorem tail:families.
import glob, re, json, os
rows = []; pertuple = []; pending = []; problems = []
fams = {(0, 1): ('cov01L7.json', 7), (1, 1): ('covIK_1_1.json', 7), (0, 2): ('covIK_0_2.json', 7)}
for fn in sorted(glob.glob('driver_*.log')):
    i, k = map(int, re.findall(r'driver_(\d+)_(\d+)', fn)[0])
    txt = open(fn).read()
    m = re.search(r'final l0 (\d+)', txt)
    ok = 'family ok' in txt
    chk = re.findall(r'check: .*?certificates verified (\d+).*OK', txt)
    if m and ok and chk:
        fams[(i, k)] = ('covIK_%d_%d.json' % (i, k), int(m.group(1)))
    else:
        problems.append((i, k, txt.strip().splitlines()[-1] if txt.strip() else 'no log'))
    for t in re.findall(r'tuple \((\d+), (\d+), (\d+)\) (.*)', txt):
        tt = tuple(map(int, t[:3])); good = t[3].rstrip().endswith('OK')
        (pertuple if good else problems).append(tt if good else (tt, t[3][-90:]))
    p = re.search(r'pending \(not run, l>10\): \[(.*?)\]', txt)
    if p and p.group(1).strip():
        pending += [(i, k, int(l)) for l in p.group(1).split(',')]
for (i, k), (fn, l0) in sorted(fams.items()):
    D = json.load(open(fn))
    rows.append((i, k, l0, len(D['certs'])))
print('families verified:', len(rows)); print(rows)
print('per-tuple verified:', sorted(pertuple))
print('pending per-tuple (l > 10):', pending)
print('problems:', problems)
L = ['\\begin{table}[ht]\\centering\\small', '\\begin{tabular}{rrrr@{\\qquad}rrrr@{\\qquad}rrrr}', '\\toprule',
     '\\((i,k)\\) & & \\(\\ell_0\\) & cones & \\((i,k)\\) & & \\(\\ell_0\\) & cones & \\((i,k)\\) & & \\(\\ell_0\\) & cones\\\\', '\\midrule']
cells = ['\\((%d,%d)\\) & & %d & %d' % r for r in rows]
while len(cells) % 3: cells.append('& & &')
for a in range(0, len(cells), 3):
    L.append(' & '.join(cells[a:a + 3]) + '\\\\')
L += ['\\bottomrule', '\\end{tabular}',
      '\\caption{Families of Theorem~\\ref{tail:families}: for each \\((i,k)\\), all \\(\\ell\\ge\\ell_0\\) are covered by the given number of certified cones. Residual tuples with \\(7\\le\\ell<\\ell_0\\) and \\(\\ell\\le10\\) were certified one by one (%d tuples).}\\label{tab:fam}' % len(pertuple),
      '\\end{table}']
open('famtable.tex', 'w').write('\n'.join(L) + '\n')
json.dump({'families': rows, 'pertuple': sorted(pertuple), 'pending': pending, 'problems': [str(p) for p in problems]},
          open('summary_phase1.json', 'w'), indent=1)
