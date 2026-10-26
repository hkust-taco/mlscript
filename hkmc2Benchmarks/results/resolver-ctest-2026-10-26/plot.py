"""Plot summary.csv; requires Matplotlib. Run after summarize.py."""

from pathlib import Path
import csv
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

directory = Path(__file__).resolve().parent
rows = list(csv.DictReader((directory/'summary.csv').open()))
assert len(rows) == 11 and all(int(row['forks']) == 3 for row in rows)
labels = ['Baseline','Completion','Shape keys','Ref. scope','Callbacks','Source facts',
          'Contexts','Observers','Generated','Workspace','Pruning']
fig, ax = plt.subplots(figsize=(11, 6.2))
colors = ['#2066A8', '#D36B16', '#238163']
metrics = [('wall_ms','Elapsed time'),('allocated_bytes','Allocated heap'),
           ('session_retained_bytes','Retained session heap')]
for (metric, label), color in zip(metrics, colors):
    baseline = float(rows[0][metric])
    values = [100*(float(row[metric])/baseline-1) for row in rows]
    low = [100*(float(row[metric+'_min'])/baseline-1) for row in rows]
    high = [100*(float(row[metric+'_max'])/baseline-1) for row in rows]
    errors = [[value-bound for value,bound in zip(values,low)],
              [bound-value for value,bound in zip(values,high)]]
    ax.errorbar(range(11), values, yerr=errors, color=color, marker='o',
                linewidth=2, markersize=4.5, capsize=3, label=label)
    ax.annotate(f'{values[-1]:+.1f}%', (10,values[-1]), xytext=(9,0),
                textcoords='offset points', color=color, va='center', fontweight='bold')
ax.axhline(0, color='#888888', linewidth=0.8, linestyle='--')
ax.set_xticks(range(11), [f'{i:02d} {label}' for i,label in enumerate(labels)],
              rotation=32, ha='right')
ax.set_xlim(-0.25,11)
ax.set_ylim(-12,32)
ax.set_ylabel('Change from baseline (%)')
ax.grid(axis='y', alpha=0.2)
ax.spines[['top','right']].set_visible(False)
ax.legend(loc='upper left', frameon=False)
fig.suptitle('Resolver changes across the full ctest suite', x=0.08, ha='left',
             fontsize=17, fontweight='bold')
ax.set_title('58 cases · sorted and sequential · one JVM processor · three forks',
             loc='left', fontsize=10, color='#555555', pad=16)
fig.text(0.08,0.025,
         'Cumulative revisions. Whiskers show fork ranges, not confidence intervals.\n'
         'Timing/allocation: median of fork means. Retained heap: separate compacting-GC runs.',
         fontsize=9, color='#555555')
fig.subplots_adjust(left=0.08,right=0.98,bottom=0.23,top=0.83)
fig.savefig(directory/'comparison.png', dpi=170)
fig.savefig(directory/'comparison.svg')
# Newlines already separate SVG path commands; trim Matplotlib's redundant
# trailing spaces without changing indentation or the rendered geometry.
svg = directory/'comparison.svg'
svg.write_text('\n'.join(line.rstrip(' ') if line.strip() else line
                         for line in svg.read_text().splitlines())+'\n')
