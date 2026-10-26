"""Save bounded profile tables after running ProfileSummary on both recordings."""

from pathlib import Path
import collections, csv, shutil, sys

source, destination = (Path(value).resolve() for value in sys.argv[1:])
destination.mkdir(exist_ok=True)
shutil.copyfile(source/'metadata.json', destination/'metadata.json')

def read(path):
    with path.open() as stream:
        return list(csv.DictReader(stream))

def write(path, rows):
    with path.open('w', newline='') as stream:
        writer = csv.DictWriter(stream, fieldnames=list(rows[0]), lineterminator='\n')
        writer.writeheader()
        writer.writerows(rows)

categories = []
retained = {}
for phase in ('09','10'):
    data = source/('phase-'+phase)/'summary'
    output = destination/('phase-'+phase)
    output.mkdir(exist_ok=True)
    for name in ('events.csv','execution-threads.csv','allocation-categories.csv',
                 'execution-categories.csv','excluded-allocation-boundaries.csv',
                 'allocation-classes.csv','allocation-sites.csv','execution-sites.csv'):
        shutil.copyfile(data/name,output/name)
    # Keep the most prominent stacks reviewable; the helper regenerates all of them.
    for name, key in [('allocation-project-stacks.csv','weight_bytes'),
                      ('execution-project-stacks.csv','events')]:
        rows = sorted(read(data/name), key=lambda row:int(row[key]), reverse=True)
        write(output/('top-100-'+name), rows[:100])
    for kind, metric in [('execution','events'),('allocation','weight_bytes')]:
        rows = read(data/(kind+'-categories.csv'))
        total = sum(int(row[metric]) for row in rows)
        for row in rows:
            categories.append({'phase':phase,'kind':kind,'category':row['key'],
                               'events':row['events'],'weight_bytes':row['weight_bytes'],
                               'share_pct':100*int(row[metric])/total})
    # JFR buffers are not globally ordered. GC IDs order the two explicit full GCs.
    collections_rows = sorted([row for row in read(data/'collections.csv')
                               if row['cause']=='System.gc()'],key=lambda row:int(row['gc_id']))
    assert len(collections_rows) == 2
    write(output/'explicit-collections.csv',collections_rows)
    ids = [row['gc_id'] for row in collections_rows]
    counts = [collections.defaultdict(lambda:[0,0]),collections.defaultdict(lambda:[0,0])]
    for row in read(data/'class-counts.csv'):
        if row['gc_id'] in ids:
            value = counts[ids.index(row['gc_id'])][row['class']]
            value[0] += int(row['count'])
            value[1] += int(row['bytes'])
    kept = {}
    for name in counts[0].keys() | counts[1].keys():
        # Exclude filler arrays and unstable generated lambda class names.
        if not name.startswith('hkmc2.') or '$$Lambda' in name:
            continue
        held, released = counts[0][name], counts[1][name]
        kept[name] = (held[0]-released[0],held[1]-released[1])
    assert kept['hkmc2.CompilerCtx'][0] == 1
    retained[phase] = kept
write(destination/'categories.csv',categories)
classes = []
temporary = {'hkmc2.semantics.ResolutionWorkspace','hkmc2.semantics.ResolutionRetention',
             'hkmc2.semantics.ResolutionRetention$Uses'}
for name in sorted(retained['09'].keys() | retained['10'].keys() | temporary):
    before, after = retained['09'].get(name,(0,0)), retained['10'].get(name,(0,0))
    if before == (0,0) and after == (0,0) and name not in temporary:
        continue
    classes.append({'class':name,'before_count':before[0],'before_bytes':before[1],
                    'after_count':after[0],'after_bytes':after[1],
                    'delta_count':after[0]-before[0],'delta_bytes':after[1]-before[1]})
write(destination/'retained-compiler-classes.csv',classes)
