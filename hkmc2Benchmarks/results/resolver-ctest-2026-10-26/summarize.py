from pathlib import Path
import csv, json, statistics as st
import sys
p=Path(sys.argv[1])
meta=json.loads((p/'metadata.json').read_text())
rows=list(csv.DictReader((p/'samples.csv').open()))
heap_path = Path(sys.argv[2]) if len(sys.argv) > 2 else p/'retained-heap.csv'
heaps=list(csv.DictReader(heap_path.open()))
metrics=['wall_ms','process_cpu_ms','allocated_bytes','gc_count','gc_ms','jit_ms','heap_used_after_bytes']
forks=[]
summary=[]
for build in meta['builds']:
    rev=build['revision']
    active=[]
    for fork in range(meta['forks']):
        measured=[r for r in rows if r['revision']==rev and int(r['fork'])==fork and r['phase']=='measured']
        heap=[r for r in heaps if r['revision']==rev and int(r['fork'])==fork]
        assert len(measured)==meta['samples'] and len(heap)==1, (build['phase'],fork,'incomplete observations')
        data={'phase':build['phase'],'revision':rev,'label':build['label'],'fork':fork,'samples':len(measured)}
        data.update({m:st.mean(float(r[m]) for r in measured) for m in metrics})
        data['wall_median_ms']=st.median(float(r['wall_ms']) for r in measured)
        data['session_retained_bytes']=int(heap[0]['session_retained_bytes'])
        data['held_after_gc_bytes']=int(heap[0]['held_after_gc_bytes'])
        data['released_after_gc_bytes']=int(heap[0]['released_after_gc_bytes'])
        split=len(measured)//2
        data['late_vs_early_wall_pct']=100*(st.mean(float(r['wall_ms']) for r in measured[split:])/st.mean(float(r['wall_ms']) for r in measured[:split])-1)
        forks.append(data)
        active.append(data)
    if not active: continue
    s={'phase':build['phase'],'revision':rev,'label':build['label'],'forks':len(active)}
    for m in metrics+['session_retained_bytes','held_after_gc_bytes','released_after_gc_bytes','late_vs_early_wall_pct']:
        s[m]=st.median(r[m] for r in active)
        s[m+'_min']=min(r[m] for r in active)
        s[m+'_max']=max(r[m] for r in active)
    for m in ['wall_ms','process_cpu_ms','allocated_bytes','session_retained_bytes']:
        previous=next((row for row in summary if int(row['phase'])==int(build['phase'])-1),None)
        baseline=next((row for row in summary if row['phase']=='00'),None)
        s[m+'_parent_pct']=100*(s[m]/previous[m]-1) if previous else ''
        s[m+'_baseline_pct']=100*(s[m]/baseline[m]-1) if baseline else ''
    summary.append(s)
for filename,data in [('forks.csv',forks),('summary.csv',summary)]:
    if not data: continue
    if filename == 'forks.csv':
        data = [{k:v for k,v in row.items() if k not in ('session_retained_bytes','held_after_gc_bytes','released_after_gc_bytes')} for row in data]
    with (p/filename).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(data[0]),lineterminator='\n')
        w.writeheader(); w.writerows(data)
print('Phase Forks Wall(s) CPU(s) Alloc(MiB) Retained(MiB) GC(ms) JIT(ms) Label')
for s in summary:
    print(s['phase'],s['forks'],f"{s['wall_ms']/1000:.3f}",f"{s['process_cpu_ms']/1000:.3f}",f"{s['allocated_bytes']/2**20:.1f}",f"{s['session_retained_bytes']/2**20:.1f}",f"{s['gc_ms']:.0f}",f"{s['jit_ms']:.0f}",s['label'])
