"""Run archived compiler builds sequentially; see results for the build manifest.

The build directory contains builds.json, phase-XX.jar and the exported benchmark
Test classpath in classpath.txt. The output directory must not already exist.
"""

from pathlib import Path
import datetime, hashlib, json, platform, random, subprocess, sys, time, zipfile

if len(sys.argv) != 4:
    raise SystemExit('Usage: bench_resolver_suite.py <repository> <build-directory> <output-directory>')
root, archive, output = (Path(value).resolve() for value in sys.argv[1:])
output.mkdir(exist_ok=False)
flags = ['-Xms1g', '-Xmx1g', '-Xss8m', '-XX:ActiveProcessorCount=1', '-XX:+UseSerialGC', '-Xbatch']
warmups, samples, forks = 12, 8, 3
builds = json.loads((archive / 'builds.json').read_text())
entries = (archive / 'classpath.txt').read_text().strip().split(':')
main = str(root / 'hkmc2/jvm/target/scala-3.8.4/classes')
assert entries.count(main) == 1
main_index = entries.index(main)
# Freeze the shared harness and test classes as well as the per-revision compiler.
# A later local compilation must not change classes midway through the experiment.
common_archives = []
for i, value in enumerate(entries):
    directory = Path(value)
    if i == main_index or not directory.is_dir():
        continue
    archive_path = output / f'common-{i:02d}.jar'
    with zipfile.ZipFile(archive_path,'w',zipfile.ZIP_DEFLATED) as jar:
        for file in sorted(directory.rglob('*')):
            if file.is_file(): jar.write(file,file.relative_to(directory).as_posix())
    entries[i] = str(archive_path)
    common_archives.append({'classpath_index':i,'source':value,'file':archive_path.name,'sha256':hashlib.sha256(archive_path.read_bytes()).hexdigest()})
# Generated JavaScript is rewritten by each suite; only source inputs are hashed.
source_paths = sorted(p for p in subprocess.check_output(['git','ls-files','-z'],cwd=root).split(b'\0') if p.endswith(b'.mls'))
def corpus_hash():
    digest = hashlib.sha256()
    for path in source_paths:
        digest.update(path+b'\0')
        digest.update((root/path.decode()).read_bytes())
    return digest.hexdigest()
source_hash = corpus_hash()
for build in builds:
    build['jar'] = str(archive / f"phase-{build['phase']}.jar")
    assert hashlib.sha256(Path(build['jar']).read_bytes()).hexdigest() == build['sha256']
rng = random.Random(582)
schedule = []
for fork in range(forks):
    order = list(range(len(builds)))
    rng.shuffle(order)
    schedule.extend({'fork':fork, 'build_index':i, 'phase':builds[i]['phase']} for i in order)
metadata = {
    'created':datetime.datetime.now().astimezone().isoformat(),
    'harness_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    'jvm':subprocess.run(['java','-version'],text=True,capture_output=True).stderr.strip(),
    'platform':platform.platform(), 'jvm_flags':flags, 'warmups':warmups, 'samples':samples,
    'forks':forks, 'test_order':'sorted names, sequential ScalaTest run without Distributor',
    'active_processors':1, 'physical_cpu_affinity':'not pinned; macOS scheduler controls core placement',
    'background_jit':False, 'suite':'every hkmc2.CompileTestRunner case, fresh CompilerCtx per batch',
    'builds':builds, 'schedule':schedule, 'common_archives':common_archives, 'mls_corpus_sha256':source_hash,
    'allocation_api':'com.sun.management.ThreadMXBean.getTotalThreadAllocatedBytes (all JVM threads)',
    'heap_method':'full GC with context held, full GC after context release, weak-reference check',
    'measurement_gc':'natural; explicit GC only in the separate final retained-heap batch',
}
(output / 'metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
records = []
for index, entry in enumerate(schedule):
    assert corpus_hash() == source_hash, 'MLscript corpus changed during benchmarking'
    build = builds[entry['build_index']]
    cp = list(entries)
    cp[main_index] = build['jar']
    command = ['java',*flags,'-cp',':'.join(cp),'hkmc2.ResolverSuiteBenchmark',build['revision'],str(entry['fork']),str(warmups),str(samples),str(output)]
    name = f"{index:02d}-phase-{build['phase']}-fork-{entry['fork']}"
    started = time.monotonic()
    start_time = datetime.datetime.now().astimezone().isoformat()
    print('START',name,build['label'],flush=True)
    with (output/(name+'.log')).open('w') as log:
        result = subprocess.run(command,cwd=root,stdout=log,stderr=subprocess.STDOUT)
    elapsed = time.monotonic()-started
    assert result.returncode == 0, (name,result.returncode)
    manifest = (output/'ctest-manifest.txt').read_text().splitlines()
    actual = [line.removeprefix('Compiling: ') for line in (output/(name+'.log')).read_text().splitlines() if line.startswith('Compiling: ')]
    assert actual == manifest*(warmups+samples+1), (name,'test ordering or corpus mismatch')
    records.append(dict(entry,name=name,started=start_time,elapsed_seconds=elapsed,returncode=result.returncode))
    (output/'runs.json').write_text(json.dumps(records,indent=2)+'\n')
    (output/'progress.json').write_text(json.dumps({'status':'benchmarking','completed':len(records),'total':len(schedule),'last':name},indent=2)+'\n')
    print('DONE',name,round(elapsed,1),'seconds',flush=True)
print('COMPLETE',len(records),'JVM runs',flush=True)
(output/'progress.json').write_text(json.dumps({'status':'complete','completed':len(records),'total':len(schedule)},indent=2)+'\n')
