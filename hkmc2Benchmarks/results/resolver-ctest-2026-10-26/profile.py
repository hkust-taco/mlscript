"""Profile phases 09 and 10 using the frozen harness of the original timing run.

The timing directory must still contain its common class JARs, and the compiler
build directory named in its metadata must still contain classpath.txt and JARs.
This reproduces the five-argument harness at 925bf62e6, including its final heap
batch. Its current-heap readings are superseded; use JFR's real class counts.
"""

from pathlib import Path
import hashlib, json, re, subprocess, sys

if len(sys.argv) != 4:
    raise SystemExit('Usage: profile.py <repository> <original-timing-directory> <new-output-directory>')
root, timed, output = (Path(value).resolve() for value in sys.argv[1:])
assert json.loads((timed/'progress.json').read_text())['status'] == 'complete'
metadata = json.loads((timed/'metadata.json').read_text())
assert metadata['harness_revision'].startswith('925bf62e6')
archive = Path(metadata['builds'][0]['jar']).parent
entries = (archive/'classpath.txt').read_text().strip().split(':')
main_index = entries.index(str(root/'hkmc2/jvm/target/scala-3.8.4/classes'))
for common in metadata['common_archives']:
    path = timed/common['file']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == common['sha256']
    entries[common['classpath_index']] = str(path)
output.mkdir(parents=True, exist_ok=False)
settings = subprocess.run(['java','-XshowSettings:properties','-version'],text=True,capture_output=True,check=True).stderr
java_home = Path(re.search(r'^\s*java.home = (.+)$', settings, re.MULTILINE).group(1))
config = (java_home/'lib/jfr/profile.jfc').read_text()
config, changed = re.subn(r'(<event name="jdk.ObjectCountAfterGC">\s*<setting name="enabled">)false',r'\g<1>true',config)
assert changed == 1
configuration = output/'profile-heap.jfc'
configuration.write_text(config)
records = []
for phase in ['09','10']:
    build = next(b for b in metadata['builds'] if b['phase'] == phase)
    assert hashlib.sha256(Path(build['jar']).read_bytes()).hexdigest() == build['sha256']
    destination = output/('phase-'+phase)
    destination.mkdir()
    cp = list(entries)
    cp[main_index] = build['jar']
    recording = destination/'recording.jfr'
    flags = metadata['jvm_flags'] + ['-XX:+UnlockExperimentalVMOptions','-XX:ObjectCountCutOffPercent=0','-XX:FlightRecorderOptions=stackdepth=256',f'-XX:StartFlightRecording=name=resolver,filename={recording},settings={configuration},delay=60s,dumponexit=true']
    command = ['java',*flags,'-cp',':'.join(cp),'hkmc2.ResolverSuiteBenchmark',build['revision'],'profile','12','8',str(destination)]
    print('PROFILE',phase,flush=True)
    with (destination/'run.log').open('w') as log:
        result = subprocess.run(command,cwd=root,stdout=log,stderr=subprocess.STDOUT)
    assert result.returncode == 0, phase
    manifest = (timed/'ctest-manifest.txt').read_text().splitlines()
    actual = [line.removeprefix('Compiling: ') for line in (destination/'run.log').read_text().splitlines() if line.startswith('Compiling: ')]
    assert actual == manifest*21
    records.append({'phase':phase,'command':command,'jfr_sha256':hashlib.sha256(recording.read_bytes()).hexdigest()})
    (output/'metadata.json').write_text(json.dumps({'java_settings':settings,'configuration_sha256':hashlib.sha256(configuration.read_bytes()).hexdigest(),'runs':records},indent=2)+'\n')
    print('PROFILE DONE',phase,flush=True)
