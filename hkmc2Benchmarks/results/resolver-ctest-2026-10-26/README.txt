Resolver changes: deterministic full-ctest benchmark
2026-10-26

This follows up the narrow benchmark in ../resolver-retention-2026-10-26.
The previous experiment did warm each JVM (20 iterations per small workload),
but it did not measure allocated bytes. It excluded prelude/runtime setup and
JavaScript generation, and forced GC outside every timed sample. Those timings
were insufficient evidence about full builds or the GC consequences of retention.

Cumulative changes; parent columns compare each row with its predecessor.
Timing deltas of a few percent need the warmup/variation caveats below.
MiB = 1,048,576 bytes. comparison.png / comparison.svg plot baseline-relative changes.

Commit     Change                     Seconds  Parent Allocated MiB  Parent Retained MiB  Parent
8feafb6a1  Baseline                     5.162      --        8396.2      --        349.7      --
a5a0c7e9f  Reuse completion flag        5.225   +1.2%        8232.8   -1.9%        344.1   -1.6%
c0b3ced26  Remove shape-key interner    5.097   -2.5%        7958.6   -3.3%        341.0   -0.9%
c603ea83d  Reference scope tokens       5.081   -0.3%        7958.6    0.0%        341.0    0.0%
f0fcf2be3  Detach compiler callbacks    5.095   +0.3%        7959.6    0.0%        338.4   -0.8%
ae34c386e  Store source facts           5.110   +0.3%        7952.2   -0.1%        335.8   -0.8%
039bc5fab  Unify context values         5.129   +0.4%        7978.7   +0.3%        335.8    0.0%
206543e21  Detach one-shot observers    5.117   -0.2%        7978.6    0.0%        335.7    0.0%
391866a98  Own generated members        5.102   -0.3%        7952.4   -0.3%        335.7    0.0%
550a374e4  Release workspace            5.054   -0.9%        8142.0   +2.4%        315.3   -6.1%
f6cce3eca  Prune interface graph        6.595  +30.5%        9671.2  +18.8%        338.3   +7.3%

The pruning step increases elapsed time by 30.5%, allocated bytes by 18.8%,
and retained session heap by 7.3% relative to its parent. Relative to the
original baseline, the final build is 27.8% slower, allocates 15.2% more,
and retains 3.2% less session heap. Before pruning, retained heap was 9.8%
below baseline. These are costs/benefits on this corpus, not universal gains.

The three fork-mean timing ranges are 5.138-5.171 s at baseline,
5.034-5.059 s before pruning, and 6.577-6.598 s afterward. The regression
is much larger than that spread. All per-commit ranges, process CPU,
GC counters, JIT counters and within-fork drift are in summary.csv.

Two early changes clearly reduce allocation: completion-state reuse saves
1.9%, then removal of the shape-key interner saves 3.3%. Most other timing
changes are small. Workspace release reduces retained heap from 335.7 to
315.3 MiB, even though it allocates 2.4% more during compilation. Freeing
temporary data and recomputing it later can lower retention while increasing
total allocation; allocation and retained heap are different measurements.

Pruning adds 1.541 s per suite. The GC collection-time counter rises by
0.176 s and the JIT compilation-time counter by only 0.004 s. Those counters
do not explain most of the extra time. They do not rule out indirect JIT
effects such as different inlining or generated-code quality.

Measurement

Every case registered by CompileTestRunnerBase for the normal ctest directories
is run sequentially in sorted test-name order: 58 cases. The runner retains the
actual test bodies, per-case instances, timeouts, diagnostic checks, compiler
calls and output writes. 56 root files use the new resolver (nine strict), and
two use the legacy language version. Imports retain their own language settings.

Each full batch uses a fresh CompilerCtx, shared across all cases in that batch.
This includes prelude/runtime setup, parsing, elaboration and resolution,
lowering, optimization, artifact finalization, JavaScript generation and writes.
It also includes ScalaTest discovery/invocation overhead. Import results are
cached within a batch; no compiler result cache is reused between batches.
Operating-system file caches are warm. SBT startup and diff-test program
execution are outside the benchmark.

JVM flags:
  -Xms1g -Xmx1g -Xss8m -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -Xbatch

One compiler-test thread, serial GC and foreground JIT compilation. The JVM sees
one processor. This does not pin the process to a physical core: macOS still
chooses core placement. The CPU and wall measurements check the practical
concurrency of this configuration. It is a controlled sequential workload,
not a prediction of ordinary parallel SBT elapsed time.

Three fresh JVMs per revision, each running 12 full-suite warmups and eight
measured full-suite batches. Warmup values are saved, not discarded from the
raw data. Each shuffled round contains all eleven compiler revisions (seed 582),
with only one benchmark JVM running at once. This produced 396 full warmup batches
and 264 measured full batches. Each JVM also ran one final heap batch, whose
heap readings were later superseded as explained below. Own SBT processes were
stopped during collection.

The archived compiler builds are the same individually validated revisions
used in the earlier experiment. Each passed hkmc2AllTests/test. Only the main
compiler JAR changes between variants; shared test/harness classes are frozen
as JARs before collection. The script verifies the compiler JAR hashes, source
corpus hash and exact case order. metadata.json and runs.json record the
revisions, schedule, flags, hashes and completion records.

Statistics

For timing/allocation/GC/JIT columns, first average all eight measured batches
within each JVM, then report the median of the three JVM averages. Averaging
within a JVM includes the cost of occasional collections instead of hiding it
with a per-batch median. Report the range of JVM averages, not a confidence
interval. Parent percentages compare adjacent cumulative revisions, not the
change enabled alone on the original baseline. The measured batches within a
JVM are not independent experiments. Small effects require caution because
there are only three forks and some JIT work remains after warmup. The last four
measured batches were generally about 1-3% faster than the first four. Thus small
adjacent timing changes are descriptive, not established speedups. The large
pruning regression remains clear across all forks.

For scale, the median first full batch took 22.70 s on the baseline and 24.17 s
after pruning, versus 5.162 s and 6.595 s in the measured warmed batches. Fresh
JVM timings would obscure much of the difference. CPU time nearly equals wall
time in the warmed single-processor runs; both are recorded in samples.csv.

Memory counters mean different things:

* Allocated bytes: the change in JDK 21 ThreadMXBean.getTotalThreadAllocatedBytes,
  an approximate cumulative Java-heap allocation counter across all JVM threads,
  including allocations subsequently collected. It includes harness allocations.
* Retained session bytes: post-full-GC used heap with the completed CompilerCtx
  strongly reachable, minus post-full-GC used heap after dropping it. A weak
  reference must confirm that the context was collected. This is measured in a
  separate heap-only JVM, using collection snapshots and forced compaction as
  explained below. These JVMs do not contribute timing/allocation results.
* heap_used_after_bytes: a snapshot before any explicit GC; this includes garbage
  and is not the retained-heap measurement.

Corrected retained-heap measurement

The first sampler read current MemoryMXBean used heap immediately after an
explicit GC. This was not a reliable estimate of live objects: Serial GC can
leave dead filler space between full compactions, and allocations while polling
can reserve a fresh thread allocation buffer. A held reading differed by only
3,712 bytes between two matched runs, while the released reading differed by
15,727,224 bytes. Those readings are preserved in superseded-heap.csv for audit;
they are not used in summary.csv or any retained-heap comparison here.

HeapProbe.java reproduces both effects. With default Serial settings, its
released collection snapshot stayed near 21.99 million bytes for three GCs,
then fell to 1.37 million on the fourth. With full compaction every time, the
snapshot immediately settled near 1.37 million, while current heap polling
still reported about 7.03 million. The two probe CSV files preserve the output.

The replacement experiment runs three fresh JVMs per revision, each compiling
all 58 sorted ctest cases once into a shared fresh CompilerCtx. It adds
-XX:MarkSweepAlwaysCompactCount=1 and sums heap MemoryPoolMXBean.getCollectionUsage
snapshots, captured at the end of each full GC. The first GC holds the context
strongly reachable; after returning without a strong reference, the second GC
must clear a WeakReference to it. The difference is session_retained_bytes.
Heap JVMs run sequentially in the same shuffled schedule, without timing
warmups: they measure the footprint of one completed session, not throughput.
Their flags, harness revision and completion records are in heap-metadata.json
and heap-runs.json. retained-heap.csv contains all 33 corrected observations.
Timing forks and heap forks are different processes; matching fork numbers
only label independent repetitions. The reported heap value is their median.

The harness was corrected after the timing experiment: source still compiles
on JDK 17, while running the allocation counter requires JDK 21 or newer.
The timing data used harness commit 925bf62e6; the corrected heap data uses
9346582db. Compiler archives are identical between experiments. None of the
heap correction changes can affect the already-completed timing measurements.

No explicit GC occurs in the timed loop. GC count and collection milliseconds
come from the collector MXBeans; their collection-time counter is not an exact
pause-time trace. Process CPU time includes GC and JIT work. Native allocation,
JIT code-cache/metaspace footprint and RSS are not measured by heap allocation.
The fixed 1 GiB heap intentionally makes ordinary GC part of the comparison;
a different collector/heap size may change relative timing.

The retained-session measurement keeps the whole compiler cache alive. It does
not separately measure the benefit of a returned Artifact no longer keeping
compiler services or the entire CompilerCtx alive after the caller releases
that context. ResolverRetentionTest checks that lifetime boundary separately.
Nor does this corpus establish the benefit for arbitrarily many unused private
bodies: its bounded-growth test covers that distinct property. These limitations
do not negate an observed cost increase on ctest.

Diagnostic profiles

One additional JVM before pruning (550a374e4), and one after (f6cce3eca), reuse
the original frozen timing harness and its 12 warmup / eight measured / one
final heap batches. Their times are excluded from the benchmark aggregates.
Recording starts 60 seconds into each JVM, so it includes remaining warmups,
measured batches and finalization; it is not limited to measured intervals.

JFR uses the installed JDK 21 profile configuration with ObjectCountAfterGC
enabled, ObjectCountCutOffPercent=0 and stackdepth=256. Allocation weights are
sampled estimates, distinct from the main benchmark's cumulative allocation
counter. Execution samples describe the main Java thread, not GC or JIT CPU.
ProfileSummary.java identifies that thread by Java thread ID 1, because
ScalaTest can temporarily rename it; execution-threads.csv records the names.

The retained-class counts explain the memory increase particularly clearly:

Class                       Before count  After count  Additional bytes
Publisher.Listener                     0      767253          18414072
ResolutionContext                    130      180533           5772896

Their additional bytes total 23.0665 MiB, essentially the entire independently
measured 23.0665 MiB session-heap increase. The contexts still occupy 32 bytes
each; the increase comes from many more distinct objects. Retained Publisher.Data
objects barely change (110857 to 110849). Both recordings have zero retained
ResolutionWorkspace, ResolutionRetention and ResolutionRetention.Uses objects:
the temporary ownership tables are released, while listener wrappers and code
ownership contexts remain in the reusable graph. The source creates a new
forCode context when code ownership changes, despite equal inference identity,
and stores a Listener around the existing callback closure.

In the post-pruning profile, of 2068 main-thread execution samples:
* 289 (14.0%) contain retention-bookkeeping frames outside finalization;
* 41 (2.0%) contain finalization/reachability frames;
* 14 (0.7%) contain forCode without either preceding category;
* 15 (0.7%) contain other graph/context rebasing frames.

The allocation-weight shares are 8.6% for retention bookkeeping, 2.9% for
forCode and 0.3% for finalization. One prominent new allocation path is
DeclaredType.Observation.sameValue under ResolutionRetention.entry/use,
called from Cache.lookup. Cache lookup has already compared its key; the
separate retention map repeats structural comparisons and allocates again.
The final sweep is a smaller directly observed cost than bookkeeping performed
throughout inference. These observations support the source-level explanation,
but are not an exact decomposition of the 30.5% elapsed-time regression.

Even at stackdepth=256, 1180/1393 before-pruning and 1766/2068 after-pruning
execution traces are truncated (84.7% and 85.4%). Allocation traces are also
often truncated. Missing outer frames can hide additional callers; the
category shares describe observed paths. Total allocation counters and the
post-GC class counts do not depend on complete stack traces.

The first allocation sample on each thread is excluded from attribution. Its
weight can include allocations made before the delayed recording began:
the main-thread boundary weights were 60,973,772,960 and 56,397,353,568 bytes.
Attributing those to the first sampled allocation site would badly distort
the profile. excluded-allocation-boundaries.csv preserves these events, and
the helper finds their timestamps in a first pass rather than assuming JFR
file order is chronological. This follows the counter difference used by
JfrObjectAllocationSample::send_allocation_sample in OpenJDK 21.

The concrete simplification targets are:

1. Keep temporary usage information with cache entries and publisher data,
   and register it once for finalization. Reuse the entry already found by
   inference instead of looking up (context, key) again in parallel ownership
   maps. This should remove duplicate hashing/equality work and tracking keys.
2. Separate code ownership from the shared graph/substitution identity. Reuse
   canonical graph contexts when only the current body changes, instead of
   allocating and retaining a fresh forCode context at callback boundaries.
3. Make the listener record carry its origin, code and callback directly, so
   ownership replaces an existing closure layer instead of adding a wrapper
   around it. Preserve the intermediate-exporter graph rebasing required by
   imported callbacks.

These are proposed refactorings, not measured fixes. Evaluate each separately
with the full-suite benchmark and preserve importer-isolation, retention and
bounded-growth regressions. The current pruning implementation should not be
presented as a general performance improvement on the evidence above.

profiles/categories.csv, profiles/retained-compiler-classes.csv and per-phase
allocation/execution tables contain the observations. The stack tables keep
the top 100 entries for review; ProfileSummary regenerates the complete tables.
The broad corpus comparison and the lifetime/growth regressions are both
needed: neither one substitutes for the other.

Categories use inclusive stacks and this disjoint priority: finalization
(ResolutionReachability, NewResolverState.finish or ResolutionRetention
close/finish/retained), other retention bookkeeping, forCode, other graph/context
rebasing, then other. They identify direct paths, not all indirect costs of
allocation, hashing, equality, inlining or GC. The before/after class counts
come from the final two explicit GCs, with the context held and then released.
The old profile harness uses normal compaction frequency: filler arrays can
remain, so only real named compiler classes are used to explain retention.
Its current-heap readings are not used as live-heap estimates.

Reproduce these diagnostic recordings while the original timing directory and
its frozen JARs are available:
  python3 profile.py '<repository>' '<original-timing-directory>' '<new-profile-directory>'
  javac -d /tmp/ctest-profile-tools ProfileSummary.java
  java -cp /tmp/ctest-profile-tools ProfileSummary '<recording.jfr>' '<summary-directory>'
  python3 profile_tables.py '<profile-directory>' '<new-tables-directory>'

Use JDK 21 for these tools. profile.py records commands, the configuration hash,
Java settings and recording hashes. Its historical five-argument harness is
925bf62e6; the current six-argument harness has the separate heap modes described
below. Main samples.csv and summary.csv never include profiled runs.

Reproduction

Compile the benchmark and obtain its test classpath:
  sbt 'hkmc2AllTests/test' 'export hkmc2Benchmarks / Test / fullClasspath'

Single selected build:
  java -Xms1g -Xmx1g -Xss8m -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -Xbatch \
    -cp '<exported classpath>' hkmc2.ResolverSuiteBenchmark \
    <revision> <fork> 12 8 0 /tmp/new-ctest-results

For a separate heap-only measurement, add -XX:MarkSweepAlwaysCompactCount=1
and use arguments: <revision> <fork> 0 0 1 /tmp/new-heap-results.

For the shuffled comparison, archive each selected revision's validated
hkmc2 JVM main classes as phase-XX.jar. Put their records in builds.json
(using the builds array in metadata.json), and the common exported classpath
in classpath.txt. The common classes must include the benchmark harness.
Then run the repository's runner with a new output directory:
  python3 hkmc2Benchmarks/bench_resolver_suite.py timing \
    '<repository>' '<build-directory>' '<new-output-directory>'

Repeat with mode heap and another new output directory for retained memory.
Run summarize.py in this results directory with its directory as the argument
to regenerate summary.csv and forks.csv from the checked-in raw samples.

The runner freezes common class directories and rejects changes to tracked
MLscript sources during collection. The generated run logs verify every case
passed and the sorted case order repeated for every batch. Large compiler JARs
and raw JFR recordings are working artifacts, not checked into the repository.

Validation

Every archived compiler revision had passed hkmc2AllTests/test before its build
was archived. The new full-suite harness passed that command before timing
collection. The JDK portability fix passed the full suite on JDK 17 (89 s),
and its runtime guard was checked there. The heap correction passed the full
suite in a fresh JDK 21 process (78 s) and a 58-case sampler smoke run. One
repeated validation in the earlier JDK 17 SBT process hit the existing 25-second
timeout in FingerTreeList, FingerTreeList_StressTest and LazyFingerTree; no
compiler or timeout settings were changed. All benchmark JVMs must pass every
case and the manifest/order assertions. No golden test output changed.

References for counter, collector and VM-option semantics:
https://docs.oracle.com/en/java/javase/21/docs/api/jdk.management/com/sun/management/ThreadMXBean.html
https://docs.oracle.com/en/java/javase/21/docs/specs/man/java.html
https://docs.oracle.com/en/java/javase/21/docs/api/java.management/java/lang/management/MemoryPoolMXBean.html
https://raw.githubusercontent.com/openjdk/jdk21u/master/src/hotspot/share/gc/shared/space.inline.hpp
https://raw.githubusercontent.com/openjdk/jdk21u/master/src/hotspot/share/jfr/support/jfrObjectAllocationSample.cpp
