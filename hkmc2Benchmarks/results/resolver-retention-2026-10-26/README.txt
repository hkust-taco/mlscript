Resolver retention: per-commit compiler timing
2026-10-26

The history contains ten resolver improvements. Each passed hkmc2AllTests/test
before being committed, with its corresponding regression tests and golden
outputs. The final compiler and regression-test files are identical to the
original combined commit 89e8ffddf. The guideline update, benchmark harness, and
benchmark results have separate commits.

Baseline 8feafb6a1 has the same compiler code as fea7071d2; it adds the benchmark
harness after the guideline-only commit. Each subsequent measurement is a
cumulative build. Its change relative to the preceding build isolates that
commit in the context of its prerequisites, rather than enabling the change
alone on the original baseline.

Measured median wall time (ms), followed by change versus preceding build.
Negative changes mean less time. Small differences may be run-to-run noise.

Phase / commit   Change                                   Finger tree    Generic imports     Private bodies
00 / 8feafb6a1   Baseline                                      892.49              10.45              48.86
01 / a5a0c7e9f   Reuse completion flag                 862.35 (-3.4%)      10.53 (+0.8%)      49.18 (+0.7%)
02 / c0b3ced26   Remove shape-key interner             807.91 (-6.3%)      10.21 (-3.0%)      48.02 (-2.4%)
03 / c603ea83d   Use reference scope tokens            809.50 (+0.2%)      10.50 (+2.8%)      48.99 (+2.0%)
04 / f0fcf2be3   Detach compilation callbacks          809.04 (-0.1%)      10.52 (+0.2%)      48.23 (-1.6%)
05 / ae34c386e   Store source metadata                 805.13 (-0.5%)      10.56 (+0.4%)      48.25 (+0.0%)
06 / 039bc5fab   Unify context representation          797.53 (-0.9%)      10.35 (-2.0%)      48.68 (+0.9%)
07 / 206543e21   Cancel one-shot observers             844.04 (+5.8%)      10.31 (-0.4%)      48.32 (-0.8%)
08 / 391866a98   Own generated members in consumer     817.14 (-3.2%)      10.38 (+0.6%)      48.06 (-0.5%)
09 / 550a374e4   Release workspace                     820.54 (+0.4%)      10.49 (+1.1%)      48.39 (+0.7%)
10 / f6cce3eca   Prune unreachable inference         1130.63 (+37.8%)     11.55 (+10.1%)     54.74 (+13.1%)

Final build versus baseline: finger-tree +26.7%; generic-imports +10.5%; private-bodies +12.0%.
Pruning versus the preceding build: finger-tree +37.8%; generic-imports +10.1%; private-bodies +13.1%.
These are compilation-time changes; retention benefits are not inferred from timing.

Method

Apple M5 Max, 18 logical CPUs, 36 GiB RAM; macOS 26.7.1 ARM64.
Java HotSpot 21.0.8+12-LTS-250; Scala 3.8.4.
JVM flags: -Xms512m -Xmx4g -XX:+UseG1GC.

Three fresh JVMs per revision. Each performs 20 warmup iterations and then 10
measured iterations of each workload, for 30 measurements per revision/workload
and 990 measured workload runs in total. Workload order rotates within each JVM.
Each round contains every revision in a shuffled order (Python Random seed 582).
Only one benchmark JVM runs at a time. SBT is shut down during the measurements.

The main compiler classes from each passing build were archived in a JAR.
Every benchmark process used the same test harness and dependency classpath,
replacing only the main compiler classes with that revision's JAR. This avoids
Scala compilation during measurement and permits shuffled revision order.
metadata.json records the schedule, revisions, JVM settings and build hashes.

Each sample uses a fresh CompilerCtx. Prelude and runtime compilation occur
outside the timed interval. A full GC runs before setup, also outside the timer.
The timed operation is uncached getElaboratedBlock, including parsing,
elaboration/resolution, lowering, optimization and artifact finalization. It
includes source-file reads, with warm operating-system filesystem caches.
Returned artifacts stay strongly reachable until the next sample.

Workloads

finger-tree: compile the existing FingerTreeList.mls library and its dependencies.
generic-imports: compile twelve consumers of a precompiled generic library. Each
consumer defines a class and uses generic identity and tuple/record producers.
private-bodies: compile a module containing 200 unused private generic functions,
each with a nested generic tuple/record producer, plus one exported function.

Reading the results

The tables report median wall time, with negative percentage changes meaning
less time (faster). Percentages compare medians, not the median of paired ratios.
summary.csv also includes quartiles, each JVM's median, thread CPU time, and
changes relative to the baseline. samples.csv contains every measured value.
JVM forks are the independent repetitions; the samples within one fork share
JIT state. Small changes overlapping run-to-run variation are inconclusive.

These timings do not measure JavaScript execution, cached rebuilds, or memory
retained by a long-lived compilation session. Explicit GC between fresh contexts
also excludes much of the downstream GC benefit of releasing retained state.
Retention and bounded-growth properties are covered by ResolverRetentionTest.
The timing results describe these three compiler workloads on this machine.

Reproduction

From the repository root at a selected revision, compile and obtain the
benchmark classpath:

  sbt 'hkmc2AllTests/test' 'export hkmc2Benchmarks / Test / fullClasspath'

Then use the exported classpath in a separate JVM (not SBT's runMain JVM):

  java -Xms512m -Xmx4g -XX:+UseG1GC -cp '<exported classpath>' \
    hkmc2.ResolverRetentionBenchmark <revision> <fork> 20 10 /tmp/samples.csv

Use fork values 0, 1 and 2 and a fresh output file for a new experiment. To
reproduce the shuffled schedule without compiling concurrently, archive each
revision's hkmc2/jvm/target/scala-3.8.4/classes as a JAR after validation, then
replace that directory entry in the shared classpath with the selected JAR.
The benchmark harness is unchanged across all measured revisions.

Focused diagnostic profiles

One additional JVM run before pruning (550a374e4) and one after (f6cce3eca),
using the same harness, workload counts and heap settings. Profiled timings
are excluded from samples.csv and every timing comparison above.

Extra JVM option:
  -XX:StartFlightRecording=filename=<file.jfr>,settings=profile,delay=10s,dumponexit=true

Export with the JDK's jfr command:
  jfr print --events jdk.ExecutionSample --json <file.jfr>

The profiles contain 785 and 1131 main-thread execution samples respectively.
They cover the whole benchmark loop after the first ten seconds, including
untimed setup and remaining warmup iterations. Most deep inference stacks were
truncated at the default stack depth (724 before; 1013 after).
These are coarse diagnostic samples, not an attribution of the entire measured
regression or exact percentages of timed compilation.

After pruning, 76 samples (6.7%) contain retention-bookkeeping frames outside
finalization; 8 (0.7%) contain finalization/reachability frames; and
7 (0.6%) contain forCode without either preceding category. The remaining
samples are ordinary inference, compiler work and runtime operations. These
figures do not account for indirect costs such as extra hashing/equality,
allocation, changed inlining or GC. profile-summary.csv records the counts.

Classification is disjoint and uses this priority: any ResolutionReachability
frame, NewResolverState.finish, or ResolutionRetention.close/finish/retained
means finalization; otherwise any ResolutionRetention frame means bookkeeping;
otherwise ResolutionContext.forCode means code ownership; otherwise other.

The final sweep is not the prominent directly visible new cost in this profile.
Useful follow-up experiments are to integrate temporary usage metadata with
cache/host entries instead of repeating lookups in parallel tracking maps, and
to reuse inference-context identities when only code ownership changes. These
are optimization candidates, not fixes established by these measurements;
the full slowdown is not yet explained. Preserve the retention and growth tests
when evaluating them. No additional compiler changes were made during profiling.
